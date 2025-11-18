import type { SemanticTokensLegend } from 'vscode';

import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  State
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;
const TOOLCHAIN_CONFIG_KEY = "toolchainPath";
let pendingToolchainPath: string | undefined;
let configListener: vscode.Disposable | undefined;
let stateListener: vscode.Disposable | undefined;

const resolveToolchainPath = (): string =>
  vscode.workspace.getConfiguration("ray").get<string>(TOOLCHAIN_CONFIG_KEY, "");

const flushPendingToolchainPath = () => {
  if (!client || pendingToolchainPath === undefined || !client.isRunning()) {
    return;
  }

  client.sendNotification("workspace/didChangeConfiguration", {
    toolchainPath: pendingToolchainPath
  });
  pendingToolchainPath = undefined;
};

const queueToolchainPathNotification = (nextPath: string) => {
  pendingToolchainPath = nextPath;
  flushPendingToolchainPath();
};

const disposeListeners = () => {
  configListener?.dispose();
  configListener = undefined;
  stateListener?.dispose();
  stateListener = undefined;
  pendingToolchainPath = undefined;
};

export function activate(context: vscode.ExtensionContext) {
  const outputChannel = vscode.window.createOutputChannel("Ray LSP");
  const log = (message: string) => {
    const timestamp = new Date().toISOString();
    outputChannel.appendLine(`[${timestamp}] ${message}`);
  };

  startLanguageClient(context, outputChannel, log);

  const restartCommand = vscode.commands.registerCommand("ray-lsp.restartServer", async () => {
    log("Restarting Ray LSP...");
    await restartLanguageClient(context, outputChannel, log);
  });
  context.subscriptions.push(restartCommand);
}

async function restartLanguageClient(
  context: vscode.ExtensionContext,
  outputChannel: vscode.OutputChannel,
  log: (message: string) => void
) {
  if (client) {
    await client.stop();
    client = undefined;
  }
  disposeListeners();
  startLanguageClient(context, outputChannel, log);
}

function startLanguageClient(
  context: vscode.ExtensionContext,
  outputChannel: vscode.OutputChannel,
  log: (message: string) => void
) {
  const root = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath ?? context.extensionUri.fsPath;

  const serverCommand =
    process.env.RAY_LSP_COMMAND ||
    vscode.workspace.getConfiguration("ray").get<string>("cliPath") ||
    "ray";

  const extraArgs = vscode.workspace.getConfiguration("ray").get<string[]>("serverArgs") ?? [];

  const serverArgs = process.env.RAY_LSP_ARGS
    ? JSON.parse(process.env.RAY_LSP_ARGS)
    : ["lsp", ...extraArgs];

  const toolchainPath = resolveToolchainPath();
  const extraEnv = vscode.workspace.getConfiguration("ray").get<Record<string, string>>("extraEnv") ?? {};
  const baseEnv: NodeJS.ProcessEnv = {
    ...process.env,
    RAY_PATH: toolchainPath,
    ...extraEnv,
  };
  const serverOptions: ServerOptions = {
    run: {
      command: serverCommand,
      args: serverArgs,
      options: { cwd: root, env: baseEnv }
    },
    debug: {
      command: serverCommand,
      args: serverArgs,
      options: { cwd: root, env: baseEnv }
    }
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "ray" }],
    outputChannel,
    initializationOptions: { toolchainPath },
    middleware: {
      async provideDocumentSemanticTokens(doc, cancel, next) {
        const res = await next(doc, cancel);
        if (res?.data && res.data instanceof Uint32Array) {
          // Pull the legend advertised by the server during initialize
          const legend =
            languageClient.initializeResult?.capabilities.semanticTokensProvider?.legend ??
            { tokenTypes: [], tokenModifiers: [] };
          const dump = dumpClientTokens(
            res.data as Uint32Array,
            legend,
            ln => doc.lineAt(ln).text
          );
          outputChannel.appendLine('[client] semantic tokens (full)');
          outputChannel.appendLine(dump);
        }
        return res;
      },
      async provideDocumentRangeSemanticTokens(doc, range, cancel, next) {
        const res = await next(doc, range, cancel);
        const data = res?.data ?? [];
        client?.outputChannel.appendLine(`[client] range semTokens ${doc.uri} -> ${data.length} ints`);
        client?.outputChannel.appendLine(JSON.stringify(data));
        return res;
      },
    }
  };

  log(`Starting Ray LSP with command: ${serverCommand} ${serverArgs.join(" ")}`);
  log(`Working directory: ${root}`);
  if (toolchainPath) {
    log(`Using toolchain path: ${toolchainPath}`);
  } else {
    log("No toolchain path configured.");
  }

  const languageClient = new LanguageClient("ray-lsp", "Ray Language Server", serverOptions, clientOptions);
  languageClient
    .start()
    .then(() => log("Language client started."))
    .catch(err => {
      log(`Failed to start language client: ${err instanceof Error ? err.stack ?? err.message : String(err)}`);
      outputChannel.show(true);
    });
  context.subscriptions.push(languageClient);

  client = languageClient;

  configListener = vscode.workspace.onDidChangeConfiguration(event => {
    if (!event.affectsConfiguration(`ray.${TOOLCHAIN_CONFIG_KEY}`)) {
      return;
    }
    const updatedToolchainPath = resolveToolchainPath();
    queueToolchainPathNotification(updatedToolchainPath);
  });
  context.subscriptions.push(configListener);

  stateListener = languageClient.onDidChangeState(({ newState }) => {
    if (newState === State.Running) {
      flushPendingToolchainPath();
    }
  });
  context.subscriptions.push(stateListener);
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}

function dumpClientTokens(
  data: Uint32Array,
  legend: { tokenTypes: string[]; tokenModifiers: string[] },
  getLine: (ln: number) => string
): string {
  let line = 0, col = 0;
  const out: string[] = [];
  for (let i = 0; i < data.length; i += 5) {
    const dLine = data[i]!, dStart = data[i + 1]!, length = data[i + 2]!;
    const tType = data[i + 3]!, tMods = data[i + 4]!;
    line += dLine;
    col = dLine === 0 ? col + dStart : dStart;
    const typeName = legend.tokenTypes[tType] ?? `unknown(${tType})`;
    const mods =
      legend.tokenModifiers.filter((_, bit) => (tMods & (1 << bit)) !== 0).join(',') || '-';
    const text = getLine(line).slice(col, col + length);
    out.push(`L${line}:${col} len=${length} type=${typeName} mods=${mods} text="${text}"`);
  }
  return out.join('\n');
}
