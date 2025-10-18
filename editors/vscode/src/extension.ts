import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  State
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;
const TOOLCHAIN_CONFIG_KEY = "toolchainPath";

const resolveToolchainPath = (): string =>
  vscode.workspace.getConfiguration("ray").get<string>(TOOLCHAIN_CONFIG_KEY, "");

export function activate(context: vscode.ExtensionContext) {
  const root = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath ?? context.extensionUri.fsPath;

  const serverCommand = process.env.RAY_LSP_COMMAND ?? "cargo";
  const serverArgs = process.env.RAY_LSP_ARGS
    ? JSON.parse(process.env.RAY_LSP_ARGS)
    : ["run", "--quiet", "-p", "ray-lsp"];

  const toolchainPath = resolveToolchainPath();
  const baseEnv: NodeJS.ProcessEnv = {
    ...process.env,
    RAY_TOOLCHAIN_PATH: toolchainPath
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
    outputChannel: vscode.window.createOutputChannel("Ray LSP"),
    initializationOptions: { toolchainPath }
  };

  const languageClient = new LanguageClient("ray-lsp", "Ray Language Server", serverOptions, clientOptions);
  languageClient.start();
  context.subscriptions.push(languageClient);

  client = languageClient;

  let pendingToolchainPath: string | undefined;

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

  const configListener = vscode.workspace.onDidChangeConfiguration(event => {
    if (!event.affectsConfiguration(`ray.${TOOLCHAIN_CONFIG_KEY}`)) {
      return;
    }
    const updatedToolchainPath = resolveToolchainPath();
    queueToolchainPathNotification(updatedToolchainPath);
  });
  context.subscriptions.push(configListener);

  const stateListener = languageClient.onDidChangeState(({ newState }) => {
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
