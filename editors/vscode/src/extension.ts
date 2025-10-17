import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export function activate(context: vscode.ExtensionContext) {
  const root = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath ?? context.extensionUri.fsPath;

  const serverCommand = process.env.RAY_LSP_COMMAND ?? "cargo";
  const serverArgs = process.env.RAY_LSP_ARGS
    ? JSON.parse(process.env.RAY_LSP_ARGS)
    : ["run", "--quiet", "-p", "ray-lsp"];

  const serverOptions: ServerOptions = {
    run: {
      command: serverCommand,
      args: serverArgs,
      options: { cwd: root }
    },
    debug: {
      command: serverCommand,
      args: serverArgs,
      options: { cwd: root }
    }
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "ray" }],
    outputChannel: vscode.window.createOutputChannel("Ray LSP")
  };

  client = new LanguageClient("ray-lsp", "Ray Language Server", serverOptions, clientOptions);
  client.start();
  context.subscriptions.push(client);
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
