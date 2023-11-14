import { ExtensionContext, commands, window } from "vscode";
import RefactorViewProvider from "./refactor-view";

// this method is called when your extension is activated
export function activate(context: ExtensionContext) {
  const provider = new RefactorViewProvider(context.extensionUri);

  context.subscriptions.push(
    window.registerWebviewViewProvider(
      RefactorViewProvider.viewId,
      provider
    )
  );

  context.subscriptions.push(
    commands.registerCommand("starmada.backup", () => {
      RefactorViewProvider.backup();
    })
  );

  context.subscriptions.push(
    commands.registerCommand("starmada.extract", () => {
      provider.extract();
    })
  );

  context.subscriptions.push(
    commands.registerCommand("starmada.apply", () => {
      RefactorViewProvider.apply();
    })
  );

  context.subscriptions.push(
    commands.registerCommand("starmada.restore", () => {
      RefactorViewProvider.restore();
    })
  );
}

// this method is called when your extension is deactivated
export function deactivate() {}
