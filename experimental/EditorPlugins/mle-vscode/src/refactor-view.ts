import * as vscode from "vscode";
import { exec } from "child_process";
import {
  getCmdHead,
  getActiveFilePath,
  getActivePosition,
  openCandidates,
  getCandidatesUri,
} from "./utils";

class RefactorViewProvider implements vscode.WebviewViewProvider {
  public static readonly viewId = "starmada.refactorView";

  private _state: {
    llevel: string;
    hlevel: string;
  };

  constructor(private readonly _extensionUri: vscode.Uri) {
    this._state = {
      llevel: "",
      hlevel: "",
    };
  }

  public static backup() {
    const cmd = `${getCmdHead()} backup`;
    console.log(cmd);
    exec(cmd, (err, _out, _) => {
      if (err) {
        console.log(err);
      }
      return;
    });
  }

  public extract() {
    const lv = (lv: string, pre: string) => {
      return lv === "" ? "" : ` ${pre} ${lv}`;
    };
    const llv = lv(this._state.llevel, "-l");
    const hlv = lv(this._state.hlevel, "-h");
    const cmd =
      `${getCmdHead()} extract -f ${getActiveFilePath()} -p ${getActivePosition()}` +
      llv +
      hlv;
    console.log(cmd);
    exec(cmd, (err, _out, _) => {
      if (err) {
        console.log(err);
      }
      return;
    });
  }

  public static apply() {
    const cmd = `${getCmdHead()} apply`;
    console.log(cmd);
    exec(cmd, (err, _out, _) => {
      if (err) {
        console.log(err);
      }
      return;
    });
  }

  public static restore() {
    const cmd = `${getCmdHead()} restore`;
    console.log(cmd);
    exec(cmd, (err, _out, _) => {
      if (err) {
        console.log(err);
      }
      return;
    });
  }

  public resolveWebviewView(
    webviewView: vscode.WebviewView,
    context: vscode.WebviewViewResolveContext,
    _token: vscode.CancellationToken
  ) {
    webviewView.webview.options = {
      // Allow scripts in the webview
      enableScripts: true,

      localResourceRoots: [this._extensionUri],
    };

    webviewView.webview.html = this._getHtmlForWebview(webviewView.webview);

    webviewView.webview.onDidReceiveMessage((data) => {
      switch (data.type) {
        case "onChange": {
          console.log("onChange");
          this._state = data.value;
          console.log(this._state);
          break;
        }
        case "onExtract": {
          RefactorViewProvider.backup();
          this.extract();
          openCandidates();
          break;
        }
        case "onApply": {
          RefactorViewProvider.apply();
          break;
        }
        case "onRestore": {
          RefactorViewProvider.restore();
          break;
        }
      }
    });
  }

  private _getHtmlForWebview(webview: vscode.Webview) {
    // Get the local path to main script run in the webview, then convert it to a uri we can use in the webview.
    const scriptUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "view", "main.js")
    );

    // Do the same for the stylesheet.
    const styleResetUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "view", "reset.css")
    );
    const styleVSCodeUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "view", "vscode.css")
    );
    const styleMainUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "view", "main.css")
    );

    // Use a nonce to only allow a specific script to be run.
    const nonce = getNonce();

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">

  <!--
    Use a content security policy to only allow loading images from https or from our extension directory,
    and only allow scripts that have a specific nonce.
  -->
  <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource}; script-src 'nonce-${nonce}';">

  <meta name="viewport" content="width=device-width, initial-scale=1.0">

  <link href="${styleResetUri}" rel="stylesheet">
  <link href="${styleVSCodeUri}" rel="stylesheet">
  <link href="${styleMainUri}" rel="stylesheet">
    
  <title>Starmada Refactor Panel</title>
</head>
<body>
  <h3>Level Range</h3>
  <span>Low Level</span>
  <input id="llevel" class="level-input"/>

  <span>High Level</span>
  <input id="hlevel" class="level-input"/>

  <div></div>

  <h3>Actions</h3>

  <button id="extract-btn" class="op-btn">
    <span class="sym">⊣ </span>
    <span class="txt">Extract</span>
  </button>
  <button id="apply-btn" class="op-btn">
    <span class="sym">☑ </span>
    <span class="txt">Apply</span>
  </button>
  <button id="restore-btn" class="op-btn">
    <span class="sym">⦾ </span>
    <span class="txt">Restore</span>
  </button>

  <script nonce="${nonce}" src="${scriptUri}"></script>
</body>
</html>`;
  }
}

function getNonce() {
  let text = "";
  const possible =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  for (let i = 0; i < 32; i++) {
    text += possible.charAt(Math.floor(Math.random() * possible.length));
  }
  return text;
}

let candidateOpens = false;

vscode.window.onDidChangeVisibleTextEditors(
  (data: readonly vscode.TextEditor[]) => {
    let candidateDoc = data.find(
      (e: vscode.TextEditor) => e.document.uri.path === getCandidatesUri().path
    );
    if (!candidateOpens && candidateDoc) {
      candidateOpens = true;
    } else if (candidateOpens && !candidateDoc) {
      RefactorViewProvider.apply();
      candidateOpens = false;
    }
  }
);

export default RefactorViewProvider;
