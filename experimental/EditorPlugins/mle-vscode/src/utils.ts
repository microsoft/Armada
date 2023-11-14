import { window, Position, workspace, Uri, commands } from "vscode";

export const getServerPath = (): string => {
  const p: string | undefined = workspace
    .getConfiguration("starmada.path")
    .get("serverPath");
  if (!p) {
    throw new Error("ServerPath must be assigned.");
  }
  return p;
};

export const getWorkspacePath = (): string => {
  let p = workspace.workspaceFolders?.[0].uri.path;
  if (!p) {
    throw new Error("Must be in a workspace.");
  }
  return p;
};

export const getCmdHead = (): string => {
  const serverPath = getServerPath();
  const wsPath = getWorkspacePath();
  const cmd = `cd ${wsPath} && ${serverPath}`;
  return cmd;
};

export const getActiveFilePath = (): string => {
  let p = window.activeTextEditor?.document.uri.path;
  if (!p) {
    throw new Error("Must be in a file.");
  }
  return p;
};

export const getActivePosition = (): string => {
  const editor = window.activeTextEditor;
  if (!editor) {
    throw new Error("Must be in an active editor.");
  }
  const selection = editor.selection;

  const posToStr = (pos: Position) => `${pos.line + 1}:${pos.character + 1}`;

  const start = posToStr(selection.start);
  const end = posToStr(selection.end);
  return start === end ? `${start}` : `${start}-${end}`;
};

export const getCandidatesUri = (): Uri => {
  const uri = Uri.joinPath(
    Uri.file(getWorkspacePath()),
    ".build",
    "candidates"
  );
  return uri;
};

export const openCandidates = (): void => {
  const uri = getCandidatesUri();
  commands.executeCommand("vscode.open", uri);
};
