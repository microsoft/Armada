// @ts-nocheck

// This script will be run within the webview itself
// It cannot access the main VS Code APIs directly.
(function () {
    const vscode = acquireVsCodeApi();

    const state = vscode.getState() || { llevel: "", hlevel: "" };

    updateState(state);

    document.querySelector('.level-input').addEventListener('input', () => {
        const state = onChange();
        updateState(state);
    });

    function addBtnListener(selector, then) {
        document.querySelector(selector).addEventListener('click', then);
    }

    addBtnListener('#extract-btn', postMessageVoid("onExtract"));
    addBtnListener('#apply-btn', postMessageVoid("onApply"));
    addBtnListener('#restore-btn', postMessageVoid("onRestore"));

    function updateState(state) {
        // Update the saved state
        vscode.setState(state);
    }

    function onChange() {
        const state = {
            llevel: document.querySelector('#llevel').value,
            hlevel: document.querySelector('#hlevel').value
        };
        vscode.postMessage({ type: 'onChange', value: state });
        return state;
    }

    function postMessageVoid(type) {
        return () => vscode.postMessage({ type: type, value: {} });
    }
}());


