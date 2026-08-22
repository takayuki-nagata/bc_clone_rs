// SPDX-License-Identifier: MIT

import init, { BcSession } from '../pkg/bc_wasm.js';

let session = null;
const history = [];
let historyIndex = -1;

const terminalBody = document.getElementById('terminal-body');
const terminalOutput = document.getElementById('terminal-output');
const inputForm = document.getElementById('input-form');
const commandInput = document.getElementById('command-input');
const engineStatus = document.getElementById('engine-status');
const clearBtn = document.getElementById('clear-btn');
const resetBtn = document.getElementById('reset-btn');
const presetButtons = document.querySelectorAll('.preset-btn');

function appendLine(text, className = '') {
  const line = document.createElement('div');
  line.className = `output-line ${className}`.trim();
  line.textContent = text;
  terminalOutput.appendChild(line);
  terminalBody.scrollTop = terminalBody.scrollHeight;
}

function executeCode(code) {
  if (!session) {
    appendLine('[Error]: Wasm engine is not ready yet.', 'error');
    return;
  }

  const trimmed = code.trim();
  if (!trimmed) return;

  // Print user command
  appendLine(`bc> ${trimmed}`, 'command');

  // Push to history
  history.push(trimmed);
  historyIndex = history.length;

  try {
    const result = session.eval(trimmed);
    if (result && result.length > 0) {
      appendLine(result.trimEnd(), 'result');
    }
  } catch (err) {
    appendLine(`[Runtime Error]: ${err}`, 'error');
  }
}

// Initialize Wasm Module
async function initWasm() {
  try {
    engineStatus.textContent = 'Loading Wasm...';
    await init();
    session = new BcSession(true); // Math library enabled
    engineStatus.textContent = 'Engine Ready (Client-Side)';
    engineStatus.classList.add('ready');
    commandInput.disabled = false;
    commandInput.focus();
  } catch (err) {
    engineStatus.textContent = 'Failed to load Wasm';
    appendLine(`[Error initializing WebAssembly]: ${err}`, 'error');
  }
}

// Form Submit Handler
inputForm.addEventListener('submit', (e) => {
  e.preventDefault();
  const val = commandInput.value;
  commandInput.value = '';
  executeCode(val);
});

// Key Navigation for History and Shortcuts
commandInput.addEventListener('keydown', (e) => {
  if (e.key === 'ArrowUp') {
    e.preventDefault();
    if (history.length > 0) {
      if (historyIndex > 0) {
        historyIndex--;
      }
      commandInput.value = history[historyIndex] || '';
    }
  } else if (e.key === 'ArrowDown') {
    e.preventDefault();
    if (historyIndex < history.length - 1) {
      historyIndex++;
      commandInput.value = history[historyIndex] || '';
    } else {
      historyIndex = history.length;
      commandInput.value = '';
    }
  } else if (e.ctrlKey && e.key.toLowerCase() === 'l') {
    e.preventDefault();
    clearTerminal();
  } else if (e.ctrlKey && e.key.toLowerCase() === 'c') {
    e.preventDefault();
    commandInput.value = '';
    appendLine('^C', 'info');
  }
});

function clearTerminal() {
  terminalOutput.innerHTML = '';
  appendLine('Terminal output cleared.', 'info');
}

clearBtn.addEventListener('click', clearTerminal);

resetBtn.addEventListener('click', () => {
  if (session) {
    session.reset(true);
    appendLine('bc session reset. All variables and functions cleared.', 'info');
  }
});

// Preset Buttons
presetButtons.forEach((btn) => {
  btn.addEventListener('click', () => {
    const code = btn.getAttribute('data-code');
    if (code) {
      executeCode(code);
      commandInput.focus();
    }
  });
});

// Focus input on clicking anywhere in terminal body
terminalBody.addEventListener('click', () => {
  commandInput.focus();
});

// Start initialization
initWasm();
