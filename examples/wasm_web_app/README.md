# bc_clone_rs WebAssembly (wasm32) Web App Example

This example demonstrates running the arbitrary-precision mathematical engine `bc_core` (`#![no_std]` + `alloc`) directly inside any modern web browser using **WebAssembly (wasm32)**.

All calculations run 100% on the client side with zero server requests.

## Prerequisites

1. Rust WebAssembly target:
   ```bash
   rustup target add wasm32-unknown-unknown
   ```
2. `wasm-bindgen-cli` tool:
   ```bash
   cargo install wasm-bindgen-cli
   ```

## Building the WebAssembly Module

To build the Wasm binary and generate JavaScript bindings:

```bash
bash scripts/build_wasm.sh
```

This compiles `bc_wasm` into `examples/wasm_web_app/pkg/` (`bc_wasm_bg.wasm` and `bc_wasm.js`).

## Running the Web Application Locally

To build and start a local HTTP server:

```bash
bash scripts/serve_wasm.sh
```

Then open your browser and navigate to:
[http://localhost:8080/www/](http://localhost:8080/www/)

## JavaScript API Usage

```javascript
import init, { eval_bc, BcSession } from './pkg/bc_wasm.js';

await init();

// 1. One-shot calculation
const result = eval_bc('2^100\n', false, 0);
console.log(result); // 1267650600228229401496703205376

// 2. Persistent interactive session
const session = new BcSession(true); // Math library enabled
session.eval('scale = 20; 4 * a(1)'); // 3.14159265358979323844
session.eval('define f(x) { return (x * 2); }');
session.eval('f(21)'); // 42
```
