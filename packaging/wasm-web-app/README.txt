bc_clone WebAssembly web app
============================

A browser calculator running the bc_clone engine (POSIX.1-2024 bc) entirely client-side.

  ./serve.sh            # then open http://localhost:8080/www/
  PORT=9000 ./serve.sh  # use another port

Contents:
  www/   the web page (index.html, app.js, style.css)
  pkg/   the WebAssembly module and its JavaScript bindings (wasm-bindgen, --target web)

Any static web server works; serve this directory and open /www/.
