bc_clone on Zephyr RTOS
=======================

The bc_clone engine as a Zephyr application (Zephyr v3.7.2): self-tests followed by an
interactive bc REPL on the console. The math library (-l) is enabled.

QEMU RISC-V 32 (requires qemu-system-riscv32):
  ./run-qemu-repl.sh        # self-tests, then the REPL (exit QEMU with Ctrl+A, X)
  ./run-qemu-selftest.sh    # self-tests only; exit status 0 if they pass

M5Stamp C3 / ESP32-C3 (requires `pip install esptool pyserial`):
  ./flash-stamp-c3.sh       # flash stamp_c3/zephyr.bin and open the REPL (PORT=/dev/ttyACM0)
  ./repl-stamp-c3.sh        # open the REPL of an already flashed board

Multi-line input (e.g. function definitions) is supported; a "... " prompt shows pending
input. Input lines are limited to 1024 characters; Ctrl+C cancels the current input.
