bc_clone for M5Stamp C3 (ESP32-C3, bare metal)
==============================================

Firmware running the bc_clone engine without an OS (esp-hal). After a self-test it offers an
interactive bc REPL over the USB serial console. The math library (-l) is enabled.

  ./flash.sh    # flash m5stamp_c3_bc.elf and open the REPL (PORT=/dev/ttyACM0 by default)
  ./repl.sh     # open the REPL of an already flashed board

Requirements: espflash (`cargo install espflash`), python3 with pyserial.
Input lines are limited to 1024 characters; Ctrl+C cancels the current input.
