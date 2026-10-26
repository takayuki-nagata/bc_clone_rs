bc_clone bare-metal self-test for QEMU RISC-V 32
================================================

Stand-alone RISC-V 32 binaries (no OS) that run the bc_clone engine's self-test suite on QEMU's
"virt" machine and report the result through QEMU's exit status.

  ./run.sh        # bc_qemu_riscv32-riscv32imac.elf
  ./run.sh imc    # bc_qemu_riscv32-riscv32imc.elf

Requirements: qemu-system-riscv32 (Debian/Ubuntu: apt install qemu-system-misc).
