/*
 * Copyright (c) 2026 Takayuki Nagata
 * SPDX-License-Identifier: MIT
 */

#include <zephyr/kernel.h>
#include <zephyr/sys/printk.h>
#include <zephyr/drivers/uart.h>
#include <stdbool.h>

static const struct device *const console_dev = DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

void zephyr_putc(char c)
{
    printk("%c", c);
}

int zephyr_getchar(void)
{
    if (!console_dev) {
        return -1;
    }
    unsigned char c;
    if (uart_poll_in(console_dev, &c) == 0) {
        return (int)c;
    }
    return -1;
}

void zephyr_msleep(uint32_t ms)
{
    k_msleep(ms);
}

#if defined(CONFIG_BOARD_QEMU_RISCV32) && !defined(CONFIG_BC_QEMU_REPL)
#include <zephyr/fatal.h>

/*
 * A fatal error (for example a stack overflow caught by CONFIG_HW_STACK_PROTECTION) ends the
 * self-test run: exit QEMU with a failure status through the SiFive test device instead of
 * halting, so that CI fails at once rather than hanging.
 */
void k_sys_fatal_error_handler(unsigned int reason, const struct arch_esf *esf)
{
    ARG_UNUSED(esf);
    printk("FATAL ERROR %u: bc_core self-tests aborted\n", reason);
    *(volatile uint32_t *)0x100000 = 0x3333;
    for (;;) {
    }
}
#endif

// Rust application entry point
extern void zephyr_rust_main(bool is_qemu);

int main(void)
{
#if defined(CONFIG_BOARD_QEMU_RISCV32) && !defined(CONFIG_BC_QEMU_REPL)
    zephyr_rust_main(true);
#else
    zephyr_rust_main(false);
#endif
    return 0;
}
