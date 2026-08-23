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

// Rust application entry point
extern void zephyr_rust_main(bool is_qemu);

int main(void)
{
#if defined(CONFIG_BOARD_QEMU_RISCV32)
    zephyr_rust_main(true);
#else
    zephyr_rust_main(false);
#endif
    return 0;
}
