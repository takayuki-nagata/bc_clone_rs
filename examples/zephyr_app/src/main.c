/*
 * Copyright (c) 2026 Takayuki Nagata
 * SPDX-License-Identifier: MIT
 */

#include <zephyr/kernel.h>
#include <zephyr/sys/printk.h>
#include <zephyr/drivers/uart.h>
#include <zephyr/device.h>
#include <string.h>
#include <stdbool.h>
#include "bc_core.h"

static const struct device *const console_dev = DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

struct test_case {
    const char *name;
    const char *code;
    bool math_enabled;
    uint32_t scale;
    const char *expected;
};

static void printk_callback(const char *str, void *user_data)
{
    (void)user_data;
    printk("%s", str);
}

static bool run_self_tests(void)
{
    printk("\n=================================================\n");
    printk("  bc_clone (bc_core) on Zephyr RTOS              \n");
    printk("=================================================\n");
    printk("[Zephyr Kernel] Initialized successfully. Starting bc_core test suite...\n\n");

    const struct test_case test_cases[] = {
        {
            .name = "Basic Arithmetic & Precedence",
            .code = "1 + 2 * 3 - 4 / 2\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "5"
        },
        {
            .name = "Scale Division",
            .code = "scale = 4; 5 / 3\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "1.6666"
        },
        {
            .name = "BigInt Power (2^100)",
            .code = "2^100\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "1267650600228229401496703205376"
        },
        {
            .name = "Recursive Factorial f(20)",
            .code = "define f(n) {\n  if (n <= 1) return (1)\n  return (n * f(n - 1))\n}\nf(20)\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "2432902008176640000"
        },
        {
            .name = "Transcendental Pi: 4 * a(1)",
            .code = "4 * a(1)\n",
            .math_enabled = true,
            .scale = 20,
            .expected = "3.14159265358979323844"
        },
        {
            .name = "Transcendental Exp: e(1)",
            .code = "e(1)\n",
            .math_enabled = true,
            .scale = 15,
            .expected = "2.718281828459045"
        },
        {
            .name = "Transcendental Log: l(2.718281828459045)",
            .code = "l(2.718281828459045)\n",
            .math_enabled = true,
            .scale = 15,
            .expected = ".999999999999999"
        },
        {
            .name = "Base Conversion (Hex to Binary)",
            .code = "ibase = 16; obase = 2; FF\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "11111111"
        },
        {
            .name = "Arrays and Dynamic Auto Scoping",
            .code = "a[0] = 10; a[1] = 20\ndefine sum(x[]) {\n  auto s\n  s = x[0] + x[1]\n  return (s)\n}\nsum(a[])\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "30"
        },
    };

    bool all_passed = true;
    char out_buf[128];

    for (size_t i = 0; i < sizeof(test_cases) / sizeof(test_cases[0]); i++) {
        const struct test_case *tc = &test_cases[i];
        printk("  Running: %-35s ... ", tc->name);

        bc_status_t status = bc_eval(
            tc->code,
            tc->math_enabled,
            tc->scale,
            out_buf,
            sizeof(out_buf)
        );

        if (status != BC_STATUS_OK) {
            printk("[FAIL] (Status error %d)\n", (int)status);
            all_passed = false;
            continue;
        }

        // Trim trailing newlines / carriage returns for comparison
        size_t len = strlen(out_buf);
        while (len > 0 && (out_buf[len - 1] == '\n' || out_buf[len - 1] == '\r' || out_buf[len - 1] == ' ')) {
            out_buf[--len] = '\0';
        }

        if (strcmp(out_buf, tc->expected) == 0) {
            printk("[PASS]\n");
        } else {
            printk("[FAIL]\n");
            printk("    Expected: \"%s\"\n", tc->expected);
            printk("    Actual  : \"%s\"\n", out_buf);
            all_passed = false;
        }
    }

    printk("\n  Streaming Callback Test: 2^16 = ");
    bc_eval_callback("2^16\n", false, 0, printk_callback, NULL, NULL);

    printk("-------------------------------------------------\n");
    if (all_passed) {
        printk("ALL ZEPHYR BC_CORE TESTS PASSED (100%%)!\n");
        printk("=================================================\n");
    } else {
        printk("SOME ZEPHYR BC_CORE TESTS FAILED!\n");
        printk("=================================================\n");
    }

    return all_passed;
}

int main(void)
{
    bool all_passed = run_self_tests();

#if defined(CONFIG_BOARD_QEMU_RISCV32)
    // Automated exit for QEMU emulation in CI
    volatile uint32_t *test_exit = (volatile uint32_t *)0x100000;
    if (all_passed) {
        *test_exit = 0x5555;
    } else {
        *test_exit = 0x3333;
    }
    return 0;
#else
    // Interactive REPL for Hardware Targets (e.g. M5Stamp C3)
    (void)all_passed;
    printk("\nEntering bc_core Interactive REPL mode (Zephyr RTOS)...\n");
    printk("Type bc expressions (e.g. 2^64, scale=10; 4*a(1), define f(x)...)\n");
    printk("bc> ");

    bc_session_t *session = bc_session_create(true);
    if (!session) {
        printk("[Error]: Failed to allocate bc_session\n");
        return -1;
    }

    char line_buf[256];
    size_t line_len = 0;

    while (1) {
        unsigned char c;
        if (uart_poll_in(console_dev, &c) != 0) {
            k_msleep(10);
            continue;
        }

        if (c == '\r' || c == '\n') {
            printk("\r\n");
            if (line_len > 0) {
                line_buf[line_len] = '\0';
                bc_session_eval_callback(session, line_buf, printk_callback, printk_callback, NULL);
                line_len = 0;
            }
            printk("bc> ");
        } else if (c == 0x08 || c == 0x7F) {
            // Backspace / Delete
            if (line_len > 0) {
                line_len--;
                printk("\b \b");
            }
        } else if (c == 0x03) {
            // Ctrl+C
            line_len = 0;
            printk("^C\r\nbc> ");
        } else if (c >= 0x20 && c <= 0x7E) {
            if (line_len + 1 < sizeof(line_buf)) {
                line_buf[line_len++] = (char)c;
                printk("%c", (char)c);
            }
        }
    }

    bc_session_destroy(session);
    return 0;
#endif
}
