/*
 * Copyright (c) 2026 Takayuki Nagata
 * SPDX-License-Identifier: MIT
 */

#include <zephyr/kernel.h>
#include <zephyr/sys/printk.h>
#include <string.h>
#include "bc_core.h"

static void printk_callback(const char *str, void *user_data)
{
    ARG_UNUSED(user_data);
    printk("%s", str);
}

typedef struct {
    const char *name;
    const char *code;
    bool math_enabled;
    uint32_t scale;
    const char *expected;
} bc_test_case_t;

int main(void)
{
    printk("\n=================================================\n");
    printk("  bc_clone (bc_core) on Zephyr RTOS (RISC-V 32)  \n");
    printk("=================================================\n");
    printk("[Zephyr Kernel] Initialized successfully. Starting bc_core test suite...\n\n");

    const bc_test_case_t test_cases[] = {
        {
            .name = "Basic Arithmetic & Precedence",
            .code = "1 + 2 * 3 - 4 / 2\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "5",
        },
        {
            .name = "Scale Division",
            .code = "scale = 4; 5 / 3\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "1.6666",
        },
        {
            .name = "BigInt Power (2^100)",
            .code = "2^100\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "1267650600228229401496703205376",
        },
        {
            .name = "Recursive Factorial f(20)",
            .code = "define f(n) {\n  if (n <= 1) return (1)\n  return (n * f(n - 1))\n}\nf(20)\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "2432902008176640000",
        },
        {
            .name = "Transcendental Pi: 4 * a(1)",
            .code = "4 * a(1)\n",
            .math_enabled = true,
            .scale = 20,
            .expected = "3.14159265358979323844",
        },
        {
            .name = "Transcendental Exp: e(1)",
            .code = "e(1)\n",
            .math_enabled = true,
            .scale = 15,
            .expected = "2.718281828459045",
        },
        {
            .name = "Transcendental Log: l(2.718281828459045)",
            .code = "l(2.718281828459045)\n",
            .math_enabled = true,
            .scale = 15,
            .expected = ".999999999999999",
        },
        {
            .name = "Base Conversion (Hex to Binary)",
            .code = "ibase = 16; obase = 2; FF\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "11111111",
        },
        {
            .name = "Arrays and Dynamic Auto Scoping",
            .code = "a[0] = 10; a[1] = 20\ndefine sum(x[]) {\n  auto s\n  s = x[0] + x[1]\n  return (s)\n}\nsum(a[])\n",
            .math_enabled = false,
            .scale = 0,
            .expected = "30",
        },
    };

    size_t num_tests = sizeof(test_cases) / sizeof(test_cases[0]);
    bool all_passed = true;
    char out_buf[256];

    for (size_t i = 0; i < num_tests; i++) {
        const bc_test_case_t *tc = &test_cases[i];
        printk("  Running: %-35s ... ", tc->name);

        memset(out_buf, 0, sizeof(out_buf));
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
    volatile uint32_t *test_exit = (volatile uint32_t *)0x100000;
    if (all_passed) {
        printk("ALL ZEPHYR BC_CORE TESTS PASSED (100%%)!\n");
        printk("=================================================\n");
        *test_exit = 0x5555;
    } else {
        printk("SOME ZEPHYR BC_CORE TESTS FAILED!\n");
        printk("=================================================\n");
        *test_exit = 0x3333;
    }

    return 0;
}
