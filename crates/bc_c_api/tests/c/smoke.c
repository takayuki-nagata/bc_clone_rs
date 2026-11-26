// SPDX-License-Identifier: MIT
//
// Links against the bc_c_api static library through include/bc_core.h and checks every entry
// point from C: the status values, the argument order and the output of each call.
// `scripts/run_c_api_link_tests.sh` builds and runs it for the std and the no_std library.
//
// Usage: smoke         run the checks; exit status 0 when all pass
//        smoke oom     evaluate a number too large for the no_std library's 64 KiB heap, then
//                      print "oom done" (the std library finishes; the no_std one halts in its
//                      panic handler and never returns)

#include "bc_core.h"

#include <stdio.h>
#include <string.h>

static int failures = 0;

static void check(int ok, const char *what) {
    if (!ok) {
        fprintf(stderr, "FAIL: %s\n", what);
        failures++;
    }
}

static void check_str(const char *got, const char *want, const char *what) {
    if (strcmp(got, want) != 0) {
        fprintf(stderr, "FAIL: %s: got \"%s\", want \"%s\"\n", what, got, want);
        failures++;
    }
}

struct collected {
    char text[256];
    int calls;
};

static void collect(const char *chunk, void *user_data) {
    struct collected *c = user_data;
    strncat(c->text, chunk, sizeof c->text - strlen(c->text) - 1);
    c->calls++;
}

static void check_status_values(void) {
    check(BC_STATUS_OK == 0 && BC_STATUS_ERR_NULL_PTR == 1 && BC_STATUS_ERR_BUFFER_TOO_SMALL == 2 &&
              BC_STATUS_ERR_EXECUTION == 3,
          "status values");
    check(sizeof(bc_status_t) == sizeof(int), "status size");
}

static void check_version(void) {
    const char *v = bc_version();
    check(v != NULL && strncmp(v, "bc_clone ", 9) == 0, "bc_version starts with bc_clone");
}

static void check_eval(void) {
    char buf[128];
    char tiny[2];

    check(bc_eval("1 + 2 * 3\n", false, 0, buf, sizeof buf) == BC_STATUS_OK, "bc_eval ok");
    check_str(buf, "7\n", "bc_eval output");

    check(bc_eval("scale=10; 4*a(1)\n", true, 0, buf, sizeof buf) == BC_STATUS_OK, "bc_eval -l");
    check_str(buf, "3.1415926532\n", "bc_eval -l output");

    check(bc_eval("scale\n", false, 5, buf, sizeof buf) == BC_STATUS_OK, "bc_eval scale");
    check_str(buf, "5\n", "bc_eval default_scale");

    check(bc_eval("1 / 0\n", false, 0, buf, sizeof buf) == BC_STATUS_ERR_EXECUTION, "bc_eval error");
    check_str(buf, "Runtime error (func=(main)): Divide by zero\n", "bc_eval diagnostic");

    check(bc_eval("1 + 1\n", false, 0, tiny, sizeof tiny) == BC_STATUS_ERR_BUFFER_TOO_SMALL,
          "bc_eval small buffer");
    check(tiny[0] == '\0', "bc_eval small buffer is empty");
    check(bc_eval("1\n", false, 0, buf, 0) == BC_STATUS_ERR_BUFFER_TOO_SMALL, "bc_eval size 0");
    check(bc_eval(NULL, false, 0, buf, sizeof buf) == BC_STATUS_ERR_NULL_PTR, "bc_eval NULL code");
    check(bc_eval("1\n", false, 0, NULL, sizeof buf) == BC_STATUS_ERR_NULL_PTR, "bc_eval NULL buf");
}

static void check_eval_callback(void) {
    struct collected out = {{0}, 0};
    struct collected err = {{0}, 0};

    check(bc_eval_callback("2^10\n", false, 0, collect, collect, &out) == BC_STATUS_OK,
          "bc_eval_callback ok");
    check_str(out.text, "1024\n", "bc_eval_callback output");

    check(bc_eval_callback("sqrt(-1)\n", false, 0, NULL, collect, &err) == BC_STATUS_ERR_EXECUTION,
          "bc_eval_callback error");
    check_str(err.text, "Runtime error (func=(main)): Square root of a negative number\n",
              "bc_eval_callback diagnostic");
    check(bc_eval_callback(NULL, false, 0, NULL, NULL, NULL) == BC_STATUS_ERR_NULL_PTR,
          "bc_eval_callback NULL code");
}

static void check_session(void) {
    char buf[128];
    bc_session_t *s = bc_session_create(false);
    check(s != NULL, "bc_session_create");

    check(bc_session_eval(s, "x = 42", buf, sizeof buf) == BC_STATUS_OK, "session assign");
    check(bc_session_eval(s, "x * 2", buf, sizeof buf) == BC_STATUS_OK, "session read");
    check_str(buf, "84\n", "session keeps x");

    struct collected out = {{0}, 0};
    struct collected err = {{0}, 0};
    check(bc_session_eval_callback(s, "x + 1", collect, collect, &out) == BC_STATUS_OK,
          "session callback");
    check_str(out.text, "43\n", "session callback output");
    check(bc_session_eval_callback(s, "ibase = 99", NULL, collect, &err) == BC_STATUS_OK,
          "session callback warning");
    check(strstr(err.text, "ibase too large") != NULL, "session callback stderr");

    check(bc_session_set_extension_policy(s, 2) == BC_STATUS_OK, "policy reject");
    check(bc_session_eval(s, "abc = 1", buf, sizeof buf) == BC_STATUS_ERR_EXECUTION,
          "policy rejects names");
    check(bc_session_set_extension_policy(s, 0) == BC_STATUS_OK, "policy allow");
    check(bc_session_set_extension_policy(s, 3) == BC_STATUS_ERR_EXECUTION, "policy 3");

    check(bc_session_set_max_depth(s, 4) == BC_STATUS_OK, "max_depth 4");
    check(bc_session_eval(s, "((((((1))))))", buf, sizeof buf) == BC_STATUS_ERR_EXECUTION,
          "max_depth rejects nesting");
    check_str(buf, "(standard_in) 1: nesting too deep\n", "max_depth diagnostic");
    check(bc_session_set_max_depth(s, BC_DEFAULT_MAX_DEPTH) == BC_STATUS_OK, "max_depth default");
    check(bc_session_set_max_depth(s, 0) == BC_STATUS_ERR_EXECUTION, "max_depth 0");
    check(bc_session_set_max_eval_depth(s, 0) == BC_STATUS_ERR_EXECUTION, "max_eval_depth 0");
    check(bc_session_set_max_eval_depth(s, 64) == BC_STATUS_OK, "max_eval_depth 64");

    bc_session_reset(s, false);
    check(bc_session_eval(s, "x", buf, sizeof buf) == BC_STATUS_OK, "session after reset");
    check_str(buf, "0\n", "reset clears x");

    check(bc_session_eval(NULL, "1", buf, sizeof buf) == BC_STATUS_ERR_NULL_PTR, "session NULL");
    check(bc_session_eval_callback(NULL, "1", NULL, NULL, NULL) == BC_STATUS_ERR_NULL_PTR,
          "session callback NULL");
    check(bc_session_set_max_depth(NULL, 8) == BC_STATUS_ERR_NULL_PTR, "max_depth NULL");
    check(bc_session_set_max_eval_depth(NULL, 8) == BC_STATUS_ERR_NULL_PTR, "max_eval_depth NULL");
    check(bc_session_set_extension_policy(NULL, 0) == BC_STATUS_ERR_NULL_PTR, "policy NULL");
    bc_session_reset(NULL, false);
    bc_session_destroy(s);
    bc_session_destroy(NULL);
}

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "oom") == 0) {
        char buf[16];
        bc_eval("x = 10^200000; 0\n", false, 0, buf, sizeof buf);
        puts("oom done");
        return 0;
    }

    check_status_values();
    check_version();
    check_eval();
    check_eval_callback();
    // Sessions repeatedly, so that the no_std library's heap is reused after each destroy.
    for (int i = 0; i < 20; i++) {
        check_session();
    }

    if (failures != 0) {
        fprintf(stderr, "%d check(s) failed\n", failures);
        return 1;
    }
    puts("all C API checks passed");
    return 0;
}
