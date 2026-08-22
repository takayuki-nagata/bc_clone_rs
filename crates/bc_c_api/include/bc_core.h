/*
 * SPDX-License-Identifier: MIT
 *
 * C-API interface for bc_core (bc_clone_rs)
 * High-performance POSIX-compliant arbitrary-precision calculator engine.
 */

#ifndef BC_CORE_H
#define BC_CORE_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Status codes returned by bc_eval functions.
 */
typedef enum {
    BC_STATUS_OK = 0,
    BC_STATUS_ERR_NULL_PTR = 1,
    BC_STATUS_ERR_BUFFER_TOO_SMALL = 2,
    BC_STATUS_ERR_EXECUTION = 3,
} bc_status_t;

/**
 * Callback function type for streaming output line-by-line or character-by-character.
 *
 * @param str Null-terminated string chunk.
 * @param user_data User-provided context pointer.
 */
typedef void (*bc_output_cb_t)(const char *str, void *user_data);

/**
 * Evaluates a bc expression or script string and writes the output into a buffer.
 *
 * @param code Null-terminated string containing the bc code to evaluate.
 * @param math_enabled If true, preloads standard math functions (s, c, a, l, e, j).
 * @param default_scale Initial fractional digit scale (e.g. 0 to 20).
 * @param out_buf Buffer where the output result string will be stored (null-terminated).
 * @param buf_size Total size of out_buf in bytes.
 * @return BC_STATUS_OK on success, or an error status code.
 */
bc_status_t bc_eval(
    const char *code,
    bool math_enabled,
    uint32_t default_scale,
    char *out_buf,
    size_t buf_size
);

/**
 * Evaluates a bc script string and sends output chunks to callback functions.
 *
 * @param code Null-terminated string containing the bc code to evaluate.
 * @param math_enabled If true, preloads standard math functions.
 * @param default_scale Initial fractional digit scale.
 * @param stdout_cb Callback invoked for standard output chunks (may be NULL).
 * @param stderr_cb Callback invoked for error/warning messages (may be NULL).
 * @param user_data Context pointer passed to callback invocations.
 * @return BC_STATUS_OK on success, or an error status code.
 */
bc_status_t bc_eval_callback(
    const char *code,
    bool math_enabled,
    uint32_t default_scale,
    bc_output_cb_t stdout_cb,
    bc_output_cb_t stderr_cb,
    void *user_data
);

/**
 * Opaque session handle representing a persistent bc execution environment.
 */
typedef struct bc_session bc_session_t;

/**
 * Creates a new persistent bc session.
 *
 * @param math_enabled If true, preloads standard math functions (s, c, a, l, e, j).
 * @return Pointer to the newly allocated session, or NULL on failure.
 */
bc_session_t *bc_session_create(bool math_enabled);

/**
 * Evaluates bc code within a persistent session and writes output into a buffer.
 * Variables, functions, and scale persist across calls to the same session.
 *
 * @param session Pointer to active bc session.
 * @param code Null-terminated string containing the bc code to evaluate.
 * @param out_buf Buffer where the output result string will be stored.
 * @param buf_size Total size of out_buf in bytes.
 * @return BC_STATUS_OK on success, or an error status code.
 */
bc_status_t bc_session_eval(
    bc_session_t *session,
    const char *code,
    char *out_buf,
    size_t buf_size
);

/**
 * Evaluates bc code within a persistent session and streams output via callback.
 *
 * @param session Pointer to active bc session.
 * @param code Null-terminated string containing the bc code to evaluate.
 * @param stdout_cb Callback invoked for standard output chunks (may be NULL).
 * @param stderr_cb Callback invoked for error/warning messages (may be NULL).
 * @param user_data Context pointer passed to callback invocations.
 * @return BC_STATUS_OK on success, or an error status code.
 */
bc_status_t bc_session_eval_callback(
    bc_session_t *session,
    const char *code,
    bc_output_cb_t stdout_cb,
    bc_output_cb_t stderr_cb,
    void *user_data
);

/**
 * Resets the session state (clearing variables and user-defined functions).
 *
 * @param session Pointer to active bc session.
 * @param math_enabled If true, retains/re-enables standard math functions.
 */
void bc_session_reset(bc_session_t *session, bool math_enabled);

/**
 * Destroys a bc session and frees associated memory.
 *
 * @param session Pointer to session to destroy (may be NULL).
 */
void bc_session_destroy(bc_session_t *session);

#ifdef __cplusplus
}
#endif

#endif /* BC_CORE_H */
