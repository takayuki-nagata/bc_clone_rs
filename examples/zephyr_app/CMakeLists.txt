# Copyright (c) 2026 Takayuki Nagata
# SPDX-License-Identifier: MIT

cmake_minimum_required(VERSION 3.20.0)

find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(bc_zephyr_app)

if(NOT DEFINED RUST_TARGET)
    if(CONFIG_BOARD_STAMP_C3 OR CONFIG_SOC_ESP32C3 OR CONFIG_SOC_SERIES_ESP32C3 OR NOT CONFIG_RISCV_ISA_EXT_A)
        set(RUST_TARGET riscv32imc-unknown-none-elf)
    else()
        set(RUST_TARGET riscv32imac-unknown-none-elf)
    endif()
endif()

get_filename_component(BC_REPO_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)
set(BC_ZEPHYR_DIR "${BC_REPO_ROOT}/crates/bc_zephyr")
set(RUST_LIB_DIR "${BC_REPO_ROOT}/target/${RUST_TARGET}/release")
set(RUST_LIB "${RUST_LIB_DIR}/libbc_zephyr.a")

# Automatically invoke Cargo to build Rust staticlib during Zephyr build
add_custom_command(
    OUTPUT ${RUST_LIB}
    COMMAND cargo build --release --target ${RUST_TARGET} --no-default-features --manifest-path "${BC_ZEPHYR_DIR}/Cargo.toml"
    WORKING_DIRECTORY ${BC_ZEPHYR_DIR}
    COMMENT "Building bc_zephyr staticlib for Zephyr target (${RUST_TARGET})..."
)

add_custom_target(bc_zephyr_staticlib DEPENDS ${RUST_LIB})

target_sources(app PRIVATE src/main.c)
add_dependencies(app bc_zephyr_staticlib)
target_link_libraries(app PRIVATE ${RUST_LIB})

