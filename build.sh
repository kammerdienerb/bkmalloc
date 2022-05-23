#!/usr/bin/env bash

### DEBUG
#     FP="-fno-omit-frame-pointer" # enable for profiling/debugging
#     BK_DEBUG="-DBK_DEBUG"
#     DEBUG="-g ${FP} -DBK_DEBUG"

### OPT
    LTO="-flto"
    MARCHTUNE="-march=native -mtune=native"
    LEVEL="-O3"
#     LEVEL="-O0"

    OPT="${LEVEL} ${MARCHTUNE} ${LTO}"

### FEATURES
    MMAP_OVERRIDE="-DBK_MMAP_OVERRIDE"
    RETURN_ADDR="-DBK_RETURN_ADDR"
    ASSERT="-DBK_DO_ASSERTIONS"
    LOG="-DBK_DO_LOGGING"

    FEATURES="${MMAP_OVERRIDE} ${RETURN_ADDR} ${ASSERT} ${LOG}"

WARN_FLAGS="-Wall -Wextra -Werror -Wno-missing-field-initializers -Wno-unused-parameter -Wno-unused-function -Wno-unused-value"
MAX_ERRS="-fmax-errors=3"
C_FLAGS="-fPIC -ftls-model=initial-exec ${DEBUG} ${OPT} ${WARN_FLAGS} ${MAX_ERRS} ${FEATURES}"
CPP_FLAGS="-fno-rtti ${C_FLAGS}"

COMPILE="gcc -shared -o libbkmalloc.so -x c bkmalloc.h -DBKMALLOC_IMPL ${C_FLAGS}"
echo ${COMPILE}
${COMPILE} || exit $?
COMPILE="g++ -shared -o libbkmalloc.so -x c++ bkmalloc.h -DBKMALLOC_IMPL ${CPP_FLAGS}"
echo ${COMPILE}
${COMPILE}
