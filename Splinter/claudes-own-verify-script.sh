#!/bin/bash
cd "$(dirname "$0")"
time ~/work/verus-install/verus-x86-linux/verus src/main.rs \
    --verify-module implementation::Implementation_v \
    --verify-module implementation::JournalImpl_v \
    --expand-errors --multiple-errors 5 \
    --time
