#!/bin/bash
cd "$(dirname "$0")"
time ~/work/verus/source/target-verus/release/verus src/main.rs \
    --expand-errors --multiple-errors 5 \
    #--time
