#!/bin/bash
cd "$(dirname "$0")"
time ~/work/verus-install/verus-x86-linux/verus src/main.rs \
    --expand-errors --multiple-errors 5 \
    #--time
