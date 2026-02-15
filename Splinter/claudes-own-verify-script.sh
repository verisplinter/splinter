#!/bin/bash
cd "$(dirname "$0")"
MODULE="${1:-}"
if [ -n "$MODULE" ]; then
    time ~/work/verus/source/target-verus/release/verus src/main.rs \
        --expand-errors --multiple-errors 5 \
        --verify-module "$MODULE"
else
    time ~/work/verus/source/target-verus/release/verus src/main.rs \
        --expand-errors --multiple-errors 5
fi
