#!/bin/bash
cd "$(dirname "$0")"
time ~/work/verus-install/verus-x86-linux/verus src/main-journalimpl.rs \
    --verify-only-module implementation::JournalImpl_v \
    --verify-only-module implementation::ILsnAddrIndex_v \
    --expand-errors --multiple-errors 5 \
    #--time
