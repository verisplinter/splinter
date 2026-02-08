#!/bin/bash
cd "$(dirname "$0")"
time ~/work/verus-install/verus-x86-linux/verus src/main-ilsnaddrindex.rs \
    --verify-only-module implementation::ILsnAddrIndex_v \
    --verify-function *reverse* \
    --expand-errors --multiple-errors 5 \
    #--time

#    --verify-module implementation::JournalImpl_v \
#    --verify-module implementation::Implementation_v \
