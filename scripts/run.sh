#!/bin/bash

set -e

# Don't try to exec compiled binary for these switches
if [[ " ${@} " =~  [[:space:]]+-[chn][[:space:]]+ ]]; then
    cargo run -- $@
else
    cargo run -- $@ && ./a.out
fi
