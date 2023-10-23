#!/bin/bash

set -e

# Don't try to exec is `-c` is specified
if [[ " ${@}" =~  [[:space:]]+-[ch][[:space:]]+ ]]; then
    cargo run -- $@
else
    cargo run -- $@ && ./a.out
fi
