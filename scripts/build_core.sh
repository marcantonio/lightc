#!/bin/bash

set -e

cargo run -- -c core/core.lt
mv .build/core.* core/
