#!/bin/bash

set -e

cargo run -- -c core/core.lt
mv core.i core.o core/
