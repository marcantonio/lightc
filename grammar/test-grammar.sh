#!/bin/bash

set -e

ANTLR_RT=/usr/share/java/antlr4-runtime.jar
GRUN_PATH=/usr/share/antlr4/grun

rm -rf tmp
mkdir tmp
antlr4 -o tmp light.g4
javac -classpath $ANTLR_RT tmp/light*.java
cd tmp
$GRUN_PATH light program -tokens -tree -gui < ../test-input.lt
cd -
