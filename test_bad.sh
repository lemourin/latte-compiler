#!/usr/bin/env bash

if [ $# -ge 1 ]; then
  TEST_DIR=$1;
else
  TEST_DIR=examples/bad;
fi;

for i in `find $TEST_DIR -type f | sort | grep \\.lat$`; do 
  echo $i; 
  file=$(basename $i .lat);
  ./latc_x86_64 $TEST_DIR/$file.lat &> /dev/null;
  if [ $? -eq 0 ]; then
    echo "[FAIL] $file should not compile"
    exit 1;
  fi;
done;
