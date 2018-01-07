#!/usr/bin/env bash

if [ $# -ge 1 ]; then
  TEST_DIR=$1;
else
  TEST_DIR=examples/good;
fi;

for i in `find $TEST_DIR -type f | sort | grep \\.lat$`; do 
  echo $i; 
  file=$(basename $i .lat);
  ./latc_x86_64 $TEST_DIR/$file.lat;
  if [ $? -ne 0 ]; then
    exit 1;
  fi;
  if [ ! -f $TEST_DIR/$file.input ]; then
    $TEST_DIR/$file | diff - $TEST_DIR/$file.output;
    if [ $? -ne 0 ]; then
      echo "[FAIL] $file failed"
      exit 1;
    fi
  else 
    $TEST_DIR/$file < $TEST_DIR/$file.input | diff - $TEST_DIR/$file.output;
    if [ $? -ne 0 ]; then
      echo "[FAIL] $file failed"
      exit 1;
    fi
  fi; 
done;
