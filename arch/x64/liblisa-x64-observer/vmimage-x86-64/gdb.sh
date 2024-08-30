#! /bin/bash

gdb -ex "target remote localhost:1234" -ex "file $1"
