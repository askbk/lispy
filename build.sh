#!/usr/bin/sh
gcc prompt.c vendor/mpc.c -lm -leditline -o prompt