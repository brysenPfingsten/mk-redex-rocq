#!/bin/sh
set -eu
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT HUP INT TERM
./mk-search --fuel 1 examples/seven.sexp > "$scratch/seven"
grep -q '^status: complete$' "$scratch/seven"
grep -q '^answer 1: {q0 = 7}$' "$scratch/seven"
./mk-search --fuel 1 --trace examples/seven.sexp > "$scratch/trace"
grep -q '^trace 1:' "$scratch/trace"
if ./mk-search --fuel 0 examples/seven.sexp > "$scratch/zero"; then exit 1; else test "$?" -eq 3; fi
grep -q '^status: fuel exhausted$' "$scratch/zero"
if ./mk-search examples/bad-call.sexp > "$scratch/out" 2> "$scratch/error"; then exit 1; else test "$?" -eq 2; fi
test ! -s "$scratch/out"
grep -q 'input rejected:' "$scratch/error"
if ./mk-search --fuel 100 examples/sevens.sexp > "$scratch/recursive"; then exit 1; else test "$?" -eq 3; fi
grep -q '^answer 1: {q0 = 7}$' "$scratch/recursive"
./mk-search examples/residual.sexp > "$scratch/residual"
grep -q '^answer 1: {q0 = (_1 . _1)}$' "$scratch/residual"
printf 'passed CLI integration checks\n'
