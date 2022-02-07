#!/bin/bash

# run from project root

leanpkg configure
bash ./_target/deps/mathlib/scripts/mk_all.sh
leanproject get-mathlib-cache
leanpkg build
