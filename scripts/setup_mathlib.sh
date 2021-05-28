#!/bin/bash

# run from project root

rm -rf leanpkg.path
rm -rf _target

cp leanpkg_mathlib.toml leanpkg.toml
leanpkg configure
bash ./_target/deps/mathlib/scripts/mk_all.sh
leanproject get-mathlib-cache
leanpkg build
