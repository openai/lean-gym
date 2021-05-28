#!/bin/bash

# run from project root

rm -rf leanpkg.path
rm -rf _target

cp leanpkg_lean-liquid.toml leanpkg.toml
leanpkg configure
mkdir ./_target/deps/lean-liquid/scripts/
cp ./_target/deps/mathlib/scripts/mk_all.sh ./_target/deps/lean-liquid/scripts/mk_all.sh
bash ./_target/deps/lean-liquid/scripts/mk_all.sh
cd _target/deps/lean-liquid && leanproject get-mathlib-cache && cd ../../../
leanpkg build
