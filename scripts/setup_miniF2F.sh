#!/bin/bash

# run from project root

rm -rf leanpkg.path
rm -rf _target

cp leanpkg_miniF2F.toml leanpkg.toml
leanpkg configure
mkdir ./_target/deps/minif2f/lean/scripts/
cp ./_target/deps/mathlib/scripts/mk_all.sh ./_target/deps/minif2f/lean/scripts/mk_all.sh
bash ./_target/deps/minif2f/lean/scripts/mk_all.sh
leanproject get-mathlib-cache
# cd _target/deps/minif2f && leanproject get-mathlib-cache && cd ../../../
leanpkg build
