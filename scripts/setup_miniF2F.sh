#!/bin/bash

# run from project root

rm -rf leanpkg.path
rm -rf _target

cp leanpkg_miniF2F.toml leanpkg.toml
leanpkg configure
bash ./_target/deps/mathlib/scripts/mk_all.sh

mv ./_target/deps/mathlib/src/all.lean ./_target/deps/minif2f/lean/src/all.lean
echo "import test" >> ./_target/deps/minif2f/lean/src/all.lean
echo "import valid" >> ./_target/deps/minif2f/lean/src/all.lean

leanproject get-mathlib-cache
leanpkg build
