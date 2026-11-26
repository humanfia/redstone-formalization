#!/usr/bin/env bash
# Prepares a git worktree of this repository for building, without downloading Mathlib again:
#
#   tools/setup-worktree.sh
#
# * `.lake/packages` becomes a link to the packages of the main checkout (same manifest).
# * When the worktree is under $HOME and /data/$USER exists, `.lake/build` becomes a link to the
#   same path under /data/$USER, so that build output does not fill the home directory.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
main="$(git worktree list --porcelain | sed -n '1s/^worktree //p')"
mkdir -p .lake
if [ "$main" != "$PWD" ] && [ ! -e .lake/packages ]; then
  [ -d "$main/.lake/packages" ] || { echo "no packages in $main; run 'lake exe cache get' there" >&2; exit 1; }
  cmp -s lake-manifest.json "$main/lake-manifest.json" || { echo "lake-manifest.json differs from $main" >&2; exit 1; }
  ln -s "$main/.lake/packages" .lake/packages
fi
data="/data/$USER"
if [ -d "$data" ] && [ ! -e .lake/build ] && [ "${PWD#"$HOME"/}" != "$PWD" ]; then
  target="$data/${PWD#"$HOME"/}/.lake/build"
  mkdir -p "$target"
  ln -s "$target" .lake/build
fi
echo "ok: $(readlink -f .lake/packages), $(readlink -f .lake/build 2>/dev/null || echo .lake/build)"
