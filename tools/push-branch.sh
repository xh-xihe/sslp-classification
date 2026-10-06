#!/usr/bin/env bash
# Publish the canonical main branch from the repository root.
# The former subdirectory-grafting publisher is retained in the layout archive.
# Usage: tools/push-branch.sh [--dry-run]
set -euo pipefail
DRY=0
if [ "${1:-}" = "--dry-run" ]; then DRY=1; shift; fi
[ "$#" -eq 0 ] || { echo "usage: $0 [--dry-run]" >&2; exit 2; }
cd "$(git rev-parse --show-toplevel)"
[ "$(git branch --show-current)" = "main" ] || {
  echo "refusing to publish: check out main in a clean root-layout clone first." >&2; exit 1;
}
[ -z "$(git status --porcelain --untracked-files=no)" ] || {
  echo "refusing to publish: tracked files have uncommitted changes." >&2; exit 1;
}
git cat-file -e HEAD:lakefile.lean
git cat-file -e HEAD:tools/build_lean.py
git fetch -q origin main
git merge-base --is-ancestor FETCH_HEAD HEAD || {
  echo "refusing to publish: local main must include remote main." >&2; exit 1;
}
if [ "$DRY" = "1" ]; then
  git push --dry-run origin HEAD:refs/heads/main
else
  git push origin HEAD:refs/heads/main
fi
