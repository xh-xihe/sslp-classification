#!/usr/bin/env bash
# Publish this working tree into the six-qubit-sslp/ subdirectory of the
# dyadic-lifts branch, without rewriting anything else on that branch.
#
# This repository is a standalone root history with files at the top level.
# The published branch is instead main plus one subdirectory. Nothing about
# that graft was written down before, so it is written down here.
#
#   usage:  tools/push-branch.sh "commit message"
#           tools/push-branch.sh --dry-run "commit message"
#
# Fail-closed: refuses to run on a dirty tree, and refuses to push a commit
# whose subdirectory tree does not match the local HEAD tree exactly.
set -euo pipefail

BRANCH=sixqubit-classification
PREFIX=six-qubit-sslp
DRY=0
if [ "${1:-}" = "--dry-run" ]; then DRY=1; shift; fi
MSG="${1:-}"
[ -n "$MSG" ] || { echo "usage: $0 [--dry-run] \"commit message\"" >&2; exit 2; }

cd "$(git rev-parse --show-toplevel)"

if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "refusing to publish: tracked files are modified. commit or stash first." >&2
  git status --short --untracked-files=no >&2
  exit 1
fi

git fetch -q origin "$BRANCH"
BASE=$(git rev-parse FETCH_HEAD)
LOCAL_TREE=$(git rev-parse HEAD^{tree})

# Build the published tree: the branch tip, with $PREFIX/ replaced wholesale.
IDX=$(mktemp)
trap 'rm -f "$IDX"' EXIT
export GIT_INDEX_FILE="$IDX"
git read-tree "$BASE"
git rm -r -q --cached --ignore-unmatch "$PREFIX"
git read-tree --prefix="$PREFIX/" "$LOCAL_TREE"
TREE=$(git write-tree)
unset GIT_INDEX_FILE

COMMIT=$(git commit-tree "$TREE" -p "$BASE" -m "$MSG")

# Verify before pushing, not after.
GOT=$(git rev-parse "$COMMIT:$PREFIX")
if [ "$GOT" != "$LOCAL_TREE" ]; then
  echo "refusing to push: grafted $PREFIX/ tree $GOT != local HEAD tree $LOCAL_TREE" >&2
  exit 1
fi
echo "base   $BASE"
echo "commit $COMMIT"
echo "tree   $PREFIX/ = $LOCAL_TREE (matches local HEAD)"

if [ "$DRY" = "1" ]; then
  echo "dry run: not pushing"
  exit 0
fi
git push origin "$COMMIT:refs/heads/$BRANCH"
git fetch -q origin "$BRANCH"
echo "pushed; $BRANCH now at $(git rev-parse --short FETCH_HEAD)"
