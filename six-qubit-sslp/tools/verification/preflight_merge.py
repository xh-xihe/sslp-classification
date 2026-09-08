#!/usr/bin/env python3
"""Build a single scratch Lean file that inlines the un-built modules in a
target's import closure, so `lake env lean` can check it while a serial build
holds the build lock.

A module added since the running build computed its plan has no `.olean` at
all, so anything importing it fails immediately with "object file ... does not
exist".  Building that olean by hand into the shared tree races the driver.
Concatenating instead is safe: emit the union of the *built* imports at the
top, then every un-built module's body in dependency order, with its own
`import` lines stripped.

Usage:
    python tools/verification/preflight_merge.py MainTheory.Foo [-o out.lean]

It also reports which modules in the closure have an olean older than their
source, or no content-validation stamp: a pre-flight over those is provisional,
not conclusive.
"""
import argparse
import hashlib
import io
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OLEAN_DIR = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean')
STAMP_DIR = os.path.join(ROOT, '.lake', 'build', 'certification', 'stamps')


def source_of(module):
    return os.path.join(ROOT, module.replace('.', os.sep) + '.lean')


def olean_of(module):
    return os.path.join(OLEAN_DIR, module.replace('.', os.sep) + '.olean')


def stamp_of(module):
    return os.path.join(STAMP_DIR, module.replace('.', os.sep) + '.json')


def imports_of(module):
    """The `import` lines at the head of a repo module, as module names."""
    out = []
    with io.open(source_of(module), encoding='utf-8') as handle:
        for line in handle:
            line = line.strip()
            if line.startswith('import '):
                out.append(line.split()[1])
            elif line and not line.startswith('--') and not line.startswith('/-'):
                break
    return out


def is_repo_module(module):
    return os.path.exists(source_of(module))


def built(module):
    return os.path.exists(olean_of(module))


def closure(target):
    """Every repo module reachable from `target`, target included."""
    seen, stack = set(), [target]
    while stack:
        module = stack.pop()
        if module in seen or not is_repo_module(module):
            continue
        seen.add(module)
        stack.extend(imports_of(module))
    return seen


def unbuilt_order(target, force=()):
    """Un-built repo modules in the target's closure, in dependency order.

    `force` names modules to inline even though an olean exists -- use it when
    that olean is older than its source, so the check reads the source instead
    of a possibly stale compiled API.
    """
    order, visiting = [], set()
    force = set(force)

    def visit(module):
        if module in order or module in visiting or not is_repo_module(module):
            return
        if built(module) and module != target and module not in force:
            return
        visiting.add(module)
        for dep in imports_of(module):
            visit(dep)
        visiting.discard(module)
        order.append(module)

    visit(target)
    return order


def freshness(target):
    """Three separate signals, because they mean different things.

    `stale`     -- the olean predates its source, so the elaborator would load
                   an older API and a clean result can be a false green.  This
                   is a weak proxy: a checkout or any other git operation
                   rewrites mtimes without changing content, and the build
                   driver validates by content hash, not by mtime.  Treat it
                   as a prompt to check the stamp, not as a verdict.
    `mismatch`  -- a stamp exists but records a different source hash: the
                   same defect, caught by content rather than by mtime.
    `unstamped` -- no stamp at all.  Expected for most modules while a serial
                   build is still walking its plan; the olean on disk may be
                   perfectly current from an earlier run, so this alone is not
                   a reason to distrust the check.
    """
    stale, mismatch, unstamped = [], [], []
    for module in sorted(closure(target)):
        if module == target or not built(module):
            continue
        src, ole = source_of(module), olean_of(module)
        if os.path.getmtime(ole) < os.path.getmtime(src):
            stale.append(module)
        path = stamp_of(module)
        if not os.path.exists(path):
            unstamped.append(module)
            continue
        try:
            record = json.loads(io.open(path, encoding='utf-8').read())
        except (OSError, ValueError):
            mismatch.append(module)
            continue
        digest = hashlib.sha256(open(src, 'rb').read()).hexdigest()
        if record.get('source_sha256') != digest:
            mismatch.append(module)
    return stale, mismatch, unstamped


def merge(target, out_path, force=()):
    inline = unbuilt_order(target, force)
    inline_set = set(inline)
    header, bodies = [], []
    for module in inline:
        for dep in imports_of(module):
            line = 'import ' + dep
            if dep not in inline_set and line not in header:
                header.append(line)
        lines = io.open(source_of(module), encoding='utf-8').read().splitlines()
        bodies.append('\n'.join(l for l in lines if not l.startswith('import ')))
    text = '\n'.join(header) + '\n' + '\n'.join(bodies) + '\n'
    io.open(out_path, 'w', encoding='utf-8', newline='').write(text)
    return inline, header, text


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument('module')
    parser.add_argument('-o', '--out', default='_preflight_tmp.lean')
    parser.add_argument('--force', nargs='*', default=[],
                        help='inline these modules even if an olean exists')
    parser.add_argument('--print-axioms', nargs='*', default=None,
                        help='append `#print axioms` lines for these names')
    args = parser.parse_args(argv)

    out_path = args.out if os.path.isabs(args.out) else os.path.join(ROOT, args.out)
    inline, header, text = merge(args.module, out_path, args.force)
    if args.print_axioms:
        text += '\n' + ''.join('#print axioms %s\n' % n for n in args.print_axioms)
        io.open(out_path, 'w', encoding='utf-8', newline='').write(text)

    stale, mismatch, unstamped = freshness(args.module)
    sys.stdout.write('scratch: %s\n' % out_path)
    sys.stdout.write('inlined %d un-built module(s): %s\n'
                     % (len(inline), ', '.join(inline)))
    sys.stdout.write('imports kept: %d\n' % len(header))
    sys.stdout.write('olean older than its source: %d%s\n'
                     % (len(stale), (' -- ' + ', '.join(stale[:6])) if stale else ''))
    sys.stdout.write('stamp records a different source: %d%s\n'
                     % (len(mismatch),
                        (' -- ' + ', '.join(mismatch[:6])) if mismatch else ''))
    sys.stdout.write('no stamp yet (build has not reached them): %d\n' % len(unstamped))
    if stale or mismatch:
        sys.stdout.write('NOTE: a clean result here is provisional, not conclusive.\n')
    else:
        sys.stdout.write('Every built module in the closure is current; a clean '
                         'result here is conclusive.\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
