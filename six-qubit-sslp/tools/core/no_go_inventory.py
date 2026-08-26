"""Authoritative, fail-closed inventory of the 51 certified no-go modules.

The single source of truth is ``tools/manifest.json`` under
``_no_go.lean_modules``.  Full-suite verification must match that mapping
exactly.  Explicit orbit arguments intentionally select a subset, but every
requested module must still exist and contain the real headline theorem.
"""
import io
import json
import os
import re


class InventoryError(RuntimeError):
    pass


HEADLINE = re.compile(r'^theorem\s+no_go_of_moments\b', re.M)


def expected_no_go_modules(repo):
    path = os.path.join(repo, 'tools', 'manifest.json')
    manifest = json.loads(io.open(path, encoding='utf-8').read())
    try:
        mapping = manifest['_no_go']['lean_modules']
    except (KeyError, TypeError):
        raise InventoryError('manifest lacks _no_go.lean_modules metadata')
    if not isinstance(mapping, dict) or len(mapping) != 51:
        raise InventoryError('manifest no-go inventory has %d entries, expected 51'
                             % (len(mapping) if isinstance(mapping, dict) else -1))
    out = {}
    for oid, module in mapping.items():
        if not re.fullmatch(r'\d+', oid) or oid not in manifest:
            raise InventoryError('invalid or absent manifest orbit key %r' % oid)
        expected_name = 'Order9' if oid == '66' else 'Orbit' + oid
        if module != expected_name:
            raise InventoryError('orbit %s maps to %r, expected conventional module %r'
                                 % (oid, module, expected_name))
        if module in out.values():
            raise InventoryError('duplicate module %r in manifest no-go inventory'
                                 % module)
        out[oid] = module
    return dict(sorted(out.items(), key=lambda kv: int(kv[0])))


def source_snapshot(repo):
    sq = os.path.join(repo, 'SixQubit')
    return {
        f: io.open(os.path.join(sq, f), encoding='utf-8').read()
        for f in os.listdir(sq) if f.endswith('.lean')
    }


def select_no_go_sources(repo, argv=(), sources=None):
    """Return ``[(filename, orbit_id, source)]`` or raise ``InventoryError``."""
    expected = expected_no_go_modules(repo)
    sources = source_snapshot(repo) if sources is None else dict(sources)
    requested = list(argv or [])
    if requested:
        unknown = sorted(set(requested) - set(expected), key=lambda x: int(x)
                         if str(x).isdigit() else -1)
        if unknown:
            raise InventoryError('requested orbit(s) not in certified no-go inventory: %s'
                                 % ', '.join(unknown))
        chosen = {oid: expected[oid] for oid in sorted(set(requested), key=int)}
    else:
        chosen = expected

    problems = []
    for oid, module in chosen.items():
        f = module + '.lean'
        if f not in sources:
            problems.append('missing %s' % f)
        elif not HEADLINE.search(sources[f]):
            problems.append('%s lacks top-level theorem no_go_of_moments' % f)

    if not requested:
        expected_files = {m + '.lean' for m in expected.values()}
        marked_files = {f for f, src in sources.items() if HEADLINE.search(src)}
        for f in sorted(marked_files - expected_files):
            problems.append('unexpected certified-looking module %s' % f)
        # The loop above distinguishes deletion from marker removal.  This set
        # comparison also guards against any future inventory-selection bug.
        for f in sorted(expected_files - marked_files):
            if not any(p.startswith('missing ' + f) or
                       p.startswith(f + ' lacks ') for p in problems):
                problems.append('expected headline absent from %s' % f)

    if problems:
        raise InventoryError('; '.join(problems))
    return [(module + '.lean', oid, sources[module + '.lean'])
            for oid, module in chosen.items()]


def inventory_selftest(repo):
    """In-memory deletion/marker/unexpected-module regression test."""
    original = source_snapshot(repo)
    expected = expected_no_go_modules(repo)
    oid, module = next(iter(expected.items()))
    filename = module + '.lean'
    variants = []

    deleted = dict(original)
    deleted.pop(filename, None)
    variants.append(('delete ' + filename, deleted, deleted != original))

    markerless = dict(original)
    bad, n = HEADLINE.subn('theorem no_go_of_moments_deleted',
                           markerless.get(filename, ''), count=1)
    markerless[filename] = bad
    variants.append(('delete headline marker in ' + filename, markerless, n == 1))

    unexpected = dict(original)
    unexpected['Orbit999.lean'] = 'theorem no_go_of_moments : False := by trivial\n'
    variants.append(('add unexpected headline module', unexpected, True))

    caught = missed = inert = 0
    details = []
    # A broken starting tree must not make every negative control appear to be
    # caught for the wrong reason (especially relevant to ``gate --selftest``).
    try:
        full = select_no_go_sources(repo, [], original)
        if len(full) != 51:
            raise InventoryError('full inventory selected %d modules' % len(full))
    except InventoryError as exc:
        missed += 1
        details.append(('MISSED', 'valid full inventory: ' + str(exc)))
    for name, mutated, injected in variants:
        if not injected:
            inert += 1
            details.append(('INERT', name))
            continue
        try:
            select_no_go_sources(repo, [], mutated)
        except InventoryError:
            caught += 1
        else:
            missed += 1
            details.append(('MISSED', name))

    # Positive control: explicit subset selection remains supported.
    try:
        one = select_no_go_sources(repo, [oid], original)
        if len(one) != 1 or one[0][1] != oid:
            raise InventoryError('wrong subset result')
    except InventoryError as exc:
        missed += 1
        details.append(('MISSED', 'valid subset: ' + str(exc)))
    return caught, missed, inert, details
