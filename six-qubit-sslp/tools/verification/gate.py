"""The acceptance gate: validate every Lean orbit module against the manifest.

This is the check that was missing, and whose absence let four modules prove a
no-go for the wrong projective order and five more carry a MomentSystem whose
rows did not match the order the headline passes its probabilities in.

SCOPE.  This gate checks the manifest data -- angle vector, residue, both
fibers -- and the right-hand side of each `m<coords>` moment row.  It does NOT
check left-hand sides, differently-named rows, normalizations or nonnegativity;
a collaborator showed that by mutating a left-hand side and a `c12`-style field
in memory and watching the gate stay green.  Those obligations are now covered
by `momentgate.py`, which identifies rows by CONTENT rather than by name and is
itself validated by an injected-mutation self-test.  Run both:

    python tools/run.py verification/gate.py
    python tools/run.py verification/momentgate.py
    python tools/run.py verification/momentgate.py --selftest

Checks, per module with a `no_go_of_moments`:
  1. `av` reproduces the manifest's (q, a).
  2. The residue in `S1_eq_fiber` equals the manifest's delta = q/m.
  3. The declared bottom/top supports have the manifest's fiber cardinalities
     and are exactly the residue fibers.
  4. Each recognized `m<coords>` right-hand side matches the headline's top
     probability order. `momentgate.py` checks every complete row.

Two parsing hazards are handled explicitly, because both produced false
positives while this was being written:
  * generated Lean uses irregular whitespace, so every pattern is `\\s+`-tolerant;
  * structure fields WRAP across lines, so fields are joined before parsing.
An over-strict parser here is worse than no gate, since it cries wolf.

Usage:  python tools/run.py verification/gate.py
Exit code is nonzero if any module fails.
"""
import io
import json
import os
import re
import sys
from itertools import combinations
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'core'))
from orbit import fiber
from no_go_inventory import (InventoryError, inventory_selftest,
                             select_no_go_sources)

SQ = os.path.join(REPO, 'SixQubit')
MAN = json.loads(io.open(os.path.join(REPO, 'tools', 'manifest.json'),
                         encoding='utf-8').read())
BITS = {'true': 1, 'false': 0}
S = r'\s+'


def bitstrings(src):
    ys, zs = {}, {}
    pat = (r'def' + S + r'(y|z)(\d+)' + S + r':' + S + r'SS\.BitString' + S +
           r'6' + S + r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
    for m in re.finditer(pat, src):
        v = [BITS[m.group(i + 3)] for i in range(6)]
        (ys if m.group(1) == 'y' else zs)[int(m.group(2))] = v
    return ys, zs


def struct_fields(src):
    """Join wrapped fields of the MomentSystem structure before parsing them.

    Restricted to the structure block. Proof bodies also contain lines indented
    by two spaces, so scanning the whole file lets a tactic line silently
    overwrite a field of the same name -- which manufactured a wave of false
    failures the first time this check was written.
    """
    k = src.find('structure MomentSystem')
    if k < 0:
        return {}
    body = src[k:]
    nl = body.index(chr(10)) + 1
    m = re.search(r'^\S', body[nl:], re.M)
    body = body[:nl + m.start()] if m else body
    out, cur = {}, None
    for ln in body.split('\n'):
        mh = re.match(r'  (\w+)\s*:\s*(.*)$', ln)
        if mh and not ln.startswith('   '):
            cur = mh.group(1)
            out[cur] = mh.group(2)
        elif cur is not None and ln.startswith('      '):
            out[cur] += ' ' + ln.strip()
        elif ln.strip() == '' or not ln.startswith(' '):
            cur = None
    return out


def headline_top(src, ys, zs):
    k = src.find('theorem no_go_of_moments')
    body = src[k:src.find(': False', k)]
    comp = [int(x) for x in re.findall(
        r'Complex\.normSq' + S + r'\(d' + S + r'\(SS\.complement' + S +
        r'y(\d+)\)\)', body)]
    if comp:
        if any(i not in ys for i in comp):
            return None, None
        return 'complement', [[1 - b for b in ys[i]] for i in comp]
    lex = [int(x) for x in re.findall(
        r'Complex\.normSq' + S + r'\(d' + S + r'z(\d+)\)', body)]
    if not lex or any(i not in zs for i in lex):
        return None, None
    return 'lex', [zs[i] for i in lex]


if '--selftest' in sys.argv:
    caught, missed, inert, details = inventory_selftest(REPO)
    for status, why in details:
        print('  %-6s %s' % (status, why))
    print('INVENTORY SELF-TEST: caught %d, missed %d, not injected %d'
          % (caught, missed, inert))
    sys.exit(1 if missed or inert else 0)

argv = [a for a in sys.argv[1:] if not a.startswith('--')]
try:
    selected = select_no_go_sources(REPO, argv)
except InventoryError as exc:
    print('FAIL - certified no-go inventory mismatch: %s' % exc)
    sys.exit(1)

fails, unchecked, ok = [], [], 0
for f, oid, src in selected:
    mod = f[:-5]
    ent = MAN.get(oid)
    if ent is None:
        fails.append((mod, 'orbit %s not in the manifest' % oid))
        continue

    problems = []
    if ent['m'] <= 0 or ent['q'] % ent['m'] != 0:
        problems.append('manifest has invalid q=%s, m=%s' % (ent['q'], ent['m']))
    else:
        expected_d = ent['q'] // ent['m']
        if ent['d'] != expected_d:
            problems.append('manifest residue %s is not q/m=%s'
                            % (ent['d'], expected_d))
        elif ent['q'] // gcd(ent['q'], ent['d']) != ent['m']:
            problems.append('manifest residue %s does not have additive order %s'
                            % (ent['d'], ent['m']))
    mav = re.search(r'def' + S + r'av' + S + r':' + S + r'Fin' + S + r'6' + S +
                    r'->' + S + r'ZMod' + S + r'(\d+)' + S + r':=' + S +
                    r'!\[([^\]]*)\]', src)
    if not mav:
        unchecked.append((mod, 'no `av` definition to check against'))
        continue
    q = int(mav.group(1))
    a = [int(x.strip()) for x in mav.group(2).split(',')]
    if q != ent['q']:
        problems.append('q=%d, manifest says %d' % (q, ent['q']))
    if sorted(a) != sorted(ent['a']):
        problems.append('a=%s, manifest says %s' % (a, ent['a']))

    md = re.search(r'SS\.weight' + S + r'av' + S + r'x' + S + r'=' + S +
                   r'(\d+)\)' + S + r'=' + S + r'S1', src)
    if md is None:
        problems.append('could not read the residue from S1_eq_fiber; a silent default would hide exactly the defect this gate exists to catch')
        d = None
    else:
        d = int(md.group(1))
    if d is not None and d != ent['d']:
        problems.append('residue %d, manifest requires delta = q/m = %d '
                        '(projective order %d)' % (d, ent['d'], ent['m']))

    ys, zs = bitstrings(src)
    if q == ent['q'] and sorted(a) == sorted(ent['a']):
        S0 = set(''.join(map(str, v)) for v in ys.values())
        want0 = set(fiber(a, q, 0))
        if not ys:
            problems.append('could not parse any declared bottom support states')
        elif S0 != want0:
            problems.append('declared bottom support is not the residue-0 fiber')
        if ys and len(ys) != ent['n0']:
            problems.append('bottom support has %d states, manifest says %d'
                            % (len(ys), ent['n0']))
        # the TOP fiber too: either declared as `def z*`, or as the image of the
        # bottom under complement.  Checking only the bottom left half the
        # support unverified.
        if d is not None:
            want1 = set(fiber(a, q, d))
            if zs:
                got1 = set(''.join(map(str, v)) for v in zs.values())
                if got1 != want1:
                    problems.append('declared top support is not the residue-%d fiber' % d)
                if len(zs) != ent['n1']:
                    problems.append('top support has %d states, manifest says %d'
                                    % (len(zs), ent['n1']))
            elif ys:
                comp = set(''.join(str(1 - b) for b in v) for v in ys.values())
                if comp != want1:
                    problems.append('complement of the bottom support is not the '
                                    'residue-%d fiber' % d)
                if len(comp) != ent['n1']:
                    problems.append('complement top support has %d states, manifest says %d'
                                    % (len(comp), ent['n1']))

    kind, top = headline_top(src, ys, zs)
    module_unchecked = False
    if top is None:
        unchecked.append((mod, 'could not resolve how the headline orders the '
                               'top probabilities'))
        module_unchecked = True
    else:
        fields = struct_fields(src)
        mism = []
        for T in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
            nm = 'm%s' % ''.join(str(j + 1) for j in T)
            row = fields.get(nm)
            if not row or '=' not in row:
                continue
            got = sorted(int(x) for x in
                         re.findall(r'r(\d+)', row.split('=')[1]))
            wantT = sorted(k for k in range(len(top))
                           if all(top[k][j] == 1 for j in T))
            if got != wantT:
                mism.append(nm)
        if mism:
            problems.append('MomentSystem rows %s do not match the order the '
                            'headline passes top probabilities (%s)'
                            % (','.join(mism[:4]) + ('...' if len(mism) > 4 else ''),
                               kind))
        bot = [ys[i] for i in sorted(ys)]

    if problems:
        fails.append((mod, '; '.join(problems)))
    elif not module_unchecked:
        ok += 1

print('modules gated: %d passed, %d failed, %d unchecked'
      % (ok, len(fails), len(unchecked)))
print()
for mod, why in unchecked:
    print('UNCHECKED %-9s %s' % (mod, why))
if unchecked:
    print()
for mod, why in fails:
    print('FAIL %-9s %s' % (mod, why))
if fails or unchecked:
    print()
    print('FAIL - an unchecked module is not a passing module; a gate that exits')
    print('       zero on what it could not read is worse than no gate at all.')
    sys.exit(1)
print('every module matches the manifest and its own headline ordering')
