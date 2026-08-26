"""Verify every (flip mask, dressing) pair used in a headline theorem is a
genuine weight-at-most-two Pauli:  |supp(e) union supp(z)| <= 2.

A weight-3 row would silently turn the statement into a distance-4 no-go, which
is a different and much weaker claim.

Two bugs this script used to have, fixed here because a collaborator's audit
caught them:
  * it defaulted to orbit 5 alone while the README claimed it covered all 51;
  * it returned exit code 0 even when a mask or dressing could not be resolved,
    so unresolved rows read as passing rows.
Now it defaults to EVERY module with a headline, and unresolved rows are a
failure, not a silence.

Usage:
    python tools/run.py verification/admis.py           # every module
    python tools/run.py verification/admis.py 5 26 31   # selected orbits
    python tools/run.py verification/admis.py --selftest

The parser is deliberately conservative and fail-closed for the headline
grammar used here; it is not a general Lean parser.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'core'))
from no_go_inventory import (InventoryError, inventory_selftest,
                             select_no_go_sources)

SQ = os.path.join(REPO, 'SixQubit')
BITS = {'true': 1, 'false': 0}
S = r'\s+'


def modules(argv):
    return select_no_go_sources(REPO, argv)


def masks(src):
    """Resolve every BitString definition: literal, bxor, stdBasis, complement."""
    d = {}
    pat = (r'def' + S + r'(\w+)' + S + r':' + S + r'SS\.BitString' + S + r'6' +
           S + r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
    for m in re.finditer(pat, src):
        d[m.group(1)] = [BITS[m.group(i + 2)] for i in range(6)]
    for m in re.finditer(r'def' + S + r'(\w+)' + S + r':' + S + r'SS\.BitString' +
                         S + r'6' + S + r':=' + S + r'SS\.stdBasis' + S + r'(\d+)', src):
        i = int(m.group(2))
        d[m.group(1)] = [1 if k == i else 0 for k in range(6)]
    for _ in range(3):                      # resolve chains
        for m in re.finditer(r'def' + S + r'(\w+)' + S + r':' + S +
                             r'SS\.BitString' + S + r'6' + S + r':=' + S +
                             r'SS\.bxor' + S + r'(\w+)' + S + r'(\w+)', src):
            a, b = m.group(2), m.group(3)
            if a in d and b in d:
                d[m.group(1)] = [d[a][i] ^ d[b][i] for i in range(6)]
        for m in re.finditer(r'def' + S + r'(\w+)' + S + r':' + S +
                             r'SS\.BitString' + S + r'6' + S + r':=' + S +
                             r'SS\.complement' + S + r'(\w+)', src):
            if m.group(2) in d:
                d[m.group(1)] = [1 - x for x in d[m.group(2)]]
    return d


def headline_block(src):
    """Headline before the top-level theorem result; never truncate at a binder."""
    k = src.find('theorem no_go_of_moments')
    if k < 0:
        return None
    stack, i = [], k
    line_comment = string = False
    block_comment = 0
    pairs = {')': '(', ']': '[', '}': '{'}
    while i < len(src):
        if line_comment:
            if src[i] == chr(10):
                line_comment = False
            i += 1
            continue
        if block_comment:
            if src.startswith('/-', i):
                block_comment += 1; i += 2
            elif src.startswith('-/', i):
                block_comment -= 1; i += 2
            else:
                i += 1
            continue
        if string:
            if src[i] == '\\':
                i += 2
            else:
                string = src[i] != '"'; i += 1
            continue
        if src.startswith('--', i):
            line_comment = True; i += 2; continue
        if src.startswith('/-', i):
            block_comment = 1; i += 2; continue
        ch = src[i]
        if ch == '"':
            string = True; i += 1; continue
        if ch in '([{':
            stack.append(ch)
        elif ch in ')]}':
            if not stack or stack.pop() != pairs[ch]:
                return None
        elif not stack and ch == ':':
            return src[k:i] if re.match(r':\s*False\s*:=', src[i:]) else None
        i += 1
    return None


def binders(body):
    """All top-level (), {} and [] binders, or None on malformed syntax."""
    out, stack, cur, outer = [], [], '', None
    pairs = {')': '(', ']': '[', '}': '{'}
    for ch in body:
        if ch in '([{':
            if not stack:
                cur, outer = '', ch
            else:
                cur += ch
            stack.append(ch)
        elif ch in ')]}':
            if not stack or stack.pop() != pairs[ch]:
                return None
            if stack:
                cur += ch
            else:
                out.append((outer, cur))
        elif stack:
            cur += ch
    return out if not stack else None


def top_tokens(text):
    """Whitespace tokens, keeping a parenthesized lambda/expression together."""
    out, stack, cur = [], [], ''
    pairs = {')': '(', ']': '[', '}': '{'}
    for ch in text.strip():
        if ch in '([{':
            stack.append(ch); cur += ch
        elif ch in ')]}':
            if not stack or stack.pop() != pairs[ch]:
                return None
            cur += ch
        elif ch.isspace() and not stack:
            if cur:
                out.append(cur); cur = ''
        else:
            cur += ch
    if stack:
        return None
    if cur:
        out.append(cur)
    return out


def binder_parts(raw):
    """Split ``names : type`` at its top-level colon."""
    stack = []
    pairs = {')': '(', ']': '[', '}': '{'}
    for i, ch in enumerate(raw):
        if ch in '([{':
            stack.append(ch)
        elif ch in ')]}':
            if not stack or stack.pop() != pairs[ch]:
                return None
        elif ch == ':' and not stack:
            return (' '.join(raw[:i].split()), ' '.join(raw[i + 1:].split()))
    return None


def row_kind(typ):
    """Exact grammar for the only four legitimate headline binder types."""
    if typ == 'SS.BitString 6 -> ℂ':
        return 'amplitude', None
    tok = top_tokens(typ)
    if not tok:
        return None, None
    bot_arg = re.compile(r'^\(Complex\.normSq \(c y\d+\)\)$')
    top_z = re.compile(r'^\(Complex\.normSq \(d z\d+\)\)$')
    top_c = re.compile(
        r'^\(Complex\.normSq \(d \(SS\.complement y\d+\)\)\)$')
    if tok[0] == 'MomentSystem' and len(tok) > 2:
        kinds = [('b' if bot_arg.fullmatch(t) else
                  'z' if top_z.fullmatch(t) else
                  'c' if top_c.fullmatch(t) else '?') for t in tok[1:]]
        first_top = next((i for i, x in enumerate(kinds) if x in 'zc'), None)
        if (first_top not in (None, 0) and all(x == 'b' for x in kinds[:first_top])
                and len(set(kinds[first_top:])) == 1 and
                kinds[first_top] in 'zc'):
            return 'moment', None
    if (len(tok) == 7 and tok[:3] == ['offSum', 'c', 'd'] and
            tok[5:] == ['=', '0']):
        return 'offSum', (tok[3], tok[4])
    if (len(tok) == 9 and tok[:2] == ['diagBot', 'c'] and tok[4:7] ==
            ['=', 'diagTop', 'd'] and tok[2:4] == tok[7:9]):
        return 'diag', (tok[2], tok[3])
    return None, None


def resolve_mask(term, defs):
    t = ' '.join(term.split())
    while t.startswith('(') and t.endswith(')'):
        inner = t[1:-1].strip()
        # Only peel a genuinely enclosing pair.
        if top_tokens(inner) is None:
            break
        t = inner
    if t == 'fun _ => false':
        return [0] * 6
    if re.fullmatch(r'\w+', t) and t in defs:
        return defs[t]
    return None


def audit_source(src):
    """Return off rows, diag rows, bad weights, unresolved hypotheses, profile."""
    defs = masks(src)
    body = headline_block(src)
    if body is None:
        return [], [], [], [('headline', 'parse', 'failed')], {}
    bs = binders(body)
    if bs is None:
        return [], [], [], [('headline', 'binders', 'malformed')], {}
    off, dia, bad, unres, prof = [], [], [], [], {}
    amplitudes = moments = 0
    for opener, raw in bs:
        parts = binder_parts(raw)
        if parts is None:
            unres.append(('hypothesis', 'no top-level colon', raw[:36]))
            continue
        names, typ = parts
        kind, args = row_kind(typ)
        if opener != '(':
            unres.append(('hypothesis', names, 'implicit/instance binder'))
            continue
        if kind == 'amplitude':
            if names.split() != ['c', 'd']:
                unres.append(('amplitude', names, 'expected c d'))
            amplitudes += 1
            continue
        if kind == 'moment':
            moments += 1
            continue
        if kind not in ('offSum', 'diag'):
            unres.append(('hypothesis', names, typ[:36]))
            continue
        e, z = args
        (off if kind == 'offSum' else dia).append((e, z))
        ev, zv = resolve_mask(e, defs), resolve_mask(z, defs)
        if ev is None or zv is None:
            unres.append((kind, e, z))
            continue
        w = sum(1 for i in range(6) if ev[i] or zv[i])
        prof[w] = prof.get(w, 0) + 1
        if w > 2:
            bad.append((kind, e, z, w))
    if amplitudes != 1:
        unres.append(('headline', 'amplitude binders', str(amplitudes)))
    if moments != 1:
        unres.append(('headline', 'MomentSystem binders', str(moments)))
    return off, dia, bad, unres, prof


def insert_extra_binder(src, binder):
    body = headline_block(src)
    if body is None:
        return src
    k = src.find('theorem no_go_of_moments')
    p = k + len(body)
    return src[:p] + chr(10) + '    ' + binder + src[p:]


def corrupt_moment_with_false(src):
    body = headline_block(src)
    if body is None:
        return src
    m = body.find('(hm : MomentSystem')
    nxt = body.find(chr(10) + '    (', m + 1)
    if m < 0 or nxt < 0:
        return src
    j = nxt - 1
    while j >= 0 and body[j].isspace():
        j -= 1
    if j < 0 or body[j] != ')':
        return src
    bad_body = body[:j] + ' ∧ False' + body[j:]
    return src.replace(body, bad_body, 1)


def selftest():
    _f, _oid, src = modules([])[0]
    tests = [
        ('extra False binder', insert_extra_binder(src, '(evil : False)')),
        ('embedded offSum name',
         insert_extra_binder(src, '(evil : myoffSumBogus = 0)')),
        ('MomentSystem and False', corrupt_moment_with_false(src)),
    ]
    inv_caught, inv_missed, inv_inert, inv_details = inventory_selftest(REPO)
    for status, why in inv_details:
        print('  %-6s inventory: %s' % (status, why))
    print('  inventory corruptions caught %d, missed %d, not injected %d'
          % (inv_caught, inv_missed, inv_inert))
    missed = inert = 0
    for name, bad_src in tests:
        if bad_src == src:
            inert += 1
            print('  INERT ', name)
        elif not audit_source(bad_src)[3]:
            missed += 1
            print('  MISSED', name)
    print('SELF-TEST: caught %d, missed %d, not injected %d'
          % (len(tests) - missed - inert, missed, inert))
    return 1 if missed or inert or inv_missed or inv_inert else 0


def main(argv):
    try:
        if '--selftest' in argv:
            return selftest()
        argv = [a for a in argv if not a.startswith('--')]
        selected = modules(argv)
    except InventoryError as exc:
        print('FAIL - certified no-go inventory mismatch: %s' % exc)
        return 1
    rc = 0
    if not selected:
        print('FAIL - no matching no_go_of_moments module was found.')
        return 1
    for f, oid, src in selected:
        off, dia, bad, unres, prof = audit_source(src)
        status = 'INADMISSIBLE' if bad else ('UNRESOLVED' if unres else 'OK')
        print('orbit %-3s %-9s %2d offSum + %2d diag rows   weights %s   %s'
              % (oid, f[:-5], len(off), len(dia), dict(sorted(prof.items())), status))
        for kind, e, z, w in bad:
            print('   *** %-10s e=%-16s z=%-16s WEIGHT %d' % (kind, e, z, w))
            rc = 1
        for kind, e, z in unres:
            print('   ??? %-10s %-18s %-36s NOT VERIFIED' % (kind, e, z))
            rc = 1
    print()
    if rc:
        print('FAIL - some headline hypothesis is extra, malformed, inadmissible, '
              'or unresolved.')
    else:
        print('PASS - every headline hypothesis is recognized, and every KL row '
              'is a genuine weight-<=2 Pauli.')
    return rc


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
