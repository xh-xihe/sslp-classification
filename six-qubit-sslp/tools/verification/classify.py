"""Classify every hypothesis of every headline theorem.

Only three categories are legitimate:
  (a) offSum ... = 0
  (b) diagBot ... = diagTop ...
  (c) MomentSystem ...

Anything else is an algebraic fact smuggled in as an assumption. That defect is
invisible from outside the proof - the theorem still says `False` and still has a
clean axiom footprint - so this check matters more than compilation does.

Usage (from the repository root):
    python tools/run.py verification/classify.py            # every orbit module
    python tools/run.py verification/classify.py 5 26 31    # selected orbits
    python tools/run.py verification/classify.py --selftest

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


def modules(argv):
    return [f for f, _oid, _src in select_no_go_sources(REPO, argv)]


def headline_block(src):
    """Return the headline before its top-level ``: False :=`` result."""
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
            i += 1; continue
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


def hypotheses(body):
    """Return all top-level binders and their delimiter, failing closed."""
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
    if typ == 'SS.BitString 6 -> ℂ':
        return 'amplitude'
    tok = top_tokens(typ)
    if not tok:
        return None
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
            return 'Moment'
    if (len(tok) == 7 and tok[:3] == ['offSum', 'c', 'd'] and
            tok[5:] == ['=', '0']):
        return 'offSum'
    if (len(tok) == 9 and tok[:2] == ['diagBot', 'c'] and tok[4:7] ==
            ['=', 'diagTop', 'd'] and tok[2:4] == tok[7:9]):
        return 'diag'
    return None


def classify_source(src):
    """Return exact category counts and every binder outside the grammar."""
    body = headline_block(src)
    if body is None:
        return 0, 0, 0, ['MALFORMED HEADLINE']
    a = b = c = 0
    other = []
    hs = hypotheses(body)
    if hs is None:
        hs = []
        other.append('MALFORMED OR UNBALANCED BINDER LIST')
    amplitudes = 0
    for opener, h in hs:
        t = ' '.join(h.split())
        parts = binder_parts(h)
        if parts is None or opener != '(':
            other.append(t[:90])
            continue
        names, typ = parts
        kind = row_kind(typ)
        if kind == 'offSum':
            a += 1
        elif kind == 'diag':
            b += 1
        elif kind == 'Moment':
            c += 1
        elif kind == 'amplitude' and names.split() == ['c', 'd']:
            amplitudes += 1
        else:
            other.append(t[:90])
    if amplitudes != 1:
        other.append('AMPLITUDE BINDER COUNT %d (expected 1)' % amplitudes)
    if c != 1:
        other.append('MOMENT BINDER COUNT %d (expected 1)' % c)
    return a, b, c, other


def insert_extra_binder(src, binder):
    body = headline_block(src)
    if body is None:
        return src
    k = src.find('theorem no_go_of_moments')
    p = k + len(body)
    return src[:p] + chr(10) + '    ' + binder + src[p:]


def corrupt_moment_with_false(src):
    """Append ``and False`` to the complete MomentSystem binder type."""
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
    f = modules([])[0]
    src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
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
    for name, bad in tests:
        if bad == src:
            inert += 1
            print('  INERT ', name)
        elif not classify_source(bad)[3]:
            missed += 1
            print('  MISSED', name)
    print('SELF-TEST: caught %d, missed %d, not injected %d'
          % (len(tests) - missed - inert, missed, inert))
    return 1 if missed or inert or inv_missed or inv_inert else 0


def main(argv):
    try:
        if '--selftest' in argv:
            return selftest()
        mods = modules([a for a in argv if not a.startswith('--')])
    except InventoryError as exc:
        print('FAIL - certified no-go inventory mismatch: %s' % exc)
        return 1
    if not mods:
        print('FAIL - no matching no_go_of_moments module was found.')
        return 1
    bad_total = 0
    print('%-12s %6s %8s %9s %8s %8s'
          % ('module', 'hyps', 'offSum', 'diag', 'Moment', 'OTHER'))
    for f in sorted(mods, key=lambda x: 66 if x == 'Order9.lean'
                    else int(re.sub(r'[^0-9]', '', x) or 0)):
        src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
        a, b, c, other = classify_source(src)
        print('%-12s %6d %8d %9d %8d %8d%s'
              % (f[:-5], a + b + c + len(other), a, b, c, len(other),
                 '' if not other else '   <<< SMUGGLED'))
        for t in other:
            print('      OTHER: %s' % t)
        bad_total += len(other)
    print()
    print('modules checked: %d' % len(mods))
    print('hypotheses outside the three legitimate categories: %d' % bad_total)
    if bad_total == 0:
        print('PASS - all current headline binders match the audited grammar.')
        return 0
    print('FAIL - an algebraic fact is being assumed rather than derived.')
    return 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
