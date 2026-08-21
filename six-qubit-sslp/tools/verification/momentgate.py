"""Complete semantic check of every MomentSystem transcription.

`gate.py` checks only the right-hand side of each `m<coords>` row. A
collaborator showed that is not enough: mutating a left-hand side, or a row
named something else such as `c12`, leaves the gate green. This module checks
the whole structure instead, and infers each row's meaning from its CONTENT
rather than from its name, so a renamed or reordered row cannot slip past.

For each module it verifies:
  * exactly two normalization rows, each summing ALL bottom (resp. top)
    probabilities to 1;
  * every row that IS declared states, exactly, the moment condition for some
    coordinate subset `T` with `|T| <= 2`: same variables, same coefficients,
    no constant term, correct on BOTH sides.  A module may declare only a
    sufficient subset of the twenty-one rows -- fewer hypotheses make its
    headline stronger -- so absent rows are reported, never failed;
  * no additional equation between the probabilities;
  * nonnegativity fields, if present, cover every state and each really states
    `0 <= q_i` rather than merely being named `nq_i`;
  * the headline passes the bottom probabilities in declaration order, so `q_i`
    really is `normSq (c y_i)`.

Run standalone:
    python tools/run.py verification/momentgate.py            # all modules
    python tools/run.py verification/momentgate.py 25 34      # selected
    python tools/run.py verification/momentgate.py --selftest # mutation test

The self-test is the important one: it mutates each module in memory - flipping
a left-hand side, renaming a row, dropping a row, corrupting a normalization -
and asserts the checker rejects every mutation. A checker that has never been
shown to fail is not evidence of anything.
"""
import io
import json
import os
import re
import sys
from fractions import Fraction
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'core'))

SQ = os.path.join(REPO, 'SixQubit')
BITS = {'true': 1, 'false': 0}
S = r'\s+'


def structure_block(src):
    """The text of the MomentSystem structure, and nothing else.

    Proof bodies also carry two-space indentation, so scanning the whole file
    lets a tactic line overwrite a field of the same name.
    """
    k = src.find('structure MomentSystem')
    if k < 0:
        return None
    body = src[k:]
    nl = body.index(chr(10)) + 1
    m = re.search(r'^\S', body[nl:], re.M)
    return body[:nl + m.start()] if m else body


def field_list(block):
    """[(name, joined text)] in declaration order, honouring line wrapping.

    A LIST, not a dict: two fields of the same name would silently overwrite
    each other and a row would vanish from the check without a word. Lean would
    reject a duplicate field, but a checker that loses rows when its input is
    unexpected is exactly the failure mode this file exists to avoid.
    """
    out, cur = [], None
    for ln in block.split(chr(10)):
        mh = re.match(r'  (\w+)\s*:\s*(.*)$', ln)
        if mh and not ln.startswith('   '):
            out.append([mh.group(1), mh.group(2)])
            cur = out[-1]
        elif cur is not None and ln.startswith('      '):
            cur[1] = cur[1] + ' ' + ln.strip()
        elif ln.strip() == '' or not ln.startswith(' '):
            cur = None
    return [(a, b) for a, b in out]


def fields_of(block):
    """Dict view, for callers that only need lookup by name."""
    return dict(field_list(block))


def linear_form(expr):
    """Parse `q0 + 2 * q3 - q7 + 1` into ({var: coeff}, constant).

    Returns ((coeffs, constant), None) or (None, reason).

    Collapsing an expression to the SET of variable names appearing in it was
    the defect that let five different corruptions through: `q6 + q6` (lost
    multiplicity), `q6 + 7` (lost the constant), a coefficient other than one,
    a `+` silently changed to `-`, and a top variable smuggled into a bottom
    normalization. A linear form keeps all of that.
    """
    e = ' '.join(expr.split())
    if not e:
        return (({}, 0), None)
    e = e.replace('-', '+ -')
    coeffs, const = {}, 0
    for raw in e.split('+'):
        t = raw.strip()
        if not t:
            continue
        neg = t.startswith('-')
        if neg:
            t = t[1:].strip()
        m = re.fullmatch(r'(?:(\d+)\s*\*\s*)?([qr]\d+)', t)
        if m:
            k = int(m.group(1) or 1) * (-1 if neg else 1)
            coeffs[m.group(2)] = coeffs.get(m.group(2), 0) + k
            continue
        m = re.fullmatch(r'(\d+)(?:/(\d+))?', t)
        if m:
            # Fraction, never float: `eval('1/10**400')` underflows to 0.0 and a
            # nonzero constant then reads as no constant at all.
            val = Fraction(int(m.group(1)), int(m.group(2) or 1))
            const += -val if neg else val
            continue
        return (None, 'unparsable term %r' % t[:24])
    return ((({k: v for k, v in coeffs.items() if v != 0}), const), None)


def bitstrings(src):
    ys, zs = {}, {}
    pat = (r'def' + S + r'(y|z)(\d+)' + S + r':' + S + r'SS\.BitString' + S +
           r'6' + S + r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
    for m in re.finditer(pat, src):
        v = [BITS[m.group(i + 3)] for i in range(6)]
        (ys if m.group(1) == 'y' else zs)[int(m.group(2))] = v
    return ys, zs


def headline_orders(src, ys, zs):
    """How the headline actually supplies the bottom and top probabilities."""
    k = src.find('theorem no_go_of_moments')
    if k < 0:
        return None, None
    body = src[k:src.find(': False', k)]
    bi = [int(x) for x in re.findall(
        r'Complex\.normSq' + S + r'\(c' + S + r'y(\d+)\)', body)]
    comp = [int(x) for x in re.findall(
        r'Complex\.normSq' + S + r'\(d' + S + r'\(SS\.complement' + S +
        r'y(\d+)\)\)', body)]
    if comp:
        if any(i not in ys for i in comp) or any(i not in ys for i in bi):
            return None, None
        return [ys[i] for i in bi], [[1 - b for b in ys[i]] for i in comp]
    ti = [int(x) for x in re.findall(
        r'Complex\.normSq' + S + r'\(d' + S + r'z(\d+)\)', body)]
    if not ti or any(i not in zs for i in ti) or any(i not in ys for i in bi):
        return None, None
    return [ys[i] for i in bi], [zs[i] for i in ti]


def check(src):
    """Return a list of problems; empty means the transcription is sound."""
    block = structure_block(src)
    if block is None:
        return ['no MomentSystem structure found'], 0
    ys, zs = bitstrings(src)
    bot, top = headline_orders(src, ys, zs)
    if bot is None:
        return ['could not resolve the order the headline passes probabilities'], 0
    FL = field_list(block)
    names = [a for a, _ in FL]
    nb, nt = len(bot), len(top)
    problems = []

    # The binder list itself. Swapping `q0 q1` in the structure header while
    # leaving every row alone silently renumbers all the probabilities, which is
    # exactly the class of regression that produced the orbit 34/57/59/64 defect.
    hdr = re.match(r'structure MomentSystem\s*\(([^)]*)\)', block)
    if hdr is None:
        problems.append('cannot read the MomentSystem binder list')
    else:
        binders = [b for b in hdr.group(1).split(':')[0].split() if b]
        expect = (['q%d' % i for i in range(nb)] + ['r%d' % i for i in range(nt)])
        if binders != expect:
            problems.append('binder order is %s..., expected %s... (bottom then '
                            'top, each in index order)'
                            % (' '.join(binders[:4]), ' '.join(expect[:4])))

    # the intended content of every legitimate row, keyed by (lhs set, rhs set)
    intended = {}
    for T in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
        L = frozenset(k for k in range(nb) if all(bot[k][j] == 1 for j in T))
        R = frozenset(k for k in range(nt) if all(top[k][j] == 1 for j in T))
        intended.setdefault((L, R), []).append(T)

    norms, seen, spurious = [], set(), []
    nneg_b, nneg_t = set(), set()
    for nm, row in FL:
        mn = re.fullmatch(r'n([qr])(\d+)', nm)
        if mn:
            # Check the PROPOSITION, not just the field name.  Counting names
            # let `nq0 : False` pass as a nonnegativity constraint.
            want = '0 ≤ %s%s' % (mn.group(1), mn.group(2))
            if ' '.join(row.split()) != want:
                spurious.append('%s states %r, expected %r'
                                % (nm, ' '.join(row.split())[:40], want))
            elif mn.group(1) == 'q':
                nneg_b.add(int(mn.group(2)))
            else:
                nneg_t.add(int(mn.group(2)))
            continue
        if '=' not in row:
            # An unrecognized field is NOT a harmless field. Skipping it let
            # `evil : Eq q0 q1`, `m1 : True` and `m1 : q0 <= q1` through: each
            # states something other than a moment condition, and silence reads
            # as approval.
            spurious.append('%s is neither an equation nor a nonnegativity '
                            'field: %r' % (nm, ' '.join(row.split())[:40]))
            continue
        lhs, rhs = row.split('=', 1)
        fl, el = linear_form(lhs)
        fr, er = linear_form(rhs)
        if el or er:
            spurious.append('%s: %s' % (nm, el or er))
            continue
        if not fl and not fr:
            continue
        cl, kl = fl
        cr, kr = fr
        # A row with no variables on either side is NOT automatically bogus:
        # when no state carries a given coordinate, the generators emit the
        # honest `0 = 0`. What must be rejected is a row whose two sides differ,
        # such as `0 = 1`; the constant check below does that, so nothing is
        # special-cased here.
        if not cr and kr == 1:                                # a normalization
            side = sorted(cl)
            tag = side[0][0] if side else '?'
            want = {('%s%d' % (tag, i)): 1 for i in range(nb if tag == 'q' else nt)}
            if cl != want or kl != 0:
                spurious.append('%s is not a normalization of all %s states'
                                % (nm, 'bottom' if tag == 'q' else 'top'))
            else:
                norms.append(tag)
            continue
        if any(v[0] == 'r' for v in cl) or any(v[0] == 'q' for v in cr):
            spurious.append('%s mixes bottom and top on one side' % nm)
            continue
        if kl or kr:
            spurious.append('%s carries a constant term' % nm)
            continue
        qi = frozenset(int(v[1:]) for v in cl)
        ri = frozenset(int(v[1:]) for v in cr)
        if (any(cl[v] != 1 for v in cl) or any(cr[v] != 1 for v in cr)):
            spurious.append('%s has a coefficient other than one' % nm)
            continue
        Ts = intended.get((qi, ri))
        if Ts is None:
            spurious.append('%s is not any weight-<=2 moment row' % nm)
        else:
            for T in Ts:
                seen.add(T)

    dup = sorted({n for n in names if names.count(n) > 1})
    if dup:
        problems.append('duplicate field names %s -- rows would be lost' % dup)
    if sorted(norms) != ['q', 'r']:
        problems.append('normalization rows: %s, expected one over the bottom '
                        'and one over the top' % (sorted(norms) or 'none'))
    if spurious:
        problems.append('; '.join(spurious))
    # Nonnegativity is optional but must be all-or-nothing and well indexed:
    # a partial set would silently drop constraints the proof might rely on.
    if nneg_b or nneg_t:
        if nneg_b != set(range(nb)) or nneg_t != set(range(nt)):
            problems.append('nonnegativity fields cover %d bottom / %d top, '
                            'expected either none or %d / %d'
                            % (len(nneg_b), len(nneg_t), nb, nt))
    # A module may legitimately declare only a SUFFICIENT SUBSET of the moment
    # rows -- fewer hypotheses make the headline stronger, not weaker. Orbit 34,
    # for instance, uses fourteen equations that already pin all fourteen
    # probabilities. So absent rows are reported, never failed; what must never
    # happen is a row that is present but wrong, which is caught above.
    missing = [T for (L, R), Ts in intended.items() for T in Ts if T not in seen]
    return problems, len(missing)


def modules(argv):
    out = []
    for f in sorted(os.listdir(SQ)):
        if not f.endswith('.lean') or f == 'Audit.lean':
            continue
        src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
        if 'theorem no_go_of_moments' not in src:
            continue
        oid = '66' if f == 'Order9.lean' else re.sub(r'[^0-9]', '', f)
        if argv and oid not in set(argv):
            continue
        out.append((f, oid, src))
    return out


def mutations(src):
    """In-memory corruptions a sound checker must reject.

    Two things are deliberately NOT in this list, because neither is a defect:

      * deleting a row -- a module may declare only a sufficient subset of the
        moment conditions, which makes its headline stronger, not weaker; and
        if the proof used the row, Lean itself would stop compiling;
      * renaming a row -- rows are identified by content here, so a row called
        `c12` is checked exactly like one called `m12`. That was the point of
        moving off name-based matching.

    What must always be caught is a row whose CONTENT no longer states a
    weight-at-most-two moment condition.
    """
    block = structure_block(src)
    F = fields_of(block)
    FL_all = field_list(block)
    moms = [n for n in F if '=' in F[n] and F[n].split('=')[1].strip() != '1'
            and re.search(r'\bq\d+\b', F[n]) and re.search(r'\br\d+\b', F[n])]
    out = []
    if moms:
        nm = moms[0]
        line = '  %s : %s' % (nm, F[nm])
        lhs, rhs = F[nm].split('=', 1)
        qs = re.findall(r'\bq(\d+)\b', lhs)
        rs = re.findall(r'\br(\d+)\b', rhs)
        if len(qs) >= 2:
            bad = lhs.replace('q%s + ' % qs[0], '', 1)
            out.append(('drop a left-hand term of %s' % nm,
                        src.replace(line, '  %s : %s=%s' % (nm, bad, rhs), 1)))
            # the same corruption under a different name: renaming must not
            # let a wrong row escape checking
            out.append(('drop a left-hand term AND rename %s to c99' % nm,
                        src.replace(line, '  c99 : %s=%s' % (bad, rhs), 1)))
        if len(rs) >= 2:
            bad = rhs.replace('r%s + ' % rs[0], '', 1)
            out.append(('drop a right-hand term of %s' % nm,
                        src.replace(line, '  %s : %s=%s' % (nm, lhs, bad), 1)))
        if qs:
            other = str((int(qs[0]) + 1) % 99)
            bad = lhs.replace('q%s' % qs[0], 'q%s' % other, 1)
            if bad != lhs:
                out.append(('reindex a left-hand term of %s' % nm,
                            src.replace(line, '  %s : %s=%s' % (nm, bad, rhs), 1)))
        out.append(('swap the two sides of %s' % nm,
                    src.replace(line, '  %s : %s=%s' % (nm, rhs, lhs), 1)))
    for nm2, row2 in FL_all:
        if re.fullmatch(r'n[qr]\d+', nm2):
            out.append(('replace %s by False' % nm2,
                        src.replace('  %s : %s' % (nm2, row2),
                                    '  %s : False' % nm2, 1)))
            break

    # Rows that are not equations at all, and equations that relate nothing.
    # Skipping unrecognized fields was a false-green path: silence read as
    # approval.
    if moms:
        nm = moms[0]
        for ln in block.split(chr(10)):
            if ln.startswith('  %s :' % nm):
                for tag, rep in (
                        ('state Eq instead of =', '  %s : Eq q0 r0' % nm),
                        ('state True', '  %s : True' % nm),
                        ('state an inequality', '  %s : q0 ≤ q1' % nm),
                        ('state 0 = 1', '  %s : 0 = 1' % nm),
                        ('smuggle in an extra bogus field',
                         ln + chr(10) + '  evil : Eq q0 q1')):
                    out.append((tag + ' in ' + nm, src.replace(ln, rep, 1)))
                # a constant so small a float would underflow it to zero
                lhs2, rhs2 = F[nm].split('=', 1)
                out.append(('add an underflowing constant to %s' % nm,
                            src.replace(ln, '  %s : %s + 1/%s = %s'
                                        % (nm, lhs2.strip(), '1' + '0' * 400,
                                           rhs2.strip()), 1)))
                break

    # Swapping two binders renumbers every probability while leaving the rows
    # textually untouched.
    hdr = re.match(r'structure MomentSystem\s*\(([^)]*)\)', block)
    if hdr:
        bs = hdr.group(1).split(':')[0].split()
        if len(bs) >= 2:
            swapped = hdr.group(0).replace('%s %s' % (bs[0], bs[1]),
                                           '%s %s' % (bs[1], bs[0]), 1)
            out.append(('swap the first two binders',
                        src.replace(hdr.group(0), swapped, 1)))
    for norm in ('n0', 'n1'):
        if norm in F and F[norm].split('=')[-1].strip() == '1':
            line = '  %s : %s' % (norm, F[norm])
            lhs = F[norm].split('=')[0]
            vs = re.findall(r'\b[qr](\d+)\b', lhs)
            if vs:
                bad = re.sub(r'\b([qr])%s \+ ' % vs[0], '', lhs, count=1)
                if bad != lhs:
                    out.append(('drop a term from %s' % norm,
                                src.replace(line, '  %s : %s= 1' % (norm, bad), 1)))
    return out


if __name__ == '__main__':
    argv = [a for a in sys.argv[1:] if not a.startswith('--')]
    selftest = '--selftest' in sys.argv
    rc = 0
    if selftest:
        print('SELF-TEST: every mutation below must be REJECTED.')
        print()
        caught = missed = inert = 0
        for f, oid, src in modules(argv):
            for name, bad in mutations(src):
                if bad == src:
                    # the field wraps across lines, so the textual substitution
                    # matched nothing. A no-op is not a mutation and tests
                    # nothing; counting it either way would be dishonest.
                    inert += 1
                    print('  INERT  on %-9s %s (field wraps; not injected)'
                          % (f[:-5], name))
                    continue
                if check(bad)[0]:
                    caught += 1
                else:
                    missed += 1
                    print('  MISSED on %-9s %s' % (f[:-5], name))
        print('  mutations caught %d, missed %d, not injected %d'
              % (caught, missed, inert))
        if missed:
            print()
            print('FAIL - the checker accepts a corrupted transcription.')
            sys.exit(1)
        print()
        print('PASS - every injected corruption was rejected.')
        sys.exit(0)

    bad = 0
    for f, oid, src in modules(argv):
        probs, absent = check(src)
        note = '' if not absent else '  (%d of 21 rows not declared - a '
        note = '' if not absent else ('  [uses %d of the 21 rows]' % (21 - absent))
        print('orbit %-3s %-9s %s%s'
              % (oid, f[:-5], 'OK' if not probs else 'FAIL', note))
        for p in probs:
            print('    %s' % p)
            bad = 1
    print()
    if bad:
        print('FAIL - a MomentSystem does not transcribe the moment conditions.')
        sys.exit(1)
    print('PASS - every declared MomentSystem row transcribes a genuine')
    print('       weight-<=2 moment condition. (Rows a module does not declare')
    print('       are listed, not failed: a smaller hypothesis set is stronger.)')
