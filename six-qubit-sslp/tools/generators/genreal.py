"""Emit the exact-realization module for one orbit.

Ten of the fifteen realizations are settled at the weight-enumerator-image
level, and all ten are proved to exist by exhibiting a code.  This generator
writes, for each, a Lean module carrying the amplitude table in the ring
`Z[sqrt 2, sqrt 3, i]` of `SixQubit/Realize.lean` and discharging the
Knill--Laflamme constraints by kernel `decide`.

The amplitudes come from Table `tab:orbits` and the base-word tables of
`documents/<date>/623/six_qubit_15_analytical_solutions.tex`, PARSED rather
than transcribed.  Each realization is a base word moved by a qubit
permutation, a translation, and optionally an exchange of the two logical
words.

Scales are rational here, unlike orbit 36:

    sixteen real terms   sc = 1/4   entries +-1        N = 16
    eight real terms     sc = 1/4   entries +-sqrt 2   N = 16
    eleven complex terms sc = 1/12  2 sqrt 3 zeta6^k   N = 144
                                    2 sqrt 6 zeta6^k

Before writing anything the generator re-checks the whole certificate in
Python, in the same eight-integer arithmetic the Lean uses.  A table that does
not verify is never emitted; the kernel `decide` is then a second, independent
confirmation rather than the only one.

    python tools/run.py generators/genreal.py            # all ten
    python tools/run.py generators/genreal.py 7 45       # selected
    python tools/run.py generators/genreal.py --check    # verify, write nothing
"""
import io
import itertools
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
DOC = os.path.join(REPO, 'documents', '20260822', '623',
                   'six_qubit_15_analytical_solutions.tex')
OUT = os.path.join(REPO, 'SixQubit')
TARGETS = [7, 8, 9, 10, 11, 16, 21, 22, 23, 45]
BS = chr(92)
NL = chr(10)


# --------------------------------------------------------------------------
# exact arithmetic in Z[sqrt2, sqrt3, i], mirroring SixQubit/Realize.lean
# --------------------------------------------------------------------------

ZERO = (0,) * 8


def zadd(x, y):
    return tuple(p + q for p, q in zip(x, y))


def zneg(x):
    return tuple(-p for p in x)


def zconj(x):
    return x[:4] + tuple(-p for p in x[4:])


def zmul(x, y):
    if x == ZERO or y == ZERO:
        return ZERO
    a0, a1, a2, a3, b0, b1, b2, b3 = x
    c0, c1, c2, c3, d0, d1, d2, d3 = y
    return (
        (a0*c0 + 2*a1*c1 + 3*a2*c2 + 6*a3*c3) - (b0*d0 + 2*b1*d1 + 3*b2*d2 + 6*b3*d3),
        (a0*c1 + a1*c0 + 3*a2*c3 + 3*a3*c2) - (b0*d1 + b1*d0 + 3*b2*d3 + 3*b3*d2),
        (a0*c2 + a2*c0 + 2*a1*c3 + 2*a3*c1) - (b0*d2 + b2*d0 + 2*b1*d3 + 2*b3*d1),
        (a0*c3 + a3*c0 + a1*c2 + a2*c1) - (b0*d3 + b3*d0 + b1*d2 + b2*d1),
        (a0*d0 + 2*a1*d1 + 3*a2*d2 + 6*a3*d3) + (b0*c0 + 2*b1*c1 + 3*b2*c2 + 6*b3*c3),
        (a0*d1 + a1*d0 + 3*a2*d3 + 3*a3*d2) + (b0*c1 + b1*c0 + 3*b2*c3 + 3*b3*c2),
        (a0*d2 + a2*d0 + 2*a1*d3 + 2*a3*d1) + (b0*c2 + b2*c0 + 2*b1*c3 + 2*b3*c1),
        (a0*d3 + a3*d0 + a1*d2 + a2*d1) + (b0*c3 + b3*c0 + b1*c2 + b2*c1))


# 2 sqrt 3 * zeta6^k and 2 sqrt 6 * zeta6^k, both in Z[sqrt2, sqrt3, i]
Z3 = {0: (0, 0, 2, 0, 0, 0, 0, 0), 1: (0, 0, 1, 0, 3, 0, 0, 0),
      2: (0, 0, -1, 0, 3, 0, 0, 0), 3: (0, 0, -2, 0, 0, 0, 0, 0),
      4: (0, 0, -1, 0, -3, 0, 0, 0), 5: (0, 0, 1, 0, -3, 0, 0, 0)}
Z6 = {0: (0, 0, 0, 2, 0, 0, 0, 0), 1: (0, 0, 0, 1, 0, 3, 0, 0),
      2: (0, 0, 0, -1, 0, 3, 0, 0), 3: (0, 0, 0, -2, 0, 0, 0, 0),
      4: (0, 0, 0, -1, 0, -3, 0, 0), 5: (0, 0, 0, 1, 0, -3, 0, 0)}
PLUS1, MINUS1 = (1, 0, 0, 0, 0, 0, 0, 0), (-1, 0, 0, 0, 0, 0, 0, 0)
PLUSR2, MINUSR2 = (0, 1, 0, 0, 0, 0, 0, 0), (0, -1, 0, 0, 0, 0, 0, 0)


# --------------------------------------------------------------------------
# parsing the source tables
# --------------------------------------------------------------------------

def load_doc():
    src = io.open(DOC, encoding='utf-8').read()
    real = {}
    for name, word, pos, neg in re.findall(
            r'\$(r' + r'\d+)\$\s*&\s*\$([01])\$\s*&\s*'
            r'\$' + BS + r'\{([01,\s]*)' + BS + r'\}\$\s*&\s*'
            r'\$' + BS + r'\{([01,\s]*)' + BS + r'\}\$', src):
        P = [w.strip() for w in pos.split(',') if w.strip()]
        N = [w.strip() for w in neg.split(',') if w.strip()]
        real.setdefault(name, {})[int(word)] = (P, N)
    cplx = {}
    for name, word, body in re.findall(r'\$(z' + r'\d+)\$\s*&\s*\$([01])\$\s*&\s*\$([^$]*)\$', src):
        items = re.findall(r'([01]{6}):(' + r'\d+):(\d+)', body)
        if items:
            cplx.setdefault(name, {})[int(word)] = [
                (t[0], int(t[1]), int(t[2])) for t in items]
    jobs = {}
    for m in re.finditer(
            r'^\s*(' + r'\d+)\s*&\s*(\d+)\s*&\s*(\d+)\s*&\s*\$\((\d(?:,\d)*)\)\$\s*&\s*'
            r'\$(' + r'\w+)\$\s*&\s*\$(?:' + BS + BS + r'id|\((\d(?:,\d)*)\))\$\s*&\s*'
            r'\$([01]{6})\$\s*&\s*(yes|no)', src, re.M):
        oid, q, mm, a, base, perm, t, swap = m.groups()
        jobs[int(oid)] = dict(
            q=int(q), m=int(mm), a=[int(c) for c in a.split(',')], base=base,
            perm=None if perm is None else [int(c) for c in perm.split(',')],
            t=t, swap=(swap == 'yes'))
    return real, cplx, jobs


def move(s, perm, t):
    """Permute qubits then translate, on document strings b5 b4 b3 b2 b1 b0."""
    bits = [int(c) for c in s][::-1]            # bits[j] is qubit j
    out = [0] * 6
    for j in range(6):
        out[perm[j] if perm else j] = bits[j]
    s2 = ''.join(str(b) for b in out[::-1])
    return ''.join(str(int(c) ^ int(tc)) for c, tc in zip(s2, t))


def qubits(s):
    """Document string b5..b0 -> tuple indexed by qubit number."""
    return tuple(int(s[5 - j]) for j in range(6))


def numof(x):
    return sum(b << j for j, b in enumerate(x))


def build_word(real, cplx, base, k, perm, t):
    """{qubit-tuple: ZQ} for logical word k, moved into place."""
    out = {}
    if base in real:
        P, N = real[base][k]
        big = (len(P) + len(N)) == 16
        pv, nv = (PLUS1, MINUS1) if big else (PLUSR2, MINUSR2)
        for w in P:
            out[qubits(move(w, perm, t))] = pv
        for w in N:
            out[qubits(move(w, perm, t))] = nv
    else:
        for w, e, d in cplx[base][k]:
            out[qubits(move(w, perm, t))] = (Z3 if d == 12 else Z6)[e % 6]
    return out


# --------------------------------------------------------------------------
# the certificate, checked here before it is written
# --------------------------------------------------------------------------

def zmat(cj, ck, Lk, x, z):
    """sum over s in Lk of (-1)^{z.s} conj(cj[s xor x]) * ck[s]."""
    acc = ZERO
    for s in Lk:
        sx = tuple(p ^ q for p, q in zip(s, x))
        a = cj.get(sx)
        if a is None:
            continue
        term = zmul(zconj(a), ck[s])
        if sum(p & q for p, q in zip(z, s)) % 2:
            term = zneg(term)
        acc = zadd(acc, term)
    return acc


def wt(x, z):
    return sum(1 for i in range(6) if x[i] or z[i])


def verify(w0, w1):
    """Every weight-<=2 Pauli: diagonals agree, both off-diagonals vanish."""
    L0, L1 = sorted(w0), sorted(w1)
    bad = 0
    for xm in range(64):
        x = tuple((xm >> j) & 1 for j in range(6))
        for zm in range(64):
            z = tuple((zm >> j) & 1 for j in range(6))
            if wt(x, z) > 2:
                continue
            if zadd(zmat(w0, w0, L0, x, z), zneg(zmat(w1, w1, L1, x, z))) != ZERO:
                bad += 1
            if zmat(w0, w1, L1, x, z) != ZERO:
                bad += 1
            if zmat(w1, w0, L0, x, z) != ZERO:
                bad += 1
    n0 = zmat(w0, w0, sorted(w0), (0,)*6, (0,)*6)
    n1 = zmat(w1, w1, sorted(w1), (0,)*6, (0,)*6)
    return bad, n0, n1


# --------------------------------------------------------------------------
# emission
# --------------------------------------------------------------------------

def zlit(v):
    return ' '.join(str(c) if c >= 0 else '(%d)' % c for c in v)


def bslit(x):
    return 'bs ' + ' '.join('true ' if b else 'false' for b in x).strip()


def table(name, word, doc):
    lines = ['/-- %s -/' % doc, 'def %s (x : SS.BitString 6) : ZQ :=' % name]
    items = sorted(word.items(), key=lambda kv: numof(kv[0]))
    for i, (x, v) in enumerate(items):
        head = '  if' if i == 0 else '  else if'
        lines.append('%s num x = %d then z8 %s' % (head, numof(x), zlit(v)))
    lines.append('  else ZQ.zero')
    return NL.join(lines)


def emit(oid, rec, w0, w1, N):
    q, a = rec['q'], rec['a']
    r0 = sum(ai * xi for ai, xi in zip(a, sorted(w0)[0])) % q
    r1 = sum(ai * xi for ai, xi in zip(a, sorted(w1)[0])) % q
    terms = len(w0)
    sc, scdoc = ('(1/12 : ℂ)', '1/12') if terms == 11 else ('(1/4 : ℂ)', '1/4')
    L0 = ',' + NL + '   '
    lst = lambda w: ('[' + L0.join(bslit(x) for x in sorted(w, key=numof)) + ']')

    return '''import Mathlib
import SS.HilbertKL
import SixQubit.Realize

/-!
# Orbit {oid}: an exact realization

Orbit {oid} of the six-qubit SSLP classification is `q = {q}`, angle vector
`a = {a}`, with the two words supported in the residue-`{r0}` and residue-`{r1}`
fibers.  This module exhibits an explicit pair and proves it is an exact
`((6,2,3))` code, so the orbit is nonempty.

The amplitudes are `{sc}` times entries of `Z[sqrt 2, sqrt 3, i]`, {terms} per
word.  All the Knill--Laflamme constraints of Pauli weight at most two are
decided by the kernel in that ring; `SixQubit/Realize.lean` transports the
decision to genuine complex matrix elements.

Generated by `tools/generators/genreal.py`, which re-checks the same
certificate in the same eight-integer arithmetic before writing.
-/

namespace SixQubit.Orbit{oid}Real

open SixQubit.Realize

/-! ## The angle record and the two supports -/

def av : Fin 6 → ZMod {q} := ![{avlit}]

def L0 : List (SS.BitString 6) :=
  {l0}

def L1 : List (SS.BitString 6) :=
  {l1}

theorem L0_nodup : L0.Nodup := by decide
theorem L1_nodup : L1.Nodup := by decide

/-- Every bottom word lies in the residue-`{r0}` fiber. -/
theorem L0_in_fiber : ∀ x ∈ L0, SS.weight av x = {r0} := by decide

/-- Every top word lies in the residue-`{r1}` fiber. -/
theorem L1_in_fiber : ∀ x ∈ L1, SS.weight av x = {r1} := by decide

/-! ## The exact amplitude tables -/

{t0}

{t1}

theorem c0z_vanishes : ∀ x : SS.BitString 6, x ∉ L0 → c0z x = ZQ.zero := by decide
theorem c1z_vanishes : ∀ x : SS.BitString 6, x ∉ L1 → c1z x = ZQ.zero := by decide

/-! ## The finite certificate -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- The Knill--Laflamme constraints of Pauli weight at most two, decided by the
kernel over all mask pairs.  The weight guard rejects the 3942 pairs of weight
three or more before any ring arithmetic is reached. -/
theorem check_all : ∀ m < 64, ∀ k < 64,
    (⟨nbit m, nbit k⟩ : SS.PauliString 6).wt ≤ 2 →
    checkKL c0z c1z L0 L1 (nbit m) (nbit k) = true := by decide

/-! ## The code -/

noncomputable section

/-- The normalizing scalar `{sc}`. -/
def sc : ℂ := {sclean}

/-- `|0_L>`. -/
def w0 : SS.State 6 ℂ := stC sc c0z

/-- `|1_L>`. -/
def w1 : SS.State 6 ℂ := stC sc c1z

/-- **Orbit {oid} is realized: this pair is an exact `((6,2,3))` code.** -/
theorem is_code : SS.HasDistance ![w0, w1] 3 :=
  is_code_of_check sc c0z c1z L0 L1 L0_nodup L1_nodup c0z_vanishes c1z_vanishes
    check_all

theorem norm0 : zmat c0z c0z L0 (fun _ => false) (fun _ => false)
    = z8 {N} 0 0 0 0 0 0 0 := by decide

theorem norm1 : zmat c1z c1z L1 (fun _ => false) (fun _ => false)
    = z8 {N} 0 0 0 0 0 0 0 := by decide

theorem sc_norm : star sc * sc * ({N} : ℂ) = 1 := by
  rw [sc]
  norm_num [Complex.star_def, Complex.conj_ofNat]

theorem w0_normalized : SS.innerC w0 w0 = 1 :=
  normalized_of sc c0z L0 L0_nodup c0z_vanishes {N} norm0 sc_norm

theorem w1_normalized : SS.innerC w1 w1 = 1 :=
  normalized_of sc c1z L1 L1_nodup c1z_vanishes {N} norm1 sc_norm

theorem w0_vanishes (s : SS.BitString 6) (hs : s ∉ L0) : w0 s = 0 :=
  stC_vanishes sc c0z L0 c0z_vanishes s hs

theorem w1_vanishes (s : SS.BitString 6) (hs : s ∉ L1) : w1 s = 0 :=
  stC_vanishes sc c1z L1 c1z_vanishes s hs

end

end SixQubit.Orbit{oid}Real
'''.format(oid=oid, q=q, a=tuple(a), r0=r0, r1=r1, sc=scdoc, sclean=sc,
           terms=terms, N=N,
           avlit=', '.join(str(x) for x in a),
           l0=lst(w0), l1=lst(w1),
           t0=table('c0z', w0, 'The bottom word, scaled by %s.' % ('12' if terms == 11 else '4')),
           t1=table('c1z', w1, 'The top word, scaled by %s.' % ('12' if terms == 11 else '4')))


def main(argv):
    check_only = '--check' in argv
    want = [int(a) for a in argv if a.isdigit()] or TARGETS
    real, cplx, jobs = load_doc()
    print('%-6s %-6s %-7s %-9s %-8s %s'
          % ('orbit', 'base', 'terms', 'residues', 'norm', 'status'))
    bad_any = False
    for oid in want:
        rec = jobs[oid]
        w0 = build_word(real, cplx, rec['base'], 0, rec['perm'], rec['t'])
        w1 = build_word(real, cplx, rec['base'], 1, rec['perm'], rec['t'])
        if rec['swap']:
            w0, w1 = w1, w0
        bad, n0, n1 = verify(w0, w1)
        q, a = rec['q'], rec['a']
        res = set(sum(ai * xi for ai, xi in zip(a, x)) % q for x in w0), \
            set(sum(ai * xi for ai, xi in zip(a, x)) % q for x in w1)
        ok = (bad == 0 and n0 == n1 and n0[1:] == (0,) * 7
              and len(res[0]) == 1 and len(res[1]) == 1)
        bad_any |= not ok
        print('%-6d %-6s %-7d %-9s %-8s %s'
              % (oid, rec['base'], len(w0),
                 '%d,%d' % (res[0].pop(), res[1].pop()) if ok else 'MIXED',
                 n0[0] if ok else '-',
                 'ok' if ok else 'FAIL (%d violations)' % bad))
        if ok and not check_only:
            path = os.path.join(OUT, 'Orbit%dReal.lean' % oid)
            io.open(path, 'w', encoding='utf-8', newline=NL).write(
                emit(oid, rec, w0, w1, n0[0]))
    print()
    print('all requested orbits verified:', not bad_any)
    return 1 if bad_any else 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
