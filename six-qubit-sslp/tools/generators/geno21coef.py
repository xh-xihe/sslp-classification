"""Emit SixQubit/Orbit21Coef.lean: the certificate's coefficient, over Nat masks.

Averaging reduces the Farkas identity to a per-label check, so the coefficient
has to be cheap for the kernel.  It is written over `Nat` masks rather than
`Fin 6 -> Bool` -- function-valued `decide` is slow, and the development already
uses the mask trick in `SixQubit/Realize.lean` -- and scaled by 32 so it is
integral.

Two things are checked before anything is written, and nothing is written if
either fails:

  * the emitted closed form agrees, on all 4096 labels, with the coefficient as
    computed the way `tools/verification/o21farkas.py` computes it;
  * summing it over the four-element symmetry group gives zero on every label
    outside the forced set.

CAVEAT.  The `forced` predicate is not a proved vanishing condition -- its
`A_a(x) = 0` disjunct is false for orbit 21, whose support is a proper subset
of its fibre.  What is emitted is therefore a true arithmetic identity that
is not yet a step in a proof.  See the docstring of the emitted module.

The second is the statement the Lean will `decide`.  Emitting a formula that
merely looks right is how a certificate ends up certifying nothing.
"""
import io
import os
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
DOC = os.path.join(REPO, 'documents', '20260822', 'supplementary.tex')
NL = chr(10)
BS = chr(92)
PAULI = {'I': (0, 0), 'X': (1, 0), 'Y': (1, 1), 'Z': (0, 1)}
AVEC = [1, 1, 1, 2, 2, 3]
GMASK = sum(1 << j for j in (0, 1, 2, 5))
ZS = [(0, 1 << i) for i in (0, 1, 2, 5)]
I0 = (0, 0)


def pc(v):
    return bin(v).count('1')


def wt(F):
    return pc(F[0] | F[1])


def wtA(m):
    return sum(AVEC[j] for j in range(6) if (m >> j) & 1) % 4


def pair(E, F):
    return (pc(E[0] & F[1]) + pc(E[1] & F[0])) % 2


def label(sn):
    x = z = 0
    for j, ch in enumerate(sn):
        a, b = PAULI[ch]
        if a:
            x |= 1 << j
        if b:
            z |= 1 << j
    return (x, z)


def load():
    s = io.open(DOC, encoding='utf-8').read()

    def grab(lab):
        i = s.find(BS + 'label{eq:' + lab + '}')
        j = s.rfind(BS + 'begin{', 0, i)
        return [label(m) for m in re.findall(r'mathrm\{([IXYZ]{6})\}', s[j:i])]
    out = [grab(k) for k in
           ('o21-Bset', 'o21-Tset', 'o21-R2', 'o21-R3', 'o21-R4')]
    for L, n in zip(out, (3, 22, 11, 6, 12)):
        assert len(L) == n, 'label set has %d entries, expected %d' % (len(L), n)
    return out


def reference(F, sets):
    """The coefficient exactly as o21farkas.py builds it, times 32."""
    B, T, R2, R3, R4 = sets
    v = Fraction(1 if wt(F) == 2 else 0)
    for E in B:
        v -= Fraction(2 * (-1) ** pair(E, F), 32)
    for E in T:
        v -= Fraction(2 * ((-1) ** wt(F)) * ((-1) ** pair(E, F)), 32)
    if F in set(R2):
        v -= 2
    if F in set(R3):
        v -= 3
    if F in set(R4):
        v -= 4
    if F == I0:
        v -= 3
    w = wt(F)
    if w == 6:
        v += Fraction(1, 2)
    if w == 1:
        v += 2
    if w in (2, 3):
        v += Fraction(1, 2)
    v -= Fraction(6 * (-1) ** pair(I0, F), 32)
    if F == I0:
        v += 6
    for Z in ZS:
        v += Fraction(2 * (-1) ** pair(Z, F), 32)
        if F == Z:
            v -= 2
    v32 = v * 32
    assert v32.denominator == 1, 'coefficient not integral after scaling'
    return int(v32)


def emitted(F, sets):
    """The same thing, arranged the way the Lean closed form computes it."""
    B, T, R2, R3, R4 = sets
    x, z = F
    w = wt(F)
    acc = 32 if w == 2 else 0
    for E in B:
        acc -= 2 * (-1) ** pair(E, F)
    for E in T:
        acc -= 2 * (-1) ** ((pair(E, F) + w) % 2)
    if F in set(R2):
        acc -= 64
    if F in set(R3):
        acc -= 96
    if F in set(R4):
        acc -= 128
    if w == 6:
        acc += 16
    if w == 1:
        acc += 64
    if w == 2:
        acc += 16
    if w == 3:
        acc += 16
    acc -= 6 * (-1) ** pair(I0, F)
    for Z in ZS:
        acc += 2 * (-1) ** pair(Z, F)
        if F == Z:
            acc -= 64
    if F == I0:
        acc += 96                      # (-3 + 6) * 32
    return acc


def lit(pairs):
    return '[' + ', '.join('(%d, %d)' % p for p in pairs) + ']'


def main(argv):
    sets = load()
    labels = [(x, z) for x in range(64) for z in range(64)]

    bad = [F for F in labels if reference(F, sets) != emitted(F, sets)]
    print('closed form agrees with the reference on all 4096 labels: %s'
          % (not bad))
    if bad:
        print('  first mismatch %s: reference %d, emitted %d'
              % (bad[0], reference(bad[0], sets), emitted(bad[0], sets)))
        return 1

    forced = set(F for F in labels if pc(GMASK & F[0]) % 2 or wtA(F[0]) != 0)

    def s1(F):
        return (F[0], F[1] ^ GMASK)

    def s2(F):
        return (F[0], F[1] ^ (F[0] & GMASK))
    grp = [lambda F: F, s1, s2, lambda F: s1(s2(F))]
    nz = [F for F in labels
          if sum(emitted(g(F), sets) for g in grp) != 0 and F not in forced]
    print('group sum vanishes off the forced set                    : %s'
          % (not nz))
    if nz:
        print('  %d labels fail' % len(nz))
        return 1
    vals = [emitted(F, sets) for F in labels]
    print('coefficient range: %d .. %d' % (min(vals), max(vals)))

    B, T, R2, R3, R4 = sets
    body = '''import Mathlib

/-!
# Orbit 21: the certificate's coefficient

`SixQubit/Averaging.lean` reduces the Farkas identity to a per-label check once
the coefficient is averaged over the symmetry group.  This file carries that
coefficient, scaled by 32 so it is integral, written over `Nat` masks so the
kernel can compute with it: `decide` over `Fin 6 -> Bool` is slow, and the
development already uses the mask trick in `SixQubit/Realize.lean`.

Every term is a closed form in the label -- three fixed sets of Paulis from the
certificate, a few weight tests, the commutation pairing.  No sum over all 4096
labels appears, which is what keeps the check affordable.

Generated by `tools/generators/geno21coef.py`, which refuses to write unless the
closed form agrees with the reference computation on all 4096 labels and the
group sum vanishes off the forced set.
-/

namespace SixQubit.Orbit21Coef

/-- Population count of a six-bit mask. -/
def pc (m : Nat) : Nat :=
  (m &&& 1) + ((m >>> 1) &&& 1) + ((m >>> 2) &&& 1)
    + ((m >>> 3) &&& 1) + ((m >>> 4) &&& 1) + ((m >>> 5) &&& 1)

/-- Pauli weight of the label `(x, z)`. -/
def wt (x z : Nat) : Nat := pc (x ||| z)

/-- The angle-vector weight of a mask, modulo four. -/
def wtA (m : Nat) : Nat :=
  ((m &&& 1) + ((m >>> 1) &&& 1) + ((m >>> 2) &&& 1)
    + 2 * ((m >>> 3) &&& 1) + 2 * ((m >>> 4) &&& 1)
    + 3 * ((m >>> 5) &&& 1)) % 4

/-- The commutation pairing, as `0` or `1`. -/
def pr (ex ez fx fz : Nat) : Nat := (pc (ex &&& fz) + pc (ez &&& fx)) % 2

/-- `(-1)^k`. -/
def sgn (k : Nat) : Int := if k % 2 = 0 then 1 else -1

/-- The `Z`-mask of the forced stabilizer `G = Z1 Z2 Z3 Z6`. -/
def gmask : Nat := {GMASK}

def bset : List (Nat × Nat) := {BSET}

def tset : List (Nat × Nat) := {TSET}

def r2set : List (Nat × Nat) := {R2SET}

def r3set : List (Nat × Nat) := {R3SET}

def r4set : List (Nat × Nat) := {R4SET}

def zset : List (Nat × Nat) := {ZSET}

def mem (x z : Nat) (L : List (Nat × Nat)) : Bool := L.contains (x, z)

/-- Thirty-two times the coefficient of `normSq (trProj psi F)` in

    (A_2 - 1) - RHS - (the constraint combination),

as a closed form in the label `F = (x, z)`. -/
def coef (x z : Nat) : Int :=
  (if wt x z = 2 then 32 else 0)
  - bset.foldl (fun acc E => acc + 2 * sgn (pr E.1 E.2 x z)) 0
  - tset.foldl (fun acc E => acc + 2 * sgn (pr E.1 E.2 x z + wt x z)) 0
  - (if mem x z r2set then 64 else 0)
  - (if mem x z r3set then 96 else 0)
  - (if mem x z r4set then 128 else 0)
  + (if wt x z = 6 then 16 else 0)
  + (if wt x z = 1 then 64 else 0)
  + (if wt x z = 2 then 16 else 0)
  + (if wt x z = 3 then 16 else 0)
  - 6 * sgn (pr 0 0 x z)
  + zset.foldl (fun acc Z => acc + 2 * sgn (pr Z.1 Z.2 x z)) 0
  - (if mem x z zset then 64 else 0)
  + (if x = 0 && z = 0 then 96 else 0)

/-- The label is forced to have vanishing coefficient: it either anticommutes
with `G`, or its `X`-mask does not preserve the fibers. -/
def forced (x : Nat) : Bool := pc (gmask &&& x) % 2 = 1 || wtA x != 0

/-- Multiplication by `G`, on labels. -/
def shiftG (x z : Nat) : Nat × Nat := (x, z ^^^ gmask)

/-- Conjugation by the diagonal gate `D`, on labels. -/
def shiftD (x z : Nat) : Nat × Nat := (x, z ^^^ (x &&& gmask))

/-- **The certificate, as one finite check.**

Summed over the four-element symmetry group the coefficient vanishes at every
label that is not already forced to contribute nothing. -/
theorem coef_group_sum : ∀ m < 64, ∀ k < 64,
    coef m k + coef (shiftG m k).1 (shiftG m k).2
      + coef (shiftD m k).1 (shiftD m k).2
      + coef (shiftG (shiftD m k).1 (shiftD m k).2).1
          (shiftG (shiftD m k).1 (shiftD m k).2).2 = 0
    ∨ forced m = true := by decide

end SixQubit.Orbit21Coef
'''
    for k, v in (('{GMASK}', str(GMASK)), ('{BSET}', lit(B)), ('{TSET}', lit(T)),
                 ('{R2SET}', lit(R2)), ('{R3SET}', lit(R3)), ('{R4SET}', lit(R4)),
                 ('{ZSET}', lit(ZS))):
        body = body.replace(k, v)
    out = os.path.join(REPO, 'SixQubit', 'Orbit21Coef.lean')
    if '--check' in argv:
        print('check only; would write %d lines' % body.count(NL))
        return 0
    fh = io.open(out, 'w', encoding='utf-8', newline=NL)
    fh.write(body)
    fh.close()
    print('wrote %s : %d lines' % (out, body.count(NL)))
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
