"""Generate `SixQubit/Orbit36Class.lean`.

The chapter "Rigidity of the order-five orbit 36" of `documents/20260821/supplementary.tex`
closes with the orbit-36 rigidity theorem: every exact ((6,2,d>=3)) solution supported on
the two orbit-36 fibers has the full twelve-term support, the six probabilities 1/10 and
six probabilities 1/15 in each logical word, and is EQUIVALENT to the canonical pair under
physical-qubit permutations, local monomial unitaries, logical basis phases, and a possible
interchange of the two logical basis vectors.

The support and magnitude halves are `SixQubit.Orbit36.full_support` and
`SixQubit.Orbit36.magnitudes_forced`; the edge-phase colouring is
`SixQubit.Orbit36Phase.phase_rigidity`; the antiunitary normal form of the top word is
`SixQubit.Orbit36Enum.top_form`.  This generator emits the remaining step: the explicit
gauge transformation carrying an arbitrary solution onto the canonical pair, expressed in
the equivalence layer `SixQubit.CodeEquiv`.

Nothing here is a hypothesis about the solution beyond the twenty-two Knill--Laflamme rows
and the moment system already used by those four modules.

Run:  python tools/generators/gen36class.py
"""

import io
import os

OUT = os.path.join(os.path.dirname(__file__), "..", "..", "SixQubit", "Orbit36Class.lean")

# ---------------------------------------------------------------------------
# geometry of the two fibers, in the SAME indexing as SixQubit/Orbit36.lean
#
#   y0 = u = 000000            z_k = complement y_k
#   y1 = v = 000011
#   y2..y5   = s_1..s_4        (vertex amplitudes)
#   y6..y11  = e12,e13,e14,e23,e24,e34   (edge amplitudes)
#
# qubit i of the string is coordinate i (0-indexed); the paper's vertex i is qubit i-1.
# ---------------------------------------------------------------------------

YBITS = {
    0: "000000",
    1: "000011",
    2: "011110",
    3: "101110",
    4: "110110",
    5: "111010",
    6: "110001",
    7: "101001",
    8: "100101",
    9: "011001",
    10: "010101",
    11: "001101",
}


def support(bits):
    return [i for i, b in enumerate(bits) if b == "1"]


def zbits(bits):
    return "".join("1" if b == "0" else "0" for b in bits)


YSUPP = {k: support(v) for k, v in YBITS.items()}
ZSUPP = {k: support(zbits(v)) for k, v in YBITS.items()}

# canonical amplitude at y_k
CANON = {
    0: "A36", 1: "A36", 2: "A36", 3: "A36", 4: "A36", 5: "A36",
    6: "E36", 7: "rho * E36", 8: "rho ^ 2 * E36",
    9: "rho ^ 2 * E36", 10: "rho * E36", 11: "E36",
}

# the two branches: pi is the relabelling of the twelve fiber points induced by sigma
PI_ID = {k: k for k in range(12)}
PI_SWP = {0: 0, 1: 1, 2: 2, 3: 3, 4: 5, 5: 4, 6: 6, 7: 8, 8: 7, 9: 10, 10: 9, 11: 11}


def prod_str(supp):
    if not supp:
        return "1"
    return " * ".join("t %d" % i for i in supp)


def eps(k):
    return "" if k <= 1 else "-"


out = io.StringIO()
w = out.write

w(r"""import Mathlib

import SixQubit.CodeEquiv
import SixQubit.Orbit36
import SixQubit.Orbit36Code
import SixQubit.Orbit36Phase
import SixQubit.Orbit36Enum

/-!
# Orbit-36 rigidity: the classification

`SixQubit.Orbit36` forces every magnitude of an exact orbit-36 solution and hence the full
twelve-term support; `SixQubit.Orbit36Phase` forces the six edge phases into the unique
proper three-edge-colouring of `K_4`; `SixQubit.Orbit36Enum` forces the top word into the
antiunitary normal form `|1_L> = tau Z_5 Z_6 X^(x)6 K |0_L>`.  This module closes the
chapter: it produces the explicit gauge transformation that carries an arbitrary solution
onto the canonical pair `(c36, d36)` of `SixQubit.Orbit36Code`, so that

    orbit36_rigidity : CodeEquiv.Equivalent ![c, d] ![Orbit36Code.c36, Orbit36Code.d36].

The equivalence is the one of `SixQubit.CodeEquiv`: a permutation of the physical qubits, a
local monomial unitary, logical basis phases, and a possible interchange of the two logical
basis vectors -- and every generator of that group preserves `SS.HasDistance _ 3`
(`CodeEquiv.hasDistance_iff_of_equivalent`), which is what makes the statement meaningful.

## The gauge

Write the solution's amplitudes as `a, b, r_i, c_ij` at the twelve points

    u = 000000,  v = 000011,  s_i = (1_{V minus i};10),  e_ij = (1_{i,j};01).

A diagonal local unitary `otimes_j diag (1, t_j)` multiplies the amplitude at `x` by the
product of `t_j` over the support of `x`, and a logical phase multiplies the whole word.
The seven conditions

    g a = A,  g t4 t5 b = A,  g (T / t_{i-1}) t4 r_i = A  (i = 1..4),  g t0 t1 t5 c12 = E

are the chapter's `7 x 7` integer matrix of determinant `-5`.  Over the unit circle a
nonsingular integer matrix is surjective; concretely the system is solved here in closed
form by one fifth root, which is exactly the index `|det T| = 5`:

    t4^5 (E^3 b^3 g^2 P^2) = A^5 r1^3 r2^3 c12^3,      P = r1 r2 r3 r4,

after which `t0` and then `t1, t2, t3, t5` are rational in the data.  The remaining five
edge equations are *not* imposed: they follow from the three-edge-colouring, because
`r_i r_j c_ij` is multiplied by a factor independent of the edge.

The `omega <-> omega^2` alternative of `Orbit36Phase.phase_rigidity` is resolved by the
transposition of physical qubits `2` and `3` (the chapter's vertices `3` and `4`), which
preserves both fibers; the two branches are the two calls to `core` below.

The top word needs no separate work: both the solution and the canonical pair are in
antiunitary normal form, so the twelve top equations follow from the twelve bottom ones
with the single logical phase

    lam1 = g^{-1} (t0 t1 t2 t3 t4 t5)^{-1} tau^{-1}.

Everything computational is decided by the Lean kernel.  No `sorry`, no `native_decide`.

This file is generated by `tools/generators/gen36class.py`.
-/

namespace SixQubit.Orbit36Class

open scoped BigOperators

noncomputable section

open SixQubit.K4Kernel (rho)
open SixQubit.Orbit36
open SixQubit.Orbit36Enum (TopForm)

/-! ## 1.  The two fiber finsets agree with the ones of `Orbit36Code` -/

theorem S0_eq : Orbit36Code.S0 = Orbit36.S0 := by decide

theorem S1_eq : Orbit36Code.S1 = Orbit36.S1 := by decide

/-! ## 2.  The canonical amplitudes

`A36` is the common vertex amplitude `1/sqrt 10` and `E36` the common edge modulus
`1/sqrt 15`; the six edges carry `1, rho, rho^2, rho^2, rho, 1`. -/

/-- The canonical vertex amplitude. -/
def A36 : ℂ := Orbit36Code.c36 y0

/-- The canonical edge amplitude on `e12`. -/
def E36 : ℂ := Orbit36Code.c36 y6

theorem c36_congr {x y : SS.BitString 6} (h : Orbit36Code.c0z x = Orbit36Code.c0z y) :
    Orbit36Code.c36 x = Orbit36Code.c36 y := by
  show Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c0z x)
      = Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c0z y)
  rw [h]

theorem toC_two_rho :
    Orbit36Code.toC (Orbit36Code.z8 (-1) 0 0 0 0 0 1 0) = 2 * rho := by
  rw [SixQubit.K4Kernel.rho]
  apply Complex.ext
  · simp only [Orbit36Code.toC_re, Orbit36Code.toCre, Orbit36Code.rz, SS.rp, Orbit36Code.z8]
    push_cast
    simp
    ring
  · simp only [Orbit36Code.toC_im, Orbit36Code.toCim, Orbit36Code.rz, SS.rp, Orbit36Code.z8]
    push_cast
    simp
    ring

theorem toC_y7 : Orbit36Code.toC (Orbit36Code.c0z y7)
    = rho * Orbit36Code.toC (Orbit36Code.c0z y6) := by
  have hmul : Orbit36Code.ZQ.mul (Orbit36Code.z8 (-1) 0 0 0 0 0 1 0) (Orbit36Code.c0z y6)
      = Orbit36Code.ZQ.add (Orbit36Code.c0z y7) (Orbit36Code.c0z y7) := by decide
  have h := congrArg Orbit36Code.toC hmul
  rw [Orbit36Code.toC_mul, Orbit36Code.toC_add, toC_two_rho] at h
  linear_combination -h / 2

""")

# ---- the twelve canonical values -------------------------------------------------
for k in [1, 2, 3, 4, 5]:
    w("theorem c36_y%d : Orbit36Code.c36 y%d = A36 := c36_congr (by decide)\n\n" % (k, k))
w("theorem c36_y11 : Orbit36Code.c36 y11 = E36 := c36_congr (by decide)\n\n")

w(r"""theorem c36_y7 : Orbit36Code.c36 y7 = rho * E36 := by
  show Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c0z y7)
      = rho * (Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c0z y6))
  rw [toC_y7]
  ring

theorem c36_y8 : Orbit36Code.c36 y8 = rho ^ 2 * E36 := by
  have h8 : Orbit36Code.c0z y8 = Orbit36Code.ZQ.conj (Orbit36Code.c0z y7) := by decide
  have h6 : Orbit36Code.ZQ.conj (Orbit36Code.c0z y6) = Orbit36Code.c0z y6 := by decide
  show Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c0z y8)
      = rho ^ 2 * (Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c0z y6))
  rw [h8, Orbit36Code.toC_conj, toC_y7, star_mul, SixQubit.Orbit36Enum.star_rho,
    ← Orbit36Code.toC_conj, h6]
  ring

theorem c36_y9 : Orbit36Code.c36 y9 = rho ^ 2 * E36 := (c36_congr (by decide)).trans c36_y8

theorem c36_y10 : Orbit36Code.c36 y10 = rho * E36 := (c36_congr (by decide)).trans c36_y7

theorem normSq_A36 : Complex.normSq A36 = 1/10 := by
  have h : star (Orbit36Code.c36 Orbit36Code.p_u) * Orbit36Code.c36 Orbit36Code.p_u = 1/10 :=
    Orbit36Code.c36_prob_vertex Orbit36Code.p_u (by decide)
  rw [show Orbit36Code.p_u = y0 from by decide, SixQubit.star_mul_self] at h
  show Complex.normSq (Orbit36Code.c36 y0) = 1/10
  have h2 : ((Complex.normSq (Orbit36Code.c36 y0) : ℝ) : ℂ) = (((1/10 : ℝ)) : ℂ) := by
    rw [h]
    norm_num
  exact Complex.ofReal_inj.mp h2

theorem normSq_E36 : Complex.normSq E36 = 1/15 := by
  have h : star (Orbit36Code.c36 Orbit36Code.p_e12) * Orbit36Code.c36 Orbit36Code.p_e12 = 1/15 :=
    Orbit36Code.c36_prob_edge Orbit36Code.p_e12 (by decide)
  rw [show Orbit36Code.p_e12 = y6 from by decide, SixQubit.star_mul_self] at h
  show Complex.normSq (Orbit36Code.c36 y6) = 1/15
  have h2 : ((Complex.normSq (Orbit36Code.c36 y6) : ℝ) : ℂ) = (((1/15 : ℝ)) : ℂ) := by
    rw [h]
    norm_num
  exact Complex.ofReal_inj.mp h2

/-! ## 3.  The canonical pair is in antiunitary normal form

`|1_L> = Z_5 Z_6 X^(x)6 K |0_L>`, i.e. `TopForm c36 d36 1`. -/

""")

w("theorem canonical_topForm : TopForm Orbit36Code.c36 Orbit36Code.d36 1 where\n")
w("  unit := by norm_num\n")
for k in range(12):
    sgn = "Orbit36Code.ZQ.conj (Orbit36Code.c0z y%d)" % k
    if k >= 2:
        sgn = "Orbit36Code.ZQ.neg (%s)" % sgn
    w("  t%d := by\n" % k)
    w("    have h : Orbit36Code.c1z z%d = %s := by decide\n" % (k, sgn))
    w("    show Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c1z z%d)\n" % k)
    w("        = %s(1 * star (Orbit36Code.sc * Orbit36Code.toC (Orbit36Code.c0z y%d)))\n"
      % (eps(k), k))
    if k >= 2:
        w("    rw [h, Orbit36Code.toC_neg, Orbit36Code.toC_conj, star_mul, Orbit36Code.sc_star]\n")
    else:
        w("    rw [h, Orbit36Code.toC_conj, star_mul, Orbit36Code.sc_star]\n")
    w("    ring\n")
w("\n")

w(r"""/-! ## 4.  The two physical-qubit permutations

The identity, and the transposition of qubits `2` and `3` -- the chapter's vertices `3`
and `4` -- which preserves both fibers and interchanges `omega` with `omega^2`. -/

/-- The identity relabelling. -/
def sid : Equiv.Perm (Fin 6) := Equiv.refl _

/-- The transposition of physical qubits `2` and `3`. -/
def swp : Equiv.Perm (Fin 6) :=
  ⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩

/-! ## 5.  The diagonal weight at each fiber point

`W t s = prod_{i in supp s} t i`. -/

""")

def coord_rw(name, bits):
    return [
        "show %s %d = %s from by decide" % (name, i, "true" if b == "1" else "false")
        for i, b in enumerate(bits)
    ]


for k in range(12):
    w("theorem W_y%d (t : Fin 6 → ℂ) : (∏ i, (if y%d i then t i else 1)) = %s := by\n"
      % (k, k, prod_str(YSUPP[k])))
    w("  rw [Fin.prod_univ_six,\n    %s]\n"
      % (",\n    ".join(coord_rw("y%d" % k, YBITS[k]))))
    w("  norm_num\n\n")

for k in range(12):
    w("theorem W_z%d (t : Fin 6 → ℂ) : (∏ i, (if z%d i then t i else 1)) = %s := by\n"
      % (k, k, prod_str(ZSUPP[k])))
    w("  rw [Fin.prod_univ_six,\n    %s]\n"
      % (",\n    ".join(coord_rw("z%d" % k, zbits(YBITS[k])))))
    w("  norm_num\n\n")

# ---------------------------------------------------------------------------
# the gauge algebra
# ---------------------------------------------------------------------------

w(r"""/-! ## 6.  Solving the gauge system

The seven conditions of the chapter's determinant-`-5` matrix, solved in closed form by a
single fifth root; the remaining five edge conditions come out for free from the
three-edge-colouring. -/

set_option maxHeartbeats 1600000 in
/-- **The gauge exists.**  Given the forced magnitudes and the three-edge-colouring of a
solution, there are a logical phase `g` and six unit phases `t 0, ..., t 5` -- one local
diagonal unitary -- carrying the twelve amplitudes onto the canonical ones `A` (six times)
and `E, rho E, rho^2 E, rho^2 E, rho E, E`.  Only the moduli of `A` and `E` are used. -/
theorem gauge_exists
    (a b r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 mu A E : ℂ)
    (ha : Complex.normSq a = 1/10) (hb : Complex.normSq b = 1/10)
    (n1 : Complex.normSq r1 = 1/10) (n2 : Complex.normSq r2 = 1/10)
    (n3 : Complex.normSq r3 = 1/10) (n4 : Complex.normSq r4 = 1/10)
    (hmu : Complex.normSq mu = 1/1500)
    (hA : Complex.normSq A = 1/10) (hE : Complex.normSq E = 1/15)
    (k12 : r1 * r2 * c12 = mu) (k34 : r3 * r4 * c34 = mu)
    (k13 : r1 * r3 * c13 = rho * mu) (k24 : r2 * r4 * c24 = rho * mu)
    (k14 : r1 * r4 * c14 = rho ^ 2 * mu) (k23 : r2 * r3 * c23 = rho ^ 2 * mu) :
    ∃ (g : ℂ) (t : Fin 6 → ℂ),
      Complex.normSq g = 1 ∧ (∀ i, Complex.normSq (t i) = 1)
        ∧ g * 1 * a = A
        ∧ g * (t 4 * t 5) * b = A
        ∧ g * (t 1 * t 2 * t 3 * t 4) * r1 = A
        ∧ g * (t 0 * t 2 * t 3 * t 4) * r2 = A
        ∧ g * (t 0 * t 1 * t 3 * t 4) * r3 = A
        ∧ g * (t 0 * t 1 * t 2 * t 4) * r4 = A
        ∧ g * (t 0 * t 1 * t 5) * c12 = E
        ∧ g * (t 0 * t 2 * t 5) * c13 = rho * E
        ∧ g * (t 0 * t 3 * t 5) * c14 = rho ^ 2 * E
        ∧ g * (t 1 * t 2 * t 5) * c23 = rho ^ 2 * E
        ∧ g * (t 1 * t 3 * t 5) * c24 = rho * E
        ∧ g * (t 2 * t 3 * t 5) * c34 = E := by
  classical
  have hane : a ≠ 0 := by intro h; rw [h, map_zero] at ha; norm_num at ha
  have hbne : b ≠ 0 := by intro h; rw [h, map_zero] at hb; norm_num at hb
  have h1ne : r1 ≠ 0 := by intro h; rw [h, map_zero] at n1; norm_num at n1
  have h2ne : r2 ≠ 0 := by intro h; rw [h, map_zero] at n2; norm_num at n2
  have h3ne : r3 ≠ 0 := by intro h; rw [h, map_zero] at n3; norm_num at n3
  have h4ne : r4 ≠ 0 := by intro h; rw [h, map_zero] at n4; norm_num at n4
  have hAne : A ≠ 0 := by intro h; rw [h, map_zero] at hA; norm_num at hA
  have hEne : E ≠ 0 := by intro h; rw [h, map_zero] at hE; norm_num at hE
  have hc12 : Complex.normSq c12 = 1/15 := by
    have h := congrArg Complex.normSq k12
    rw [map_mul, map_mul, n1, n2, hmu] at h
    linarith
  have hc12ne : c12 ≠ 0 := by intro h; rw [h, map_zero] at hc12; norm_num at hc12
  have hPne : r1 * r2 * r3 * r4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h1ne h2ne) h3ne) h4ne
  have m13 : r3 * c13 = rho * (r2 * c12) :=
    mul_left_cancel₀ h1ne (by linear_combination k13 - rho * k12)
  have m14 : r4 * c14 = rho ^ 2 * (r2 * c12) :=
    mul_left_cancel₀ h1ne (by linear_combination k14 - rho ^ 2 * k12)
  have m23 : r3 * c23 = rho ^ 2 * (r1 * c12) :=
    mul_left_cancel₀ h2ne (by linear_combination k23 - rho ^ 2 * k12)
  have m24 : r4 * c24 = rho * (r1 * c12) :=
    mul_left_cancel₀ h2ne (by linear_combination k24 - rho * k12)
  have m34 : r3 * r4 * c34 = r1 * r2 * c12 := by linear_combination k34 - k12
  obtain ⟨g, hga⟩ : ∃ g : ℂ, g * a = A := ⟨A / a, by field_simp⟩
  have hg : Complex.normSq g = 1 := by
    have h := congrArg Complex.normSq hga
    rw [map_mul, ha, hA] at h
    linarith
  have hgne : g ≠ 0 := by intro h; rw [h, map_zero] at hg; norm_num at hg
  obtain ⟨t4, hK⟩ : ∃ t4 : ℂ,
      t4 ^ 5 * (E ^ 3 * b ^ 3 * g ^ 2 * (r1 * r2 * r3 * r4) ^ 2)
        = A ^ 5 * r1 ^ 3 * r2 ^ 3 * c12 ^ 3 := by
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq
      (A ^ 5 * r1 ^ 3 * r2 ^ 3 * c12 ^ 3 / (E ^ 3 * b ^ 3 * g ^ 2 * (r1 * r2 * r3 * r4) ^ 2))
      (show 0 < 5 by norm_num)
    refine ⟨u, ?_⟩
    rw [hu]
    field_simp
  have h4unit : Complex.normSq t4 = 1 := by
    have hpow : Complex.normSq t4 ^ 5 = 1 := by
      have h := congrArg Complex.normSq hK
      simp only [map_mul, map_pow, hA, n1, n2, n3, n4, hc12, hE, hb, hg] at h
      norm_num at h
      linarith
    have hnn : 0 ≤ Complex.normSq t4 := Complex.normSq_nonneg t4
    rcases lt_trichotomy (Complex.normSq t4) 1 with h | h | h
    · exact absurd hpow (by
        have := pow_lt_one₀ hnn h (by norm_num : (5:ℕ) ≠ 0)
        exact ne_of_lt this)
    · exact h
    · exact absurd hpow (by
        have := one_lt_pow₀ h (by norm_num : (5:ℕ) ≠ 0)
        exact ne_of_gt this)
  have h4ne' : t4 ≠ 0 := by intro h; rw [h, map_zero] at h4unit; norm_num at h4unit
  obtain ⟨t0, h0⟩ : ∃ t0 : ℂ,
      t0 * (g * t4 ^ 2 * (r1 * r2 * r3 * r4) * E * b) = A ^ 2 * r1 ^ 2 * r2 * c12 :=
    ⟨A ^ 2 * r1 ^ 2 * r2 * c12 / (g * t4 ^ 2 * (r1 * r2 * r3 * r4) * E * b), by field_simp⟩
  have h0unit : Complex.normSq t0 = 1 := by
    have h := congrArg Complex.normSq h0
    simp only [map_mul, map_pow, hA, n1, n2, n3, n4, hc12, hE, hb, hg, h4unit] at h
    norm_num at h
    linarith
  have key2 : t0 ^ 2 * (r2 * A * c12) = E * r1 * t4 * b := by
    have hD : g * t4 ^ 2 * (r1 * r2 * r3 * r4) * E * b ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hgne (pow_ne_zero _ h4ne'))
        hPne) hEne) hbne
    refine mul_left_cancel₀ (pow_ne_zero 2 hD) ?_
    linear_combination (t0 * (g * t4 ^ 2 * (r1 * r2 * r3 * r4) * E * b)
      + A ^ 2 * r1 ^ 2 * r2 * c12) * (r2 * A * c12) * h0 - r1 * hK
  have key1 : g * t0 ^ 3 * t4 * (r1 * r2 * r3 * r4) = A * r1 ^ 3 := by
    refine mul_right_cancel₀ (show r2 * A * c12 ≠ 0 from
      mul_ne_zero (mul_ne_zero h2ne hAne) hc12ne) ?_
    linear_combination (g * t4 * (r1 * r2 * r3 * r4) * t0) * key2 + r1 * h0
  obtain ⟨t1, he1⟩ : ∃ t1 : ℂ, t1 * r1 = t0 * r2 := ⟨t0 * r2 / r1, by field_simp⟩
  obtain ⟨t2, he2⟩ : ∃ t2 : ℂ, t2 * r1 = t0 * r3 := ⟨t0 * r3 / r1, by field_simp⟩
  obtain ⟨t3, he3⟩ : ∃ t3 : ℂ, t3 * r1 = t0 * r4 := ⟨t0 * r4 / r1, by field_simp⟩
  obtain ⟨t5, he5⟩ : ∃ t5 : ℂ, t5 * (g * t4 * b) = A := ⟨A / (g * t4 * b), by field_simp⟩
  have u1 : Complex.normSq t1 = 1 := by
    have h := congrArg Complex.normSq he1
    rw [map_mul, map_mul, n1, n2, h0unit] at h
    linarith
  have u2 : Complex.normSq t2 = 1 := by
    have h := congrArg Complex.normSq he2
    rw [map_mul, map_mul, n1, n3, h0unit] at h
    linarith
  have u3 : Complex.normSq t3 = 1 := by
    have h := congrArg Complex.normSq he3
    rw [map_mul, map_mul, n1, n4, h0unit] at h
    linarith
  have u5 : Complex.normSq t5 = 1 := by
    have h := congrArg Complex.normSq he5
    simp only [map_mul, hg, h4unit, hb, hA] at h
    linarith
  have hgb : r1 * (g * t4 * b) ≠ 0 :=
    mul_ne_zero h1ne (mul_ne_zero (mul_ne_zero hgne h4ne') hbne)
  have hgb2 : r1 ^ 2 * (g * t4 * b) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h1ne) (mul_ne_zero (mul_ne_zero hgne h4ne') hbne)
  refine ⟨g, ![t0, t1, t2, t3, t4, t5], hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h0unit
    · exact u1
    · exact u2
    · exact u3
    · exact h4unit
    · exact u5
  · show g * 1 * a = A
    linear_combination hga
  · show g * (t4 * t5) * b = A
    linear_combination he5
  · show g * (t1 * t2 * t3 * t4) * r1 = A
    refine mul_right_cancel₀ (pow_ne_zero 3 h1ne) ?_
    linear_combination (g * t4 * r1 * (t2 * r1) * (t3 * r1)) * he1
      + (g * t4 * r1 * (t0 * r2) * (t3 * r1)) * he2
      + (g * t4 * r1 * (t0 * r2) * (t0 * r3)) * he3 + key1
  · show g * (t0 * t2 * t3 * t4) * r2 = A
    refine mul_right_cancel₀ (pow_ne_zero 3 h1ne) ?_
    linear_combination (g * t0 * t4 * r2 * r1 * (t3 * r1)) * he2
      + (g * t0 * t4 * r2 * r1 * (t0 * r3)) * he3 + key1
  · show g * (t0 * t1 * t3 * t4) * r3 = A
    refine mul_right_cancel₀ (pow_ne_zero 3 h1ne) ?_
    linear_combination (g * t0 * t4 * r3 * r1 * (t3 * r1)) * he1
      + (g * t0 * t4 * r3 * r1 * (t0 * r2)) * he3 + key1
  · show g * (t0 * t1 * t2 * t4) * r4 = A
    refine mul_right_cancel₀ (pow_ne_zero 3 h1ne) ?_
    linear_combination (g * t0 * t4 * r4 * r1 * (t2 * r1)) * he1
      + (g * t0 * t4 * r4 * r1 * (t0 * r2)) * he2 + key1
  · show g * (t0 * t1 * t5) * c12 = E
    refine mul_right_cancel₀ hgb ?_
    linear_combination (g * t0 * t5 * c12 * (g * t4 * b)) * he1
      + (g * t0 ^ 2 * r2 * c12) * he5 + g * key2
  · show g * (t0 * t2 * t5) * c13 = rho * E
    refine mul_right_cancel₀ hgb ?_
    linear_combination (g * t0 * t5 * c13 * (g * t4 * b)) * he2
      + (g * t0 ^ 2 * r3 * c13) * he5 + (g * t0 ^ 2 * A) * m13 + (rho * g) * key2
  · show g * (t0 * t3 * t5) * c14 = rho ^ 2 * E
    refine mul_right_cancel₀ hgb ?_
    linear_combination (g * t0 * t5 * c14 * (g * t4 * b)) * he3
      + (g * t0 ^ 2 * r4 * c14) * he5 + (g * t0 ^ 2 * A) * m14 + (rho ^ 2 * g) * key2
  · show g * (t1 * t2 * t5) * c23 = rho ^ 2 * E
    refine mul_right_cancel₀ hgb2 ?_
    linear_combination (g * t5 * c23 * (g * t4 * b) * (t2 * r1)) * he1
      + (g * t5 * c23 * (g * t4 * b) * (t0 * r2)) * he2
      + (g * t0 ^ 2 * r2 * r3 * c23) * he5 + (g * t0 ^ 2 * r2 * A) * m23
      + (rho ^ 2 * r1 * g) * key2
  · show g * (t1 * t3 * t5) * c24 = rho * E
    refine mul_right_cancel₀ hgb2 ?_
    linear_combination (g * t5 * c24 * (g * t4 * b) * (t3 * r1)) * he1
      + (g * t5 * c24 * (g * t4 * b) * (t0 * r2)) * he3
      + (g * t0 ^ 2 * r2 * r4 * c24) * he5 + (g * t0 ^ 2 * r2 * A) * m24
      + (rho * r1 * g) * key2
  · show g * (t2 * t3 * t5) * c34 = E
    refine mul_right_cancel₀ hgb2 ?_
    linear_combination (g * t5 * c34 * (g * t4 * b) * (t3 * r1)) * he2
      + (g * t5 * c34 * (g * t4 * b) * (t0 * r3)) * he3
      + (g * t0 ^ 2 * r3 * r4 * c34) * he5 + (g * t0 ^ 2 * A) * m34
      + (r1 * g) * key2

""")

# ---------------------------------------------------------------------------
# core assembly
# ---------------------------------------------------------------------------

w(r"""/-! ## 7.  From the twelve fiber equations to the whole state vector -/

""")

w("set_option maxHeartbeats 1600000 in\n")
w("/-- **The classification, given a solved gauge.**  `v k` is the solution's amplitude at\n")
w("the image of the `k`-th fiber point; the twelve `e` hypotheses say that the diagonal\n")
w("unitary `t` and the logical phase `g` carry them onto the canonical amplitudes, and the\n")
w("twelve `hw` hypotheses are the solution's antiunitary normal form transported along the\n")
w("same relabelling.  Everything else is the bookkeeping that turns twelve equations on the\n")
w("fibers into an identity of full state vectors. -/\n")
w("theorem core (c d : SS.BitString 6 → ℂ) (σ : Equiv.Perm (Fin 6)) (g tau : ℂ)\n")
w("    (t : Fin 6 → ℂ) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : ℂ)\n")
w("    (hc : ∀ s, s ∉ Orbit36.S0 → c s = 0)\n")
w("    (hd : ∀ s, s ∉ Orbit36.S1 → d s = 0)\n")
w("    (hS0 : ∀ s : SS.BitString 6, CodeEquiv.permStr σ s ∈ Orbit36.S0 → s ∈ Orbit36.S0)\n")
w("    (hS1 : ∀ s : SS.BitString 6, CodeEquiv.permStr σ s ∈ Orbit36.S1 → s ∈ Orbit36.S1)\n")
w("    (hg : Complex.normSq g = 1) (ht : ∀ i, Complex.normSq (t i) = 1)\n")
w("    (htau : Complex.normSq tau = 1)\n")
for k in range(12):
    w("    (hv%d : c (CodeEquiv.permStr σ y%d) = v%d)\n" % (k, k, k))
for k in range(12):
    w("    (hw%d : d (CodeEquiv.permStr σ z%d) = %s(tau * star v%d))\n" % (k, k, eps(k), k))
for k in range(12):
    w("    (e%d : Orbit36Code.c36 y%d = g * (%s) * v%d)\n" % (k, k, prod_str(YSUPP[k]), k))
w("    : CodeEquiv.Equivalent ![c, d] ![Orbit36Code.c36, Orbit36Code.d36] := by\n")

w(r"""  classical
  have hgne : g ≠ 0 := CodeEquiv.ne_zero_of_normSq hg
  have htne : ∀ i, t i ≠ 0 := fun i => CodeEquiv.ne_zero_of_normSq (ht i)
  have htaune : tau ≠ 0 := CodeEquiv.ne_zero_of_normSq htau
  have hsg : star g = g⁻¹ := eq_inv_of_mul_eq_one_left (CodeEquiv.unit_of_normSq hg)
  have hst : ∀ i, star (t i) = (t i)⁻¹ :=
    fun i => eq_inv_of_mul_eq_one_left (CodeEquiv.unit_of_normSq (ht i))
  have hn0 : t 0 ≠ 0 := htne 0
  have hn1 : t 1 ≠ 0 := htne 1
  have hn2 : t 2 ≠ 0 := htne 2
  have hn3 : t 3 ≠ 0 := htne 3
  have hn4 : t 4 ≠ 0 := htne 4
  have hn5 : t 5 ≠ 0 := htne 5
  set lam1 : ℂ := g⁻¹ * (t 0 * t 1 * t 2 * t 3 * t 4 * t 5)⁻¹ * tau⁻¹ with hlam1def
  have hlam1 : Complex.normSq lam1 = 1 := by
    rw [hlam1def]
    simp only [map_mul, map_inv₀, hg, htau, ht]
    norm_num
  -- the bottom word, at every one of the sixty-four basis strings
  have hbot : ∀ s : SS.BitString 6,
      Orbit36Code.c36 s = g * (∏ i, (if s i then t i else 1)) * c (CodeEquiv.permStr σ s) := by
    intro s
    by_cases hs : s ∈ Orbit36.S0
    · fin_cases hs
""")
for k in range(12):
    w("      · rw [W_y%d, hv%d]\n        exact e%d\n" % (k, k, k))
w(r"""    · rw [Orbit36Code.c36_vanishes_off_S0 s (by rw [S0_eq]; exact hs),
        hc _ (fun hmem => hs (hS0 s hmem))]
      ring
  -- the top word
  have htop : ∀ s : SS.BitString 6,
      Orbit36Code.d36 s = lam1 * (∏ i, (if s i then t i else 1)) * d (CodeEquiv.permStr σ s) := by
    intro s
    by_cases hs : s ∈ Orbit36.S1
    · fin_cases hs
""")
for k in range(12):
    w("      · rw [W_z%d, hw%d, canonical_topForm.t%d, e%d, hlam1def]\n" % (k, k, k, k))
    if k == 0:
        w("        simp only [star_mul, star_one, hsg]\n")
    else:
        w("        simp only [star_mul, hsg, hst]\n")
    w("        field_simp\n")
w(r"""    · rw [Orbit36Code.d36_vanishes_off_S1 s (by rw [S1_eq]; exact hs),
        hd _ (fun hmem => hs (hS1 s hmem))]
      ring
  -- assemble the gauge element
  refine ⟨⟨σ, fun _ => false, fun _ => 1, t, fun _ => by simp, ht⟩, ![g, lam1], false,
    ?_, ?_⟩
  · intro k
    fin_cases k
    · exact hg
    · exact hlam1
  · intro k
    fin_cases k
    · funext s
      show Orbit36Code.c36 s
          = g * ((∏ i, (if s i then t i else 1))
              * c (CodeEquiv.permStr σ (SS.bxor s (fun _ => false))))
      rw [SS.bxor_zero, hbot s]
      ring
    · funext s
      show Orbit36Code.d36 s
          = lam1 * ((∏ i, (if s i then t i else 1))
              * d (CodeEquiv.permStr σ (SS.bxor s (fun _ => false))))
      rw [SS.bxor_zero, htop s]
      ring

/-! ## 8.  The orbit-36 rigidity theorem -/

""")

# ---------------------------------------------------------------------------
# main theorem
# ---------------------------------------------------------------------------

MOMENT = """    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
"""

ROWS = """    (ho0 : offSum c d ex1 w0 = 0)
    (ho1 : offSum c d ex1 w2 = 0)
    (ho2 : offSum c d ex1 w3 = 0)
    (ho3 : offSum c d ex1 w4 = 0)
    (ho4 : offSum c d ex2 w0 = 0)
    (ho5 : offSum c d ex2 w1 = 0)
    (ho6 : offSum c d ex2 w3 = 0)
    (ho7 : offSum c d ex2 w4 = 0)
    (ho8 : offSum c d ex3 w0 = 0)
    (ho9 : offSum c d ex3 w1 = 0)
    (ho10 : offSum c d ex3 w2 = 0)
    (ho11 : offSum c d ex3 w4 = 0)
    (ho12 : offSum c d ex4 w0 = 0)
    (ho13 : offSum c d ex4 w1 = 0)
    (ho14 : offSum c d ex4 w2 = 0)
    (ho15 : offSum c d ex4 w3 = 0)
    (ho16 : offSum c d ex15 w0 = 0)
    (ho17 : offSum c d ex25 w0 = 0)
    (ho18 : offSum c d ex35 w0 = 0)
    (ho19 : offSum c d ex45 w0 = 0)
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d SixQubit.Orbit36Enum.ex16 w0 = 0)
"""

ROWLIST = " ".join("ho%d" % i for i in range(21))

w("set_option maxHeartbeats 3200000 in\n")
w(r"""/-- **Orbit-36 rigidity.**  Every exact solution of the weight-at-most-two
Knill--Laflamme system supported on the two orbit-36 fibers is carried onto the canonical
pair by a permutation of the physical qubits, a local monomial unitary and two logical
basis phases.  Together with `Orbit36.full_support` and `Orbit36.magnitudes_forced` -- the
full twelve-term support and the six probabilities `1/10` and six `1/15` in each word --
this is the chapter's rigidity theorem: orbit 36 carries exactly one equivalence class.

The hypotheses are exactly those of `Orbit36Enum.top_form`: the support conditions, one
`MomentSystem`, and the twenty-two weight-at-most-two cross Knill--Laflamme rows. -/
theorem orbit36_rigidity (c d : SS.BitString 6 → ℂ)
    (hc : ∀ s, s ∉ Orbit36.S0 → c s = 0)
    (hd : ∀ s, s ∉ Orbit36.S1 → d s = 0)
""")
w(MOMENT)
w(ROWS)
w("    : CodeEquiv.Equivalent ![c, d] ![Orbit36Code.c36, Orbit36Code.d36] := by\n")
w("  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=\n")
w("    Orbit36.magnitudes_forced c d hm %s\n" % ROWLIST)
w("  obtain ⟨mu, hmu, hM12, hM34, hbr⟩ :=\n")
w("    Orbit36Phase.phase_rigidity c d hm %s\n" % ROWLIST)
w("  obtain ⟨tau, htf⟩ :=\n")
w("    SixQubit.Orbit36Enum.top_form c d hm %s ho21\n" % ROWLIST)
w("  have htau : Complex.normSq tau = 1 := by\n")
w("    have h := htf.unit\n")
w("    rw [SixQubit.star_mul_self] at h\n")
w("    exact_mod_cast h\n")
w("  rcases hbr with ⟨b13, b24, b14, b23⟩ | ⟨b13, b24, b14, b23⟩\n")

for branch, (pi, perm, hyps) in enumerate([
        (PI_ID, "sid",
         {"k12": "hM12", "k34": "hM34", "k13": "b13", "k24": "b24", "k14": "b14", "k23": "b23"}),
        (PI_SWP, "swp",
         {"k12": "hM12", "k34": "hM34", "k13": "b14", "k24": "b23", "k14": "b13", "k23": "b24"}),
]):
    w("  · obtain ⟨g, t, hg, ht, %s⟩ :=\n" % ", ".join("f%d" % k for k in range(12)))
    w("      gauge_exists (c y%d) (c y%d) (c y%d) (c y%d) (c y%d) (c y%d)\n"
      % tuple(pi[k] for k in range(6)))
    w("        (c y%d) (c y%d) (c y%d) (c y%d) (c y%d) (c y%d) mu A36 E36\n"
      % tuple(pi[k] for k in range(6, 12)))
    for k in range(6):
        w("        q%d " % pi[k])
    w("\n")
    for k in range(6, 12):
        pass
    w("        hmu normSq_A36 normSq_E36\n")
    for nm in ["k12", "k34", "k13", "k24", "k14", "k23"]:
        w("        (by linear_combination %s)\n" % hyps[nm])
    w("    refine core c d %s g tau t %s\n"
      % (perm, " ".join("(c y%d)" % pi[k] for k in range(12))))
    w("      hc hd (by decide) (by decide) hg ht htau\n")
    for k in range(12):
        w("      (congrArg c (by decide)) ")
    w("\n")
    for k in range(12):
        w("      (by rw [show CodeEquiv.permStr %s z%d = z%d from by decide]; exact htf.t%d)\n"
          % (perm, k, pi[k], pi[k]))
    for k in range(12):
        w("      (by rw [%s]; linear_combination -%s)\n"
          % ({0: "show Orbit36Code.c36 y0 = A36 from rfl",
              6: "show Orbit36Code.c36 y6 = E36 from rfl"}.get(
              k, "c36_y%d" % k), "f%d" % k))

w(r"""
/-- The canonical pair really is an exact `((6,2,3))` code, so by the invariance of
`CodeEquiv` every solution of the orbit-36 Knill--Laflamme system is one too. -/
theorem solution_hasDistance (c d : SS.BitString 6 → ℂ)
    (hc : ∀ s, s ∉ Orbit36.S0 → c s = 0)
    (hd : ∀ s, s ∉ Orbit36.S1 → d s = 0)
""")
w(MOMENT)
w(ROWS)
w("    : SS.HasDistance ![c, d] 3 :=\n")
w("  (CodeEquiv.hasDistance_iff_of_equivalent\n")
w("    (orbit36_rigidity c d hc hd hm %s ho21)).mpr Orbit36Code.canonical_is_code\n" % ROWLIST)


# ---- the chapter's theorem, as one statement --------------------------------------
mags = ["Complex.normSq (c y%d) = %s" % (k, "1/10" if k <= 5 else "1/15") for k in range(12)]
mags += ["Complex.normSq (d z%d) = %s" % (k, "1/10" if k <= 5 else "1/15") for k in range(12)]
supp = ["c y%d ≠ 0" % k for k in range(12)] + ["d z%d ≠ 0" % k for k in range(12)]

w(r"""
/-- **The chapter's orbit-36 rigidity theorem, in one statement.**  Every exact solution of
the weight-at-most-two Knill--Laflamme system supported on the two orbit-36 fibers has

  * six probabilities `1/10` and six probabilities `1/15` in each logical word,
  * the full twelve-term support in each logical word, and
  * is equivalent to the canonical pair under physical-qubit permutations, local monomial
    unitaries, logical basis phases, and a possible interchange of the two logical basis
    vectors.

The three components are `Orbit36.magnitudes_forced`, `Orbit36.full_support` and
`orbit36_rigidity`; the first two do not need the support conditions or the `X_1 X_6`
row. -/
theorem orbit36_theorem (c d : SS.BitString 6 → ℂ)
    (hc : ∀ s, s ∉ Orbit36.S0 → c s = 0)
    (hd : ∀ s, s ∉ Orbit36.S1 → d s = 0)
""")
w(MOMENT)
w(ROWS)
w("    : (%s)\n" % ("\n        ∧ ".join(mags)))
w("      ∧ (%s)\n" % ("\n        ∧ ".join(supp)))
w("      ∧ CodeEquiv.Equivalent ![c, d] ![Orbit36Code.c36, Orbit36Code.d36] :=\n")
w("  ⟨Orbit36.magnitudes_forced c d hm %s,\n" % ROWLIST)
w("   Orbit36.full_support c d hm %s,\n" % ROWLIST)
w("   orbit36_rigidity c d hc hd hm %s ho21⟩\n" % ROWLIST)

w("""
end

end SixQubit.Orbit36Class
""")

with io.open(os.path.abspath(OUT), "w", encoding="utf-8", newline="\n") as f:
    f.write(out.getvalue())

print("wrote", os.path.abspath(OUT))
