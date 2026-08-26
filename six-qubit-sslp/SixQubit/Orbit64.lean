import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 64

Orbit 64 of the classification in `six_qubit_sslp_v7.tex`: q = 8, angle
vector a = (1, 1, 3, 3, 3, 6), closed in Section 12.

The exact moment polytope is zero dimensional, so the fourteen
probabilities are forced and strictly positive.  A flip of the first qubit
then has exactly two incidences whose sources differ in coordinate 2, and
the rank-two Walsh system closes the orbit.

Everything computational is decided by the Lean kernel; `native_decide` is
not used, so neither the Lean compiler nor its runtime is trusted.
-/

namespace SixQubit.Orbit64

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The orbit -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y2 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y3 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y4 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def y5 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y6 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

/-- The bottom support: the residue-zero fiber. -/
def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6}

/-- The top support is the bitwise complement of the bottom one. -/
def S1 : Finset (SS.BitString 6) := S0.image SS.complement

/-- The angle vector of this orbit. -/
def av : Fin 6 -> ZMod 8 := ![1, 1, 3, 3, 3, 6]

/-- The support is exactly the residue-zero fiber, decided over all
sixty-four strings.  This certifies the transcription against the angle
vector: a single wrong bit would make this fail. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

/-- The complementary fiber carries residue 1. -/
theorem S1_residue :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## The two-edge incidence -/

def t1 : SS.BitString 6 := bs true  false false false false false  -- 100000
def t2 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

/-- Flip of the first qubit. -/
def e1 : SS.BitString 6 := SS.stdBasis 0

/-- The separating coordinate. -/
def e2 : SS.BitString 6 := SS.stdBasis 1

theorem incidence : S1.filter (fun y => SS.bxor y e1 ∈ S0) = {t1, t2} := by decide
theorem t1_ne_t2 : t1 ≠ t2 := by decide
theorem flip_t1 : SS.bxor t1 e1 = y0 := by decide
theorem flip_t2 : SS.bxor t2 e1 = y1 := by decide
theorem sign_t1 : SS.bdot e2 t1 = false := by decide
theorem sign_t2 : SS.bdot e2 t2 = true := by decide
theorem sign0_t1 : SS.bdot (fun _ => false) t1 = false := by decide
theorem sign0_t2 : SS.bdot (fun _ => false) t2 = false := by decide
theorem t1_eq_compl : t1 = SS.complement y1 := by decide

/-! ## The two off-diagonal matrix elements -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

def A (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y0) * d t1
def B (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y1) * d t2

theorem offSum_X1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d e1 (fun _ => false) = A c d + B c d := by
  unfold offSum
  rw [incidence, Finset.sum_pair t1_ne_t2, sign0_t1, sign0_t2, flip_t1, flip_t2]
  simp [SixQubit.signMul, A, B]

theorem offSum_X1Z2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d e1 e2 = A c d - B c d := by
  unfold offSum
  rw [incidence, Finset.sum_pair t1_ne_t2, sign_t1, sign_t2, flip_t1, flip_t2]
  simp [SixQubit.signMul, A, B]
  ring

/-! ## The moment system, solved -/

/-- Two normalizations, the six one-bit moment equalities, the five
two-bit equalities for coordinate pairs (1,j), and the pair (2,3).
The integer coefficient matrix is nonsingular -- determinant 48 up to
the ordering of rows and columns -- so the fourteen probabilities are
forced.

`q i` is the probability of the bottom string `y i`; `r i` is the
probability of the top string `complement (y i)`, which is exactly the
order `no_go_of_moments` passes them in.  Every row below is computed
against that ordering by `tools/generators/genmomrows.py`. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 = 1
  m1 : q2 + q3 + q4 + q5 + q6 = r0 + r1
  m2 : q1 + q3 + q4 + q5 + q6 = r0 + r2
  m3 : q1 + q2 + q5 + q6 = r0 + r3 + r4
  m4 : q1 + q2 + q4 + q6 = r0 + r3 + r5
  m5 : q1 + q2 + q4 + q5 = r0 + r3 + r6
  m6 : q1 + q2 + q3 = r0 + r4 + r5 + r6
  m12 : q3 + q4 + q5 + q6 = r0
  m13 : q2 + q5 + q6 = r0
  m14 : q2 + q4 + q6 = r0
  m15 : q2 + q4 + q5 = r0
  m16 : q2 + q3 = r0
  m23 : q1 + q5 + q6 = r0

/-- The fourteen equations determine the fourteen probabilities. -/
theorem MomentSystem.solution {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) :
    q0 = 5/16 ∧ q1 = 3/16 ∧ q2 = 3/16 ∧ q3 = 1/8 ∧ q4 = 1/16 ∧ q5 = 1/16 ∧ q6 = 1/16 ∧
    r0 = 5/16 ∧ r1 = 3/16 ∧ r2 = 3/16 ∧ r3 = 1/8 ∧ r4 = 1/16 ∧ r5 = 1/16 ∧ r6 = 1/16 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Every forced probability is strictly positive, so every displayed
string lies in the actual support of any putative code. -/
theorem MomentSystem.pos {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) :
    0 < q0 ∧ 0 < q1 ∧ 0 < q2 ∧ 0 < q3 ∧ 0 < q4 ∧ 0 < q5 ∧ 0 < q6 ∧
    0 < r0 ∧ 0 < r1 ∧ 0 < r2 ∧ 0 < r3 ∧ 0 < r4 ∧ 0 < r5 ∧ 0 < r6 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, h0, h1, h2, h3, h4, h5, h6⟩ := h.solution
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-! ## The no-go -/

/-- Rank-two Walsh system: the Walsh matrix has determinant minus two, so
both edge contributions vanish. -/
theorem two_edge {u v : ℂ} (h1 : u + v = 0) (h2 : u - v = 0) : u = 0 ∧ v = 0 := by
  constructor
  · linear_combination (h1 + h2) / 2
  · linear_combination (h1 - h2) / 2

theorem edge_vanishes (c d : SS.BitString 6 -> ℂ)
    (hX1 : offSum c d e1 (fun _ => false) = 0)
    (hX1Z2 : offSum c d e1 e2 = 0) : A c d = 0 ∧ B c d = 0 := by
  rw [offSum_X1] at hX1
  rw [offSum_X1Z2] at hX1Z2
  exact two_edge hX1 hX1Z2

theorem no_go (c d : SS.BitString 6 -> ℂ)
    (hc : c y0 ≠ 0) (hd : d t1 ≠ 0)
    (hX1 : offSum c d e1 (fun _ => false) = 0)
    (hX1Z2 : offSum c d e1 e2 = 0) : False := by
  have hA := (edge_vanishes c d hX1 hX1Z2).1
  unfold A at hA
  rcases mul_eq_zero.mp hA with h | h
  · exact hc (by simpa using congrArg star h)
  · exact hd h

/-- **Orbit 64 is impossible.**  Nothing is assumed about the
probabilities: they are forced by `MomentSystem` and are strictly positive,
so the two endpoint amplitudes cannot vanish. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6))
            (Complex.normSq (d (SS.complement y0))) (Complex.normSq (d (SS.complement y1))) (Complex.normSq (d (SS.complement y2))) (Complex.normSq (d (SS.complement y3))) (Complex.normSq (d (SS.complement y4))) (Complex.normSq (d (SS.complement y5))) (Complex.normSq (d (SS.complement y6))))
    (hX1 : offSum c d e1 (fun _ => false) = 0)
    (hX1Z2 : offSum c d e1 e2 = 0) : False := by
  obtain ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hr0, hr1, hr2, hr3, hr4, hr5, hr6⟩ := hm.pos
  refine no_go c d ?_ ?_ hX1 hX1Z2
  · intro hz; rw [hz] at hq0; simp at hq0
  · intro hz; rw [← t1_eq_compl, hz] at hr1; simp at hr1

end

end SixQubit.Orbit64
