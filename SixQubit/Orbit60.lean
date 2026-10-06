import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 60

Orbit 60 of `six_qubit_sslp_v7.tex`: q = 7, angle vector
a = (1, 2, 2, 2, 4, 4), closed in Section 13.

Here the exact moment polytope has dimension 2, so the probabilities are
*not* all determined.  They do not need to be: the four probabilities at the
endpoints of the two edges are constant on the whole polytope, and that is
all the two-edge Walsh obstruction uses.  The theorem `MomentSystem.endpoints`
derives exactly those four values from the moment equations.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit60

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The orbit -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y2 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def y3 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y4 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y5 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y6 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y7 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def y8 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8}
def S1 : Finset (SS.BitString 6) := S0.image SS.complement

def av : Fin 6 -> ZMod 7 := ![1, 2, 2, 2, 4, 4]

/-- The support is exactly the residue-zero fiber, decided over all
sixty-four strings: this certifies the transcription. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_residue :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## The two-edge incidence -/

def t1 : SS.BitString 6 := bs true  false false false false false  -- 100000
def t2 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

/-- Flip of qubit 1. -/
def ef : SS.BitString 6 := SS.stdBasis 0

/-- The separating coordinate, qubit 2. -/
def ez : SS.BitString 6 := SS.stdBasis 1

theorem incidence : S1.filter (fun y => SS.bxor y ef ∈ S0) = {t1, t2} := by decide
theorem t1_ne_t2 : t1 ≠ t2 := by decide
theorem flip_t1 : SS.bxor t1 ef = y0 := by decide
theorem flip_t2 : SS.bxor t2 ef = y1 := by decide
theorem sign_t1 : SS.bdot ez t1 = false := by decide
theorem sign_t2 : SS.bdot ez t2 = true := by decide
theorem sign0_t1 : SS.bdot (fun _ => false) t1 = false := by decide
theorem sign0_t2 : SS.bdot (fun _ => false) t2 = false := by decide
theorem t1_eq_compl : t1 = SS.complement y1 := by decide

/-! ## The two off-diagonal matrix elements -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

def A (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y0) * d t1
def B (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y1) * d t2

theorem offSum_flip (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef (fun _ => false) = A c d + B c d := by
  unfold offSum
  rw [incidence, Finset.sum_pair t1_ne_t2, sign0_t1, sign0_t2, flip_t1, flip_t2]
  simp [SixQubit.signMul, A, B]

theorem offSum_flipZ (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef ez = A c d - B c d := by
  unfold offSum
  rw [incidence, Finset.sum_pair t1_ne_t2, sign_t1, sign_t2, flip_t1, flip_t2]
  simp [SixQubit.signMul, A, B]
  ring

/-! ## The moment system -/

/-- The two normalizations and all twenty-one moment equalities of the exact
diagonal system.  The polytope is 2 dimensional, so these do not determine
every probability; they do determine the four that the obstruction uses. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 = 1
  m1 : q2 + q3 + q4 + q5 + q6 + q7 + q8 = r0 + r1
  m2 : q1 + q6 + q7 + q8 = r0 + r2 + r3 + r4 + r5
  m3 : q1 + q4 + q5 + q8 = r0 + r2 + r3 + r6 + r7
  m4 : q1 + q2 + q3 + q8 = r0 + r4 + r5 + r6 + r7
  m5 : q1 + q3 + q5 + q7 = r0 + r2 + r4 + r6 + r8
  m6 : q1 + q2 + q4 + q6 = r0 + r3 + r5 + r7 + r8
  c12 : q6 + q7 + q8 = r0
  c13 : q4 + q5 + q8 = r0
  c14 : q2 + q3 + q8 = r0
  c15 : q3 + q5 + q7 = r0
  c16 : q2 + q4 + q6 = r0
  c23 : q1 + q8 = r0 + r2 + r3
  c24 : q1 + q8 = r0 + r4 + r5
  c25 : q1 + q7 = r0 + r2 + r4
  c26 : q1 + q6 = r0 + r3 + r5
  c34 : q1 + q8 = r0 + r6 + r7
  c35 : q1 + q5 = r0 + r2 + r6
  c36 : q1 + q4 = r0 + r3 + r7
  c45 : q1 + q3 = r0 + r4 + r6
  c46 : q1 + q2 = r0 + r5 + r7
  c56 : q1 = r0 + r8

/-- The four endpoint probabilities are constant on the moment polytope. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) :
    q0 = 3/14 ∧ q1 = 2/7 ∧ r1 = 2/7 ∧ r0 = 3/14 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Hence all four are strictly positive. -/
theorem MomentSystem.endpoints_pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) :
    0 < q0 ∧ 0 < q1 ∧ 0 < r1 ∧ 0 < r0 := by
  obtain ⟨e1, e2, e3, e4⟩ := h.endpoints
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all

/-! ## The no-go -/

theorem two_edge {u v : ℂ} (h1 : u + v = 0) (h2 : u - v = 0) : u = 0 ∧ v = 0 := by
  constructor
  · linear_combination (h1 + h2) / 2
  · linear_combination (h1 - h2) / 2

theorem edge_vanishes (c d : SS.BitString 6 -> ℂ)
    (hf : offSum c d ef (fun _ => false) = 0)
    (hfz : offSum c d ef ez = 0) : A c d = 0 ∧ B c d = 0 := by
  rw [offSum_flip] at hf
  rw [offSum_flipZ] at hfz
  exact two_edge hf hfz

theorem no_go (c d : SS.BitString 6 -> ℂ)
    (hc : c y0 ≠ 0) (hd : d t1 ≠ 0)
    (hf : offSum c d ef (fun _ => false) = 0)
    (hfz : offSum c d ef ez = 0) : False := by
  have hA := (edge_vanishes c d hf hfz).1
  unfold A at hA
  rcases mul_eq_zero.mp hA with h | h
  · exact hc (by simpa using congrArg star h)
  · exact hd h

/-- **Orbit 60 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8))
            (Complex.normSq (d (SS.complement y0))) (Complex.normSq (d (SS.complement y1))) (Complex.normSq (d (SS.complement y2))) (Complex.normSq (d (SS.complement y3))) (Complex.normSq (d (SS.complement y4))) (Complex.normSq (d (SS.complement y5))) (Complex.normSq (d (SS.complement y6))) (Complex.normSq (d (SS.complement y7))) (Complex.normSq (d (SS.complement y8))))
    (hf : offSum c d ef (fun _ => false) = 0)
    (hfz : offSum c d ef ez = 0) : False := by
  obtain ⟨hqA, hqB, hrA, hrB⟩ := hm.endpoints_pos
  refine no_go c d ?_ ?_ hf hfz
  · intro hz; rw [hz] at hqA; simp at hqA
  · intro hz; rw [← t1_eq_compl, hz] at hrA; simp at hrA

end

end SixQubit.Orbit60
