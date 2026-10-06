import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit order-nine no-go, certified by the kernel

This file formalizes Section 11 of `six_qubit_sslp_v7.tex`:

> No exact ((6,2,d>=3)) qubit code admits a projective diagonal transversal
> logical element of order 9.

The obstruction is a rank-two Walsh system attached to one weight-one flip.
Section 10 of the document pins the unique order-nine moment orbit: the bottom
support is the seven strings listed in `S0` below, the top support is their
bitwise complement, and the fourteen probabilities are forced and strictly
positive.  Taking that moment data as given, the present file closes the
endpoint.

Everything computational here is decided by the Lean kernel.  `native_decide`
is not used, so neither the Lean compiler nor its runtime is trusted.
-/

namespace SixQubit.Order9

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The order-nine moment orbit of Section 10 -/

/-- Convenience constructor, reading a bitstring left to right. -/
def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false
def y1 : SS.BitString 6 := bs true  true  true  true  false false
def y2 : SS.BitString 6 := bs true  true  true  false true  false
def y3 : SS.BitString 6 := bs true  false false true  true  false
def y4 : SS.BitString 6 := bs true  true  false false false true
def y5 : SS.BitString 6 := bs true  false true  false false true
def y6 : SS.BitString 6 := bs false true  true  true  true  true

/-- The bottom support: the seven strings of the Section 10 table. -/
def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6}

/-- The top support is the bitwise complement of the bottom one, because the
angle sum is congruent to one modulo nine. -/
def S1 : Finset (SS.BitString 6) := S0.image SS.complement

/-- The two top strings joined to the bottom support by a flip of qubit one. -/
def t1 : SS.BitString 6 := bs true false false false false false
def t2 : SS.BitString 6 := bs true true  true  true  true  true

/-- Flip of the first qubit. -/
def e1 : SS.BitString 6 := SS.stdBasis 0

/-- The second coordinate, used to separate the two contributions. -/
def e2 : SS.BitString 6 := SS.stdBasis 1

/-- The trivial dressing: no `Z` factor at all.  Naming it, rather than writing
an anonymous `fun _ => false`, is what lets the admissibility checker resolve
the `X` row and confirm it is a weight-one Pauli. -/
def w0 : SS.BitString 6 := bs false false false false false false

/-! ## The support really is the subset-sum fiber

The seven strings above were transcribed from the table in Section 10.  The
next two facts certify that transcription against the angle vector itself, so
a copying error cannot go unnoticed: `S0` is exactly the residue-zero fiber of
the order-nine angle vector, and the complementary fiber carries residue one.
-/

/-- The order-nine angle vector of Section 10.  This is the manifest entry for
orbit 66: `q = 9`, `a = (1, 2, 2, 4, 4, 6)`, projective order `m = 9`, hence
residue shift `d = q/m = 1`. -/
def av : Fin 6 -> ZMod 9 := ![1, 2, 2, 4, 4, 6]

/-- `S0` is precisely the set of all six-bit strings whose weighted subset sum
vanishes modulo nine.  Decided over all sixty-four strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter (fun x => SS.weight av x = 0) = S0 := by
  decide

/-- The top support is exactly the residue-`d` fiber, with `d = q/m = 1` the
manifest shift.  Residue one is also what makes the top support the bitwise
complement of the bottom one, since the angle sum `1+2+2+4+4+6 = 19` is one
modulo nine. -/
theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## The incidence structure, decided by the kernel -/

/-- Exactly two top-support strings are joined to the bottom support by the
flip of qubit one.  This is the two-edge hypothesis of the obstruction lemma. -/
theorem incidence : S1.filter (fun y => SS.bxor y e1 ∈ S0) = {t1, t2} := by decide

theorem t1_ne_t2 : t1 ≠ t2 := by decide

/-- `t1` is the complement of `y6`, i.e. it is the seventh entry of the top
support in the complement ordering `SS.complement y0, ..., SS.complement y6`.
The headline below names that slot in complement form so that the ordering of
the moment rows is visible from the statement itself. -/
theorem complement_y6 : SS.complement y6 = t1 := by decide

/-- The bottom endpoint of the first edge. -/
theorem flip_t1 : SS.bxor t1 e1 = y0 := by decide

/-- The bottom endpoint of the second edge. -/
theorem flip_t2 : SS.bxor t2 e1 = y6 := by decide

/-- The two top strings differ in the second coordinate, so a `Z` there gives
them opposite signs.  This is the separating coordinate of the lemma. -/
theorem sign_t1 : SS.bdot e2 t1 = false := by decide

theorem sign_t2 : SS.bdot e2 t2 = true := by decide

/-- With no `Z` factor both contributions carry the same sign. -/
theorem sign0_t1 : SS.bdot w0 t1 = false := by decide

theorem sign0_t2 : SS.bdot w0 t2 = false := by decide

/-! ## The two off-diagonal matrix elements -/

/-- The off-diagonal matrix element of the Pauli with flip `e` and phase pattern
`z`, up to a global nonzero prefactor: a sum over the top-support strings that
the flip joins to the bottom support.  Here `c` carries the amplitudes of the
logical zero and `d` those of the logical one. -/
def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

/-- The two edge contributions of the obstruction. -/
def A (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y0) * d t1
def B (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y6) * d t2

theorem offSum_X1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d e1 w0 = A c d + B c d := by
  unfold offSum
  rw [incidence, Finset.sum_pair t1_ne_t2, sign0_t1, sign0_t2, flip_t1, flip_t2]
  simp [SixQubit.signMul, A, B]

theorem offSum_X1Z2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d e1 e2 = A c d - B c d := by
  unfold offSum
  rw [incidence, Finset.sum_pair t1_ne_t2, sign_t1, sign_t2, flip_t1, flip_t2]
  simp [SixQubit.signMul, A, B]
  ring


/-! ## The moment system of Section 10, solved

Section 10 asserts that the exact moment polytope at this endpoint is zero
dimensional: fourteen of the moment equations have an integer coefficient
matrix of determinant -36, so the fourteen probabilities are forced.  The
statement below is the constructive form of that assertion, and it is what
removes the moment table from the hypotheses of the no-go.
-/

/-- The fourteen moment equations that Section 10 solves exactly.  The
variables are the seven bottom probabilities and the seven top ones, in the
order of the Section 10 table.  The equations are the two normalizations,
the six one-bit moment equalities (`m1`-`m6`), the five two-bit equalities
for the coordinate pairs (1,j) (`m12`-`m16`), and the pair (2,3) (`m23`).
Every row is stated against the same ordering the headline uses: `q_i` is the
probability of `y_i`, and `r_k` that of `SS.complement y_k`.  The document
records that the resulting integer coefficient matrix has determinant -36,
hence a unique solution; the theorems below exhibit that solution. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 = 1
  m1 : q1 + q2 + q3 + q4 + q5 = r0 + r6
  m2 : q1 + q2 + q4 + q6 = r0 + r3 + r5
  m3 : q1 + q2 + q5 + q6 = r0 + r3 + r4
  m4 : q1 + q3 + q6 = r0 + r2 + r4 + r5
  m5 : q2 + q3 + q6 = r0 + r1 + r4 + r5
  m6 : q4 + q5 + q6 = r0 + r1 + r2 + r3
  m12 : q1 + q2 + q4 = r0
  m13 : q1 + q2 + q5 = r0
  m14 : q1 + q3 = r0
  m15 : q2 + q3 = r0
  m16 : q4 + q5 = r0
  m23 : q1 + q2 + q6 = r0 + r3

/-- **Section 10, exact form.**  The fourteen equations determine the fourteen
probabilities, reproducing the table of Section 10 entry by entry. -/
theorem MomentSystem.solution {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) :
    q0 = 2/9 ∧ q1 = 1/18 ∧ q2 = 1/18 ∧ q3 = 1/6 ∧ q4 = 1/9 ∧ q5 = 1/9 ∧ q6 = 5/18 ∧
    r0 = 2/9 ∧ r1 = 1/18 ∧ r2 = 1/18 ∧ r3 = 1/6 ∧ r4 = 1/9 ∧ r5 = 1/9 ∧ r6 = 5/18 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Every one of the fourteen forced probabilities is strictly positive, so every
displayed basis string lies in the actual support of any putative code. -/
theorem MomentSystem.pos {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) :
    0 < q0 ∧ 0 < q1 ∧ 0 < q2 ∧ 0 < q3 ∧ 0 < q4 ∧ 0 < q5 ∧ 0 < q6 ∧
    0 < r0 ∧ 0 < r1 ∧ 0 < r2 ∧ 0 < r3 ∧ 0 < r4 ∧ 0 < r5 ∧ 0 < r6 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, f0, f1, f2, f3, f4, f5, f6⟩ := h.solution
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-! ## The two-edge flip obstruction -/

/-- **Lemma 11.1 of the document.**  A rank-two Walsh system: if the two edge
contributions satisfy both the unsigned and the signed vanishing condition,
both are zero.  The Walsh matrix has determinant minus two, so it is invertible
over the complex numbers. -/
theorem two_edge {u v : ℂ} (h1 : u + v = 0) (h2 : u - v = 0) : u = 0 ∧ v = 0 := by
  constructor
  · linear_combination (h1 + h2) / 2
  · linear_combination (h1 - h2) / 2

/-! ## The no-go -/

/-- **Theorem 11.2, amplitude form.**  If the two off-diagonal Knill--Laflamme
equations for `X` on qubit one and for `X` on qubit one times `Z` on qubit two
both hold, then the amplitude product on the first edge vanishes.  Since the
Section 10 moment table forces both endpoint amplitudes to be nonzero, no such
code exists. -/
theorem edge_vanishes (c d : SS.BitString 6 -> ℂ)
    (hX1 : offSum c d e1 w0 = 0)
    (hX1Z2 : offSum c d e1 e2 = 0) :
    A c d = 0 ∧ B c d = 0 := by
  rw [offSum_X1] at hX1
  rw [offSum_X1Z2] at hX1Z2
  exact two_edge hX1 hX1Z2

/-- **Theorem 11.2.**  No amplitudes supported on the order-nine moment orbit
satisfy the two off-diagonal distance-three conditions while keeping the four
endpoint amplitudes nonzero. -/
theorem no_go (c d : SS.BitString 6 -> ℂ)
    (hc0 : c y0 ≠ 0) (hd1 : d t1 ≠ 0)
    (hX1 : offSum c d e1 w0 = 0)
    (hX1Z2 : offSum c d e1 e2 = 0) : False := by
  have hA := (edge_vanishes c d hX1 hX1Z2).1
  unfold A at hA
  rcases mul_eq_zero.mp hA with h | h
  · exact hc0 (by simpa using congrArg star h)
  · exact hd1 h

/-- **Theorem 11.2, from the moment system.**  No amplitudes on this orbit
satisfy the fourteen moment equations of Section 10 together with the two
off-diagonal distance-three conditions.  Nothing is assumed about the
probabilities: they are forced by `MomentSystem` and are positive, so the two
endpoint amplitudes cannot vanish. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2))
            (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6))
            (Complex.normSq (d (SS.complement y0))) (Complex.normSq (d (SS.complement y1)))
            (Complex.normSq (d (SS.complement y2))) (Complex.normSq (d (SS.complement y3)))
            (Complex.normSq (d (SS.complement y4))) (Complex.normSq (d (SS.complement y5)))
            (Complex.normSq (d (SS.complement y6))))
    (hX1 : offSum c d e1 w0 = 0)
    (hX1Z2 : offSum c d e1 e2 = 0) : False := by
  obtain ⟨hq0, -, -, -, -, -, -, -, -, -, -, -, -, hr6⟩ := hm.pos
  rw [complement_y6] at hr6
  refine no_go c d ?_ ?_ hX1 hX1Z2
  · intro h; rw [h] at hq0; simp at hq0
  · intro h; rw [h] at hr6; simp at hr6

end

end SixQubit.Order9
