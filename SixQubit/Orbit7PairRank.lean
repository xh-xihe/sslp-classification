import SixQubit.Orbit7Boundary

/-!
# Orbit 7: the physical two-qubit marginal and its matrix rank

The active-coordinate marginal is represented as the literal `4 × 4`
block-diagonal matrix from the manuscript.  This file also proves, over the
kernel definition `Matrix.rank`, that two nonzero rank-one diagonal blocks
have rank exactly two.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

/-- The active-zero diagonal block of the pair marginal. -/
def pairZeroBlock (c : SS.State 6 ℂ) (s : Fin 5) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ U c i j + starA c s i j

/-- The active-one diagonal block of the pair marginal. -/
def pairOneBlock (d : SS.State 6 ℂ) (s : Fin 5) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ W d i j + starB d s i j

/-- The normalized code-projector marginal on the zero-angle qubit and the
active qubit `s`.  The first product coordinate indexes the zero-angle
spinor, and the second indexes the active qubit.  There is no missing global
factor `1/2`: in the target normal form each block is `3U = (1/2)(6U)` (and
likewise for `W`), exactly as in the manuscript's `P/2` convention. -/
def pairMarginal (c d : SS.State 6 ℂ) (s : Fin 5) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.blockDiagonal ![pairZeroBlock c s, pairOneBlock d s]

/-- Rank two at a specified active coordinate. -/
def PairRankTwoAt (c d : SS.State 6 ℂ) (s : Fin 5) : Prop :=
  (pairMarginal c d s).rank = 2

/-- The manuscript's structural rank-two-pair assertion. -/
def HasPairRankTwo (c d : SS.State 6 ℂ) : Prop :=
  ∃ s : Fin 5, PairRankTwoAt c d s

/-- A scaled outer-product block. -/
def scaledOuter (u : Spinor) (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ a * (u i * star (u j))

/-- A block is nonzero rank one in the literal matrix-rank sense. -/
def IsNonzeroRankOneBlock (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M.rank = 1 ∧ M ≠ 0

private def pickedRow (iu : Fin 2) : Fin 1 → Fin 2 := fun _ ↦ iu

/-- A nonzero scaled outer product has matrix rank exactly one. -/
theorem scaledOuter_rank (u : Spinor) (a : ℂ) (iu : Fin 2)
    (hu : u iu ≠ 0) (ha : a ≠ 0) :
    (scaledOuter u a).rank = 1 := by
  let M := scaledOuter u a
  have hfac : M = Matrix.vecMulVec u (fun j ↦ a * star (u j)) := by
    ext i j
    simp [M, scaledOuter, Matrix.vecMulVec]
    ring
  have hupper : M.rank ≤ 1 := by
    rw [hfac]
    exact Matrix.rank_vecMulVec_le u (fun j ↦ a * star (u j))
  have hrow :
      (M.submatrix (pickedRow iu) (Equiv.refl _)).row (0 : Fin 1) ≠ 0 := by
    intro hz
    have hentry := congrFun hz iu
    change a * (u iu * star (u iu)) = 0 at hentry
    have hdiag : a * (u iu * star (u iu)) ≠ 0 :=
      mul_ne_zero ha (mul_ne_zero hu (by simpa using hu))
    exact hdiag hentry
  have hli : LinearIndependent ℂ
      (M.submatrix (pickedRow iu) (Equiv.refl _)).row := by
    rw [linearIndependent_unique_iff]
    exact hrow
  have hrpick :
      (M.submatrix (pickedRow iu) (Equiv.refl _)).rank = 1 := by
    rw [hli.rank_matrix]
    decide
  have hlower : 1 ≤ M.rank := by
    have hle := Matrix.rank_submatrix_le (pickedRow iu) (Equiv.refl _) M
    rw [hrpick] at hle
    exact hle
  change M.rank = 1
  exact Nat.le_antisymm hupper hlower

theorem scaledOuter_isNonzeroRankOne (u : Spinor) (a : ℂ) (iu : Fin 2)
    (hu : u iu ≠ 0) (ha : a ≠ 0) :
    IsNonzeroRankOneBlock (scaledOuter u a) := by
  refine ⟨scaledOuter_rank u a iu hu ha, ?_⟩
  intro hz
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M iu iu) hz
  change a * (u iu * star (u iu)) = 0 at hentry
  exact (mul_ne_zero ha (mul_ne_zero hu (by simpa using hu))) hentry

/-- A generic block diagonal matrix with two scaled outer-product blocks. -/
def twoOuterBlocks (u v : Spinor) (a b : ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.blockDiagonal ![scaledOuter u a, scaledOuter v b]

private def twoOuterLeft (u v : Spinor) :
    Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun p k ↦ if p.2 = k then (if k = 0 then u p.1 else v p.1) else 0

private def twoOuterRight (u v : Spinor) (a b : ℂ) :
    Matrix (Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun k q ↦
    if q.2 = k then
      (if k = 0 then a * star (u q.1) else b * star (v q.1))
    else 0

private lemma twoOuterBlocks_factor (u v : Spinor) (a b : ℂ) :
    twoOuterBlocks u v a b =
      twoOuterLeft u v * twoOuterRight u v a b := by
  ext p q
  rcases p with ⟨pi, pk⟩
  rcases q with ⟨qi, qk⟩
  fin_cases pk <;> fin_cases qk <;>
    simp [twoOuterBlocks, twoOuterLeft, twoOuterRight,
      scaledOuter, Matrix.blockDiagonal_apply, Matrix.mul_apply] <;>
    ring

private def pickedRows (iu iv : Fin 2) : Fin 2 → (Fin 2 × Fin 2) :=
  ![(iu, 0), (iv, 1)]

private lemma pickedRows_linearIndependent (u v : Spinor) (a b : ℂ)
    (iu iv : Fin 2) (hu : u iu ≠ 0) (hv : v iv ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℂ
      (fun k ↦ (twoOuterBlocks u v a b).row (pickedRows iu iv k)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hfun :
      (∑ i, g i •
        (twoOuterBlocks u v a b).row (pickedRows iu iv i)) = 0 := hg
  fin_cases k
  · have hentry := congrFun hfun (iu, 0)
    simp [pickedRows, twoOuterBlocks, scaledOuter, Matrix.blockDiagonal_apply,
      Fin.sum_univ_two] at hentry
    rcases hentry with h | h | h
    · exact h
    · exact (ha h).elim
    · exact (hu h).elim
  · have hentry := congrFun hfun (iv, 1)
    simp [pickedRows, twoOuterBlocks, scaledOuter, Matrix.blockDiagonal_apply,
      Fin.sum_univ_two] at hentry
    rcases hentry with h | h | h
    · exact h
    · exact (hb h).elim
    · exact (hv h).elim

/-- Two nonzero scaled outer-product blocks have literal matrix rank two.
The upper bound is a factorization through `Fin 2`; the lower bound is a
kernel-checked pair of linearly independent rows with disjoint block support.
-/
theorem twoOuterBlocks_rank (u v : Spinor) (a b : ℂ)
    (iu iv : Fin 2) (hu : u iu ≠ 0) (hv : v iv ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (twoOuterBlocks u v a b).rank = 2 := by
  let M := twoOuterBlocks u v a b
  have hli : LinearIndependent ℂ
      (fun k ↦ M.row (pickedRows iu iv k)) := by
    exact pickedRows_linearIndependent u v a b iu iv hu hv ha hb
  have hli' : LinearIndependent ℂ
      (M.submatrix (pickedRows iu iv) (Equiv.refl _)).row := by
    simpa [Matrix.submatrix] using hli
  have hrpick :
      (M.submatrix (pickedRows iu iv) (Equiv.refl _)).rank = 2 := by
    rw [hli'.rank_matrix]
    decide
  have hlower : 2 ≤ M.rank := by
    have hle := Matrix.rank_submatrix_le
      (pickedRows iu iv) (Equiv.refl _) M
    rw [hrpick] at hle
    exact hle
  have hupper : M.rank ≤ 2 := by
    rw [show M = twoOuterLeft u v * twoOuterRight u v a b by
      exact twoOuterBlocks_factor u v a b]
    exact (Matrix.rank_mul_le_left (twoOuterLeft u v)
      (twoOuterRight u v a b)).trans (by
        simpa using Matrix.rank_le_card_width (twoOuterLeft u v))
  change M.rank = 2
  exact Nat.le_antisymm hupper hlower

end

end SixQubit.Orbit7Universal
