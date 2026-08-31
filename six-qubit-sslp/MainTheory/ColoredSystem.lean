import Mathlib
import MainTheory.Rationalize

/-!
# The coloured augmented system

This file formalizes the linear-algebra step in equations (2.18)--(2.20) of
`documents/20260822/main.tex`.  Equal first moments and normalized positive
weights imply that every pure colour vector is an explicit real linear
combination of augmented support rows.  Consequently every vector in the
kernel of the augmented row matrix has zero colour coordinates.

The statement is deliberately independent of quantum notation.  A colour
`k` has a finite family of physical rows `pt k i`, weights `p k i`, and a
constant colour vector `col k`.  `base` is the reference sector and `owner g`
is the sector carrying the basis colour `g`.
-/

namespace MainTheory.ColoredSystem

open scoped BigOperators

variable {n : ℕ} {κ γ : Type*} {ι : κ → Type*} {𝕜 : Type*}
variable [Fintype γ] [DecidableEq γ] [∀ k, Fintype (ι k)]

/-- A physical support row augmented by the constant vector of its colour. -/
def augmentedRow (pt : ∀ k, ι k → Fin n → 𝕜) (col : κ → γ → 𝕜)
    (k : κ) (i : ι k) : Sum (Fin n) γ → 𝕜
  | Sum.inl j => pt k i j
  | Sum.inr g => col k g

/-- The augmented matrix, indexed by all coloured support rows. -/
def augmentedMatrix (pt : ∀ k, ι k → Fin n → 𝕜) (col : κ → γ → 𝕜) :
    Matrix (Sigma ι) (Sum (Fin n) γ) 𝕜 :=
  fun r => augmentedRow pt col r.1 r.2

/-- The probability-weighted average of the augmented rows of one colour. -/
def weightedRow (pt : ∀ k, ι k → Fin n → ℝ) (col : κ → γ → ℝ)
    (p : ∀ k, ι k → ℝ) (k : κ) : Sum (Fin n) γ → ℝ :=
  fun c => ∑ i, p k i * augmentedRow pt col k i c

/-- A vector supported on one colour coordinate. -/
def pureColor (g : γ) : Sum (Fin n) γ → ℝ
  | Sum.inl _ => 0
  | Sum.inr h => if h = g then 1 else 0

omit [Fintype γ] [DecidableEq γ] in
@[simp] theorem weightedRow_physical
    (pt : ∀ k, ι k → Fin n → ℝ) (col : κ → γ → ℝ)
    (p : ∀ k, ι k → ℝ) (k : κ) (j : Fin n) :
    weightedRow pt col p k (Sum.inl j) = ∑ i, p k i * pt k i j := by
  rfl

omit [Fintype γ] [DecidableEq γ] in
theorem weightedRow_color
    (pt : ∀ k, ι k → Fin n → ℝ) (col : κ → γ → ℝ)
    (p : ∀ k, ι k → ℝ) (k : κ) (g : γ) :
    weightedRow pt col p k (Sum.inr g) =
      col k g * ∑ i, p k i := by
  simp only [weightedRow, augmentedRow]
  rw [mul_comm, Finset.sum_mul]

omit [Fintype γ] in
/-- Equation (2.19): common physical means cancel, while normalized sector
weights leave exactly one colour basis vector. -/
theorem weightedRow_sub_eq_pureColor
    (pt : ∀ k, ι k → Fin n → ℝ) (col : κ → γ → ℝ)
    (p : ∀ k, ι k → ℝ) (base : κ) (owner : γ → κ)
    (hnorm : ∀ k, ∑ i, p k i = 1)
    (hmean : ∀ k j,
      (∑ i, p k i * pt k i j) = ∑ i, p base i * pt base i j)
    (hbase : ∀ g, col base g = 0)
    (howner : ∀ g h, col (owner g) h = if h = g then 1 else 0)
    (g : γ) :
    weightedRow pt col p (owner g) - weightedRow pt col p base =
      pureColor g := by
  funext c
  cases c with
  | inl j =>
      simp only [Pi.sub_apply, weightedRow_physical, pureColor]
      rw [hmean]
      exact sub_self _
  | inr h =>
      simp only [Pi.sub_apply, pureColor]
      rw [weightedRow_color, weightedRow_color, hnorm, hnorm, hbase,
        howner]
      ring

omit [DecidableEq γ] in
/-- Dotting a weighted row with a vector is the weighted sum of the individual
row dot products. -/
theorem dotProduct_weightedRow
    (pt : ∀ k, ι k → Fin n → ℝ) (col : κ → γ → ℝ)
    (p : ∀ k, ι k → ℝ) (k : κ) (v : Sum (Fin n) γ → ℝ) :
    dotProduct (weightedRow pt col p k) v =
      ∑ i, p k i * dotProduct (augmentedRow pt col k i) v := by
  classical
  simp only [dotProduct, weightedRow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Equation (2.20): every kernel vector has zero colour coordinates.

Unlike the old prose-only argument, this theorem refers to the actual
augmented matrix and proves each coordinate equality checked by the kernel. -/
theorem kernel_color_zero
    (pt : ∀ k, ι k → Fin n → ℝ) (col : κ → γ → ℝ)
    (p : ∀ k, ι k → ℝ) (base : κ) (owner : γ → κ)
    (hnorm : ∀ k, ∑ i, p k i = 1)
    (hmean : ∀ k j,
      (∑ i, p k i * pt k i j) = ∑ i, p base i * pt base i j)
    (hbase : ∀ g, col base g = 0)
    (howner : ∀ g h, col (owner g) h = if h = g then 1 else 0)
    (v : Sum (Fin n) γ → ℝ)
    (hv : (augmentedMatrix pt col).mulVec v = 0) (g : γ) :
    v (Sum.inr g) = 0 := by
  have hzero (k : κ) :
      dotProduct (weightedRow pt col p k) v = 0 := by
    rw [dotProduct_weightedRow]
    apply Finset.sum_eq_zero
    intro i _
    have hi : dotProduct (augmentedRow pt col k i) v = 0 := by
      simpa only [augmentedMatrix, Matrix.mulVec, Pi.zero_apply] using
        congrFun hv ⟨k, i⟩
    rw [hi, mul_zero]
  have hpure := weightedRow_sub_eq_pureColor pt col p base owner
    hnorm hmean hbase howner g
  calc
    v (Sum.inr g) = dotProduct (pureColor g) v := by
      classical
      simp [dotProduct, pureColor]
    _ = dotProduct
        (weightedRow pt col p (owner g) - weightedRow pt col p base) v := by
      rw [hpure]
    _ = dotProduct (weightedRow pt col p (owner g)) v -
        dotProduct (weightedRow pt col p base) v := by
      exact sub_dotProduct _ _ _
    _ = 0 := by rw [hzero, hzero, sub_self]

/-! ## The protected rationalization theorem -/

/-- The coloured argument and rationalization composed into one theorem.

The rows and right-hand side are rational, `u` is an arbitrary real solution,
and the sector probabilities are real.  The returned rational solution solves
the same system and has *exactly the same* colour coordinates as `u`. -/
theorem exists_rational_solution_preserving_colors
    (pt : ∀ k, ι k → Fin n → ℚ) (col : κ → γ → ℚ)
    (p : ∀ k, ι k → ℝ) (base : κ) (owner : γ → κ)
    (hnorm : ∀ k, ∑ i, p k i = 1)
    (hmean : ∀ k j,
      (∑ i, p k i * (pt k i j : ℝ)) =
        ∑ i, p base i * (pt base i j : ℝ))
    (hbase : ∀ g, col base g = 0)
    (howner : ∀ g h, col (owner g) h = if h = g then 1 else 0)
    (rhs : Sigma ι → ℚ) (u : Sum (Fin n) γ → ℝ)
    (hu : ((augmentedMatrix pt col).map (algebraMap ℚ ℝ)).mulVec u =
      fun r => algebraMap ℚ ℝ (rhs r)) :
    ∃ u' : Sum (Fin n) γ → ℚ,
      (augmentedMatrix pt col).mulVec u' = rhs ∧
        ∀ g, algebraMap ℚ ℝ (u' (Sum.inr g)) = u (Sum.inr g) := by
  have hbaseR : ∀ g, (col base g : ℝ) = 0 := by
    intro g
    exact_mod_cast hbase g
  have hownerR : ∀ g h, (col (owner g) h : ℝ) =
      if h = g then 1 else 0 := by
    intro g h
    rw [howner]
    split <;> simp
  have hkernel : ∀ v : Sum (Fin n) γ → ℝ,
      ((augmentedMatrix pt col).map (algebraMap ℚ ℝ)).mulVec v = 0 →
        ∀ g, v (Sum.inr g) = 0 := by
    intro v hv g
    apply kernel_color_zero
      (pt := fun k i j => (pt k i j : ℝ))
      (col := fun k h => (col k h : ℝ)) p base owner
      hnorm hmean hbaseR hownerR v
    have hmat :
        augmentedMatrix (fun k i j => (pt k i j : ℝ))
            (fun k h => (col k h : ℝ)) =
          (augmentedMatrix pt col).map (algebraMap ℚ ℝ) := by
      ext r c
      cases c <;> rfl
    rw [hmat]
    exact hv
  exact MainTheory.Rationalize.exists_solution_preserving_coordinates
    (augmentedMatrix pt col) rhs Sum.inr u hu hkernel

end MainTheory.ColoredSystem
