import Mathlib

/-! Primal averaging and strict-support dual certificates for real moments.
These lemmas use arbitrary real probabilities, never rationality of a code.
-/

namespace MainTheory.MatrixPositiveSupportCertificates
noncomputable section
open scoped BigOperators Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Nonempty n]

structure Feasible (M : Matrix m n ℝ) (b : m → ℝ) (p : n → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ p j
  equations : M.mulVec p = b

def ExactSupport (s : Finset n) (p : n → ℝ) : Prop := ∀ j, 0 < p j ↔ j ∈ s

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem zero_off_support {s : Finset n} {p : n → ℝ}
    (hn : ∀ j, 0 ≤ p j) (hs : ExactSupport s p) {j : n} (hj : j ∉ s) : p j = 0 := by
  have h : ¬ 0 < p j := by rw [hs j]; exact hj
  exact le_antisymm (le_of_not_gt h) (hn j)

def average (v : n → n → ℝ) : n → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i, v i

omit [Fintype m] [DecidableEq n] in
theorem average_feasible (M : Matrix m n ℝ) (b : m → ℝ) (v : n → n → ℝ)
    (hv : ∀ i, Feasible M b (v i)) : Feasible M b (average v) := by
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  constructor
  · intro j
    change 0 ≤ (Fintype.card n : ℝ)⁻¹ * (∑ i, v i) j
    rw [Finset.sum_apply]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hcard))
      (Finset.sum_nonneg fun i _ => (hv i).nonneg j)
  · change M.mulVecLin ((Fintype.card n : ℝ)⁻¹ • ∑ i, v i) = b
    rw [map_smul,map_sum]
    have he : ∀ i, M.mulVecLin (v i) = b := fun i => (hv i).equations
    simp_rw [he]
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ext i
    change (Fintype.card n : ℝ)⁻¹ * ((Fintype.card n : ℝ) * b i) = b i
    rw [← mul_assoc,inv_mul_cancel₀ (ne_of_gt hcard),one_mul]

theorem average_exact_support (s : Finset n) (v : n → n → ℝ)
    (hn : ∀ i j, 0 ≤ v i j)
    (hoff : ∀ i j, j ∉ s → v i j = 0)
    (hpos : ∀ j ∈ s, 0 < v j j) : ExactSupport s (average v) := by
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  intro j
  change 0 < (Fintype.card n : ℝ)⁻¹ * (∑ i, v i) j ↔ j ∈ s
  rw [Finset.sum_apply]
  constructor
  · intro h
    by_contra hj
    have hz : (∑ i, v i j) = 0 := Finset.sum_eq_zero fun i _ => hoff i j hj
    rw [hz,mul_zero] at h
    exact (lt_irrefl 0) h
  · intro hj
    apply mul_pos (inv_pos.mpr hcard)
    exact Finset.sum_pos' (fun i _ => hn i j) ⟨j,Finset.mem_univ j,hpos j hj⟩

omit [Nonempty n] in
theorem dual_product_nonneg {M : Matrix m n ℝ} {b : m → ℝ} {p : n → ℝ}
    {s : Finset n} {y : m → ℝ}
    (hp : Feasible M b p) (hs : ExactSupport s p)
    (hy : ∀ j ∈ s, 0 ≤ M.vecMul y j) : 0 ≤ y ⬝ᵥ b := by
  have hn : ∀ j, 0 ≤ M.vecMul y j * p j := by
    intro j
    by_cases hj : j ∈ s
    · exact mul_nonneg (hy j hj) (hp.nonneg j)
    · rw [zero_off_support hp.nonneg hs hj,mul_zero]
  have he := Matrix.dotProduct_mulVec y M p
  rw [hp.equations] at he
  rw [he]
  exact Finset.sum_nonneg fun j _ => hn j

omit [Nonempty n] in
theorem negative_dual_excludes {M : Matrix m n ℝ} {b : m → ℝ}
    {s : Finset n} {y : m → ℝ}
    (hy : ∀ j ∈ s, 0 ≤ M.vecMul y j) (hb : y ⬝ᵥ b < 0) :
    ¬ ∃ p, Feasible M b p ∧ ExactSupport s p := by
  rintro ⟨p,hp,hs⟩
  exact (not_le_of_gt hb) (dual_product_nonneg hp hs hy)

omit [Nonempty n] in
theorem zero_dual_excludes {M : Matrix m n ℝ} {b : m → ℝ}
    {s : Finset n} {y : m → ℝ}
    (hy : ∀ j ∈ s, 0 ≤ M.vecMul y j) (hb : y ⬝ᵥ b = 0)
    (hj : ∃ j ∈ s, 0 < M.vecMul y j) :
    ¬ ∃ p, Feasible M b p ∧ ExactSupport s p := by
  rintro ⟨p,hp,hs⟩
  have hn : ∀ j, 0 ≤ M.vecMul y j * p j := by
    intro j
    by_cases hj : j ∈ s
    · exact mul_nonneg (hy j hj) (hp.nonneg j)
    · rw [zero_off_support hp.nonneg hs hj,mul_zero]
  obtain ⟨j,hjs,hjpos⟩ := hj
  have hsum : 0 < M.vecMul y ⬝ᵥ p :=
    Finset.sum_pos' (fun j _ => hn j)
      ⟨j,Finset.mem_univ j,mul_pos hjpos ((hs j).mpr hjs)⟩
  have he := Matrix.dotProduct_mulVec y M p
  rw [hp.equations,hb] at he
  rw [← he] at hsum
  exact (lt_irrefl 0) hsum

end
end MainTheory.MatrixPositiveSupportCertificates
