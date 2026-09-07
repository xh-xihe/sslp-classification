import MainTheory.FiniteMomentLP

/-! Actual active-face dimensions for the full finite-pipeline moment LP. -/

namespace MainTheory.FiniteMomentLP

open scoped Matrix BigOperators
open MainTheory.FiniteMomentMatrix

noncomputable section

private def extendRows {ι ρ κ : Type*} (A : Matrix ι κ ℝ) : Matrix (Sum ι ρ) κ ℝ :=
  Sum.elim A (fun _ => 0)

private theorem rank_extendRows {ι ρ κ : Type*} [Fintype ι] [Fintype ρ] [Fintype κ]
    [DecidableEq ι] (A : Matrix ι κ ℝ) : (extendRows (ρ := ρ) A).rank = A.rank := by
  let E : Matrix (Sum ι ρ) ι ℝ := Sum.elim (fun i j => if i = j then 1 else 0) (fun _ _ => 0)
  have he : E * A = extendRows (ρ := ρ) A := by
    ext r j
    cases r <;> simp [E, extendRows, Matrix.mul_apply]
  have hu := Matrix.rank_mul_le_right E A
  rw [he] at hu
  have hl := Matrix.rank_submatrix_le (Sum.inl : ι → Sum ι ρ) (Equiv.refl κ)
    (extendRows (ρ := ρ) A)
  have hl' : A.rank ≤ (extendRows (ρ := ρ) A).rank := hl
  exact le_antisymm hu hl'

theorem full_restricted_rank {n : ℕ} (pair : FP) (columns : Fin n → LabeledWord)
    (hinside : ∀ i, InFiber pair (columns i)) :
    (((fullMatrixQ pair).map (algebraMap ℚ ℝ)).submatrix id columns).rank =
      (MainTheory.FiniteMomentMatrix.matrix columns).rank := by
  have he : ((fullMatrixQ pair).map (algebraMap ℚ ℝ)).submatrix id columns =
      extendRows (ρ := LabeledWord) (MainTheory.FiniteMomentMatrix.matrix columns) := by
    ext r j
    cases r with
    | inl r =>
      simp [fullMatrixQ, extendRows, MainTheory.FiniteMomentMatrix.matrix,
        MainTheory.FiniteMomentMatrix.matrixZ]
    | inr x =>
      by_cases hx : columns j = x
      · subst x
        simp [fullMatrixQ, extendRows, hinside j]
      · simp [fullMatrixQ, extendRows, hx]
  rw [he]
  exact rank_extendRows _

private def columnEquiv {n : ℕ} (columns : Fin n → LabeledWord)
    (hinj : Function.Injective columns) : Fin n ≃ (Finset.univ.image columns) :=
  Equiv.ofBijective (fun i => ⟨columns i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => hinj (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
      exact ⟨i, Subtype.ext hi⟩⟩

theorem rank_on_column_image {n : ℕ} (pair : FP) (columns : Fin n → LabeledWord)
    (hinj : Function.Injective columns) (hinside : ∀ i, InFiber pair (columns i)) :
    (((fullMatrixQ pair).map (algebraMap ℚ ℝ)).submatrix id
      ((↑) : (Finset.univ.image columns) → LabeledWord)).rank =
      (MainTheory.FiniteMomentMatrix.matrix columns).rank := by
  have h := Matrix.rank_submatrix
    (((fullMatrixQ pair).map (algebraMap ℚ ℝ)).submatrix id
      ((↑) : (Finset.univ.image columns) → LabeledWord))
    (Equiv.refl _) (columnEquiv columns hinj)
  have he : (((fullMatrixQ pair).map (algebraMap ℚ ℝ)).submatrix id
      ((↑) : (Finset.univ.image columns) → LabeledWord)).submatrix
      (Equiv.refl _) (columnEquiv columns hinj) =
        ((fullMatrixQ pair).map (algebraMap ℚ ℝ)).submatrix id columns := rfl
  rw [he] at h
  rw [← h]
  exact full_restricted_rank pair columns hinside

theorem affine_dimension_eq_of_face {n : ℕ} (pair : FP)
    (face : MainTheory.FinitePipeline.FaceData) (hface : face.Valid pair)
    (columns : Fin n → LabeledWord) (hinj : Function.Injective columns)
    (hcover : ∀ c, InActive face c ↔ ∃ i, columns i = c) :
    Module.finrank ℝ (affineSpan ℝ (polytope pair)).direction =
      n - (MainTheory.FiniteMomentMatrix.matrix columns).rank := by
  let U := Finset.univ.image columns
  have hactive : MainTheory.LPDimension.activeVariables
      ((fullMatrixQ pair).map (algebraMap ℚ ℝ)) (fun r => (fullRhsQ r : ℝ)) = U := by
    ext c
    rw [MainTheory.LPDimension.mem_activeVariables]
    change (∃ p ∈ polytope pair, 0 < p c) ↔ c ∈ U
    rw [active_real_iff pair face hface c, hcover]
    simp [U]
  have hinside : ∀ i, InFiber pair (columns i) := by
    intro i
    have ha := (hcover (columns i)).2 ⟨i, rfl⟩
    rcases hc : columns i with ⟨b, x⟩
    simp only [hc, InActive, InFiber] at ha ⊢
    cases b
    · exact hface.2.2.2.2.1 x ha
    · exact hface.2.2.2.2.2.1 x ha
  have hcard : U.card = n := by
    simp [U, Finset.card_image_of_injective _ hinj]
  have hd := MainTheory.LPDimension.dimension_eq_active_card_sub_rank
    ((fullMatrixQ pair).map (algebraMap ℚ ℝ)) (fun r => (fullRhsQ r : ℝ))
    (polytope_nonempty pair face hface)
  rw [hactive, hcard] at hd
  rw [rank_on_column_image pair columns hinj hinside] at hd
  exact hd

end
end MainTheory.FiniteMomentLP
