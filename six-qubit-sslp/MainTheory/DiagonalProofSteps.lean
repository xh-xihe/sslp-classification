import QECC.UniformRepresentative

/-! Entrywise and scalar computations in the finite diagonal-group proof. -/
namespace MainTheory.DiagonalProofSteps

open scoped BigOperators
open QECC
open Matrix
noncomputable section
variable {n K : ℕ}

theorem real_circle_exp (s : ℝ) :
    ((AddCircle.toCircle (s : LocalPhase) : Circle) : ℂ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem conjugation_entry (theta : PhaseVector n) (P : Operator n)
    (x y : BitString n) :
    (diagonalGate theta * P * (diagonalGate theta).conjTranspose) x y =
      (((supportPhase theta x - supportPhase theta y).toCircle : Circle) : ℂ) *
        P x y := by
  classical
  rw [diagonalGate_conjTranspose]
  simp only [diagonalGate, Matrix.mul_diagonal, Matrix.diagonal_mul,
    supportPhase_neg, sub_eq_add_neg, AddCircle.toCircle_add, Circle.coe_mul]
  ring

theorem real_conjugation_entry (t : Fin n → ℝ) (P : Operator n)
    (x y : BitString n) :
    (diagonalGate (fun j => (t j : LocalPhase)) * P *
        (diagonalGate (fun j => (t j : LocalPhase))).conjTranspose) x y =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((realSupportWeight t x - realSupportWeight t y : ℝ) : ℂ)) * P x y := by
  rw [conjugation_entry, supportPhase_coe_real, supportPhase_coe_real,
    ← AddCircle.coe_sub, real_circle_exp]

theorem hamiltonian_commutator (C : CodeProjector n K) (h : Fin n → ℝ)
    (x y : BitString n) :
    (CodeProjector.weightedNumberOp h * C.proj -
      C.proj * CodeProjector.weightedNumberOp h) x y =
      ((realSupportWeight h x - realSupportWeight h y : ℝ) : ℂ) * C.proj x y := by
  classical
  simp only [CodeProjector.weightedNumberOp, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

theorem hamiltonian_scalar (C : CodeProjector n K) (h mu : Fin n → ℝ)
    (hmu : ∀ j, C.proj * numberOp j * C.proj = (mu j : ℂ) • C.proj)
    (hedge : ∀ x y, C.proj x y ≠ 0 → realSupportWeight h x = realSupportWeight h y) :
    CodeProjector.weightedNumberOp h * C.proj =
      ((∑ j, h j * mu j : ℝ) : ℂ) • C.proj := by
  calc
    _ = CodeProjector.weightedNumberOp h * (C.proj * C.proj) := by rw [C.idempotent]
    _ = (CodeProjector.weightedNumberOp h * C.proj) * C.proj := by rw [Matrix.mul_assoc]
    _ = (C.proj * CodeProjector.weightedNumberOp h) * C.proj := by
      rw [C.weightedNumberOp_commutes h hedge]
    _ = _ := C.weightedNumberOp_compression h mu hmu

theorem kernel_direction_scalar (C : CodeProjector n K) (h mu : Fin n → ℝ)
    (hmu : ∀ j, C.proj * numberOp j * C.proj = (mu j : ℂ) • C.proj)
    (hedge : ∀ x y, C.proj x y ≠ 0 → realSupportWeight h x = realSupportWeight h y) :
    diagonalGate (fun j => (h j : LocalPhase)) * C.proj =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ j, h j * mu j : ℝ) : ℂ)) • C.proj := by
  classical
  ext x y
  simp only [diagonalGate, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases hxy : C.proj x y = 0
  · simp [hxy]
  · have he := congrFun (congrFun (hamiltonian_scalar C h mu hmu hedge) x) y
    simp only [CodeProjector.weightedNumberOp, Matrix.diagonal_mul,
      Matrix.smul_apply, smul_eq_mul] at he
    have hw : realSupportWeight h x = ∑ j, h j * mu j :=
      Complex.ofReal_injective (mul_right_cancel₀ hxy he)
    rw [supportPhase_coe_real, real_circle_exp, hw]

theorem preserving_integer_edges_iff (C : CodeProjector n K)
    (t : Fin n → ℝ) :
    C.Preserves (fun j => (t j : LocalPhase)) ↔
      ∀ e : C.Edge, ∃ z : ℤ,
        realSupportWeight t e.val.1 - realSupportWeight t e.val.2 = (z : ℝ) := by
  constructor
  · intro h e
    have he := h e.val.1 e.val.2 e.property
    rw [supportPhase_coe_real, supportPhase_coe_real] at he
    have hz : ((realSupportWeight t e.val.1 - realSupportWeight t e.val.2 : ℝ) :
        LocalPhase) = 0 := by rw [AddCircle.coe_sub, he, sub_self]
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    exact ⟨z, by simpa using hz.symm⟩
  · intro h x y hxy
    obtain ⟨z, hz⟩ := h ⟨(x, y), hxy⟩
    rw [supportPhase_coe_real, supportPhase_coe_real]
    apply sub_eq_zero.mp
    rw [← AddCircle.coe_sub, hz]
    exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z, by simp⟩

theorem preserving_integer_matrix_iff (C : CodeProjector n K) [Fintype C.Edge]
    (t : Fin n → ℝ) :
    diagonalGate (fun j => (t j : LocalPhase)) * C.proj *
        (diagonalGate (fun j => (t j : LocalPhase))).conjTranspose = C.proj ↔
      ∃ b : C.Edge → ℤ,
        (C.edgeMatrix.map ((Int.castRingHom ℝ) : ℤ → ℝ)) *ᵥ t =
          fun e => (b e : ℝ) := by
  classical
  rw [← C.preserves_iff_gate_conjugates, preserving_integer_edges_iff]
  constructor
  · intro h
    choose b hb using h
    refine ⟨b, funext fun e => ?_⟩
    rw [C.edgeMatrix_mulVec]
    exact hb e
  · rintro ⟨b, hb⟩ e
    refine ⟨b e, ?_⟩
    have he := congrFun hb e
    simpa only [C.edgeMatrix_mulVec] using he

theorem real_projective_replacement (C : CodeProjector n K) (r h mu : Fin n → ℝ)
    (hmu : ∀ j, C.proj * numberOp j * C.proj = (mu j : ℂ) • C.proj)
    (hedge : ∀ x y, C.proj x y ≠ 0 → realSupportWeight h x = realSupportWeight h y) :
    diagonalGate (fun j => ((r j + h j : ℝ) : LocalPhase)) * C.proj =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ j, h j * mu j : ℝ) : ℂ)) •
        (diagonalGate (fun j => (r j : LocalPhase)) * C.proj) := by
  have he : (fun j => ((r j + h j : ℝ) : LocalPhase)) =
      (fun j => (r j : LocalPhase)) + (fun j => (h j : LocalPhase)) := rfl
  rw [he, diagonalGate_add, Matrix.mul_assoc, kernel_direction_scalar C h mu hmu hedge,
    Matrix.mul_smul]

end
end MainTheory.DiagonalProofSteps
