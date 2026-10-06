import MainTheory.BoundedUnitaryGroup
import MainTheory.KLNecessity

/-! # The faithful matrix representation of projective unitaries

The adjoint action on logical operators is the concrete unitary matrix
U ⊗ conjugate(U). Its kernel consists exactly of scalar unitaries.
-/

namespace MainTheory.UnitaryAdjointRepresentation

noncomputable section

open scoped Matrix Kronecker ComplexConjugate

variable {L : Type*} [Fintype L] [DecidableEq L]

private theorem conjugate_mem_unitary (U : Matrix.unitaryGroup L ℂ) :
    (U.val.map (starRingEnd ℂ)) ∈ Matrix.unitaryGroup L ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have h := congrArg (fun A : Matrix L L ℂ => A.map (starRingEnd ℂ)) U.property.1
  simpa only [Matrix.star_eq_conjTranspose, Matrix.map_mul,
    Matrix.conjTranspose_map (starRingEnd ℂ) (fun _ => rfl),
    Matrix.map_one _ (map_zero _) (map_one _)] using h

/-- The actual adjoint representation matrix on the matrix-unit basis. -/
def adjoint : Matrix.unitaryGroup L ℂ →* Matrix.unitaryGroup (L × L) ℂ where
  toFun U := ⟨U.val ⊗ₖ U.val.map (starRingEnd ℂ),
    Matrix.kronecker_mem_unitary U.property (conjugate_mem_unitary U)⟩
  map_one' := by
    apply Subtype.ext
    change (1 : Matrix L L ℂ) ⊗ₖ (1 : Matrix L L ℂ).map (starRingEnd ℂ) = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_kronecker_one]
  map_mul' U V := by
    apply Subtype.ext
    change (U.val * V.val) ⊗ₖ (U.val * V.val).map (starRingEnd ℂ) = _
    rw [Matrix.map_mul, Matrix.mul_kronecker_mul]
    rfl

@[simp] theorem adjoint_entry (U : Matrix.unitaryGroup L ℂ) (a b c d : L) :
    (adjoint U).val (a, b) (c, d) = U.val a c * conj (U.val b d) := rfl

/-- Global scalar unitaries are precisely the kernel of the adjoint action. -/
theorem adjoint_eq_one_iff (U : Matrix.unitaryGroup L ℂ) :
    adjoint U = 1 ↔ ∃ c : ℂ, U.val = c • (1 : Matrix L L ℂ) := by
  constructor
  · intro h
    have hm := congrArg Subtype.val h
    have hgram (p q : L × L) :
        ∑ _ : Unit, U.val p.1 p.2 * conj (U.val q.1 q.2) =
          (1 : Matrix L L ℂ) p.1 p.2 * conj ((1 : Matrix L L ℂ) q.1 q.2) := by
      have he := congrFun (congrFun hm (p.1, q.1)) (p.2, q.2)
      by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
        simpa [adjoint, Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.one_apply,
          Prod.mk.injEq, hp, hq] using he
    obtain ⟨c, hc⟩ := FiniteKrausChannel.proportional_of_rank_one_gram
      (fun (_ : Unit) (p : L × L) => U.val p.1 p.2)
      (fun p : L × L => (1 : Matrix L L ℂ) p.1 p.2) hgram
    refine ⟨c (), ?_⟩
    ext a b
    exact hc () (a, b)
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    ext ⟨a, b⟩ ⟨e, f⟩
    have hn : c * conj c = 1 := by
      have he := congrArg (fun A : Matrix L L ℂ => A a a) U.property.2
      simpa [hc, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm] using he
    change U.val a e * conj (U.val b f) = (1 : Matrix (L × L) (L × L) ℂ) (a, b) (e, f)
    rw [hc]
    by_cases hae : a = e <;> by_cases hbf : b = f <;>
      simp [Matrix.smul_apply, Matrix.one_apply, hae, hbf, hn]

theorem adjoint_pow_eq_one_iff (U : Matrix.unitaryGroup L ℂ) (m : ℕ) :
    adjoint U ^ m = 1 ↔ ∃ c : ℂ, (U ^ m).val = c • (1 : Matrix L L ℂ) := by
  rw [← map_pow, adjoint_eq_one_iff]

/-- The displayed matrix represents conjugation of every logical operator. -/
theorem adjoint_mulVec (U : Matrix.unitaryGroup L ℂ) (X : Matrix L L ℂ) :
    (adjoint U).val.mulVec (fun p : L × L => X p.1 p.2) =
      fun p : L × L => (U.val * X * U.val.conjTranspose) p.1 p.2 := by
  classical
  funext ⟨a, b⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, adjoint_entry,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change U.val a j * star (U.val b i) * X j i = U.val a j * X j i * star (U.val b i)
  ring

/-- Two unitaries have the same adjoint action exactly when they differ by
one global scalar. -/
theorem adjoint_eq_iff (U V : Matrix.unitaryGroup L ℂ) :
    adjoint U = adjoint V ↔ ∃ c : ℂ, U.val = c • V.val := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, adjoint_eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have he := congrArg (fun M : Matrix L L ℂ => M * V.val) hc
    have hinv : (V⁻¹).val * V.val = 1 := V.property.1
    change (U.val * (V⁻¹).val) * V.val = (c • (1 : Matrix L L ℂ)) * V.val at he
    simpa only [Matrix.mul_assoc, hinv, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] using he
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hinv : V.val * (V⁻¹).val = 1 := V.property.2
    change U.val * (V⁻¹).val = c • (1 : Matrix L L ℂ)
    rw [hc, Matrix.smul_mul, hinv]

/-- Uniform projective orders imply finiteness of the faithful adjoint image. -/
theorem finite_adjoint_image_of_bounded_projective_order
    (G : Subgroup (Matrix.unitaryGroup L ℂ)) (B : ℕ)
    (hB : ∀ U : G, ∃ m : ℕ, 0 < m ∧ m ≤ B ∧
      ∃ c : ℂ, (U.val ^ m).val = c • (1 : Matrix L L ℂ)) :
    Finite (G.map adjoint) := by
  apply BoundedUnitaryGroup.finite_of_bounded_order (G.map adjoint) B
  intro g
  obtain ⟨U, hU, hg⟩ := g.property
  obtain ⟨m, hm, hmB, hc⟩ := hB ⟨U, hU⟩
  refine ⟨m, hm, hmB, ?_⟩
  apply Subtype.ext
  change g.val ^ m = 1
  rw [← hg]
  exact (adjoint_pow_eq_one_iff U m).2 hc

end

end MainTheory.UnitaryAdjointRepresentation
