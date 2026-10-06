import MainTheory.Orbit36MomentMinor

namespace MainTheory.Orbit36CharacterSpan

open MainTheory.Orbit36MomentCharacters MainTheory.Orbit36MomentMinor

noncomputable def realMinor : Matrix (Fin 12) (Fin 12) ℝ :=
  momentMinor.map (algebraMap ℚ ℝ)

theorem real_determinant_exact : realMinor.det = -(2 : ℝ)^19 := by
  calc
    realMinor.det = (momentMinor.det : ℝ) :=
      ((algebraMap ℚ ℝ).map_det momentMinor).symm
    _ = -(2 : ℝ)^19 := by rw [determinant_exact]; norm_num

theorem realMinor_isUnit : IsUnit realMinor := by
  apply (Matrix.isUnit_iff_isUnit_det realMinor).mpr
  rw [real_determinant_exact]
  norm_num

theorem characters_span_all_functions (f : Fin 12 → ℝ) :
    ∃ a : Fin 12 → ℝ, ∀ j, ∑ i, a i * (momentMinor i j : ℝ) = f j := by
  obtain ⟨a, ha⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr realMinor_isUnit f
  exact ⟨a, congrFun ha⟩

theorem equal_of_character_moments (p q : Fin 12 → ℝ)
    (h : ∀ r, ∑ j, (momentMinor r j : ℝ) * p j =
      ∑ j, (momentMinor r j : ℝ) * q j) : p = q := by
  exact Matrix.mulVec_injective_iff_isUnit.mpr realMinor_isUnit (funext h)

end MainTheory.Orbit36CharacterSpan
