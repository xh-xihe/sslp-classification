import MainTheory.FinitePhaseAverage

/-! Fourth-root projection of cubic counts equals the continuous phase projection. -/

namespace MainTheory.CubicContinuousPhaseProjection
noncomputable section
open MainTheory.FinitePhaseAverage
open scoped BigOperators
variable {J I : Type*} [Fintype J] [DecidableEq J]

def continuousCharacter (z : J → ℂ) (a : J → Fin 4) : ℂ :=
  ∏ j, (z j)^(a j).val

def finiteSum (counts : I → J → Fin 4) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => ∑ p : J → Fin 4, character p (counts i)*A i j*star (character p (counts j))

def projection (counts : I → J → Fin 4) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => if counts i=counts j then A i j else 0

theorem finite_sum (counts : I → J → Fin 4) (A : Matrix I I ℂ) :
    finiteSum counts A=(4 : ℂ)^Fintype.card J • projection counts A := by
  ext i j
  have h : finiteSum counts A i j=
      (∑ p : J → Fin 4, character p (counts i)*star (character p (counts j)))*A i j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [h,tensor_pairing]
  by_cases he : counts i=counts j <;>
    simp only [he, if_true, if_false, Matrix.smul_apply, smul_eq_mul,
      projection, zero_mul, mul_zero]

theorem finite_average (counts : I → J → Fin 4) (A : Matrix I I ℂ) :
    ((4 : ℂ)^Fintype.card J)⁻¹ • finiteSum counts A=projection counts A := by
  rw [finite_sum,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)),one_smul]

omit [DecidableEq J] in
theorem character_unit (z : J → ℂ) (hz : ∀ j, z j*star (z j)=1)
    (a : J → Fin 4) : continuousCharacter z a*star (continuousCharacter z a)=1 := by
  unfold continuousCharacter
  rw [star_prod,← Finset.prod_mul_distrib]
  simp_rw [star_pow,← mul_pow,hz]
  simp

omit [DecidableEq J] in
theorem arbitrary_phase_fixed (counts : I → J → Fin 4) (A : Matrix I I ℂ)
    (z : J → ℂ) (hz : ∀ j, z j*star (z j)=1) (i j : I) :
    continuousCharacter z (counts i)*projection counts A i j*
      star (continuousCharacter z (counts j))=projection counts A i j := by
  by_cases h : counts i=counts j
  · simp only [projection,h,if_true]
    rw [show continuousCharacter z (counts j)*A i j*
      star (continuousCharacter z (counts j))=
      (continuousCharacter z (counts j)*star (continuousCharacter z (counts j)))*A i j by ring,
      character_unit z hz,one_mul]
  · simp only [projection,h,if_false,mul_zero,zero_mul]

end
end MainTheory.CubicContinuousPhaseProjection
