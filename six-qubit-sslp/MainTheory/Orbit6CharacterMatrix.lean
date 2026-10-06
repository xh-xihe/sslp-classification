import Mathlib
set_option autoImplicit false
namespace MainTheory.Orbit6CharacterMatrix
open scoped Matrix

def W5 : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![1,1,1,1,1],![1,1,-1,-1,-1],![1,-1,1,-1,-1],
    ![1,-1,-1,1,-1],![1,-1,-1,-1,1]]
theorem determinant_checked : W5.det=-48 := by decide +kernel

theorem rows_force_zero (p r1 r2 r3 r4 : ℂ)
    (h0 : p+r1+r2+r3+r4=0)
    (h1 : p+r1-r2-r3-r4=0)
    (h2 : p-r1+r2-r3-r4=0)
    (h3 : p-r1-r2+r3-r4=0)
    (h4 : p-r1-r2-r3+r4=0) :
    p=0 ∧ r1=0 ∧ r2=0 ∧ r3=0 ∧ r4=0 := by
  have hp : p=0 := by
    linear_combination (1/3 : ℂ)*h0+(1/6 : ℂ)*(h1+h2+h3+h4)
  refine ⟨hp,?_,?_,?_,?_⟩
  · linear_combination (1/2 : ℂ)*(h0+h1)-hp
  · linear_combination (1/2 : ℂ)*(h0+h2)-hp
  · linear_combination (1/2 : ℂ)*(h0+h3)-hp
  · linear_combination (1/2 : ℂ)*(h0+h4)-hp
end MainTheory.Orbit6CharacterMatrix
