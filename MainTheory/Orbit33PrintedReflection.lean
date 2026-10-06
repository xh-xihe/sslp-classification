import Mathlib

/-! Literal six-block character matrix and reflection in the SI orbit-33
derivation. The statements use only rational matrix algebra; no no-go or
inconsistent full-KL hypothesis is used to obtain the identities.
-/

namespace MainTheory.Orbit33PrintedReflection
open scoped BigOperators Matrix
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def C : Matrix (Fin 6) (Fin 6) ℚ :=
  ![![1,1,1,1,1,1],![1,1,-1,-1,-1,-1],![1,-1,1,-1,-1,-1],
    ![1,-1,-1,1,1,-1],![1,-1,-1,1,-1,1],![1,-1,-1,-1,1,1]]

def R : Fin 6 → ℚ := ![3/10,1/5,1/5,1/10,1/10,1/10]
def J : Matrix (Fin 6) (Fin 6) ℚ := Matrix.diagonal ![1,-1,-1,-1,-1,-1]

def inverseMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  ![![3/10,1/5,1/5,1/10,1/10,1/10],
    ![1/5,3/10,-1/5,-1/10,-1/10,-1/10],
    ![1/5,-1/5,3/10,-1/10,-1/10,-1/10],
    ![1/10,-1/10,-1/10,1/5,1/5,-3/10],
    ![1/10,-1/10,-1/10,1/5,-3/10,1/5],
    ![1/10,-1/10,-1/10,-3/10,1/5,1/5]]

theorem inverse_right : C*inverseMatrix=1 := by decide +kernel
theorem inverse_left : inverseMatrix*C=1 := by decide +kernel

theorem inverse : C⁻¹=inverseMatrix := by
  exact Matrix.inv_eq_right_inv inverse_right

theorem reflection : C⁻¹*J*C=fun i j => 2*R i-(if i=j then 1 else 0) := by
  rw [inverse]
  decide +kernel

theorem determinant : Matrix.det C=160 := by decide +kernel

end MainTheory.Orbit33PrintedReflection
