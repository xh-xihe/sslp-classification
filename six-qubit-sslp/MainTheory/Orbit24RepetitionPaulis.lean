import MainTheory.Orbit24ParityFrames
import Orbit2.TensorPauli
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit24RepetitionPaulis
open scoped BigOperators Matrix
open Orbit2.TensorPauli
noncomputable section
def RG : Matrix (Fin 2 → Fin 2) (Fin 2) GaussianInt :=
  fun x r => if x 0=r ∧ x 1=r then 1 else 0
def operatorG (k : Label 2) : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) GaussianInt :=
  fun x y => localG (k 0) (x 0) (y 0)*localG (k 1) (x 1) (y 1)
def labels : Fin 3 → Label 2 := ![![3,0],![1,1],![2,1]]
def effectivePauli : Fin 3 → Fin 4 := ![3,1,2]
def R : Matrix (Fin 2 → Fin 2) (Fin 2) ℂ := RG.map GaussianInt.toComplex
theorem gaussian_isometry : RGᴴ*RG=1 := by decide +kernel
theorem gaussian_compressions : ∀ k : Fin 3,
    RGᴴ*operatorG (labels k)*RG=localG (effectivePauli k) := by decide +kernel
theorem actual_operator (k : Label 2) :
    (operatorG k).map GaussianInt.toComplex=operator k := by
  ext x y
  simp [operatorG,operator,tensor,Fin.prod_univ_two,localC,Matrix.map_apply,
    GaussianInt.toComplex_mul]
theorem actual_adjoint : Rᴴ=(RGᴴ).map GaussianInt.toComplex := by
  ext x y
  simp [R,Matrix.conjTranspose_apply,Matrix.map_apply,GaussianInt.toComplex_star]
theorem actual_isometry : Rᴴ*R=1 := by
  rw [actual_adjoint,R,← Matrix.map_mul,gaussian_isometry]
  ext x y
  fin_cases x <;> fin_cases y <;> norm_num [Matrix.map_apply,Matrix.one_apply]
theorem actual_compressions (k : Fin 3) :
    Rᴴ*operator (labels k)*R=localC (effectivePauli k) := by
  rw [actual_adjoint,← actual_operator,R,← Matrix.map_mul,← Matrix.map_mul,
    gaussian_compressions]
  rfl
theorem physical_weights : ∀ k : Fin 3,
    (Finset.univ.filter fun j : Fin 2 => labels k j≠0).card≤2 := by decide +kernel
theorem literal_repetition (r : Fin 2) (x : Fin 2 → Fin 2) :
    R x r=(if x 0=r ∧ x 1=r then 1 else 0) := by
  simp [R,RG,Matrix.map_apply]
end
end MainTheory.Orbit24RepetitionPaulis
