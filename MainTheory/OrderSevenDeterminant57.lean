import MainTheory.OrderSevenSupportDisplays
import MainTheory.MomentMatrix23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderSevenDeterminant57
open MainTheory.OrderSevenSupportDisplays

def leftWords : Fin 7 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (bottom57 i)).toFin
def rightWords : Fin 7 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (top57 i)).toFin

def row : Fin 14 → Fin 23 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13]
def fullColumn : Fin 14 → Fin 14 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13]
def column (j : Fin 14) : Sum (Fin 7) (Fin 7) :=
  if h : (fullColumn j).val < 7 then Sum.inl ⟨(fullColumn j).val,h⟩
  else Sum.inr ⟨(fullColumn j).val-7,by have h' := (fullColumn j).isLt; omega⟩

def matrix : Matrix (Fin 14) (Fin 14) ℚ := fun i j =>
  MainTheory.MomentMatrix23.matrixQ leftWords rightWords (row i) (column j)
def lower : Matrix (Fin 14) (Fin 14) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, -2, -2, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 1, 0, 0, (-1/7), (-2/7), 1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, (-1/7), (-2/7), 0, 1, 0, 0, 0, 0;
    0, 0, 0, -1, -2, -2, (6/7), (-2/7), 1, 1, 1, 0, 0, 0;
    0, 1, 0, 0, 1, 0, (-1/7), (-2/7), 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 1, (-1/7), (-2/7), 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 1, 1, (-1/7), (-2/7), 0, 0, 0, 1, 1, 1]
def upper : Matrix (Fin 14) (Fin 14) ℚ := !![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 1, 1, 0, -1, 0, 0, 0, 0, 0, -1;
    0, 0, -1, -1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1;
    0, 0, 0, -1, 1, 1, 2, -1, -1, -1, -2, 0, 0, 1;
    0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, -1, 0, 1;
    0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, 1;
    0, 0, 0, 0, 0, 0, 7, -2, -2, -2, -2, -2, -2, 5;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]
def perm : Equiv.Perm (Fin 14) := Equiv.swap (1 : Fin 14) 2 * Equiv.swap (2 : Fin 14) 5 * Equiv.swap (3 : Fin 14) 6 * Equiv.swap (5 : Fin 14) 6 * Equiv.swap (6 : Fin 14) 7 * Equiv.swap (8 : Fin 14) 11 * Equiv.swap (9 : Fin 14) 10 * Equiv.swap (10 : Fin 14) 12 * Equiv.swap (11 : Fin 14) 12

theorem factorization : matrix.submatrix perm id=lower*upper := by decide +kernel
theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem perm_sign : Equiv.Perm.sign perm=-1 := by decide +kernel
theorem determinant : matrix.det=-28 := by
  have hd : (matrix.submatrix perm id).det=28 := by
    rw [factorization,Matrix.det_mul,
      Matrix.det_of_lowerTriangular lower lower_triangular,
      Matrix.det_of_upperTriangular upper_triangular]
    norm_num [lower,upper,Fin.prod_univ_succ]
  have h := Matrix.det_permute perm matrix
  rw [perm_sign] at h
  norm_num at h
  linarith
theorem determinant_nonzero : matrix.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.OrderSevenDeterminant57
