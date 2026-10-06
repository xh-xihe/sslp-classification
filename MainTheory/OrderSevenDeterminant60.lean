import MainTheory.OrderSevenSupportDisplays
import MainTheory.MomentMatrix23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderSevenDeterminant60
open MainTheory.OrderSevenSupportDisplays

def leftWords : Fin 9 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (bottom60 i)).toFin
def rightWords : Fin 9 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (top60 i)).toFin

def row : Fin 16 → Fin 23 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,18]
def fullColumn : Fin 16 → Fin 18 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,17]
def column (j : Fin 16) : Sum (Fin 9) (Fin 9) :=
  if h : (fullColumn j).val < 9 then Sum.inl ⟨(fullColumn j).val,h⟩
  else Sum.inr ⟨(fullColumn j).val-9,by have h' := (fullColumn j).isLt; omega⟩

def matrix : Matrix (Fin 16) (Fin 16) ℚ := fun i j =>
  MainTheory.MomentMatrix23.matrixQ leftWords rightWords (row i) (column j)
def lower : Matrix (Fin 16) (Fin 16) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, -1, (-1/2), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 0, (-1/2), 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, (-1/2), 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, (-5/2), 1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, -1, (-1/2), 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0;
    0, 1, 1, 1, (1/2), 0, 0, 0, (1/2), 0, 0, 1, (-1/2), 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), (1/2), (1/2), (-9/4), 5, 1, 0;
    0, 0, 0, 0, 0, -1, 0, 0, (-7/2), 1, -1, -1, 1, -3, -2, 1]
def upper : Matrix (Fin 16) (Fin 16) ℚ := !![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 1, 1, 1, 1, 0, -1, 0, 0, 0, 0, 0, -1;
    0, 0, -1, 0, -1, -1, 0, -1, 1, 0, 0, -1, 0, -1, -1, 1;
    0, 0, 0, -1, -1, 0, -1, -1, 1, 0, 0, 0, -1, -1, 0, 1;
    0, 0, 0, 0, 2, 0, 0, 2, -1, 0, 0, 0, 0, 2, 0, -1;
    0, 0, 0, 0, 0, -1, -1, -1, (5/2), -1, -1, -1, -1, -1, -2, (3/2);
    0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 1, 0, 1, 1, 1, -1;
    0, 0, 0, 0, 0, 0, 0, 1, (1/2), -1, 1, 0, 0, 1, 0, (-1/2);
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1, -1, (3/2), (3/2), -2, (3/2);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, -1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1/2);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, (17/4);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7]
def perm : Equiv.Perm (Fin 16) := Equiv.swap (1 : Fin 16) 2 * Equiv.swap (2 : Fin 16) 4 * Equiv.swap (4 : Fin 16) 5 * Equiv.swap (5 : Fin 16) 6 * Equiv.swap (6 : Fin 16) 14 * Equiv.swap (7 : Fin 16) 15 * Equiv.swap (9 : Fin 16) 12 * Equiv.swap (10 : Fin 16) 11

theorem factorization : matrix.submatrix perm id=lower*upper := by decide +kernel
theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem perm_sign : Equiv.Perm.sign perm=1 := by decide +kernel
theorem determinant : matrix.det=-28 := by
  have hd : (matrix.submatrix perm id).det=-28 := by
    rw [factorization,Matrix.det_mul,
      Matrix.det_of_lowerTriangular lower lower_triangular,
      Matrix.det_of_upperTriangular upper_triangular]
    norm_num [lower,upper,Fin.prod_univ_succ]
  have h := Matrix.det_permute perm matrix
  rw [perm_sign] at h
  norm_num at h
  linarith
theorem determinant_nonzero : matrix.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.OrderSevenDeterminant60
