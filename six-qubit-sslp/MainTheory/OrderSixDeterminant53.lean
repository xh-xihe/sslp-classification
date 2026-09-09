import MainTheory.OrderSixSupportDisplays
import MainTheory.MomentMatrix23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderSixDeterminant53
open MainTheory.OrderSixSupportDisplays

def leftWords : Fin 10 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (bottom53 i)).toFin
def rightWords : Fin 10 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (top53 i)).toFin

def row : Fin 17 → Fin 23 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,17,21]
def fullColumn : Fin 17 → Fin 20 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
def column (j : Fin 17) : Sum (Fin 10) (Fin 10) :=
  if h : (fullColumn j).val < 10 then Sum.inl ⟨(fullColumn j).val,h⟩
  else Sum.inr ⟨(fullColumn j).val-10,by have h' := (fullColumn j).isLt; omega⟩

def matrix : Matrix (Fin 17) (Fin 17) ℚ := fun i j =>
  MainTheory.MomentMatrix23.matrixQ leftWords rightWords (row i) (column j)
def lower : Matrix (Fin 17) (Fin 17) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, (-1/2), (1/2), (1/2), (-1/3), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, (-1/2), (1/2), (1/2), (-1/3), 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, (-1/2), (1/2), (1/2), (-1/3), 0, -1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, (1/2), (1/2), (1/2), (-1/3), 1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, -1, (2/3), 0, 0, 0, (-1/3), 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, (1/2), (1/4), 1, (-1/4), 1, 0, 0, 0;
    0, 1, 0, 0, 1, 0, (-1/3), 0, 0, 0, (-1/3), 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 1, (-1/3), 0, 0, 0, (-1/3), 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 1, 1, (-1/3), 0, 0, 0, (-1/3), 0, 0, 0, 1, 1, 1]
def upper : Matrix (Fin 17) (Fin 17) ℚ := !![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 1, 0, 1, 1, 0, -1, 0, 0, -1, 0, 0, -1;
    0, 0, -1, 1, -1, -1, 0, 0, 0, 1, 0, 0, -1, 1, -1, -1, 0;
    0, 0, 0, 2, -1, -1, 0, 1, 1, 2, -1, -1, -1, 1, -2, -2, -1;
    0, 0, 0, 0, -1, 0, 1, -1, 0, 1, 0, 0, 0, 0, -1, 0, 1;
    0, 0, 0, 0, 0, -1, 1, 0, -1, 1, 0, 0, 0, 0, 0, -1, 1;
    0, 0, 0, 0, 0, 0, 3, 0, 0, 3, -1, -1, -1, -1, -1, -1, 2;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, (-5/6), (-5/6), (1/6), (1/6), (1/6), (1/6), (-5/6);
    0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2, (-5/6), (-5/6), (1/6), (1/6), (-5/6), (-5/6), (7/6);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/4);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]
def perm : Equiv.Perm (Fin 17) := Equiv.swap (1 : Fin 17) 2 * Equiv.swap (2 : Fin 17) 5 * Equiv.swap (3 : Fin 17) 6 * Equiv.swap (5 : Fin 17) 6 * Equiv.swap (6 : Fin 17) 7 * Equiv.swap (7 : Fin 17) 10 * Equiv.swap (8 : Fin 17) 14 * Equiv.swap (9 : Fin 17) 15 * Equiv.swap (13 : Fin 17) 16 * Equiv.swap (14 : Fin 17) 15

theorem factorization : matrix.submatrix perm id=lower*upper := by decide +kernel
theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem perm_sign : Equiv.Perm.sign perm=1 := by decide +kernel
theorem determinant : matrix.det=24 := by
  have hd : (matrix.submatrix perm id).det=24 := by
    rw [factorization,Matrix.det_mul,
      Matrix.det_of_lowerTriangular lower lower_triangular,
      Matrix.det_of_upperTriangular upper_triangular]
    norm_num [lower,upper,Fin.prod_univ_succ]
  have h := Matrix.det_permute perm matrix
  rw [perm_sign] at h
  norm_num at h
  linarith
theorem determinant_nonzero : matrix.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.OrderSixDeterminant53
