import MainTheory.OrderSixSupportDisplays
import MainTheory.MomentMatrix23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderSixDeterminant55
open MainTheory.OrderSixSupportDisplays

def leftWords : Fin 11 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (bottom55 i)).toFin
def rightWords : Fin 11 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (top55 i)).toFin

def row : Fin 18 → Fin 23 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18]
def fullColumn : Fin 18 → Fin 22 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18]
def column (j : Fin 18) : Sum (Fin 11) (Fin 11) :=
  if h : (fullColumn j).val < 11 then Sum.inl ⟨(fullColumn j).val,h⟩
  else Sum.inr ⟨(fullColumn j).val-11,by have h' := (fullColumn j).isLt; omega⟩

def matrix : Matrix (Fin 18) (Fin 18) ℚ := fun i j =>
  MainTheory.MomentMatrix23.matrixQ leftWords rightWords (row i) (column j)
def lower : Matrix (Fin 18) (Fin 18) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, (-1/2), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, -1, 0, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, -1, 0, -1, -2, (2/3), 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, -1, (-1/2), 1, -1, (2/3), -1, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 1, (1/2), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, (-1/3), 0, 1, 0, -1, 1, 0, 0, 0, 0, 0;
    0, 1, 1, -1, (-1/2), 0, 0, 0, 0, 0, 0, 1, (-1/2), 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 1, 0, 0, 0;
    0, 0, -1, 2, (1/2), 0, 1, (-2/3), 1, 0, 0, (-4/3), (7/6), -1, (1/6), 1, 0, 0;
    0, 1, 1, -1, (-1/2), 0, -1, (1/3), 0, 1, 1, -3, (3/2), -1, 1, 0, 1, 0;
    0, 0, 0, 1, (1/2), 0, 0, 0, 0, 0, 0, 1, 0, 1, (-1/2), 0, (-3/4), 1]
def upper : Matrix (Fin 18) (Fin 18) ℚ := !![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, -1, 0, 0, -1, 0, 0, -1;
    0, 0, -1, 1, -1, 1, 0, 0, 0, -1, 1, 0, 0, -1, 1, -1, 0, 0;
    0, 0, 0, 1, -1, 0, -1, 1, 0, 0, 1, 0, 0, 0, 1, -1, -1, 1;
    0, 0, 0, 0, 2, 2, 2, -2, 0, 0, 0, -1, -1, -1, -1, 1, 1, -3;
    0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, (-1/2), (-1/2), (-1/2), (1/2), (1/2), (1/2), (-1/2);
    0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, -2, -2, -2, -2, -2, -2, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, (-3/2), (-3/2), (-1/2), (-1/2), (-1/2), (1/2), (1/2);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-7/6), (-7/6), (-1/6), (-1/6), (-1/6), (5/6), (-1/6);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-7/6), (-7/6), (-1/6), (-1/6), (-1/6), (5/6), (-1/6);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), (1/2), (-1/2), (1/2), (-1/2), (1/2), (-1/2);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, (-3/2), 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-3/2), -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/4)]
def perm : Equiv.Perm (Fin 18) := Equiv.swap (1 : Fin 18) 2 * Equiv.swap (2 : Fin 18) 3 * Equiv.swap (3 : Fin 18) 4 * Equiv.swap (4 : Fin 18) 6 * Equiv.swap (5 : Fin 18) 9 * Equiv.swap (6 : Fin 18) 7 * Equiv.swap (7 : Fin 18) 9 * Equiv.swap (8 : Fin 18) 13 * Equiv.swap (9 : Fin 18) 10 * Equiv.swap (10 : Fin 18) 14 * Equiv.swap (15 : Fin 18) 17

theorem factorization : matrix.submatrix perm id=lower*upper := by decide +kernel
theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem perm_sign : Equiv.Perm.sign perm=-1 := by decide +kernel
theorem determinant : matrix.det=-36 := by
  have hd : (matrix.submatrix perm id).det=36 := by
    rw [factorization,Matrix.det_mul,
      Matrix.det_of_lowerTriangular lower lower_triangular,
      Matrix.det_of_upperTriangular upper_triangular]
    norm_num [lower,upper,Fin.prod_univ_succ]
  have h := Matrix.det_permute perm matrix
  rw [perm_sign] at h
  norm_num at h
  linarith
theorem determinant_nonzero : matrix.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.OrderSixDeterminant55
