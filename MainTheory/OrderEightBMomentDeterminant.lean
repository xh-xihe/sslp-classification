import MainTheory.OrderEightSupportDisplays
import MainTheory.MomentMatrix23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderEightBMomentDeterminant

open MainTheory.OrderEightSupportDisplays

def leftWords : Fin 8 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (bottomB i)).toFin
def rightWords : Fin 8 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (topB i)).toFin

def column (j : Fin 15) : Sum (Fin 8) (Fin 8) :=
  if h : j.val+1 < 8 then Sum.inl ⟨j.val+1,h⟩
  else Sum.inr ⟨j.val+1-8,by omega⟩

def matrix : Matrix (Fin 15) (Fin 15) ℚ := fun i j =>
  MainTheory.MomentMatrix23.matrixQ leftWords rightWords (i.castLE (by decide)) (column j)

def lower : Matrix (Fin 15) (Fin 15) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, -1, 0, (1/2), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, -1, (-4/5), 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 0, (1/2), (3/5), (-1/8), (-5/8), 1, 0, 0, 0, 0, 0, 0;
    1, 1, 1, 1, 0, (-2/5), (-1/8), (-5/8), 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, -1, -1, (-2/5), (1/2), (-1/2), 1, -1, 1, 0, 0, 0, 0;
    1, 1, 1, 0, 0, (-2/5), (-1/8), (-5/8), 0, 1, 0, 1, 0, 0, 0;
    1, 1, 0, 1, 1, (2/5), (-1/2), (-1/2), 0, 0, 0, -1, 1, 0, 0;
    1, 0, 1, 1, (1/2), (1/5), (-1/4), (-1/4), 0, 0, 0, -1, 1, 1, 0;
    1, 1, 1, 1, (1/2), (-1/5), (1/4), (5/4), -1, 1, (-1/2), 0, (-1/4), (-3/4), 1]

def upper : Matrix (Fin 15) (Fin 15) ℚ := !![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, -1;
    0, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0, -1, -1, 0;
    0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0;
    0, 0, 0, 0, -2, 1, 1, 0, 0, 0, 0, 0, -2, 1, 1;
    0, 0, 0, 0, 0, (-5/2), (-1/2), -3, -1, -1, -1, -1, -1, (-7/2), (-3/2);
    0, 0, 0, 0, 0, 0, (8/5), (-17/5), (-9/5), (-9/5), (-9/5), (-9/5), (-9/5), (-9/5), (-1/5);
    0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]

def perm : Equiv.Perm (Fin 15) := Equiv.swap (1 : Fin 15) 2 * Equiv.swap (2 : Fin 15) 3 * Equiv.swap (3 : Fin 15) 4 * Equiv.swap (4 : Fin 15) 5 * Equiv.swap (5 : Fin 15) 6 * Equiv.swap (6 : Fin 15) 7 * Equiv.swap (8 : Fin 15) 11 * Equiv.swap (10 : Fin 15) 12

theorem factorization : matrix.submatrix perm id=lower*upper := by decide +kernel

theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem perm_sign : Equiv.Perm.sign perm=1 := by decide +kernel

theorem determinant : matrix.det=32 := by
  have hd : (matrix.submatrix perm id).det=32 := by
    rw [factorization,Matrix.det_mul,
      Matrix.det_of_lowerTriangular lower lower_triangular,
      Matrix.det_of_upperTriangular upper_triangular]
    norm_num [lower,upper,Fin.prod_univ_succ]
  have h := Matrix.det_permute perm matrix
  rw [perm_sign] at h
  norm_num at h
  linarith

theorem determinant_nonzero : matrix.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.OrderEightBMomentDeterminant
