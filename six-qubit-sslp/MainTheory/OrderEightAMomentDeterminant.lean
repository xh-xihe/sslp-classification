import MainTheory.OrderEightSupportDisplays
import MainTheory.MomentMatrix23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderEightAMomentDeterminant

open MainTheory.OrderEightSupportDisplays

def leftWords : Fin 7 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (bottomA i)).toFin
def rightWords : Fin 7 → MainTheory.FinitePipeline.Word6 :=
  fun i => (BitVec.ofFnLE (topA i)).toFin

def column (j : Fin 14) : Sum (Fin 7) (Fin 7) :=
  if h : j.val+0 < 7 then Sum.inl ⟨j.val+0,h⟩
  else Sum.inr ⟨j.val+0-7,by omega⟩

def matrix : Matrix (Fin 14) (Fin 14) ℚ := fun i j =>
  MainTheory.MomentMatrix23.matrixQ leftWords rightWords (i.castLE (by decide)) (column j)

def lower : Matrix (Fin 14) (Fin 14) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, (-1/2), (-3/2), 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, -1, 1, 0, (-1/4), (-3/8), 1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, (-1/4), (-3/8), 0, 1, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, (-1/4), (-3/8), 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, (-1/2), (-3/2), (3/4), (-3/8), 1, 1, 1, 1, 0, 0;
    0, 1, 0, 0, 0, 1, (-1/4), (-3/8), 0, 0, 0, 0, 1, 0;
    0, 1, 0, 1, 0, 1, (-1/4), (-3/8), 0, 0, 1, 0, 1, 1]

def upper : Matrix (Fin 14) (Fin 14) ℚ := !![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 1, 1, 0, -1, 0, 0, 0, 0, 0, -1;
    0, 0, -1, 0, -1, 0, 1, 0, 0, -1, 0, -1, 0, 1;
    0, 0, 0, -1, -1, 0, 1, 0, 0, 0, -1, -1, 0, 1;
    0, 0, 0, 0, -2, 1, 3, -1, -1, -1, -1, -3, 0, 2;
    0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, 1;
    0, 0, 0, 0, 0, 0, 4, (-3/2), (-3/2), (-3/2), (-3/2), (-3/2), (-3/2), (5/2);
    0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, -2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]

def perm : Equiv.Perm (Fin 14) := Equiv.swap (1 : Fin 14) 2 * Equiv.swap (2 : Fin 14) 5 * Equiv.swap (3 : Fin 14) 4 * Equiv.swap (4 : Fin 14) 6 * Equiv.swap (5 : Fin 14) 6 * Equiv.swap (6 : Fin 14) 7 * Equiv.swap (8 : Fin 14) 11 * Equiv.swap (9 : Fin 14) 10 * Equiv.swap (11 : Fin 14) 12

theorem factorization : matrix.submatrix perm id=lower*upper := by decide +kernel

theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem perm_sign : Equiv.Perm.sign perm=-1 := by decide +kernel

theorem determinant : matrix.det=-48 := by
  have hd : (matrix.submatrix perm id).det=48 := by
    rw [factorization,Matrix.det_mul,
      Matrix.det_of_lowerTriangular lower lower_triangular,
      Matrix.det_of_upperTriangular upper_triangular]
    norm_num [lower,upper,Fin.prod_univ_succ]
  have h := Matrix.det_permute perm matrix
  rw [perm_sign] at h
  norm_num at h
  linarith

theorem determinant_nonzero : matrix.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.OrderEightAMomentDeterminant
