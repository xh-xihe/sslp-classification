import MainTheory.OrderNineMomentUniqueness

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderNineMomentDeterminant

open MainTheory.OrderNineMomentUniqueness

def column (j : Fin 14) : Sum (Fin 7) (Fin 7) :=
  if h : j.val < 7 then Sum.inl ⟨j.val,h⟩ else Sum.inr ⟨j.val-7,by omega⟩

def matrix : Matrix (Fin 14) (Fin 14) ℚ := fun i j =>
  Sum.elim (leftRows i) (rightRows i) (column j)

def lower : Matrix (Fin 14) (Fin 14) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, (-2/3), 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, -1, 1, 1, (-1/3), (-5/9), 1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, (-1/3), (-5/9), 0, 1, 0, 0, 0, 0;
    0, 1, 0, 1, 1, 0, (-1/3), (-5/9), 0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 0, (-1/3), (-5/9), 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, -1, (-2/3), (2/3), (-5/9), 1, 1, 1, 3, 1, 0;
    0, 1, 0, 1, 1, (1/3), (-1/3), (-2/9), 0, 0, 0, -1, (-2/5), 1]

def upper : Matrix (Fin 14) (Fin 14) ℚ := !![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 1, 1, 0, -1, 0, 0, 0, 0, 0, -1;
    0, 0, -1, 0, -1, -1, 1, 0, 0, -1, 0, -1, -1, 1;
    0, 0, 0, -1, 0, -1, 1, 0, 0, 0, -1, 0, -1, 1;
    0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, 1, 0;
    0, 0, 0, 0, 0, -3, 3, -1, -1, -1, -1, -1, -4, 2;
    0, 0, 0, 0, 0, 0, 3, (-5/3), (-5/3), (-5/3), (-5/3), (-5/3), (-5/3), (4/3);
    0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, -2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-4/5)]

def perm : Equiv.Perm (Fin 14) := Equiv.swap (1 : Fin 14) 2 * Equiv.swap (2 : Fin 14) 5 * Equiv.swap (5 : Fin 14) 6 * Equiv.swap (6 : Fin 14) 7 * Equiv.swap (8 : Fin 14) 11 * Equiv.swap (9 : Fin 14) 10

theorem actual_rows (i j : Fin 14) : matrix i j=
    MainTheory.MomentMatrix23.matrixQ
      MainTheory.OrderNineMomentStatistics.leftWords MainTheory.OrderNineMomentStatistics.rightWords
      (i.castLE (by decide)) (column j) := by
  rw [checked_rows]
  rfl

theorem factorization : matrix.submatrix perm id=lower*upper := by decide +kernel

theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem perm_sign : Equiv.Perm.sign perm=1 := by decide +kernel

theorem determinant : matrix.det= -36 := by
  have h := Matrix.det_permute perm matrix
  rw [perm_sign] at h
  norm_num at h
  rw [← h,factorization,Matrix.det_mul,
    Matrix.det_of_lowerTriangular lower lower_triangular,
    Matrix.det_of_upperTriangular upper_triangular]
  norm_num [lower,upper,Fin.prod_univ_succ]

theorem determinant_nonzero : matrix.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.OrderNineMomentDeterminant
