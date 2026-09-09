import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MainTheory.TriangleIncidenceFive

def edges : Fin 10 → Finset (Fin 5) := ![{0,2}, {0,1}, {0,3}, {0,4}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4}]
def triangles : Fin 10 → Finset (Fin 5) := ![{0,1,2}, {0,1,3}, {0,1,4}, {0,2,3}, {0,3,4}, {0,2,4}, {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}]
def incidence : Matrix (Fin 10) (Fin 10) ℚ := fun i j => if edges j ⊆ triangles i then 1 else 0
def lower : Matrix (Fin 10) (Fin 10) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    1, -1, -2, 1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 1, 1, 0, 0, 0, 0, 0;
    1, -1, -1, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, (-1/2), -1, 1]
def upper : Matrix (Fin 10) (Fin 10) ℚ := !![1, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, -1, 1, 0, -1, 1, 0, 0, 0;
    0, 0, 0, 2, -1, -1, 2, 1, 0, 0;
    0, 0, 0, 0, 1, 0, -1, -1, 0, 1;
    0, 0, 0, 0, 0, 1, -1, -1, 1, 0;
    0, 0, 0, 0, 0, 0, 2, 3, -1, -1;
    0, 0, 0, 0, 0, 0, 0, -2, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -2, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 3]

theorem edge_enumeration : Function.Injective edges ∧
    ∀ e : Finset (Fin 5),e.card=2 ↔ ∃ i,edges i=e := by decide +kernel

theorem triangle_enumeration : Function.Injective triangles ∧
    ∀ t : Finset (Fin 5),t.card=3 ↔ ∃ i,triangles i=t := by decide +kernel

theorem factorization : incidence=lower*upper := by decide +kernel

theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem determinant : incidence.det= -48 := by
  rw [factorization,Matrix.det_mul,Matrix.det_of_lowerTriangular lower lower_triangular,
    Matrix.det_of_upperTriangular upper_triangular]
  norm_num [lower,upper,Fin.prod_univ_succ]

theorem determinant_nonzero : incidence.det ≠ 0 := by rw [determinant]; norm_num

end MainTheory.TriangleIncidenceFive
