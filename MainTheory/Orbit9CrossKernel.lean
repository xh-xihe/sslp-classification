import MainTheory.Orbit9SmallMatrixDisplays
import SixQubit.Orbit9Cross

set_option autoImplicit false

namespace MainTheory.Orbit9CrossKernel

open MainTheory.Orbit9SmallMatrixDisplays

theorem constants (A B C t : ℂ) (hsum : A+B+C=0) :
    (cross A B C).mulVec (fun _ => t)=0 := by
  funext i
  fin_cases i <;> simp [cross,Matrix.mulVec,Fin.sum_univ_succ,dotProduct] <;>
    linear_combination t*hsum

theorem kernel_iff_constant (A B C : ℂ) (hsum : A+B+C=0)
    (hsq : A^2+B^2+C^2=0) (hC : C ≠ 0) (z : Fin 4 → ℂ) :
    (cross A B C).mulVec z=0 ↔ ∃ t, z=fun _ => t := by
  constructor
  · intro hz
    have e0 := congrFun hz 0
    have e1 := congrFun hz 1
    have e2 := congrFun hz 2
    simp [cross,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at e0 e1 e2
    let t := (z 0+z 1+z 2+z 3)/4
    obtain ⟨h0,h1,h2,h3⟩ := SixQubit.Orbit9Cross.cross_edges_zero A B C
      (z 0-t) (z 1-t) (z 2-t) (z 3-t) hsum hsq hC
      (by linear_combination e0-t*hsum)
      (by linear_combination e1-t*hsum)
      (by linear_combination e2-t*hsum)
      (by dsimp [t]; ring)
    refine ⟨t,?_⟩
    funext i
    fin_cases i
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h2
    · exact sub_eq_zero.mp h3
  · rintro ⟨t,rfl⟩
    exact constants A B C t hsum

end MainTheory.Orbit9CrossKernel
