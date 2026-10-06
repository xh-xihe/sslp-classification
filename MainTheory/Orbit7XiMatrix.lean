import MainTheory.Orbit7JacobianKernel

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit7XiMatrix

noncomputable def coefficients (omega : ℂ) : Matrix (Fin 5) (Fin 6) ℂ :=
  !![0,0,0,-1,omega + 1,-omega;
    0,-1,-omega,0,0,omega + 1;
    -1,0,omega + 1,0,-omega,0;
    -omega,omega + 1,0,-1,0,0;
    omega + 1,-omega,-1,-1,-omega,omega + 1]

noncomputable def rightInverse (omega : ℂ) : Matrix (Fin 6) (Fin 5) ℂ :=
  !![-omega/2 - 1/2,omega/2,-1/2,omega/2 + 1/2,0;
    -omega/6 - 1/3,omega/3 - 1/3,-omega/6 - 1/3,1/6 - omega/6,omega/3 + 1/6;
    -omega/3 - 1/6,2*omega/3 + 1/3,-omega/3 - 1/6,omega/6 + 1/3,omega/6 - 1/6;
    -omega/3 - 2/3,omega/6 - 1/6,omega/6 - 1/6,omega/6 - 1/6,omega/6 - 1/6;
    -2*omega/3 - 1/3,omega/3 + 1/6,omega/3 + 1/6,omega/3 + 1/6,omega/3 + 1/6;
    0,0,0,0,0]

noncomputable def rightError (_omega : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![-2/3,1/3,1/3,1/3,1/3;
    1/3,-2/3,1/3,-1/6,-1/6;
    1/3,1/3,-2/3,-1/6,-1/6;
    1/3,-1/6,-1/6,-2/3,1/3;
    1/3,-1/6,-1/6,1/3,-2/3]

noncomputable def kernelProjector (_omega : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,0,0,0,0,-1;
    0,1,0,0,0,-1;
    0,0,1,0,0,-1;
    0,0,0,1,0,-1;
    0,0,0,0,1,-1;
    0,0,0,0,0,0]

noncomputable def kernelError (_omega : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![-1/2,1/2,-1/2,0,-1/2,1;
    1/2,-1/2,-1/2,0,-1/3,5/6;
    0,0,-1,0,-1/6,7/6;
    0,0,0,0,-2/3,2/3;
    0,0,0,0,-4/3,4/3;
    0,0,0,0,0,0]

theorem right_inverse (omega : ℂ) (hw : 1+omega+omega^2=0) :
    coefficients omega * rightInverse omega = 1 := by
  have he : coefficients omega * rightInverse omega - 1 = (1+omega+omega^2) • rightError omega := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coefficients,rightInverse,rightError] <;> ring
  rw [hw,zero_smul] at he
  exact sub_eq_zero.mp he

theorem kernel_projector (omega : ℂ) (hw : 1+omega+omega^2=0) :
    rightInverse omega * coefficients omega = kernelProjector omega := by
  have he : rightInverse omega * coefficients omega - kernelProjector omega = (1+omega+omega^2) • kernelError omega := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coefficients,rightInverse,kernelProjector,kernelError] <;> ring
  rw [hw,zero_smul] at he
  exact sub_eq_zero.mp he

theorem rank_five (omega : ℂ) (hw : 1+omega+omega^2=0) :
    (coefficients omega).rank=5 := by
  have h := Matrix.rank_mul_le_left (coefficients omega) (rightInverse omega)
  rw [right_inverse omega hw,Matrix.rank_one] at h
  exact Nat.le_antisymm (Matrix.rank_le_card_height _) h

theorem kernel_iff (omega : ℂ) (hw : 1+omega+omega^2=0) (v : Fin 6 → ℂ) :
    (coefficients omega).mulVec v=0 ↔ ∃ t : ℂ, v=fun _ => t := by
  constructor
  · intro h
    have hh := congrArg (fun z => (rightInverse omega).mulVec z) h
    change (rightInverse omega).mulVec ((coefficients omega).mulVec v) = (rightInverse omega).mulVec 0 at hh
    rw [Matrix.mulVec_mulVec,kernel_projector omega hw,Matrix.mulVec_zero] at hh
    refine ⟨v 5,?_⟩
    funext i
    have hi := congrFun hh i
    fin_cases i <;> simp [kernelProjector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hi ⊢
    all_goals linear_combination hi
  · rintro ⟨t,rfl⟩
    funext i
    fin_cases i <;> simp [coefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

end MainTheory.Orbit7XiMatrix
