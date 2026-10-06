import MainTheory.PairEmbeddedAction

set_option autoImplicit false

namespace MainTheory.PairMarginalCovariance

open MainTheory.PairPartialTrace SixQubit.Orbit7DirectMarginal

theorem covariance (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5) (A : Matrix Pair Pair ℂ) :
    directPairMarginal (fun k => (embed s A).mulVec (code k)) s=
      A*directPairMarginal code s*A.conjTranspose := by
  ext p q
  simp only [directPairMarginal,directPurePairMarginal,
    MainTheory.PairEmbeddedAction.action_assembled,Matrix.mul_apply,
    Matrix.conjTranspose_apply,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext a
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end MainTheory.PairMarginalCovariance
