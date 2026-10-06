import MainTheory.Orbit26MatchingPhysical
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26MatchingNotation
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors MainTheory.Orbit26NormalizedRows
open MainTheory.Orbit26MatchingPhysical MainTheory.Orbit26NonmatchingPhysical
open MainTheory.Orbit26PhysicalMatrices
open MainTheory.Orbit26 (M2)
open SixQubit.Orbit26 (S0 S1)
noncomputable section
def kappa (v w : Vec) : ℝ := ‖star v ⬝ᵥ w‖
theorem kappa_sq (v w : Vec) : kappa v w^2=Complex.normSq (star v ⬝ᵥ w) := by
  exact (Complex.normSq_eq_norm_sq _).symm
theorem kappa_bounds (v w : Vec) (hv : nsq v=1) (hw : nsq w=1) :
    0≤kappa v w ∧ kappa v w≤1 := by
  have huv : Complex.normSq (v 0)+Complex.normSq (v 1)=1 := by
    simpa [nsq,Fin.sum_univ_two] using hv
  have hs := SixQubit.Block26.cauchy_schwarz_unit (v 0) (v 1) (w 0) (w 1) huv
  have huw : Complex.normSq (w 0)+Complex.normSq (w 1)=1 := by
    simpa [nsq,Fin.sum_univ_two] using hw
  rw [huw] at hs
  have hb : kappa v w^2≤1 := by
    simpa [kappa_sq,SixQubit.Block26.ip,dotProduct,Fin.sum_univ_two,Pi.star_apply] using hs
  refine ⟨norm_nonneg _,?_⟩
  nlinarith [norm_nonneg (star v ⬝ᵥ w)]
theorem complementary_projector_sum (P Q : M2) (h : P+Q=1) :
    (1-P)+(1-Q)=P+Q := by
  rw [← h]
  abel
theorem physical_kappa_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) :
    kappa (unitAnchor (C c 3)) (unitAnchor (D d 3))=0 := by
  rw [kappa,physical_anchor_orthogonal c d hc hd hnc hnd hkl lam mu hC hD,norm_zero]
end
end MainTheory.Orbit26MatchingNotation
