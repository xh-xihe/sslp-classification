import MainTheory.Orbit12Frames
import MainTheory.Orbit12MomentDisplays
import MainTheory.Orbit6LineCompletion
set_option autoImplicit false
namespace MainTheory.Orbit12AnchorLines
open scoped Matrix
open SixQubit.Orbit12 MainTheory.Orbit12Frames MainTheory.Orbit12MomentDisplays
open MainTheory.Orbit6SpinorDisplays MainTheory.Orbit6LineCompletion
noncomputable section

theorem wedge_of_cross_zero (u v U V : Fin 2 → ℂ)
    (h : Matrix.vecMulVec U (star u)+Matrix.vecMulVec V (star v)=0)
    (hU : U≠0) : wedge u v=0 := by
  have hj : ∃ j : Fin 2,U j≠0 := by
    by_contra hn
    push_neg at hn
    apply hU
    funext j
    exact hn j
  obtain ⟨j,hj⟩ := hj
  have h0 := congrFun (congrFun h j) 0
  have h1 := congrFun (congrFun h j) 1
  change U j*star (u 0)+V j*star (v 0)=0 at h0
  change U j*star (u 1)+V j*star (v 1)=0 at h1
  have hw : (star (u 0)*star (v 1)-star (u 1)*star (v 0))*U j=0 := by
    linear_combination star (v 1)*h0-star (v 0)*h1
  have hs := (mul_eq_zero.mp hw).resolve_right hj
  have hh := congrArg star hs
  simp only [star_sub,star_mul',star_star,star_zero] at hh
  unfold wedge
  linear_combination hh

theorem actual_anchor_lines (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∃ t : ℂ,v c=t • u c) ∧ (∃ t : ℂ,vt d=t • ut d) := by
  have hm := physical_moments c d hc hd hnc hnd hkl
  have hu := bottom_zero_anchor _ _ hm
  have hU := top_zero_anchor _ _ hm
  have hun : u c≠0 := by
    intro hz
    have hz0 := congrFun hz 0
    have hz1 := congrFun hz 1
    change c y0=0 at hz0
    change c y8=0 at hz1
    change Complex.normSq (c y0)+Complex.normSq (c y8)=1/4 at hu
    norm_num [hz0,hz1] at hu
  have hUn : ut d≠0 := by
    intro hz
    have hz0 := congrFun hz 0
    have hz1 := congrFun hz 1
    change d z0=0 at hz0
    change d z8=0 at hz1
    change Complex.normSq (d z0)+Complex.normSq (d z8)=1/4 at hU
    norm_num [hz0,hz1] at hU
  have hx := (physical_blocks c d hc hd hnc hnd hkl).1
  change Matrix.vecMulVec (ut d) (star (u c))+Matrix.vecMulVec (vt d) (star (v c))=0 at hx
  have hw := wedge_of_cross_zero _ _ _ _ hx hUn
  have hxc : Matrix.vecMulVec (u c) (star (ut d))+
      Matrix.vecMulVec (v c) (star (vt d))=0 := by
    have hh := congrArg Matrix.conjTranspose hx
    simpa only [Matrix.conjTranspose_add,Matrix.conjTranspose_vecMulVec,
      star_star,Matrix.conjTranspose_zero] using hh
  have hW := wedge_of_cross_zero _ _ _ _ hxc hun
  exact ⟨wedge_zero_scalar _ _ hun hw,wedge_zero_scalar _ _ hUn hW⟩

end
end MainTheory.Orbit12AnchorLines
