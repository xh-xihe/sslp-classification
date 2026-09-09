import MainTheory.Orbit8PhaseNormalization
import MainTheory.PauliFamilyTrace

set_option autoImplicit false

namespace MainTheory.Orbit8ProjectorNormalization

open MainTheory.PairPartialTrace MainTheory.Orbit8PhaseNormalization
open SixQubit.Orbit8Universal

theorem rephase_kernel (c d : SS.State 6 ℂ) (z : ℂ) (hz : star z*z=1) :
    familyKernel ![z • c,d]=familyKernel ![c,d] := by
  ext x y
  simp only [familyKernel,Fin.sum_univ_two]
  change (z*c x)*star (z*c y)+d x*star (d y)=c x*star (c y)+d x*star (d y)
  rw [star_mul]
  linear_combination (c x*star (c y))*hz

theorem normalized_kernel (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    familyKernel ![phase c • c,d]=familyKernel ![c,d] :=
  rephase_kernel c d (phase c)
    (phase_unit c (rigid_coordinate_norms c d hc hd hnc hnd hcode).1)

end MainTheory.Orbit8ProjectorNormalization
