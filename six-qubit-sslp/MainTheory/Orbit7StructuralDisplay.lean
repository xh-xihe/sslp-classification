import SixQubit.Orbit7UniversalFinal
import MainTheory.Orbit7MatrixDisplays

set_option autoImplicit false

namespace MainTheory.Orbit7StructuralDisplay

open SixQubit.Orbit7Universal SixQubit.Orbit7DirectMarginal
open MainTheory.Orbit7MatrixDisplays

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
  (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem collinear_target (hcol : extremeDet c d=0) : TargetStar c d := by
  have h := collinear_pair_blocks_normal_form c d hc hd hnc hnd hcode hcol 0
  refine ⟨0,?_,?_⟩
  · intro i j
    have hh := congrFun (congrFun h.1 i) j
    change U c i j+starA c 0 i j=3*U c i j at hh
    linear_combination hh
  · intro i j
    have hh := congrFun (congrFun h.2 i) j
    change W d i j+starB d 0 i j=3*W d i j at hh
    linear_combination hh

theorem universal_target : TargetStar c d := by
  rcases boundary_reduction c d hc hd hnc hnd hcode with ht | hf
  · exact ht
  · by_cases hcol : extremeDet c d=0
    · exact collinear_target c d hc hd hnc hnd hcode hcol
    · exact full_support_independent_target c d hc hd hnc hnd hcode hf hcol

theorem direct_structure : ∃ s : Fin 5,
    directPairMarginal ![c,d] s = Matrix.blockDiagonal ![(1/2 : ℂ) • Pu c,(1/2 : ℂ) • Pv d] := by
  obtain ⟨s,hA,hB⟩ := universal_target c d hc hd hnc hnd hcode
  refine ⟨s,?_⟩
  rw [direct_uniform_eq_pairMarginal c d hc hd hcode s]
  exact target_pair_blocks c d s hA hB

end MainTheory.Orbit7StructuralDisplay
