import MainTheory.Orbit8EnumeratorDisplays

set_option autoImplicit false

namespace MainTheory.Orbit8FamilyDisplays

open MainTheory.Orbit8EnumeratorDisplays SixQubit.Orbit8Universal

theorem family_vectors (psi : Fin 2 → SS.State 6 ℂ) (alpha : ℝ)
    (hA : SixQubit.Orbit8Family.IsFamilyA psi alpha)
    (hB : SixQubit.Orbit8Family.IsFamilyB psi alpha) :
    (fun j : Fin 7 => normalizedA psi j)=![1,alpha,1-alpha,0,11+4*alpha,16-alpha,3-3*alpha] ∧
    (fun j : Fin 7 => normalizedB psi j)=![1,alpha,1-alpha,24+6*alpha,35+10*alpha,40-7*alpha,27-9*alpha] := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hA
  obtain ⟨b0,b1,b2,b3,b4,b5,b6⟩ := hB
  constructor
  · funext j
    fin_cases j <;> norm_num [normalizedA,a0,a1,a2,a3,a4,a5,a6]
  · funext j
    fin_cases j <;> norm_num [normalizedB,b0,b1,b2,b3,b4,b5,b6]

theorem alpha_range (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (1/2 : ℝ)=36*(1/6)^2/2 ∧
    36*(1/6)^2/2 ≤ normalizedA ![c,d] 1 ∧
    normalizedA ![c,d] 1 ≤ 36*(1/6)^2 ∧ 36*(1/6)^2=(1 : ℝ) := by
  have h := lineAlpha_bounds c d hc hd hnc hnd hcode
  change (1/2 : ℝ) ≤ normalizedA ![c,d] 1 ∧ normalizedA ![c,d] 1 ≤ 1 at h
  norm_num
  exact h

theorem universal_vectors (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (fun j : Fin 7 => normalizedA ![c,d] j)=
      ![1,normalizedA ![c,d] 1,1-normalizedA ![c,d] 1,0,
        11+4*normalizedA ![c,d] 1,16-normalizedA ![c,d] 1,3-3*normalizedA ![c,d] 1] :=
  (family_vectors _ _ (universal_family_A c d hc hd hnc hnd hcode)
    (universal_family_B c d hc hd hnc hnd hcode)).1

theorem endpoint (psi : Fin 2 → SS.State 6 ℂ)
    (hA : SixQubit.Orbit8Family.IsFamilyA psi 1)
    (hB : SixQubit.Orbit8Family.IsFamilyB psi 1) :
    (fun j : Fin 7 => normalizedA psi j)=![1,1,0,0,15,15,0] := by
  have h := (family_vectors psi 1 hA hB).1
  norm_num at h
  exact h

end MainTheory.Orbit8FamilyDisplays
