import Mathlib

import SixQubit.Orbit45AttainRows

/-!
# Orbit 45: exact interval attainment

This file closes the constructive direction.  It uses the explicit twenty
amplitudes from `Orbit45Attain`, not an existential orthogonal completion.
The two parameter charts below cover `[2/3,3/4]` and `[3/4,1]`.
-/

namespace SixQubit.Orbit45Attain

open scoped BigOperators ComplexConjugate
open SixQubit.Realize
open SixQubit.Orbit45Support
open SixQubit.Orbit45Universal
open SixQubit.Orbit45Family

noncomputable section

/-- The enumerator coordinate carried by a direct-family parameter tuple. -/
def directParameter (a1 a2 a3 : ℝ) : ℝ :=
  32 * (a1^4 + a2^4 + a3^4)

/-- Every algebraically admissible direct tuple has exactly the asserted
full A/B enumerator image. -/
theorem direct_families
    (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ)
    (hp : Params a1 a2 a3 q u1 v1 u2 v2 u3 v3) :
    IsFamilyA (code a1 a2 a3 q u1 v1 u2 v2 u3 v3)
        (directParameter a1 a2 a3) ∧
      IsFamilyB (code a1 a2 a3 q u1 v1 u2 v2 u3 v3)
        (directParameter a1 a2 a3) := by
  let c := cword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  let d := dword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  have hc : ∀ x, x ∉ S0 → c x = 0 := by
    simpa [c] using cword_support a1 a2 a3 q u1 v1 u2 v2 u3 v3
  have hd : ∀ y, y ∉ S1 → d y = 0 := by
    simpa [d] using dword_support a1 a2 a3 q u1 v1 u2 v2 u3 v3
  have hnc : SS.innerC c c = 1 := by
    simpa [c] using cword_normalized a1 a2 a3 q u1 v1 u2 v2 u3 v3 hp
  have hnd : SS.innerC d d = 1 := by
    simpa [d] using dword_normalized a1 a2 a3 q u1 v1 u2 v2 u3 v3 hp
  have hdist : SS.HasDistance ![c,d] 3 := by
    simpa [c,d] using direct_is_code a1 a2 a3 q u1 v1 u2 v2 u3 v3 hp
  obtain ⟨t, htlo, hthi, hA, hB⟩ :=
    universal_family c d hc hd hnc hnd hdist
  have hb : BlockMasses c d (4*a1^2) (4*a2^2) (4*a3^2) := by
    simpa [c,d] using
      direct_block_masses a1 a2 a3 q u1 v1 u2 v2 u3 v3 hp
  have hphase := SixQubit.Orbit45Phase.phase_relations c d hc hd hdist
  have hA2 := SixQubit.Orbit45A2.Aco_two_value c d
    (4*a1^2) (4*a2^2) (4*a3^2) hc hd hdist hb hphase
  have hcoord : SS.MacWilliams.Aco ![c,d] 2 =
      4 * directParameter a1 a2 a3 := by
    rw [hA2]
    unfold directParameter
    ring
  have ht : t = directParameter a1 a2 a3 := by
    rcases hA with ⟨_,_,hAt,_,_,_,_⟩
    nlinarith
  subst t
  simpa [c,d] using And.intro hA hB

/-- A packaged direct tuple, including exact fibre support, normalization,
distance three, and both complete enumerators. -/
theorem direct_certificate
    (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ)
    (hp : Params a1 a2 a3 q u1 v1 u2 v2 u3 v3) :
    let c := cword a1 a2 a3 q u1 v1 u2 v2 u3 v3
    let d := dword a1 a2 a3 q u1 v1 u2 v2 u3 v3
    (∀ x, x ∉ S0 → c x = 0) ∧
    (∀ y, y ∉ S1 → d y = 0) ∧
    SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
    SS.HasDistance ![c,d] 3 ∧
    IsFamilyA ![c,d] (directParameter a1 a2 a3) ∧
    IsFamilyB ![c,d] (directParameter a1 a2 a3) := by
  dsimp only
  refine ⟨cword_support _ _ _ _ _ _ _ _ _ _,
    dword_support _ _ _ _ _ _ _ _ _ _,
    cword_normalized _ _ _ _ _ _ _ _ _ _ hp,
    dword_normalized _ _ _ _ _ _ _ _ _ _ hp,
    direct_is_code _ _ _ _ _ _ _ _ _ _ hp, ?_⟩
  exact direct_families _ _ _ _ _ _ _ _ _ _ hp

/-! ## The upper chart: `3/4 ≤ t ≤ 1` -/

theorem high_chart (t : ℝ) (hlo : (3/4 : ℝ) ≤ t) (hi : t ≤ 1) :
    ∃ a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ,
      Params a1 a2 a3 q u1 v1 u2 v2 u3 v3 ∧
      directParameter a1 a2 a3 = t := by
  let r : ℝ := Real.sqrt (4*t - 3)
  let p : ℝ := (1+r)/2
  let g1 : ℝ := (1-p)/2
  let g2 : ℝ := p/2
  let g3 : ℝ := 1/2
  let a1 : ℝ := Real.sqrt (g1/4)
  let a2 : ℝ := Real.sqrt (g2/4)
  let a3 : ℝ := Real.sqrt (g3/4)
  let q : ℝ := Real.sqrt (1/8)
  have hrad : 0 ≤ 4*t - 3 := by nlinarith
  have hr0 : 0 ≤ r := by simp [r]
  have hr2 : r^2 = 4*t - 3 := by
    simpa [r] using Real.sq_sqrt hrad
  have hrle : r ≤ 1 := by nlinarith
  have hp0 : 0 ≤ p := by dsimp [p]; nlinarith
  have hple : p ≤ 1 := by dsimp [p]; nlinarith
  have hg10 : 0 ≤ g1 := by dsimp [g1]; nlinarith
  have hg20 : 0 ≤ g2 := by dsimp [g2]; nlinarith
  have hg30 : 0 ≤ g3 := by norm_num [g3]
  have ha1 : a1^2 = g1/4 := by
    simpa [a1] using Real.sq_sqrt (by positivity : 0 ≤ g1/4)
  have ha2 : a2^2 = g2/4 := by
    simpa [a2] using Real.sq_sqrt (by positivity : 0 ≤ g2/4)
  have ha3 : a3^2 = g3/4 := by
    simpa [a3] using Real.sq_sqrt (by positivity : 0 ≤ g3/4)
  have hq : q^2 = 1/8 := by
    simp [q]
  have hparams : Params a1 a2 a3 q 1 0 1 0 (-1) 0 := by
    refine ⟨?_, hq, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · rw [ha1, ha2, ha3]
      dsimp [g1,g2,g3,p]
      ring
    · rw [ha1, ha2, ha3]
      dsimp [g1,g2,g3,p]
      ring
    · ring
  have hpar : directParameter a1 a2 a3 = t := by
    unfold directParameter
    rw [show a1^4 = (a1^2)^2 by ring,
      show a2^4 = (a2^2)^2 by ring,
      show a3^4 = (a3^2)^2 by ring,
      ha1, ha2, ha3]
    dsimp [g1,g2,g3,p]
    nlinarith
  exact ⟨a1,a2,a3,q,1,0,1,0,-1,0,hparams,hpar⟩

/-! ## The lower chart: `2/3 ≤ t ≤ 3/4` -/

theorem low_chart (t : ℝ) (hlo : (2/3 : ℝ) ≤ t)
    (hi : t ≤ (3/4 : ℝ)) :
    ∃ a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ,
      Params a1 a2 a3 q u1 v1 u2 v2 u3 v3 ∧
      directParameter a1 a2 a3 = t := by
  let r : ℝ := Real.sqrt (3*t - 2)
  let s : ℝ := (1-2*r)/3
  let ga : ℝ := (1+s)/4
  let gb : ℝ := (1-s)/2
  let a1 : ℝ := Real.sqrt (ga/4)
  let a2 : ℝ := Real.sqrt (ga/4)
  let a3 : ℝ := Real.sqrt (gb/4)
  let q : ℝ := Real.sqrt (1/8)
  let w : ℝ := Real.sqrt s
  let u : ℝ := (1-s)/(1+s)
  let v : ℝ := 2*w/(1+s)
  have hrad : 0 ≤ 3*t - 2 := by nlinarith
  have hr0 : 0 ≤ r := by simp [r]
  have hr2 : r^2 = 3*t - 2 := by
    simpa [r] using Real.sq_sqrt hrad
  have hrle : r ≤ 1/2 := by nlinarith
  have hs0 : 0 ≤ s := by dsimp [s]; nlinarith
  have hsle : s ≤ 1/3 := by dsimp [s]; nlinarith
  have hden : 1+s ≠ 0 := by nlinarith
  have hga0 : 0 ≤ ga := by dsimp [ga]; nlinarith
  have hgb0 : 0 ≤ gb := by dsimp [gb]; nlinarith
  have ha1 : a1^2 = ga/4 := by
    simpa [a1] using Real.sq_sqrt (by positivity : 0 ≤ ga/4)
  have ha2 : a2^2 = ga/4 := by
    simpa [a2] using Real.sq_sqrt (by positivity : 0 ≤ ga/4)
  have ha3 : a3^2 = gb/4 := by
    simpa [a3] using Real.sq_sqrt (by positivity : 0 ≤ gb/4)
  have hq : q^2 = 1/8 := by
    simp [q]
  have hw : w^2 = s := by
    simpa [w] using Real.sq_sqrt hs0
  have hu : u^2 + v^2 = 1 := by
    dsimp [u,v]
    field_simp [hden]
    nlinarith
  have hparams : Params a1 a2 a3 q u v u (-v) (-1) 0 := by
    refine ⟨?_, hq, hu, ?_, by norm_num, ?_, ?_⟩
    · rw [ha1, ha3]
      dsimp [ga,gb]
      ring
    · nlinarith [hu]
    · rw [ha1, ha3]
      dsimp [ga,gb,u]
      field_simp [hden]
      ring
    · rw [ha1]
      ring
  have hpar : directParameter a1 a2 a3 = t := by
    unfold directParameter
    rw [show a1^4 = (a1^2)^2 by ring,
      show a3^4 = (a3^2)^2 by ring,
      ha1, ha3]
    dsimp [ga,gb,s]
    nlinarith
  exact ⟨a1,a2,a3,q,u,v,u,-v,-1,0,hparams,hpar⟩

/-- The two explicit charts cover the entire closed manuscript interval. -/
theorem directParameter_surjective (t : ℝ) (hlo : (2/3 : ℝ) ≤ t)
    (hi : t ≤ 1) :
    ∃ a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ,
      Params a1 a2 a3 q u1 v1 u2 v2 u3 v3 ∧
      directParameter a1 a2 a3 = t := by
  by_cases hmid : t ≤ (3/4 : ℝ)
  · exact low_chart t hlo hmid
  · exact high_chart t (le_of_lt (lt_of_not_ge hmid)) hi

/-- **Exact orbit-45 interval attainment.**  For every point of the full
interval there are two explicitly defined codewords on the two complete
fibres.  They are normalized, satisfy the kernel-level distance predicate,
and have the complete raw A/B enumerators stated in the manuscript. -/
theorem interval_attainment (t : ℝ) (hlo : (2/3 : ℝ) ≤ t) (hi : t ≤ 1) :
    ∃ c d : SS.State 6 ℂ,
      (∀ x, x ∉ S0 → c x = 0) ∧
      (∀ y, y ∉ S1 → d y = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c,d] 3 ∧
      IsFamilyA ![c,d] t ∧ IsFamilyB ![c,d] t := by
  obtain ⟨a1,a2,a3,q,u1,v1,u2,v2,u3,v3,hp,hpar⟩ :=
    directParameter_surjective t hlo hi
  let c := cword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  let d := dword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  have hcert := direct_certificate a1 a2 a3 q u1 v1 u2 v2 u3 v3 hp
  dsimp only at hcert
  rcases hcert with ⟨hc,hd,hnc,hnd,hDist,hA,hB⟩
  rw [hpar] at hA hB
  exact ⟨c,d,by simpa [c] using hc,by simpa [d] using hd,
    by simpa [c] using hnc,by simpa [d] using hnd,
    by simpa [c,d] using hDist,by simpa [c,d] using hA,
    by simpa [c,d] using hB⟩

/-- The same attainment theorem with support stated directly as the two
`av`-weight fibres rather than through their exact ten-element tables. -/
theorem interval_attainment_full_fibres (t : ℝ)
    (hlo : (2/3 : ℝ) ≤ t) (hi : t ≤ 1) :
    ∃ c d : SS.State 6 ℂ,
      (∀ x, SS.weight av x ≠ 0 → c x = 0) ∧
      (∀ y, SS.weight av y ≠ 3 → d y = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c,d] 3 ∧
      IsFamilyA ![c,d] t ∧ IsFamilyB ![c,d] t := by
  obtain ⟨c,d,hc,hd,hnc,hnd,hDist,hA,hB⟩ :=
    interval_attainment t hlo hi
  refine ⟨c,d,?_,?_,hnc,hnd,hDist,hA,hB⟩
  · intro x hx
    apply hc x
    intro hxS
    have hxF : x ∈ (Finset.univ : Finset (SS.BitString 6)).filter
        (fun z => SS.weight av z = 0) := by
      rw [S0_eq_fiber]
      exact hxS
    exact hx (Finset.mem_filter.mp hxF).2
  · intro y hy
    apply hd y
    intro hyS
    have hyF : y ∈ (Finset.univ : Finset (SS.BitString 6)).filter
        (fun z => SS.weight av z = 3) := by
      rw [S1_eq_fiber]
      exact hyS
    exact hy (Finset.mem_filter.mp hyF).2

end

end SixQubit.Orbit45Attain
