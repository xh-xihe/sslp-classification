import MainTheory.Orbit7StructuralDisplay

set_option autoImplicit false

namespace MainTheory.Orbit7EnumeratorDisplays

open SixQubit.Orbit7Universal SS.MacWilliams SixQubit.Orbit7Family

noncomputable def normalizedA (psi : Fin 2 → SS.State 6 ℂ) (j : ℕ) : ℝ := Aco psi j/4
noncomputable def normalizedB (psi : Fin 2 → SS.State 6 ℂ) (j : ℕ) : ℝ := Bco psi j/4

noncomputable def shadowZero (psi : Fin 2 → SS.State 6 ℂ) : ℝ :=
  (1/128)*(∑ P : SS.PauliString 6,(-1 : ℝ)^P.wt*Complex.normSq (trProj psi P))

theorem shadow_formula (psi : Fin 2 → SS.State 6 ℂ) (hd : SS.HasDistance psi 3)
    (h0 : Aco psi 0=4) :
    shadowZero psi=(1/4)*(1-normalizedA psi 1-normalizedA psi 2-normalizedA psi 3) ∧
      0 ≤ shadowZero psi := by
  constructor
  · obtain ⟨h4,h5,h6⟩ := macwilliams_six psi hd h0
    rw [shadowZero,SS.Shadow.alt_sum_as_Aco]
    norm_num [Finset.sum_range_succ,normalizedA]
    linear_combination (h0+h4-h5+h6)/128
  · exact mul_nonneg (by norm_num) (SS.Shadow.alt_sum_nonneg psi)

theorem family_vectors (psi : Fin 2 → SS.State 6 ℂ) (a : ℝ)
    (hA : IsFamilyA psi a) (hB : IsFamilyB psi a) :
    (fun j : Fin 7 => normalizedA psi j) = ![1,a,1-a,0,11+4*a,16-a,3-3*a] ∧
    (fun j : Fin 7 => normalizedB psi j) = ![1,a,1-a,24+6*a,35+10*a,40-7*a,27-9*a] := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hA
  obtain ⟨b0,b1,b2,b3,b4,b5,b6⟩ := hB
  constructor
  · funext j
    fin_cases j <;> norm_num [normalizedA,a0,a1,a2,a3,a4,a5,a6]
  · funext j
    fin_cases j <;> norm_num [normalizedB,b0,b1,b2,b3,b4,b5,b6]

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
  (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem low_bound : 1 ≤ normalizedA ![c,d] 1+normalizedA ![c,d] 2 := by
  have h := target_low_bound c d hc hd hnc hnd hcode
    (MainTheory.Orbit7StructuralDisplay.universal_target c d hc hd hnc hnd hcode)
  dsimp only [normalizedA]
  linarith

theorem line_identities :
    normalizedA ![c,d] 1+normalizedA ![c,d] 2=1 ∧ normalizedA ![c,d] 3=0 := by
  have hl := low_bound c d hc hd hnc hnd hcode
  have hn : ∀ k : Fin 2,SS.innerC (![c,d] k) (![c,d] k)=1 := by
    intro k
    fin_cases k
    · exact hnc
    · exact hnd
  have h0 := SixQubit.Pin.Aco_zero ![c,d] hn
  have hs := SS.Shadow.shadow_bound ![c,d] hcode h0
  have hp := SixQubit.Pin.Aco_nonneg ![c,d] 3
  dsimp only [normalizedA] at hl ⊢
  constructor <;> linarith

theorem universal_vectors : ∃ a : ℝ,0 ≤ a ∧ a ≤ 1 ∧
    a=normalizedA ![c,d] 1 ∧
    (fun j : Fin 7 => normalizedA ![c,d] j) = ![1,a,1-a,0,11+4*a,16-a,3-3*a] ∧
    (fun j : Fin 7 => normalizedB ![c,d] j) = ![1,a,1-a,24+6*a,35+10*a,40-7*a,27-9*a] := by
  obtain ⟨a,ha0,ha1,hA,hB,_⟩ := uniform_universal_converse c d hc hd hnc hnd hcode
  have h1 := hA.2.1
  refine ⟨a,ha0,ha1,?_,family_vectors _ a hA hB⟩
  dsimp only [normalizedA]
  linarith

end MainTheory.Orbit7EnumeratorDisplays
