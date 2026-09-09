import SixQubit.Orbit7UniversalMatrix

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit7StateExpansion

open SixQubit.Orbit7Universal

noncomputable def spinorTerm (s : Spinor) (base x : SS.BitString 6) : ℂ :=
  if x = base then s 0 else if x = SS.bxor base abit then s 1 else 0

theorem spinorTerm_eq (f : SS.State 6 ℂ) (base x : SS.BitString 6) :
    spinorTerm (spinor f base) base x = if x ∈ spinSupport base then f x else 0 := by
  by_cases h0 : x = base
  · subst x
    simp [spinorTerm,spinSupport,spinor]
  · by_cases h1 : x = SS.bxor base abit
    · subst x
      simp [spinorTerm,spinSupport,spinor,h0]
    · simp [spinorTerm,spinSupport,h0,h1]

theorem partition0 : ∀ x : SS.BitString 6,
    (if x ∈ spinSupport zero then 1 else 0) +
      (∑ e ∈ edgePairs, if x ∈ spinSupport (aBase e.1 e.2) then 1 else 0) =
        (if x ∈ S0 then 1 else 0 : ℕ) := by decide +kernel

theorem partition2 : ∀ x : SS.BitString 6,
    (if x ∈ spinSupport activeAll then 1 else 0) +
      (∑ e ∈ edgePairs, if x ∈ spinSupport (bBase e.1 e.2) then 1 else 0) =
        (if x ∈ S2 then 1 else 0 : ℕ) := by decide +kernel

private theorem reconstruct (f : SS.State 6 ℂ) (S : Finset (SS.BitString 6))
    (extreme : SS.BitString 6) (base : Fin 5 × Fin 5 → SS.BitString 6)
    (hp : ∀ x, (if x ∈ spinSupport extreme then 1 else 0) +
      (∑ e ∈ edgePairs, if x ∈ spinSupport (base e) then 1 else 0) =
        (if x ∈ S then 1 else 0 : ℕ))
    (hf : ∀ x, x ∉ S → f x = 0) (x : SS.BitString 6) :
    f x = spinorTerm (spinor f extreme) extreme x +
      ∑ e ∈ edgePairs, spinorTerm (spinor f (base e)) (base e) x := by
  have hpc : (if x ∈ spinSupport extreme then (1 : ℂ) else 0) +
      (∑ e ∈ edgePairs, if x ∈ spinSupport (base e) then (1 : ℂ) else 0) =
        (if x ∈ S then (1 : ℂ) else 0) := by exact_mod_cast hp x
  have h := congrArg (fun z : ℂ => z * f x) hpc
  simp only [spinorTerm_eq]
  simp only [add_mul,Finset.sum_mul,ite_mul,one_mul,zero_mul] at h
  rw [h]
  by_cases hx : x ∈ S
  · simp [hx]
  · simp [hx,hf x hx]

theorem bottom_expansion (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0) :
    c = fun x => spinorTerm (spinor c zero) zero x +
      ∑ e ∈ edgePairs, spinorTerm (spinor c (aBase e.1 e.2)) (aBase e.1 e.2) x := by
  funext x
  exact reconstruct c S0 zero (fun e => aBase e.1 e.2) partition0 (full_support0 hc) x

theorem top_expansion (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0) :
    d = fun x => (∑ e ∈ edgePairs,
      spinorTerm (spinor d (bBase e.1 e.2)) (bBase e.1 e.2) x) +
        spinorTerm (spinor d activeAll) activeAll x := by
  funext x
  rw [add_comm]
  exact reconstruct d S2 activeAll (fun e => bBase e.1 e.2) partition2 (full_support2 hd) x

end MainTheory.Orbit7StateExpansion
