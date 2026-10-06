import MainTheory.CompletePauliCoefficients
import SixQubit.Orbit21Farkas

set_option autoImplicit false

namespace MainTheory.Orbit21FarkasDisplay

open SixQubit.Orbit21Farkas SS.MacWilliams SS.ShadowTwisted
open MainTheory.CompletePauliCoefficients

theorem b_normalization (psi : Fin 2 → SS.State 6 ℂ) (E : ℕ × ℕ)
    (hx : E.1 < 64) (hz : E.2 < 64) : bRaw psi E/128=b psi (ofMask E) := by
  rw [bRaw_eq_frob psi E hx hz]
  unfold b
  ring

theorem s_normalization (psi : Fin 2 → SS.State 6 ℂ) (E : ℕ × ℕ)
    (hx : E.1 < 64) (hz : E.2 < 64) :
    tRaw psi E/128=MainTheory.CompleteShadowTrace.coefficient psi (ofMask E) := by
  have he : tRaw psi E=∑ P : SS.PauliString 6,
      (-1 : ℝ)^P.wt*pairSign (ofMask E) P*Complex.normSq (trProj psi P) := by
    unfold tRaw maskSum
    simp_rw [tsign_eq_shadowSign E hx hz]
    exact (sum_pauli (fun P : SS.PauliString 6 =>
      (-1 : ℝ)^P.wt*pairSign (ofMask E) P*Complex.normSq (trProj psi P))).symm
  rw [he,MainTheory.CompleteShadowTrace.coefficient_transform]
  simp only [← mul_div_assoc,← Finset.sum_div]
  ring

noncomputable def selectedA (psi : Fin 2 → SS.State 6 ℂ) (L : List (ℕ × ℕ)) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString 6 =>
    SixQubit.Orbit21Coef.mem (SixQubit.Realize.num P.x) (SixQubit.Realize.num P.z) L),a psi P

theorem r_normalization (psi : Fin 2 → SS.State 6 ℂ) (L : List (ℕ × ℕ)) :
    rRaw psi L/4=selectedA psi L := by
  unfold rRaw maskSum
  rw [← sum_pauli (fun P : SS.PauliString 6 =>
    (if SixQubit.Orbit21Coef.mem (SixQubit.Realize.num P.x) (SixQubit.Realize.num P.z) L
      then (1 : ℝ) else 0)*Complex.normSq (trProj psi P))]
  unfold selectedA a
  rw [Finset.sum_div,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  split_ifs <;> simp

theorem list_sum_div (L : List (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (L.map f).sum/128=(L.map (fun E => f E/128)).sum := by
  induction L with
  | nil => simp
  | cons E L ih => simp only [List.map_cons,List.sum_cons,add_div,ih]

theorem b_total (psi : Fin 2 → SS.State 6 ℂ) (L : List (ℕ × ℕ))
    (hL : ∀ E ∈ L,E.1 < 64 ∧ E.2 < 64) :
    bTotal psi L/128=(L.map (fun E => b psi (ofMask E))).sum := by
  rw [bTotal,list_sum_div]
  congr 1
  apply List.map_congr_left
  intro E hE
  exact b_normalization psi E (hL E hE).1 (hL E hE).2

theorem s_total (psi : Fin 2 → SS.State 6 ℂ) (L : List (ℕ × ℕ))
    (hL : ∀ E ∈ L,E.1 < 64 ∧ E.2 < 64) :
    tTotal psi L/128=(L.map (fun E => MainTheory.CompleteShadowTrace.coefficient psi (ofMask E))).sum := by
  rw [tTotal,list_sum_div]
  congr 1
  apply List.map_congr_left
  intro E hE
  exact s_normalization psi E (hL E hE).1 (hL E hE).2

theorem identity (psi : Fin 2 → SS.State 6 ℂ)
    (h0 : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → psi 0 x=0)
    (h1 : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → psi 1 x=0)
    (hnorm : ∀ i,SS.innerC (psi i) (psi i)=1) (hd : SS.HasDistance psi 3) :
    Aco psi 2/4-1=
      2*(SixQubit.Orbit21Coef.bset.map (fun E => b psi (ofMask E))).sum+
      2*(SixQubit.Orbit21Coef.tset.map
        (fun E => MainTheory.CompleteShadowTrace.coefficient psi (ofMask E))).sum+
      2*selectedA psi SixQubit.Orbit21Coef.r2set+
      3*selectedA psi SixQubit.Orbit21Coef.r3set+
      4*selectedA psi SixQubit.Orbit21Coef.r4set := by
  have hc := certificate_identity psi hnorm hd
  have hr : residual psi=0 := by
    rw [residual_eq_pauli]
    exact SixQubit.Orbit21Residual.residual_vanishes psi h0 h1
  rw [hr] at hc
  unfold positiveRhs at hc
  rw [← b_total psi _ bset_bounds,← s_total psi _ tset_bounds,
    ← r_normalization,← r_normalization,← r_normalization]
  linarith

end MainTheory.Orbit21FarkasDisplay
