import MainTheory.Orbit2PrintedPurityMasses

/-! The SI's four active support patterns and the two printed purity equations. -/

namespace MainTheory.Orbit2PrintedActiveMasses

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.PurityReduction Orbit2.PhysicalFlatness
open MainTheory.Orbit2PrintedPurityMasses
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def transverse (p : Label 7) : ℕ := ∑ i : Fin 4,
  if p ⟨i.val+3,by omega⟩=1 ∨ p ⟨i.val+3,by omega⟩=2 then 1 else 0

def longitudinal (p : Label 7) : ℕ := ∑ i : Fin 4,
  if p ⟨i.val+3,by omega⟩=3 then 1 else 0

def pattern (k : Fin 3) (p : Label 7) : Bool := supported p A &&
  decide (transverse p=(![0,2,2] k : ℕ) ∧ longitudinal p=(![1,0,1] k : ℕ))

def a (V : Encoder) : ℝ := mass V (pattern 0)
def u (V : Encoder) : ℝ := mass V (pattern 1)
def v (V : Encoder) : ℝ := mass V (pattern 2)

theorem pattern_counts : ∀ k : Fin 3,
    (Finset.univ.filter (fun q : Label 4 => pattern k (packed 0 0 0 q))).card=
      (![4,24,48] k : ℕ) := by
  intro k
  fin_cases k
  all_goals decide +kernel

theorem partition_active (d : Fin 4) : ∀ q : Label 3,
    let p := packed 0 0 0 (![d,q 0,q 1,q 2])
    ¬(forbidden p ∨ forbidden (partner p)) →
    indicator (supported p A)=indicator (decide (p=fun _ => 0))+
      indicator (pattern 0 p)+indicator (pattern 1 p)+indicator (pattern 2 p)+
      indicator (transverseFourMass p) := by
  fin_cases d
  all_goals decide +kernel

theorem active_pack (p : Label 7) (h : supported p A) :
    packed 0 0 0 (![p 3,p 4,p 5,p 6])=p := by
  have hp := of_decide_eq_true h
  have h0 : p 0=0 := (hp 0).resolve_right (by decide)
  have h1 : p 1=0 := (hp 1).resolve_right (by decide)
  have h2 : p 2=0 := (hp 2).resolve_right (by decide)
  funext i
  fin_cases i
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm
  · rfl
  · rfl
  · rfl
  · rfl

theorem partition (p : Label 7) (ha : supported p A)
    (hz : ¬(forbidden p ∨ forbidden (partner p))) :
    indicator (supported p A)=indicator (decide (p=fun _ => 0))+
      indicator (pattern 0 p)+indicator (pattern 1 p)+indicator (pattern 2 p)+
      indicator (transverseFourMass p) := by
  have hp := partition_active (p 3) (![p 4,p 5,p 6])
  have he := active_pack p ha
  change ¬(forbidden (packed 0 0 0 ![p 3,p 4,p 5,p 6]) ∨
    forbidden (partner (packed 0 0 0 ![p 3,p 4,p 5,p 6]))) →
    indicator (supported (packed 0 0 0 ![p 3,p 4,p 5,p 6]) A)=
      indicator (decide (packed 0 0 0 ![p 3,p 4,p 5,p 6]=fun _ => 0))+
      indicator (pattern 0 (packed 0 0 0 ![p 3,p 4,p 5,p 6]))+
      indicator (pattern 1 (packed 0 0 0 ![p 3,p 4,p 5,p 6]))+
      indicator (pattern 2 (packed 0 0 0 ![p 3,p 4,p 5,p 6]))+
      indicator (transverseFourMass (packed 0 0 0 ![p 3,p 4,p 5,p 6])) at hp
  rw [he] at hp
  exact hp hz

theorem active_partition (V : Encoder) : maskMass V A=1+a V+u V+v V+w V := by
  have he (p : Label 7) : (if supported p A then V.labelMass p else 0)=
      (if p=(fun _ => 0) then V.labelMass p else 0)+
      (if pattern 0 p then V.labelMass p else 0)+
      (if pattern 1 p then V.labelMass p else 0)+
      (if pattern 2 p then V.labelMass p else 0)+
      (if transverseFourMass p then V.labelMass p else 0) := by
    by_cases hz : forbidden p ∨ forbidden (partner p)
    · have h0 : V.labelMass p=0 := by
        rcases hz with hz|hz
        · exact V.labelMass_forbidden_zero p hz
        · rw [← V.labelMass_pairing p]
          exact V.labelMass_forbidden_zero _ hz
      simp [h0]
    · by_cases ha : supported p A
      · have hp := partition_active (p 3) (![p 4,p 5,p 6])
        have h := partition p ha hz
        unfold indicator at h
        split_ifs at h ⊢ <;> simp_all
      · have hi : p≠(fun _ => 0) := by
          intro h
          subst p
          exact ha (by decide)
        simp [ha,hi,pattern,transverseFourMass]
  unfold maskMass a u v w mass
  simp_rw [he,Finset.sum_add_distrib]
  have hi : V.labelMass (fun _ => 0)=1 := by
    change V.purificationMass (identityPauli 7)=1
    exact V.purificationMass_identity
  simp [hi]

theorem s_as_named (V : Encoder) : s V=a V+u V+v V+w V := by
  rw [s,active_partition]
  ring

theorem mass_nonneg (V : Encoder) (f : Label 7 → Bool) : 0 ≤ mass V f := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact V.purificationMass_nonneg (decode p)
  · rfl

theorem vanishing_masses (V : Encoder) : b V=0 ∧ m V=0 ∧ w V=0 := by
  have hb := mass_nonneg V spectatorMass
  have hm := mass_nonneg V mixedMass
  have hw := mass_nonneg V transverseFourMass
  have h := purity_sos V
  change 0 ≤ b V at hb
  change 0 ≤ m V at hm
  change 0 ≤ w V at hw
  constructor
  · linarith
  constructor <;> linarith

theorem purity_one_named (V : Encoder) : 1+(a V+u V+v V+w V)=2*(1+b V) := by
  rw [← s_as_named]
  exact purity_one V

theorem active_low_mass (V : Encoder) : a V+u V+v V=1 := by
  have h := active_partition V
  rw [active_mass,vanishing_masses V |>.2.2] at h
  linarith

theorem purity_two_named (V : Encoder) :
    2*(4*(1+b V)+a V+m V)=
      4*(1+(a V+u V+v V+w V))-2*u V-2*v V-4*w V+mass V H3 := by
  have hz := vanishing_masses V
  have hh := (purity_h V).1
  have ha := active_low_mass V
  rw [hz.1,hz.2.1,hz.2.2,hh,hz.1]
  linarith

end

end MainTheory.Orbit2PrintedActiveMasses
