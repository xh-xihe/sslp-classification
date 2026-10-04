import Orbit2.Complete

/-! The named real masses and complementary-purity equalities in the SI. -/

namespace MainTheory.Orbit2PrintedPurityMasses

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.PurityReduction Orbit2.PhysicalFlatness
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def mass (V : Encoder) (f : Label 7 → Bool) : ℝ :=
  ∑ p,if f p then V.labelMass p else 0

def b (V : Encoder) : ℝ := mass V spectatorMass
def m (V : Encoder) : ℝ := mass V mixedMass
def w (V : Encoder) : ℝ := mass V transverseFourMass
def s (V : Encoder) : ℝ := maskMass V A-1

def H (p : Label 7) : Bool := supported p RA && decide (p 0=1 ∨ p 0=2)
def H3 (p : Label 7) : Bool := H p && decide
  ((∑ i : Fin 6,if p i.succ=0 then 0 else 1 : ℕ)=3)
def H4 (p : Label 7) : Bool := H p && decide
  ((∑ i : Fin 6,if p i.succ=0 then 0 else 1 : ℕ)=4)

theorem mass_pair (V : Encoder) (f : Label 7 → Bool) :
    mass V (fun p => f (partner p))=mass V f := by
  simpa only [mass,partnerEquiv,Function.Involutive.coe_toPerm,V.labelMass_pairing] using
    partnerEquiv.sum_comp (fun p => if f p then V.labelMass p else 0)

theorem unpack (p : Label 7) : packed (p 0) (p 1) (p 2) (fun i => p ⟨i.val+3,by omega⟩)=p := by
  funext i
  fin_cases i <;> rfl

theorem spectator_partition_packed (r b c : Fin 4) : ∀ a : Label 4,
    let p := packed r b c a
    indicator (supported p B)=indicator (decide (p=fun _ => 0))+indicator (spectatorMass p) := by
  fin_cases r <;> fin_cases b <;> fin_cases c
  all_goals decide +kernel

theorem spectator_partition (p : Label 7) :
    indicator (supported p B)=indicator (decide (p=fun _ => 0))+indicator (spectatorMass p) := by
  have h := spectator_partition_packed (p 0) (p 1) (p 2) (fun i => p ⟨i.val+3,by omega⟩)
  simpa only [unpack] using h

theorem spectator_mass (V : Encoder) : maskMass V B=1+b V := by
  have he : ∀ p : Label 7,(if supported p B then V.labelMass p else 0)=
      (if p=(fun _ => 0) then V.labelMass p else 0)+
      (if spectatorMass p then V.labelMass p else 0) := by
    intro p
    have h := spectator_partition p
    unfold indicator at h
    split_ifs at h ⊢ <;> simp_all
  unfold maskMass b mass
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hi : V.labelMass (fun _ => 0)=1 := by
    change V.purificationMass (identityPauli 7)=1
    exact V.purificationMass_identity
  simp [hi]

theorem purity_one (V : Encoder) : 1+s V=2*(1+b V) := by
  have h := purity_A_B V
  rw [spectator_mass] at h
  unfold s
  linarith

theorem reference_partition_packed (r b c : Fin 4) : ∀ a : Label 4,
    let p := packed r b c a
    indicator (supported p RA)=indicator (supported p A)+
      indicator (supported (partner p) A)+indicator (H p) := by
  fin_cases r <;> fin_cases b <;> fin_cases c
  all_goals decide +kernel

theorem reference_partition (p : Label 7) :
    indicator (supported p RA)=indicator (supported p A)+
      indicator (supported (partner p) A)+indicator (H p) := by
  have h := reference_partition_packed (p 0) (p 1) (p 2) (fun i => p ⟨i.val+3,by omega⟩)
  simpa only [unpack] using h

theorem reference_mass (V : Encoder) : maskMass V RA=2*maskMass V A+mass V H := by
  have he : ∀ p : Label 7,(if supported p RA then V.labelMass p else 0)=
      (if supported p A then V.labelMass p else 0)+
      (if supported (partner p) A then V.labelMass p else 0)+
      (if H p then V.labelMass p else 0) := by
    intro p
    have h := reference_partition p
    unfold indicator at h
    split_ifs at h ⊢ <;> simp_all
  have hp := mass_pair V (fun p => supported p A)
  change (∑ p,if supported (partner p) A then V.labelMass p else 0)=maskMass V A at hp
  unfold maskMass
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hp]
  change maskMass V A+maskMass V A+mass V H=2*maskMass V A+mass V H
  ring

theorem reference_h (V : Encoder) : mass V H=4*(1+b V) := by
  have h := purity_B V
  rw [reference_mass,purity_A_B,spectator_mass] at h
  linarith

theorem transverse_geometry_packed (r b c : Fin 4) : ∀ a : Label 4,
    let p := packed r b c a
    ¬(forbidden p ∨ forbidden (partner p)) →
      indicator (H p)=indicator (H3 p)+indicator (H4 p) ∧
      indicator (H3 (partner p))=indicator (H4 p) := by
  fin_cases r <;> fin_cases b <;> fin_cases c
  all_goals decide +kernel

theorem transverse_geometry (p : Label 7) :
    ¬(forbidden p ∨ forbidden (partner p)) →
      indicator (H p)=indicator (H3 p)+indicator (H4 p) ∧
      indicator (H3 (partner p))=indicator (H4 p) := by
  have h := transverse_geometry_packed (p 0) (p 1) (p 2) (fun i => p ⟨i.val+3,by omega⟩)
  simpa only [unpack] using h

theorem transverse_partition (V : Encoder) : mass V H=mass V H3+mass V H4 := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hz : forbidden p ∨ forbidden (partner p)
  · have h0 : V.labelMass p=0 := by
      rcases hz with hz|hz
      · exact V.labelMass_forbidden_zero p hz
      · rw [← V.labelMass_pairing p]
        exact V.labelMass_forbidden_zero _ hz
    simp [h0]
  · have h := (transverse_geometry p hz).1
    unfold indicator at h
    split_ifs at h ⊢ <;> simp_all

theorem transverse_pair (V : Encoder) : mass V H3=mass V H4 := by
  rw [← mass_pair V H3]
  unfold mass
  apply Finset.sum_congr rfl
  intro p _
  by_cases hz : forbidden p ∨ forbidden (partner p)
  · have h0 : V.labelMass p=0 := by
      rcases hz with hz|hz
      · exact V.labelMass_forbidden_zero p hz
      · rw [← V.labelMass_pairing p]
        exact V.labelMass_forbidden_zero _ hz
    simp [h0]
  · have h := (transverse_geometry p hz).2
    unfold indicator at h
    split_ifs at h ⊢ <;> simp_all

theorem purity_h (V : Encoder) : mass V H3=2*(1+b V) ∧ mass V H4=2*(1+b V) := by
  have hp := transverse_partition V
  have he := transverse_pair V
  have hh := reference_h V
  constructor <;> linarith

theorem purity_sos (V : Encoder) : b V+m V+w V=0 := by
  have h := (masses_vanish V.labelMass (fun p => V.purificationMass_nonneg (decode p))
    V.labelMass_pairing V.labelMass_forbidden_zero (purity_combination_zero V)).1
  have he (p : Label 7) : (targetCoefficient p : ℝ)*V.labelMass p=
      (if spectatorMass p then V.labelMass p else 0)+
      (if mixedMass p then V.labelMass p else 0)+
      (if transverseFourMass p then V.labelMass p else 0) := by
    simp only [targetCoefficient,Int.cast_add,indicator]
    split_ifs <;> norm_num <;> ring
  simp_rw [he] at h
  simpa only [Finset.sum_add_distrib,b,m,w,mass] using h

end

end MainTheory.Orbit2PrintedPurityMasses
