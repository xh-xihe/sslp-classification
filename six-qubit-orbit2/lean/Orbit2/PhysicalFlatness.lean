import Orbit2.PurificationSymmetry
import Orbit2.PurityReduction

namespace Orbit2.PhysicalFlatness
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.HilbertBridge Orbit2.PurityReduction
open SS.MacWilliams
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable def maskMass (V : Encoder) (S : Fin 7 → Bool) : ℝ :=
  ∑ p : Label 7, if supported p S then V.labelMass p else 0

theorem labelSite_zero : ∀ x z : Bool, labelSite x z = 0 ↔ x=false ∧ z=false := by
  decide +kernel

theorem support_label (p : SS.PauliString 7) :
    supp p = Finset.univ.filter (fun i => label p i ≠ 0) := by
  ext i
  simp only [supp,Finset.mem_filter,Finset.mem_univ,true_and,label]
  cases hx : p.x i <;> cases hz : p.z i <;> simp [labelSite,hx,hz]

theorem support_mask (p : SS.PauliString 7) (S : Fin 7 → Bool) :
    supp p ⊆ Finset.univ.filter (fun i => S i) ↔ supported (label p) S := by
  rw [support_label]
  simp only [Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and,
    supported,decide_eq_true_eq]
  constructor
  · intro h i
    by_cases hi : label p i=0
    · exact Or.inl hi
    · exact Or.inr (h hi)
  · intro h i hi
    exact (h i).resolve_left hi

theorem zero_mask (p : SS.PauliString 7) (S : Fin 7 → Bool) :
    (∀ i ∈ Finset.univ.filter (fun i => S i), p.x i=false ∧ p.z i=false) ↔
      supported (label p) (fun i => !(S i)) := by
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,supported,decide_eq_true_eq]
  constructor
  · intro h i
    by_cases hi : S i
    · exact Or.inl ((labelSite_zero _ _).mpr (h i hi))
    · exact Or.inr (by simpa using hi)
  · intro h i hi
    have hz : label p i=0 := (h i).resolve_right (by simpa [hi])
    exact (labelSite_zero _ _).mp hz

theorem complement (V : Encoder) (S : Fin 7 → Bool) :
    128 * maskMass V S = (4 : ℝ)^(Finset.univ.filter (fun i => S i)).card *
      maskMass V (fun i => !(S i)) := by
  have hd := V.complementary_purity (Finset.univ.filter (fun i => S i))
  have hm (p : SS.PauliString 7) : V.labelMass (label p) = V.purificationMass p := by
    unfold Encoder.labelMass
    have hi : decode (label p) = p := (pauliEquiv 7).left_inv p
    rw [hi]
  have hleft : (∑ p ∈ Finset.univ.filter (fun p : SS.PauliString 7 => supp p ⊆ Finset.univ.filter (fun i => S i)),
      V.purificationMass p) = maskMass V S := by
    have he := (pauliEquiv 7).sum_comp (fun p => if supported p S then V.labelMass p else 0)
    simpa only [maskMass,Finset.sum_filter,support_mask,pauliEquiv,Equiv.coe_fn_mk,hm] using he
  have hright : (∑ p ∈ Finset.univ.filter (fun p : SS.PauliString 7 =>
      ∀ i ∈ Finset.univ.filter (fun i => S i), p.x i=false ∧ p.z i=false), V.purificationMass p) =
      maskMass V (fun i => !(S i)) := by
    have he := (pauliEquiv 7).sum_comp (fun p => if supported p (fun i => !(S i)) then V.labelMass p else 0)
    simpa only [maskMass,Finset.sum_filter,zero_mask,pauliEquiv,Equiv.coe_fn_mk,hm] using he
  rwa [hleft,hright] at hd

def RB : Fin 7 → Bool := fun i => decide (i.val ≤ 2)
def Bi (i : Fin 4) : Fin 7 → Bool := fun j => B j || decide (j.val=i.val+3)
def RAi (i : Fin 4) : Fin 7 → Bool := fun j => RA j && decide (j.val≠i.val+3)

theorem mask_counts : (Finset.univ.filter (fun i => B i)).card = 2 ∧
    (Finset.univ.filter (fun i => RB i)).card = 3 ∧
      ∀ i, (Finset.univ.filter (fun j => Bi i j)).card = 3 := by decide +kernel
theorem mask_complements : (fun i => !(B i)) = RA ∧ (fun i => !(RB i)) = A ∧
    ∀ j, (fun i => !(Bi j i)) = RAi j := by decide +kernel

theorem purity_B (V : Encoder) : maskMass V RA = 8 * maskMass V B := by
  have h := complement V B
  rw [mask_counts.1,mask_complements.1] at h
  norm_num at h
  linarith

theorem purity_A_RB (V : Encoder) : maskMass V A = 2 * maskMass V RB := by
  have h := complement V RB
  rw [mask_counts.2.1,mask_complements.2.1] at h
  norm_num at h
  linarith

theorem purity_Bi (V : Encoder) (i : Fin 4) : maskMass V (RAi i) = 2 * maskMass V (Bi i) := by
  have h := complement V (Bi i)
  rw [mask_counts.2.2 i,mask_complements.2.2 i] at h
  norm_num at h
  linarith

theorem RB_vector (p : Label 7) (hp : supported p RB) :
    p = ![p 0,p 1,p 2,0,0,0,0] := by
  unfold supported at hp
  simp only [decide_eq_true_eq] at hp
  have ha (i : Fin 4) : p ⟨i.val+3,by omega⟩ = 0 := by
    have h := hp ⟨i.val+3,by omega⟩
    exact h.resolve_right (by simp [RB])
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · simpa using ha ⟨0,by decide⟩
  · simpa using ha ⟨1,by decide⟩
  · simpa using ha ⟨2,by decide⟩
  · simpa using ha ⟨3,by decide⟩

theorem RB_physical_weight : ∀ r b c : Fin 4,
    (∑ i : Fin 6, if (![r,b,c,0,0,0,0] : Label 7) i.succ = 0 then 0 else 1 : ℕ) ≤ 2 := by
  decide +kernel

theorem RB_B_support : ∀ r b c : Fin 4,
    supported (![r,b,c,0,0,0,0] : Label 7) B ↔ r=0 := by decide +kernel

theorem purity_RB_B (V : Encoder) : maskMass V RB = maskMass V B := by
  unfold maskMass
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : supported p RB
  · have hvec := RB_vector p hp
    have hweight : (∑ i : Fin 6, if p i.succ=0 then 0 else 1 : ℕ) ≤ 2 := by
      conv_lhs => rw [hvec]
      exact RB_physical_weight _ _ _
    by_cases h0 : p 0=0
    · have hb : supported p B := by
        have hb := (RB_B_support (p 0) (p 1) (p 2)).mpr h0
        rwa [← hvec] at hb
      simp [hp,hb]
    · have hm := V.reference_KL_mass_zero p h0 hweight
      simp [hm]
  · have hb : ¬ supported p B := by
      intro hb
      apply hp
      unfold supported at hb ⊢
      simp only [decide_eq_true_eq] at hb ⊢
      intro i
      rcases hb i with hi|hi
      · exact Or.inl hi
      · apply Or.inr
        have hsub : ∀ i : Fin 7, B i → RB i := by decide +kernel
        exact hsub i hi
    simp [hp,hb]

theorem purity_A_B (V : Encoder) : maskMass V A = 2 * maskMass V B := by
  rw [purity_A_RB,purity_RB_B]

theorem purity_combination_expansion (V : Encoder) :
    (∑ p : Label 7, (purityCoefficient p : ℝ)*V.labelMass p) =
      2*(∑ i : Fin 4, maskMass V (RAi i)) - 4*(∑ i : Fin 4, maskMass V (Bi i)) -
        2*maskMass V A - maskMass V RA + 12*maskMass V B := by
  have hm (S : Fin 7 → Bool) :
      (∑ p : Label 7, (indicator (supported p S) : ℝ)*V.labelMass p) = maskMass V S := by
    unfold maskMass
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : supported p S <;> simp [indicator,hp]
  have hs (S : Fin 4 → Fin 7 → Bool) :
      (∑ p : Label 7, ∑ i : Fin 4, (indicator (supported p (S i)) : ℝ)*V.labelMass p) =
        ∑ i : Fin 4, maskMass V (S i) := by
    rw [Finset.sum_comm]
    simp_rw [hm]
  have ht (p : Label 7) : (purityCoefficient p : ℝ)*V.labelMass p =
      2*(∑ i : Fin 4, (indicator (supported p (RAi i)) : ℝ)*V.labelMass p) -
      4*(∑ i : Fin 4, (indicator (supported p (Bi i)) : ℝ)*V.labelMass p) -
      2*(indicator (supported p A) : ℝ)*V.labelMass p -
      (indicator (supported p RA) : ℝ)*V.labelMass p +
      12*(indicator (supported p B) : ℝ)*V.labelMass p := by
    unfold purityCoefficient RAi Bi
    push_cast
    simp only [← Finset.sum_mul]
    ring
  simp_rw [ht]
  simp only [mul_assoc,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hs,hs,hm,hm,hm]

theorem purity_combination_zero (V : Encoder) :
    (∑ p : Label 7, (purityCoefficient p : ℝ)*V.labelMass p) = 0 := by
  rw [purity_combination_expansion]
  have hA := purity_A_B V
  have hB := purity_B V
  have hi : (∑ i : Fin 4, maskMass V (RAi i)) = 2*(∑ i : Fin 4, maskMass V (Bi i)) := by
    simp_rw [purity_Bi]
    rw [Finset.mul_sum]
  linarith

/-- The spectator, mixed spectator-Z, and four-transverse masses vanish for
every actual encoder, with no assumed purity or correlation equations. -/
theorem target_masses_zero (V : Encoder) :
    ∀ p : Label 7, 0 < targetCoefficient p → V.labelMass p = 0 := by
  exact (masses_vanish V.labelMass (fun p => V.purificationMass_nonneg (decode p))
    V.labelMass_pairing V.labelMass_forbidden_zero (purity_combination_zero V)).2

theorem spectator_positive (p : Label 7) (hp : spectatorMass p) : 0 < targetCoefficient p := by
  simp only [targetCoefficient,indicator,hp,if_true]
  split_ifs <;> norm_num

theorem spectator_flat (V : Encoder) : maskMass V B = 1 := by
  unfold maskMass
  rw [Finset.sum_eq_single (fun _ => 0)]
  · have hs : supported (fun _ : Fin 7 => 0) B := by decide +kernel
    have hi : decode (fun _ : Fin 7 => 0) = identityPauli 7 := by rfl
    simp only [hs,if_true,Encoder.labelMass,hi,V.purificationMass_identity]
  · intro p _ hp
    by_cases hs : supported p B
    · have hsp : spectatorMass p := by simp [spectatorMass,hs,hp]
      rw [if_pos hs,target_masses_zero V p (spectator_positive p hsp)]
    · simp [hs]
  · simp

theorem active_mass (V : Encoder) : maskMass V A = 2 := by
  rw [purity_A_B,spectator_flat]
  norm_num

def activeEmbedding (a : Label 4) : Label 7 := ![0,0,0,a 0,a 1,a 2,a 3]
def activeWeight (a : Label 4) : ℕ := ∑ i, if a i=0 then 0 else 1
theorem active_weight_bound : ∀ a : Label 4, activeWeight a ≤ 4 := by decide +kernel

theorem active_four_zero_reason : ∀ a : Label 4, activeWeight a=4 →
    forbidden (activeEmbedding a) ∨ forbidden (partner (activeEmbedding a)) ∨
      0 < targetCoefficient (activeEmbedding a) := by decide +kernel

theorem active_four_zero (V : Encoder) (a : Label 4) (ha : activeWeight a=4) :
    V.labelMass (activeEmbedding a) = 0 := by
  rcases active_four_zero_reason a ha with h|h|h
  · exact V.labelMass_forbidden_zero _ h
  · rw [← V.labelMass_pairing (activeEmbedding a)]
    exact V.labelMass_forbidden_zero _ h
  · exact target_masses_zero V _ h

end Orbit2.PhysicalFlatness
