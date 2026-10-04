import Orbit2.PhysicalFlatness

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unnecessarySeqFocus false

namespace Orbit2.PhysicalFlatness
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.HilbertBridge Orbit2.PurityReduction
open SS.MacWilliams
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def physicalWeight (p : Label 6) : ℕ := ∑ i, if p i=0 then 0 else 1
noncomputable def physicalMass (V : Encoder) (p : Label 6) : ℝ :=
  Complex.normSq (trProj V.psi (decode p))/4

theorem reference_identity_expectation (V : Encoder) (p : Label 6) :
    SS.innerC V.purification (SS.pauliAct (decode (Fin.cons (0 : Fin 4) p)) V.purification) =
      trProj V.psi (decode p) := by
  rw [column_compression (referenceColumn V.tensorMatrix) V.purification V.purification_column,
    reference_compression]
  have hf : ∀ j : Fin 2, FiveQubit.flipSite (0 : Fin 4) j = j := by decide +kernel
  simp only [hf,localC_zero,Matrix.one_apply,if_true,one_mul]
  unfold trProj
  apply Finset.sum_congr rfl
  intro j _
  have h := compression V.tensorMatrix (decode p) j j
  rw [label_decode,V.tensor_words] at h
  exact h.symm

theorem reference_identity_mass (V : Encoder) (p : Label 6) :
    V.labelMass (Fin.cons (0 : Fin 4) p) = physicalMass V p := by
  unfold Encoder.labelMass Encoder.purificationMass physicalMass
  rw [reference_identity_expectation]

theorem physicalMass_nonneg (V : Encoder) (p : Label 6) : 0 ≤ physicalMass V p :=
  div_nonneg (Complex.normSq_nonneg _) (by norm_num)

theorem physical_enumerator (V : Encoder) (w : ℕ) :
    V.A w = ∑ p : Label 6, if physicalWeight p=w then physicalMass V p else 0 := by
  unfold Encoder.A Aco
  rw [Finset.sum_div,Finset.sum_filter]
  have hm (p : SS.PauliString 6) : physicalMass V (label p) =
      Complex.normSq (trProj V.psi p)/4 := by
    unfold physicalMass
    have hi : decode (label p) = p := (pauliEquiv 6).left_inv p
    rw [hi]
  have hw (p : SS.PauliString 6) : physicalWeight (label p) = p.wt := label_weight p
  have h := (pauliEquiv 6).sum_comp
    (fun p => if physicalWeight p=w then physicalMass V p else 0)
  simpa only [pauliEquiv,Equiv.coe_fn_mk,hw,hm,ite_div,zero_div] using h

def labelSplit : Label 7 ≃ Fin 4 × Label 6 where
  toFun p := (p 0,fun i => p i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv p := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by rcases p with ⟨r,t⟩; rfl

theorem label_sum_split (f : Label 7 → ℝ) :
    (∑ p, f p) = ∑ r : Fin 4, ∑ q : Label 6, f (Fin.cons r q) := by
  simpa only [Fintype.sum_prod_type] using (labelSplit.symm.sum_comp f).symm

theorem active_reference_zero (r : Fin 4) (p : Label 6)
    (hs : supported (Fin.cons r p) A) : r=0 := by
  unfold supported at hs
  simp only [decide_eq_true_eq] at hs
  have h := hs 0
  simpa [A] using h

theorem active_projection (V : Encoder) : maskMass V A =
    ∑ p : Label 6, if supported (Fin.cons (0 : Fin 4) p) A then physicalMass V p else 0 := by
  unfold maskMass
  rw [label_sum_split]
  have he (r : Fin 4) :
      (∑ p : Label 6, if supported (Fin.cons r p) A then V.labelMass (Fin.cons r p) else 0) =
        if r=0 then (∑ p : Label 6, if supported (Fin.cons (0 : Fin 4) p) A then physicalMass V p else 0) else 0 := by
    by_cases hr : r=0
    · subst r
      simp only [if_true,reference_identity_mass]
    · have hs (p : Label 6) : ¬ supported (Fin.cons r p) A := fun hp => hr (active_reference_zero r p hp)
      simp [hr,hs]
  simp_rw [he]
  simp

theorem active_supported_high_zero (V : Encoder) (p : Label 6)
    (hs : supported (Fin.cons (0 : Fin 4) p) A) (hw : 3 < physicalWeight p) :
    physicalMass V p = 0 := by
  unfold supported at hs
  simp only [decide_eq_true_eq] at hs
  have h0 : p 0=0 := by
    have h := hs ⟨1,by decide⟩
    change p 0=0 ∨ false at h
    exact h.resolve_right (by simp)
  have h1 : p 1=0 := by
    have h := hs ⟨2,by decide⟩
    change p 1=0 ∨ false at h
    exact h.resolve_right (by simp)
  let a : Label 4 := fun i => p ⟨i.val+2,by omega⟩
  have he : p = ![0,0,a 0,a 1,a 2,a 3] := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · rfl
    · rfl
    · rfl
    · rfl
  have hweight : physicalWeight p = activeWeight a := by
    rw [he]
    simp [physicalWeight,activeWeight,Fin.sum_univ_succ]
  have hb := active_weight_bound a
  have ha : activeWeight a=4 := by omega
  have hlabel : Fin.cons (0 : Fin 4) p = activeEmbedding a := by
    rw [he]
    funext i
    fin_cases i <;> rfl
  have hz := active_four_zero V a ha
  rw [← hlabel,reference_identity_mass] at hz
  exact hz

theorem active_mass_upper_bound (V : Encoder) : maskMass V A ≤
    ∑ p : Label 6, if physicalWeight p ≤ 3 then physicalMass V p else 0 := by
  rw [active_projection]
  apply Finset.sum_le_sum
  intro p _
  by_cases hs : supported (Fin.cons (0 : Fin 4) p) A
  · by_cases hw : physicalWeight p ≤ 3
    · simp [hs,hw]
    · have hz := active_supported_high_zero V p hs (by omega)
      simp [hs,hw,hz]
  · by_cases hw : physicalWeight p ≤ 3
    · simpa [hs,hw] using physicalMass_nonneg V p
    · simp [hs,hw]

theorem low_weight_partition (V : Encoder) :
    (∑ p : Label 6, if physicalWeight p ≤ 3 then physicalMass V p else 0) =
      V.A 0 + V.A 1 + V.A 2 + V.A 3 := by
  have hp (w : ℕ) (m : ℝ) : (if w≤3 then m else 0) =
      (if w=0 then m else 0) + (if w=1 then m else 0) +
        (if w=2 then m else 0) + (if w=3 then m else 0) := by
    split_ifs <;> simp_all <;> omega
  simp_rw [hp]
  simp only [Finset.sum_add_distrib]
  rw [← physical_enumerator V 0,← physical_enumerator V 1,
    ← physical_enumerator V 2,← physical_enumerator V 3]

end Orbit2.PhysicalFlatness

namespace Orbit2

/-- The orbit-specific affine plane is proved for every physical Encoder.
No complementary-purity, mass-zero, or frame hypothesis remains. -/
theorem Encoder.flat (V : Encoder) : V.A 1 + V.A 2 + V.A 3 = 1 := by
  have h := PhysicalFlatness.active_mass_upper_bound V
  rw [PhysicalFlatness.active_mass,PhysicalFlatness.low_weight_partition,V.A_zero] at h
  have hs := V.shadow
  linarith

theorem Encoder.enumerator_of_rigidity (V : Encoder) (hz : V.A 3=0) :
    0 ≤ V.A 1 ∧ V.A 1 ≤ 1 ∧ (fun w : Fin 7 => V.A w.val) = enumeratorLine (V.A 1) :=
  V.enumerator_of_A3_zero V.flat hz

end Orbit2
