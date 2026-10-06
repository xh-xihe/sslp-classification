import MainTheory.Orbit31SupportSemantics

/-! All coordinate faces are encoded, including arbitrary real supports. -/
set_option autoImplicit false
namespace MainTheory.Orbit31SupportMaskEquiv
noncomputable section
open MainTheory.Orbit31SupportSemantics

theorem mask_injective : Function.Injective (fun mask : Fin 65536 => maskSet mask.val) := by
  intro a b he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 16
  · let j : Fin 16 := ⟨k,hk⟩
    change maskSet a.val = maskSet b.val at he
    have hj : j ∈ maskSet a.val ↔ j ∈ maskSet b.val := by rw [he]
    simp only [mem_maskSet] at hj
    exact Bool.eq_iff_iff.mpr hj
  · have hpow : 65536 ≤ 2^k := by
      calc
        65536 = 2^16 := rfl
        _ ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le a.isLt hpow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.isLt hpow)]

theorem mask_surjective : Function.Surjective (fun mask : Fin 65536 => maskSet mask.val) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨mask_injective,?_⟩).2
  norm_num [Fintype.card_finset]

def maskEquiv : Fin 65536 ≃ Finset (Fin 16) :=
  Equiv.ofBijective _ ⟨mask_injective,mask_surjective⟩

theorem real_support_encoded (p : Fin 16 → ℝ) :
    ∃ mask : Fin 65536, MainTheory.MatrixPositiveSupportCertificates.ExactSupport (maskSet mask.val) p := by
  classical
  obtain ⟨mask,hm⟩ := mask_surjective (Finset.univ.filter fun j => 0 < p j)
  change maskSet mask.val = Finset.univ.filter (fun j => 0 < p j) at hm
  refine ⟨mask,?_⟩
  intro j
  rw [hm]
  simp

end
end MainTheory.Orbit31SupportMaskEquiv
