import MainTheory.ProbabilityFrames
import MainTheory.SevenQubitExampleData

/-! The actual complex code and its complete distance-two KL certificate. -/
namespace MainTheory.SevenQubitExampleStates

open scoped BigOperators
open MainTheory.SevenQubitExampleData
noncomputable section

def probR (k : Fin 2) (x : SS.BitString 7) : ℝ := (probability k x : ℝ)

theorem probR_nonneg (k : Fin 2) (x : SS.BitString 7) : 0 ≤ probR k x := by
  unfold probR
  exact_mod_cast probability_nonneg k x

theorem probR_sum (k : Fin 2) : ∑ x, probR k x = 1 := by
  unfold probR
  exact_mod_cast probability_sum k

theorem probR_disjoint (k l : Fin 2) (hkl : k ≠ l) (x : SS.BitString 7) :
    probR k x = 0 ∨ probR l x = 0 := by
  rcases probability_disjoint k l hkl x with h | h
  · exact Or.inl (by unfold probR; exact_mod_cast h)
  · exact Or.inr (by unfold probR; exact_mod_cast h)

def state := MainTheory.ProbabilityFrames.state probR
def frame := MainTheory.ProbabilityFrames.frame probR probR_nonneg probR_sum probR_disjoint

theorem normSq_state (k : Fin 2) (x : SS.BitString 7) :
    Complex.normSq (state k x) = probR k x :=
  MainTheory.ProbabilityFrames.state_normSq probR probR_nonneg k x

theorem state_zero (k : Fin 2) (x : SS.BitString 7) :
    state k x = 0 ↔ probability k x = 0 := by
  rw [state, MainTheory.ProbabilityFrames.state_eq_zero probR probR_nonneg]
  exact Rat.cast_eq_zero

theorem star_mul_state (k : Fin 2) (x : SS.BitString 7) :
    star (state k x) * state k x = ((probability k x : ℚ) : ℂ) := by
  change star (Complex.ofReal (Real.sqrt (probR k x))) *
    Complex.ofReal (Real.sqrt (probR k x)) = _
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (probR_nonneg k x)]
  simp [probR]

theorem diagonal_element (z : SS.BitString 7) (k l : Fin 2) :
    SS.innerC (state k) (SS.pauliAct ⟨fun _ => false, z⟩ (state l)) =
      if k = l then ((∑ x, probability k x * character z x : ℚ) : ℂ) else 0 := by
  have hy : (⟨fun _ => false, z⟩ : SS.PauliString 7).numY = 0 := by
    simp [SS.PauliString.numY]
  simp only [SS.innerC, SS.pauliAct, hy, pow_zero, one_mul, SS.bxor_zero]
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    cases hb : SS.bdot z x
    · simpa [SS.signC, character, hb] using star_mul_state k x
    · simpa [SS.signC, character, hb] using congrArg Neg.neg (star_mul_state k x)
  · rw [if_neg hkl]
    apply Finset.sum_eq_zero
    intro x _
    rcases probability_disjoint k l hkl x with hk | hl
    · rw [(state_zero k x).mpr hk, star_zero, zero_mul]
    · rw [(state_zero l x).mpr hl]
      simp [SS.signC]

theorem flip_element (P : SS.PauliString 7) (j : Fin 7)
    (hx : P.x = SS.stdBasis j) (k l : Fin 2) :
    SS.innerC (state k) (SS.pauliAct P (state l)) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rcases single_flip_disjoint k l j x with hk | hl
  · simp only [SS.pauliAct]
    rw [(state_zero k x).mpr hk, star_zero, zero_mul]
  · simp only [SS.pauliAct, hx]
    rw [(state_zero l _).mpr hl]
    simp [SS.signC]

theorem hamming_x_le (P : SS.PauliString 7) : SS.hammingWt P.x ≤ P.wt := by
  apply Finset.card_le_card
  intro j hj
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true] using
    Or.inl (show P.x j = true from by simpa using hj)

theorem hasDistance_two : SS.HasDistance state 2 := by
  intro P hP
  have hx : SS.hammingWt P.x ≤ 1 := le_trans (hamming_x_le P) (by omega)
  rcases mask_low_weight P.x hx with hx0 | ⟨j, hxj⟩
  · have hz : SS.hammingWt P.z ≤ 1 := by
      simpa [SS.hammingWt, SS.PauliString.wt, hx0] using (show P.wt ≤ 1 by omega)
    refine ⟨((∑ x, probability 0 x * character P.z x : ℚ) : ℂ), ?_⟩
    intro k l
    have hPeq : P = ⟨fun _ => false, P.z⟩ := by cases P; simpa using hx0
    rw [hPeq, diagonal_element]
    by_cases hkl : k = l
    · rw [if_pos hkl, if_pos hkl]
      congr 1
      fin_cases k
      · rfl
      · exact (diagonal_low_weight P.z hz).symm
    · rw [if_neg hkl, if_neg hkl]
  · refine ⟨0, fun k l => ?_⟩
    rw [flip_element P j hxj]
    simp

def code : MainTheory.CodeSpec.ExactCode 7 2 2 :=
  ⟨by norm_num, frame, hasDistance_two⟩

theorem zz12_expectations :
    SS.innerC (state 0) (SS.pauliAct zz12 (state 0)) = 1 ∧
      SS.innerC (state 1) (SS.pauliAct zz12 (state 1)) = -1/3 := by
  constructor
  · change SS.innerC (state 0) (SS.pauliAct ⟨fun _ => false, zz12.z⟩ (state 0)) = 1
    rw [diagonal_element, if_pos rfl, zz12_data.2.2.1]
    norm_num
  · change SS.innerC (state 1) (SS.pauliAct ⟨fun _ => false, zz12.z⟩ (state 1)) = -1/3
    rw [diagonal_element, if_pos rfl, zz12_data.2.2.2]
    norm_num

theorem not_hasDistance_three : ¬ SS.HasDistance state 3 := by
  intro h
  obtain ⟨c, hc⟩ := h zz12 (by simpa only [zz12_data.1] using (show 2 ≤ 3 - 1 by decide))
  have h0 := hc 0 0
  have h1 := hc 1 1
  rw [zz12_expectations.1] at h0
  rw [zz12_expectations.2] at h1
  simp only [ite_true] at h0 h1
  norm_num [← h0] at h1

theorem first_moments (k : Fin 2) (j : Fin 7) :
    (∑ x, Complex.normSq (state k x) * (if x j then 1 else 0 : ℝ)) = (mean j : ℝ) := by
  simp_rw [normSq_state]
  unfold probR
  have he := congrArg (fun s : ℚ => (s : ℝ))
    (MainTheory.SevenQubitExampleData.first_moments k j)
  simpa only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_one, Rat.cast_zero] using he

end
end MainTheory.SevenQubitExampleStates
