import SixQubit.MacWilliams
import SixQubit.ShadowTwisted

/-! # Label-sensitive scalar identities for a chosen logical involution

These identities concern actual complex state vectors. They are independent
of amplitudes, normalization, stabilizer assumptions and scalar LP payloads.
-/

namespace SixQubit.ParityPauliScalars

open SS.MacWilliams SS.Shadow SS.ShadowTwisted

noncomputable section

variable {n : ℕ}

theorem chi_bdot (u v : SS.BitString n) :
    chi u v = if SS.bdot u v then -1 else 1 := by
  have h := signC_bdot u v (1 : ℂ)
  cases hb : SS.bdot u v
  · simp only [hb, SS.signC_false, mul_one] at h
    exact (Complex.ofReal_inj.mp h).symm
  · simp only [hb, SS.signC_true, mul_one] at h
    have hc : ((-1 : ℝ) : ℂ) = (chi u v : ℂ) := by simpa using h
    exact (Complex.ofReal_inj.mp hc).symm

def logicalSign (k : Fin 2) : ℝ := if k = 0 then 1 else -1

def Supported (mask : SS.BitString n) (sign : ℝ) (u : SS.State n ℂ) : Prop :=
  ∀ s, chi mask s ≠ sign → u s = 0

def ParityPair (mask : SS.BitString n) (psi : Fin 2 → SS.State n ℂ) : Prop :=
  ∀ k, Supported mask (logicalSign k) (psi k)

theorem mel_zshift {mask : SS.BitString n} {u v : SS.State n ℂ}
    {sign : ℝ} (hv : Supported mask sign v) (x z : SS.BitString n) :
    mel u v ⟨x, SS.bxor z mask⟩ = (sign : ℂ) * mel u v ⟨x,z⟩ := by
  classical
  unfold mel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : chi mask s = sign
  · rw [chi_bxor_left, hs]
    push_cast
    ring
  · simp [hv s hs]

theorem mel_zero {mask : SS.BitString n} {u v : SS.State n ℂ}
    {a b : ℝ} (hu : Supported mask a u) (hv : Supported mask b v)
    (P : SS.PauliString n) (hab : a ≠ b * chi mask P.x) :
    mel u v P = 0 := by
  classical
  unfold mel
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : chi mask s = b
  · have ht : chi mask (SS.bxor s P.x) ≠ a := by
      rw [chi_bxor_right, hs]
      exact Ne.symm hab
    simp [hu _ ht]
  · simp [hv s hs]

theorem offdiag_zero {mask : SS.BitString n} {psi : Fin 2 → SS.State n ℂ}
    (h : ParityPair mask psi) (P : SS.PauliString n) (hc : chi mask P.x = 1) :
    mel (psi 0) (psi 1) P = 0 ∧ mel (psi 1) (psi 0) P = 0 := by
  constructor
  · apply mel_zero (h 0) (h 1) P
    norm_num [logicalSign, hc]
  · apply mel_zero (h 1) (h 0) P
    norm_num [logicalSign, hc]

theorem diagonal_zero {mask : SS.BitString n} {psi : Fin 2 → SS.State n ℂ}
    (h : ParityPair mask psi) (P : SS.PauliString n) (hc : chi mask P.x = -1) :
    ∀ k, mel (psi k) (psi k) P = 0 := by
  intro k
  apply mel_zero (h k) (h k) P
  fin_cases k <;> norm_num [logicalSign, hc]

theorem odd_trace_zero {mask : SS.BitString n} {psi : Fin 2 → SS.State n ℂ}
    (h : ParityPair mask psi) (P : SS.PauliString n) (hc : chi mask P.x = -1) :
    trProj psi P = 0 := by
  rw [trProj_eq]
  simp [melTr, diagonal_zero h P hc]

/-- `b_E = a_E + a_DE` in the unnormalized trace/Frobenius convention. -/
theorem diagonal_relation {mask : SS.BitString n} {psi : Fin 2 → SS.State n ℂ}
    (h : ParityPair mask psi) (P : SS.PauliString n) (hc : chi mask P.x = 1) :
    2 * frob psi P = Complex.normSq (trProj psi P) +
      Complex.normSq (trProj psi ⟨P.x, SS.bxor P.z mask⟩) := by
  obtain ⟨h01, h10⟩ := offdiag_zero h P hc
  have h0 := mel_zshift (u := psi 0) (h 0) P.x P.z
  have h1 := mel_zshift (u := psi 1) (h 1) P.x P.z
  have hs0 : (logicalSign 0 : ℂ) = 1 := by norm_num [logicalSign]
  have hs1 : (logicalSign 1 : ℂ) = -1 := by norm_num [logicalSign]
  rw [hs0, one_mul] at h0
  rw [hs1, neg_one_mul] at h1
  simp only [frob, normSq_innerC, Fin.sum_univ_two, h01, h10,
    Complex.normSq_zero, add_zero, zero_add, normSq_trProj, melTr, h0, h1]
  rw [← sub_eq_add_neg, Complex.normSq_add, Complex.normSq_sub]
  ring

theorem TfT_eq_swapped (psi : Fin 2 → SS.State n ℂ)
    (ex ez : SS.BitString n) (a b : Fin 2) :
    TfT psi ex ez a b = (psignT ez (SS.complement ex) : ℂ) * TfT psi ex ez b a := by
  classical
  have hc (s : SS.BitString n) :
      SS.complement (SS.bxor (SS.bxor s (SS.complement ex)) ex) = s := by
    funext i
    simp only [SS.complement, SS.bxor_apply]
    cases s i <;> cases ex i <;> rfl
  have hb (s : SS.BitString n) :
      SS.bxor s (SS.complement ex) = SS.complement (SS.bxor s ex) := by
    funext i
    simp only [SS.complement, SS.bxor_apply]
    cases s i <;> cases ex i <;> rfl
  unfold TfT
  rw [← sum_bxor_reindex (SS.complement ex), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [hc, psignT_bxor, hb]
  push_cast
  ring

theorem TfT_diagonal_zero (psi : Fin 2 → SS.State n ℂ)
    (ex ez : SS.BitString n) (hs : psignT ez (SS.complement ex) = -1) (a : Fin 2) :
    TfT psi ex ez a a = 0 := by
  have h := TfT_eq_swapped psi ex ez a a
  rw [hs] at h
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] at h
  have hsum : TfT psi ex ez a a + TfT psi ex ez a a = 0 := by
    linear_combination h
  exact (add_self_eq_zero.mp hsum)

theorem TfT_offdiag_zero {mask : SS.BitString n} {psi : Fin 2 → SS.State n ℂ}
    (h : ParityPair mask psi) (ex ez : SS.BitString n)
    (hc : chi mask (SS.complement ex) = 1) (a b : Fin 2) (hab : a ≠ b) :
    TfT psi ex ez a b = 0 := by
  classical
  have hb (s : SS.BitString n) :
      SS.complement (SS.bxor s ex) = SS.bxor s (SS.complement ex) := by
    funext i
    simp only [SS.complement, SS.bxor_apply]
    cases s i <;> cases ex i <;> rfl
  unfold TfT
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : chi mask s = logicalSign a
  · have ht : chi mask (SS.complement (SS.bxor s ex)) ≠ logicalSign b := by
      rw [hb, chi_bxor_right, hs, hc, mul_one]
      fin_cases a <;> fin_cases b <;> norm_num [logicalSign] at *
    rw [h b _ ht]
    simp
  · simp [h a s hs]

/-- Label-sensitive shadow zero, with explicit algebraic sign hypotheses. -/
theorem shadow_zero {mask : SS.BitString n} {psi : Fin 2 → SS.State n ℂ}
    (h : ParityPair mask psi) (E : SS.PauliString n)
    (hc : chi mask (SS.complement E.x) = 1)
    (hs : psignT E.z (SS.complement E.x) = -1) :
    (∑ P : SS.PauliString n,
      (-1 : ℝ) ^ P.wt * pairSign E P * Complex.normSq (trProj psi P)) = 0 := by
  have hz (a b : Fin 2) : TfT psi E.x E.z a b = 0 := by
    by_cases hab : a = b
    · subst b
      exact TfT_diagonal_zero psi E.x E.z hs a
    · exact TfT_offdiag_zero h E.x E.z hc a b hab
  have ht := altT_sum_eq_coreT psi E
  rw [coreT_eq_sum_normSq] at ht
  simp only [hz, Complex.normSq_zero, Complex.ofReal_zero,
    Finset.sum_const_zero, mul_zero] at ht
  rw [← Complex.ofReal_sum] at ht
  exact Complex.ofReal_inj.mp ht

end
end SixQubit.ParityPauliScalars
