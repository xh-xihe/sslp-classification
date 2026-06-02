import DyadicLifts.Buddy
import DyadicLifts.KLStep
import DyadicLifts.AnchorCoeff

/-!
# Anchor-leakage formulas

This formalizes the anchor-leakage part of `dyadic_theorem_lean.tex`'s Lemma
*anchor-leakage*: a weight-`≤1` old-block Pauli cannot connect the bottom (resp.
top) anchor to the non-anchor part `u_{r+1}` (resp. `v_{r+1}`), while in the
weight-`≤2` case the unique buddy is the only possible contribution.

* `leakage_bottom_wt_le1` — `⟨0ⁿ|A|u_{r+1}⟩ = 0` for `wt A ≤ 1`.
* `leakage_top_wt_le1` — `⟨1ⁿ|A|v_{r+1}⟩ = 0` for `wt A ≤ 1`.
* `leakage_bottom_wt_le2_formula` and `leakage_top_wt_le2_formula` isolate the
  unique buddy term used in the `B = II` diagonal KL propagation case.

All lemmas in this module are closed Lean proofs.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- `dist (zeros n) t = wt t`. -/
lemma dist_zeros_left (t : BitString n) : dist (zeros n) t = hammingWt t := by
  rw [dist]
  congr 1
  funext i
  simp [bxor, zeros]

/-- Weight of the bottom buddy is `2`. -/
lemma hammingWt_qbud (n0 r : ℕ) : hammingWt (qbud n0 r) = 2 := by
  rw [qbud, hammingWt_append, hammingWt_zeros, hammingWt_ones]

/-- Distance from the top buddy to the top anchor is `2`. -/
lemma dist_pbud_ones (n0 r : ℕ) : dist (pbud n0 r) (ones (nr n0 (r + 1))) = 2 := by
  have ho : (ones (nr n0 (r + 1))) = Fin.append (ones (nr n0 r)) (ones 2) := ones_append
  rw [pbud, ho, dist_append, dist_self]
  rw [zero_add]
  rw [show dist (zeros 2) (ones 2) = hammingWt (ones 2) from dist_zeros_left (ones 2)]
  rw [hammingWt_ones]

lemma pauliME_two_complement_flip (B : Fin 2 → SQ) :
    pauliME B (ones 2) (zeros 2) = conj (pauliME B (zeros 2) (ones 2)) := by
  rw [pauli2_eta B]
  cases B 0 <;> cases B 1 <;>
    simp [pauliME_two, zeros, ones, Complex.conj_I]

lemma pauliME_identity_self (s : BitString n) :
    pauliME (fun _ : Fin n => SQ.I) s s = 1 := by
  unfold pauliME
  apply Finset.prod_eq_one
  intro i _
  simp [sqME]

lemma pauliME_ones_pbud_eq_conj_zeros_qbud
    (A : Fin (nr n0 (r + 1)) → SQ) (hA : pauliWt A ≤ 2) :
    pauliME A (ones (nr n0 (r + 1))) (pbud n0 r)
      = conj (pauliME A (zeros (nr n0 (r + 1))) (qbud n0 r)) := by
  have hzeros : (zeros (nr n0 (r + 1))) =
      Fin.append (zeros (nr n0 r)) (zeros 2) := zeros_append
  have hones : (ones (nr n0 (r + 1))) =
      Fin.append (ones (nr n0 r)) (ones 2) := ones_append
  have hsplit := pauliWt_split A
  rw [← pauliSplit A, hzeros, hones, qbud, pbud, pauliME_append, pauliME_append]
  by_cases hnew : pauliME (Pr A) (zeros 2) (ones 2) = 0
  · have hnew' : pauliME (Pr A) (ones 2) (zeros 2) = 0 := by
      rw [pauliME_two_complement_flip, hnew, map_zero]
    simp [hnew, hnew']
  · have hdist : 2 ≤ pauliWt (Pr A) := by
      have hd := dist_le_pauliWt hnew
      have hzo : dist (zeros 2) (ones 2) = 2 := by
        rw [dist_zeros_left, hammingWt_ones]
      omega
    have hOldWt : pauliWt (Pl A) = 0 := by
      rw [pauliWt_split] at hA
      omega
    have hOld : Pl A = fun _ => SQ.I := (pauliWt_eq_zero_iff (Pl A)).mp hOldWt
    rw [hOld, pauliME_identity_self, pauliME_identity_self,
      pauliME_two_complement_flip]
    simp

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

/-- The bottom buddy coefficient is the next bottom anchor coefficient. -/
lemma piece_true_bottom_qbud_coeff (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) true
        (psr m0 a0 ψ0 false (r + 1)) (qbud n0 r)
      = acoeff0 m0 a0 ψ0 (r + 1) := by
  have hp : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  have hAq : Asum (ar m0 a0 (r + 1)) (qbud n0 r) = mr m0 (r + 1) := by
    rw [qbud]
    change Asum (aUp (mr m0 r) (ar m0 a0 r))
      (Fin.append (zeros (nr n0 r)) (ones 2)) = mr m0 (r + 1)
    rw [Asum_aUp, bleft_append, bright_append, Asum_zeros]
    simp [ones, b2n]
    rw [mr_succ_eq]
    ring
  have hcarry : hibit (mr m0 (r + 1)) (ar m0 a0 (r + 1)) (qbud n0 r) = true := by
    rw [hibit, hAq]
    have hpM : 1 ≤ mr m0 (r + 1) := mr_pos (m0 := m0) (by have := hss.hm; omega) (r + 1)
    have hlt : mr m0 (r + 1) < 2 * mr m0 (r + 1) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact decide_eq_true (by rfl)
  rw [piece, if_pos hcarry, anchor_coeff_succ0 hss r]
  unfold acoeff0 qbud
  change
    liftVec (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)
        (Fin.append (zeros (nr n0 r)) (ones 2))
      =
      psr m0 a0 ψ0 false r (zeros (nr n0 r)) * isqrt2
  rw [liftVec, bleft_append, bright_append, hibit_ar_zeros hss r, Bool.xor_false,
    bflag_false_ones]

/-- The top buddy coefficient is the next top anchor coefficient. -/
lemma piece_false_top_pbud_coeff (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) false
        (psr m0 a0 ψ1 true (r + 1)) (pbud n0 r)
      = acoeff1 m0 a0 ψ1 (r + 1) := by
  have hAt : Asum (ar m0 a0 (r + 1)) (pbud n0 r) = mr m0 (r + 1) - 1 := by
    rw [pbud]
    change Asum (aUp (mr m0 r) (ar m0 a0 r))
      (Fin.append (ones (nr n0 r)) (zeros 2)) = mr m0 (r + 1) - 1
    rw [Asum_aUp, bleft_append, bright_append, Asum_ones, sum_ar hss r]
    simp [zeros, b2n]
    rw [mr_succ_eq]
  have hcarry : hibit (mr m0 (r + 1)) (ar m0 a0 (r + 1)) (pbud n0 r) = false := by
    rw [hibit, hAt]
    have hp : 1 ≤ mr m0 (r + 1) := mr_pos (m0 := m0) (by have := hss.hm; omega) (r + 1)
    have hlt : mr m0 (r + 1) - 1 < 2 * mr m0 (r + 1) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact decide_eq_false_iff_not.mpr (by omega)
  rw [piece, if_pos hcarry, anchor_coeff_succ1 hss r]
  unfold acoeff1 pbud
  change
    liftVec (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)
        (Fin.append (ones (nr n0 r)) (zeros 2))
      =
      psr m0 a0 ψ1 true r (ones (nr n0 r)) * isqrt2
  rw [liftVec, bleft_append, bright_append, hibit_ar_ones hss r, Bool.xor_true,
    Bool.not_true, bflag_false_zeros]

/-- **Bottom leakage formula, weight `≤2`:** only the unique buddy contributes. -/
lemma leakage_bottom_wt_le2_formula (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ) (A : Fin (nr n0 (r + 1)) → SQ)
    (hA : pauliWt A ≤ 2) :
    mel (ket (zeros (nr n0 (r + 1)))) A
        (piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) true
          (psr m0 a0 ψ0 false (r + 1)))
      =
      pauliME A (zeros (nr n0 (r + 1))) (qbud n0 r)
        * acoeff0 m0 a0 ψ0 (r + 1) := by
  rw [mel_ket_left]
  rw [Finset.sum_eq_single (qbud n0 r)]
  · rw [piece_true_bottom_qbud_coeff hss r]
  · intro t _ htq
    by_cases hx :
        piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) true
          (psr m0 a0 ψ0 false (r + 1)) t = 0
    · simp [hx]
    · by_cases hp : pauliME A (zeros (nr n0 (r + 1))) t = 0
      · simp [hp]
      · have hdist : dist (zeros (nr n0 (r + 1))) t ≤ pauliWt A := dist_le_pauliWt hp
        have hwt : hammingWt t ≤ 2 := by
          rw [dist_zeros_left] at hdist
          omega
        have hbud := buddy0 hss hsupp0 r hx hwt
        exact (htq hbud).elim
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- **Top leakage formula, weight `≤2`:** only the unique top buddy contributes. -/
lemma leakage_top_wt_le2_formula (hss : StrongSeed n0 m0 a0)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) (A : Fin (nr n0 (r + 1)) → SQ)
    (hA : pauliWt A ≤ 2) :
    mel (ket (ones (nr n0 (r + 1)))) A
        (piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) false
          (psr m0 a0 ψ1 true (r + 1)))
      =
      pauliME A (ones (nr n0 (r + 1))) (pbud n0 r)
        * acoeff1 m0 a0 ψ1 (r + 1) := by
  rw [mel_ket_left]
  rw [Finset.sum_eq_single (pbud n0 r)]
  · rw [piece_false_top_pbud_coeff hss r]
  · intro t _ htp
    by_cases hx :
        piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) false
          (psr m0 a0 ψ1 true (r + 1)) t = 0
    · simp [hx]
    · by_cases hp : pauliME A (ones (nr n0 (r + 1))) t = 0
      · simp [hp]
      · have hdist : dist (ones (nr n0 (r + 1))) t ≤ pauliWt A := dist_le_pauliWt hp
        have htdist : dist t (ones (nr n0 (r + 1))) ≤ 2 := by
          rw [dist_comm]
          omega
        have hbud := buddy1 hss hsupp1 r hx htdist
        exact (htp hbud).elim
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- **Anchor-leakage vanishing (bottom), weight `≤1`.** -/
lemma leakage_bottom_wt_le1 (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ) (A : Fin (nr n0 (r + 1)) → SQ)
    (hA : pauliWt A ≤ 1) :
    mel (ket (zeros (nr n0 (r + 1)))) A
        (piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) true (psr m0 a0 ψ0 false (r + 1))) = 0 := by
  apply mel_ket_left_eq_zero
  intro t ht
  rcases Nat.lt_or_ge (pauliWt A) (dist (zeros (nr n0 (r + 1))) t) with h | h
  · exact h
  · exfalso
    rw [dist_zeros_left] at h
    have hbud := buddy0 hss hsupp0 r ht (by omega)
    rw [hbud, hammingWt_qbud] at h
    omega

/-- **Anchor-leakage vanishing (top), weight `≤1`.** -/
lemma leakage_top_wt_le1 (hss : StrongSeed n0 m0 a0)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) (A : Fin (nr n0 (r + 1)) → SQ)
    (hA : pauliWt A ≤ 1) :
    mel (ket (ones (nr n0 (r + 1)))) A
        (piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) false (psr m0 a0 ψ1 true (r + 1))) = 0 := by
  apply mel_ket_left_eq_zero
  intro t ht
  rcases Nat.lt_or_ge (pauliWt A) (dist (ones (nr n0 (r + 1))) t) with h | h
  · exact h
  · exfalso
    have hdt : dist t (ones (nr n0 (r + 1))) ≤ 2 := by rw [dist_comm]; omega
    have hbud := buddy1 hss hsupp1 r ht hdt
    rw [dist_comm, hbud, dist_pbud_ones] at h
    omega

end Seed

end DyadicLifts
