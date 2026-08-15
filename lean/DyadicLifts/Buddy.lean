import DyadicLifts.NoSmallWeight
import DyadicLifts.AnchorRecursion

/-!
# Unique low-weight buddy strings

This formalizes `dyadic_theorem_lean.tex`'s Lemma *buddy-unique*.

For `r ≥ 1` the carry-`1` part `u_r` of the bottom codeword has a *unique*
weight-`≤2` support string, namely `q_r = 0^{n_r-2}11`; dually the carry-`0` part
`v_r` of the top codeword has a unique support string within distance `2` of the
top anchor, namely `p_r = 1^{n_r-2}00`.

The combinatorial core is `buddy_core`: a weight-`≤2` string with integer subset
sum `m_{r+1}` on rung `r+1` must be `0^{n_r}11`.

All lemmas in this module are closed Lean proofs.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- `Asum a t ≤ wt(t)·(m-1)` when every angle is `≤ m-1`. -/
lemma Asum_le_wt_mul (a : Fin n → ℕ) (m : ℕ) (h : ∀ j, a j ≤ m - 1) (t : BitString n) :
    Asum a t ≤ hammingWt t * (m - 1) := by
  rw [Asum, hammingWt_eq_sum, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro i _
  rw [mul_comm (b2n (t i)) (m - 1)]
  exact Nat.mul_le_mul (h i) (le_refl _)

/-- A weight-zero string is all-zero. -/
lemma hammingWt_zero_eq_zeros {u : BitString n} (h : hammingWt u = 0) : u = zeros n := by
  funext i
  by_contra hi
  have htrue : u i = true := by cases hu : u i <;> simp_all [zeros]
  have hmem : i ∈ (Finset.univ.filter (fun j => u j = true)) := by simp [htrue]
  have hpos : 0 < hammingWt u := by
    rw [hammingWt]; exact Finset.card_pos.mpr ⟨i, hmem⟩
  omega

/-- The tag value-sum equals the tag Hamming weight (for a 2-bit block). -/
lemma tag_sum_eq_wt (w : BitString 2) :
    b2n (w 0) + b2n (w 1) = hammingWt w := by
  rw [hammingWt_eq_sum, Fin.sum_univ_two]

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

/-- **Every component of `a^{(r)}` is `≤ m_r - 1`.** -/
lemma comp_le (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    ∀ j : Fin (nr n0 r), ar m0 a0 r j ≤ mr m0 r - 1 := by
  induction r with
  | zero =>
      intro j
      have he : ar m0 a0 0 = a0 := rfl
      have he0 : mr m0 0 = m0 := rfl
      rw [he, he0]
      have hb := hss.hbound j; have hm := hss.hm; omega
  | succ r ih =>
      intro j
      have hp : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
      have hmsucc : mr m0 (r + 1) = 2 * mr m0 r := mr_succ_eq m0 r
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [ar_succ_left, hmsucc]
        have := ih i; omega
      · rw [ar_succ_right, hmsucc]; omega

/-- **Combinatorial buddy core:** a weight-`≤2` string on rung `r+1` whose integer
subset sum is `m_{r+1}` must be `0^{n_r}11`. -/
lemma buddy_core (hss : StrongSeed n0 m0 a0) (r : ℕ)
    (t : BitString (nr n0 (r + 1)))
    (hA : Asum (ar m0 a0 (r + 1)) t = mr m0 (r + 1))
    (hwt : hammingWt t ≤ 2) :
    t = Fin.append (zeros (nr n0 r)) (ones 2) := by
  have hp : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  have hmsucc : mr m0 (r + 1) = 2 * mr m0 r := mr_succ_eq m0 r
  have hsplit : Asum (ar m0 a0 (r + 1)) t
      = Asum (ar m0 a0 r) (bleft t) + mr m0 r * (b2n (bright t 0) + b2n (bright t 1)) :=
    Asum_aUp (mr m0 r) (ar m0 a0 r) t
  have hwtsplit : hammingWt t = hammingWt (bleft t) + hammingWt (bright t) := by
    conv_lhs => rw [← append_bleft_bright t]
    rw [hammingWt_append]
  have hbwt : hammingWt (bright t) = b2n (bright t 0) + b2n (bright t 1) :=
    (tag_sum_eq_wt (bright t)).symm
  have hALbound : Asum (ar m0 a0 r) (bleft t) ≤ hammingWt (bleft t) * (mr m0 r - 1) :=
    Asum_le_wt_mul (ar m0 a0 r) (mr m0 r) (comp_le hss r) (bleft t)
  set AL := Asum (ar m0 a0 r) (bleft t) with hALdef
  set wL := hammingWt (bleft t) with hwLdef
  set T := b2n (bright t 0) + b2n (bright t 1) with hTdef
  rw [hsplit, hmsucc] at hA
  have hTle : T ≤ 2 := by
    have := b2n_le_one (bright t 0); have := b2n_le_one (bright t 1); omega
  have hgoal : wL = 0 ∧ T = 2 := by
    interval_cases T
    · exfalso
      have hwL2 : wL ≤ 2 := by omega
      have hALle : AL ≤ 2 * (mr m0 r - 1) :=
        le_trans hALbound (Nat.mul_le_mul_right (mr m0 r - 1) hwL2)
      have hlt : 2 * (mr m0 r - 1) < 2 * mr m0 r := by omega
      omega
    · exfalso
      have hwL1 : wL ≤ 1 := by omega
      have hALle : AL ≤ 1 * (mr m0 r - 1) :=
        le_trans hALbound (Nat.mul_le_mul_right (mr m0 r - 1) hwL1)
      omega
    · have hwL0 : wL ≤ 0 := by omega
      exact ⟨by omega, rfl⟩
  have hbl : bleft t = zeros (nr n0 r) := hammingWt_zero_eq_zeros (by rw [← hwLdef]; exact hgoal.1)
  have hbr : bright t = ones 2 := bright_eq_ones_of_tag (by rw [← hTdef]; exact hgoal.2)
  conv_lhs => rw [← append_bleft_bright t]
  rw [hbl, hbr]

/-! ## Carry bridge -/

/-- On the bottom sector, a carry-`true` string has the non-anchor subset sum `m_r`. -/
lemma asum_of_carry_true (hss : StrongSeed n0 m0 a0) (r : ℕ) {s : BitString (nr n0 r)}
    (hsupp : Asum (ar m0 a0 r) s % mr m0 r = 0)
    (hcarry : hibit (mr m0 r) (ar m0 a0 r) s = true) :
    Asum (ar m0 a0 r) s = mr m0 r := by
  have hp : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  have htot := total_lt_ar hss r
  have hne : ¬ (hibit (mr m0 r) (ar m0 a0 r) s = false) := by rw [hcarry]; simp
  rw [hibit_false_iff_asum_zero hp (ar m0 a0 r) htot hsupp] at hne
  rcases two_value (ar m0 a0 r) 0 (by omega) htot s (by simpa using hsupp) with h | h
  · exact absurd h hne
  · simpa using h

/-! ## Buddy strings -/

/-- The rung-`(r+1)` bottom buddy `q = 0^{n_r}11`. -/
def qbud (n0 r : ℕ) : BitString (nr n0 (r + 1)) := Fin.append (zeros (nr n0 r)) (ones 2)

/-- The rung-`(r+1)` top buddy `p = 1^{n_r}00`. -/
def pbud (n0 r : ℕ) : BitString (nr n0 (r + 1)) := Fin.append (ones (nr n0 r)) (zeros 2)

/-- `pbud = complement qbud`. -/
lemma pbud_eq_complement_qbud (n0 r : ℕ) : pbud n0 r = complement (qbud n0 r) := by
  rw [qbud, pbud, complement_append]
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp [complement, zeros, ones, Fin.append_left, Fin.append_right]

/-- **Buddy-uniqueness (bottom):** the only weight-`≤2` support string of the carry-`1`
part `u_{r+1}` of the bottom codeword is `q = 0^{n_r}11`. -/
lemma buddy0 (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ)
    {t : BitString (nr n0 (r + 1))}
    (hu : piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) true (psr m0 a0 ψ0 false (r + 1)) t ≠ 0)
    (hwt : hammingWt t ≤ 2) :
    t = qbud n0 r := by
  rw [piece] at hu
  by_cases hc : hibit (mr m0 (r + 1)) (ar m0 a0 (r + 1)) t = true
  · rw [if_pos hc] at hu
    have hmem : Asum (ar m0 a0 (r + 1)) t % mr m0 (r + 1) = 0 := by
      have := psr_supp0 hss hsupp0 (r + 1) t hu; rwa [mem_S0] at this
    have hA : Asum (ar m0 a0 (r + 1)) t = mr m0 (r + 1) :=
      asum_of_carry_true hss (r + 1) hmem hc
    exact buddy_core hss r t hA hwt
  · simp only [Bool.not_eq_true] at hc
    rw [if_neg (by rw [hc]; simp)] at hu
    exact absurd rfl hu

/-- **Buddy-uniqueness (top):** the only support string of the carry-`0` part `v_{r+1}`
within Hamming distance `2` of the top anchor is `p = 1^{n_r}00`. -/
lemma buddy1 (hss : StrongSeed n0 m0 a0)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ)
    {t : BitString (nr n0 (r + 1))}
    (hv : piece (mr m0 (r + 1)) (ar m0 a0 (r + 1)) false (psr m0 a0 ψ1 true (r + 1)) t ≠ 0)
    (hdist : dist t (ones (nr n0 (r + 1))) ≤ 2) :
    t = pbud n0 r := by
  set M := mr m0 (r + 1) with hMdef
  set a := ar m0 a0 (r + 1) with hadef
  have hp : 1 ≤ M := mr_pos (m0 := m0) (by have := hss.hm; omega) (r + 1)
  have htot := total_lt_ar hss (r + 1)
  rw [piece] at hv
  by_cases hc : hibit M a t = false
  · rw [if_pos hc] at hv
    have hmem : Asum a t % M = (M - 1) % M := by
      have := psr_supp1 hss hsupp1 (r + 1) t hv; rwa [mem_S1] at this
    have hmlt : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by omega)
    have hAt : Asum a t = M - 1 := by
      rw [hmlt] at hmem
      rcases two_value a (M - 1) (by omega) htot t hmem
        with h | h
      · exact h
      · exfalso
        have hcarry : hibit M a t = true := by
          rw [hibit, asum_mod_two_m a htot t, h]
          exact decide_eq_true (by omega)
        rw [hc] at hcarry; exact absurd hcarry (by simp)
    have hcompl_A : Asum a (complement t) = M := by
      have hadd : Asum a (complement t) + Asum a t = ∑ i, a i := Asum_complement_add a t
      have hsum : (∑ i, a i) = 2 * M - 1 := sum_ar hss (r + 1)
      omega
    have hcompl_wt : hammingWt (complement t) ≤ 2 := by
      have hde : dist t (ones (nr n0 (r + 1))) = hammingWt (complement t) := by
        rw [dist, ← complement_eq_bxor_ones]
      rw [hde] at hdist; exact hdist
    have hcq : complement t = qbud n0 r := buddy_core hss r (complement t) hcompl_A hcompl_wt
    rw [pbud_eq_complement_qbud, ← hcq, complement_complement]
  · simp only [Bool.not_eq_false] at hc
    rw [if_neg (by rw [hc]; simp)] at hv
    exact absurd rfl hv

end Seed

end DyadicLifts
