import DyadicLifts.Ladder
import DyadicLifts.AnchorRecursion
import DyadicLifts.SelfComplement

/-!
# No small-weight strings in the opposite residue block

This formalizes `dyadic_theorem_lean.tex`, Section 6:

* `comp_good` — *Component facts for iterated angle vectors*: from rung `1` on,
  every component `x` of `a^{(r)}` satisfies `2x ≤ m_r` and `m₀ ∣ x ∨ x ≤ m₀−2`.
* `no_small_S1` — *No small strings in the top residue block*: for `r ≥ 1` no
  string of Hamming weight `≤ 2` lies in `S₁(a^{(r)}; m_r)`.
* `no_small_S0_near_top` — the complement form: no `S₀` string lies within Hamming
  distance `≤ 2` of `1^{n_r}`.

All lemmas in this module are closed Lean proofs.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- The subset sum is the sum of the angles at the `true` positions. -/
lemma Asum_eq_filter_sum (a : Fin n → ℕ) (t : BitString n) :
    Asum a t = ∑ i ∈ Finset.univ.filter (fun i => t i = true), a i := by
  rw [Asum, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [b2n_eq_ite]
  by_cases h : t i = true <;> simp [h]

/-- If every angle satisfies `2·aⱼ ≤ M`, then `2·A_a(t) ≤ M·wt(t)`. -/
lemma two_Asum_le (a : Fin n → ℕ) (M : ℕ) (hbound : ∀ j, 2 * a j ≤ M) (t : BitString n) :
    2 * Asum a t ≤ M * hammingWt t := by
  rw [Asum, hammingWt_eq_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  have hb := hbound i
  by_cases h : t i = true
  · rw [h]; simp only [b2n_true, mul_one]; omega
  · simp only [Bool.not_eq_true] at h; rw [h]; simp [b2n]

/-- `m₀ ∣ m_r`. -/
lemma m0_dvd_mr (m0 r : ℕ) : m0 ∣ mr m0 r := by
  rw [mr_eq]; exact Dvd.intro_left _ rfl

/-- `m_{r+1} = 2·m_r` (definitional). -/
lemma mr_succ_eq (m0 r : ℕ) : mr m0 (r + 1) = 2 * mr m0 r := rfl

/-- `a^{(r+1)} = (a^{(r)}, m_r, m_r)` (definitional). -/
lemma ar_succ_eq {n0 : ℕ} (m0 : ℕ) (a0 : Fin n0 → ℕ) (r : ℕ) :
    ar m0 a0 (r + 1) = Fin.append (ar m0 a0 r) ![mr m0 r, mr m0 r] := rfl

/-- `2 m₀ ≤ m_{r+1}`. -/
lemma two_mul_m0_le_mr_succ {m0 : ℕ} (r : ℕ) : 2 * m0 ≤ mr m0 (r + 1) := by
  rw [mr_eq, pow_succ]
  have h : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  calc 2 * m0 = 2 ^ 1 * m0 := by ring
    _ ≤ 2 ^ r * 2 * m0 := by
        have h2 : 2 ^ 1 ≤ 2 ^ r * 2 := by rw [pow_one]; nlinarith [h]
        exact Nat.mul_le_mul_right _ h2

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ}

/-- Value of the appended angle vector on an old-block index. -/
lemma ar_succ_left (r : ℕ) (i : Fin (nr n0 r)) :
    ar m0 a0 (r + 1) (Fin.castAdd 2 i) = ar m0 a0 r i := by
  rw [ar_succ_eq]; exact Fin.append_left _ _ i

/-- Value of the appended angle vector on a new-block index. -/
lemma ar_succ_right (r : ℕ) (i : Fin 2) :
    ar m0 a0 (r + 1) (Fin.natAdd (nr n0 r) i) = mr m0 r := by
  rw [ar_succ_eq, Fin.append_right]; fin_cases i <;> rfl

/-- **Component facts (Lemma):** every component of `a^{(r+1)}` is small (`2x ≤ m_{r+1}`)
and is either a multiple of `m₀` or `≤ m₀−2`. -/
lemma comp_good (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    ∀ j : Fin (nr n0 (r + 1)),
      2 * ar m0 a0 (r + 1) j ≤ mr m0 (r + 1) ∧
        (m0 ∣ ar m0 a0 (r + 1) j ∨ ar m0 a0 (r + 1) j ≤ m0 - 2) := by
  induction r with
  | zero =>
      intro j
      have he : ar m0 a0 0 = a0 := rfl
      have he0 : mr m0 0 = m0 := rfl
      have hmsucc : mr m0 1 = 2 * m0 := rfl
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [ar_succ_left, he, hmsucc]
        have hb := hss.hbound i; have hm := hss.hm
        exact ⟨by omega, Or.inr hb⟩
      · rw [ar_succ_right, he0, hmsucc]
        exact ⟨by omega, Or.inl (dvd_refl _)⟩
  | succ r ih =>
      intro j
      have hmsucc : mr m0 (r + 1 + 1) = 2 * mr m0 (r + 1) := mr_succ_eq m0 (r + 1)
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [ar_succ_left, hmsucc]
        obtain ⟨hb, hd⟩ := ih i
        exact ⟨by omega, hd⟩
      · rw [ar_succ_right, hmsucc]
        exact ⟨by omega, Or.inl (m0_dvd_mr m0 (r + 1))⟩

/-- **No small strings in the top block (i):** for `r ≥ 1` (written `r+1`), no string
of Hamming weight `≤ 2` lies in `S₁(a^{(r+1)}; m_{r+1})`. -/
lemma no_small_S1 (hss : StrongSeed n0 m0 a0) (r : ℕ)
    (t : BitString (nr n0 (r + 1))) (hwt : hammingWt t ≤ 2)
    (hmem : t ∈ S1 (ar m0 a0 (r + 1)) (mr m0 (r + 1))) : False := by
  set M := mr m0 (r + 1) with hMdef
  set a := ar m0 a0 (r + 1) with hadef
  have hm0 : 2 ≤ m0 := hss.hm
  have h2m0 : 2 * m0 ≤ M := two_mul_m0_le_mr_succ r
  have hM4 : 4 ≤ M := by omega
  have hdM : m0 ∣ M := by rw [hMdef]; exact m0_dvd_mr m0 (r + 1)
  have hbnd : 2 * Asum a t ≤ M * hammingWt t :=
    two_Asum_le a M (fun j => (comp_good hss r j).1) t
  have hmemv : Asum a t % M = (M - 1) % M := by rw [mem_S1] at hmem; exact hmem
  have hM1mod : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by omega)
  rw [hM1mod] at hmemv
  have hAle : Asum a t ≤ M := by
    have hwt2 : M * hammingWt t ≤ M * 2 := by gcongr
    omega
  have hAeq : Asum a t = M - 1 := by
    rcases lt_or_eq_of_le hAle with hlt | heq
    · rwa [Nat.mod_eq_of_lt hlt] at hmemv
    · exfalso; rw [heq, Nat.mod_self] at hmemv; omega
  rcases Nat.lt_or_ge (hammingWt t) 2 with hlt2 | hge2
  · have hcase : hammingWt t = 0 ∨ hammingWt t = 1 := by omega
    rcases hcase with h | h
    · rw [h] at hbnd; omega
    · rw [h, mul_one] at hbnd; omega
  · have hcard : (Finset.univ.filter (fun i => t i = true)).card = 2 := by
      have hwt2 : hammingWt t = 2 := le_antisymm hwt hge2
      rwa [hammingWt] at hwt2
    obtain ⟨j, k, hjk, hF⟩ := Finset.card_eq_two.mp hcard
    have hAsplit : Asum a t = a j + a k := by
      rw [Asum_eq_filter_sum, hF, Finset.sum_pair hjk]
    rw [hAsplit] at hAeq
    obtain ⟨hbj, hdj⟩ := comp_good hss r j
    obtain ⟨hbk, hdk⟩ := comp_good hss r k
    rw [← hadef] at hbj hdj hbk hdk
    rcases hdj with hdivj | hsmallj <;> rcases hdk with hdivk | hsmallk
    · -- both divisible: m₀ ∣ (a j + a k) and m₀ ∣ M with a j + a k + 1 = M ⟹ m₀ ∣ 1
      have hdsum : m0 ∣ (a j + a k) := dvd_add hdivj hdivk
      have hEq : a j + a k + 1 = M := by omega
      have hd1 : m0 ∣ 1 := by
        have hd : m0 ∣ (a j + a k + 1) := by rw [hEq]; exact hdM
        exact (Nat.dvd_add_right hdsum).mp hd
      have := Nat.le_of_dvd (by norm_num) hd1
      omega
    · -- a j divisible, a k ≤ m₀-2: m₀ ∣ (a k + 1), 0 < a k + 1 ≤ m₀-1
      have hEq : a j + (a k + 1) = M := by omega
      have hdvd_ak1 : m0 ∣ (a k + 1) := by
        have hd : m0 ∣ (a j + (a k + 1)) := by rw [hEq]; exact hdM
        exact (Nat.dvd_add_right hdivj).mp hd
      have := Nat.le_of_dvd (by omega) hdvd_ak1
      omega
    · -- a k divisible, a j ≤ m₀-2
      have hEq : a k + (a j + 1) = M := by omega
      have hdvd_aj1 : m0 ∣ (a j + 1) := by
        have hd : m0 ∣ (a k + (a j + 1)) := by rw [hEq]; exact hdM
        exact (Nat.dvd_add_right hdivk).mp hd
      have := Nat.le_of_dvd (by omega) hdvd_aj1
      omega
    · -- both small: a j + a k ≤ 2(m₀-2) < 2m₀-1 ≤ M-1
      omega

/-- **No small strings near the top anchor (ii):** for `r ≥ 1`, no `S₀` string lies
within Hamming distance `≤ 2` of `1^{n_{r+1}}`. -/
lemma no_small_S0_near_top (hss : StrongSeed n0 m0 a0) (r : ℕ)
    (s : BitString (nr n0 (r + 1))) (hdist : dist s (ones (nr n0 (r + 1))) ≤ 2)
    (hmem : s ∈ S0 (ar m0 a0 (r + 1)) (mr m0 (r + 1))) : False := by
  set M := mr m0 (r + 1) with hMdef
  set a := ar m0 a0 (r + 1) with hadef
  have hm0 : 2 ≤ m0 := hss.hm
  have h2m0 : 2 * m0 ≤ M := two_mul_m0_le_mr_succ r
  have hcompl_mem : complement s ∈ S1 a M := by
    have hmem0 : Asum a s % M = 0 := by rw [mem_S0] at hmem; exact hmem
    have hadd : Asum a (complement s) + Asum a s = ∑ i, a i := Asum_complement_add a s
    have hsum : (∑ i, a i) = 2 * M - 1 := sum_ar hss (r + 1)
    rw [mem_S1]
    have hdvd : M ∣ Asum a s := Nat.dvd_of_mod_eq_zero hmem0
    obtain ⟨q, hq⟩ := hdvd
    have hAs_le : Asum a s ≤ 2 * M - 1 := by
      have := Asum_le_total a s; rw [hsum] at this; exact this
    have hqlt : q < 2 := by
      by_contra hc
      push_neg at hc
      have hmul : M * 2 ≤ M * q := by gcongr
      omega
    rw [Nat.mod_eq_of_lt (show M - 1 < M by omega)]
    interval_cases q
    · rw [Nat.mul_zero] at hq
      have hc : Asum a (complement s) = 2 * M - 1 := by omega
      rw [hc, show 2 * M - 1 = M + (M - 1) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (show M - 1 < M by omega)]
    · rw [Nat.mul_one] at hq
      have hc : Asum a (complement s) = M - 1 := by omega
      rw [hc, Nat.mod_eq_of_lt (show M - 1 < M by omega)]
  have hwt : hammingWt (complement s) ≤ 2 := by
    have hde : dist s (ones (nr n0 (r + 1))) = hammingWt (complement s) := by
      rw [dist, ← complement_eq_bxor_ones]
    rwa [hde] at hdist
  exact no_small_S1 hss r (complement s) hwt hcompl_mem

end Seed

end DyadicLifts
