import DyadicLifts.Ladder
import DyadicLifts.BellLift

/-!
# Anchor recursion and carry structure (toward `kl_propagation_step`)

Structural invariants of the rung codewords needed by the weight-`≤2` KL
propagation:

* `hibit_false_iff_asum_zero` / `hibit_true_iff_asum_top` — on the support the carry
  bit is read off the integer subset sum;
* `anchor_unique_bottom` / `anchor_unique_top` — `0ⁿ`/`1ⁿ` are the unique bottom/top
  support strings of subset sum `0`/`2m_r−1` at every rung.

All lemmas in this module are closed Lean proofs.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

/-- `m_r ≥ 2` along the ladder. -/
lemma mr_two_le {m0 : ℕ} (hm0 : 2 ≤ m0) (r : ℕ) : 2 ≤ mr m0 r := by
  induction r with
  | zero => exact hm0
  | succ r ih => rw [mr]; omega

/-! ## Reading the carry bit off the subset sum -/

/-- On `S₀`, the carry bit `hibit` is `false` iff the integer subset sum is `0`. -/
lemma hibit_false_iff_asum_zero {n m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) {s : BitString n} (hs : Asum a s % m = 0) :
    hibit m a s = false ↔ Asum a s = 0 := by
  have hmod : Asum a s % (2 * m) = Asum a s := asum_mod_two_m a htot s
  rw [hibit, hmod, decide_eq_false_iff_not]
  rcases two_value a 0 (by omega) htot s hs with hval | hval <;> rw [hval] <;> omega

/-- On `S₁`, the carry bit `hibit` is `true` iff the integer subset sum is `2m-1`. -/
lemma hibit_true_iff_asum_top {n m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) {s : BitString n} (hs : Asum a s % m = (m - 1) % m) :
    hibit m a s = true ↔ Asum a s = 2 * m - 1 := by
  have hmod : Asum a s % (2 * m) = Asum a s := asum_mod_two_m a htot s
  have hmlt : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
  rw [hibit, hmod, decide_eq_true_eq]
  rcases two_value a (m - 1) (by omega) htot s (by rw [hs, hmlt]) with hval | hval <;>
    rw [hval] <;> omega

/-- Both tag bits are `false` iff their value-sum is `0`. -/
lemma bright_eq_zeros_of_tag {s : BitString (n + 2)}
    (h : b2n (bright s 0) + b2n (bright s 1) = 0) : bright s = zeros 2 := by
  have h0 : bright s 0 = false ∧ bright s 1 = false := by
    cases ha : bright s 0 <;> cases hb : bright s 1 <;> simp_all [b2n]
  funext i; fin_cases i <;> simp [zeros, h0.1, h0.2]

/-- Both tag bits are `true` iff their value-sum is `2`. -/
lemma bright_eq_ones_of_tag {s : BitString (n + 2)}
    (h : b2n (bright s 0) + b2n (bright s 1) = 2) : bright s = ones 2 := by
  have h0 : bright s 0 = true ∧ bright s 1 = true := by
    cases ha : bright s 0 <;> cases hb : bright s 1 <;> simp_all [b2n]
  funext i; fin_cases i <;> simp [ones, h0.1, h0.2]

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

/-! ## Anchor uniqueness (by induction along the ladder) -/

/-- **Bottom anchor uniqueness:** `0^{n_r}` is the only bottom support string of
integer subset sum `0`. -/
lemma anchor_unique_bottom (hss : StrongSeed n0 m0 a0)
    (hu0 : ∀ s, ψ0 s ≠ 0 → Asum a0 s = 0 → s = zeros n0)
    (r : ℕ) (s : BitString (nr n0 r)) (hs : psr m0 a0 ψ0 false r s ≠ 0)
    (hA : Asum (ar m0 a0 r) s = 0) : s = zeros (nr n0 r) := by
  induction r with
  | zero => exact hu0 s hs hA
  | succ r ih =>
      have hm1 : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
      have hw' : liftVec (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r) s ≠ 0 := hs
      rw [liftVec, Bool.xor_false] at hw'
      have hψ : psr m0 a0 ψ0 false r (bleft s) ≠ 0 := left_ne_zero_of_mul hw'
      have hAsum : Asum (ar m0 a0 (r + 1)) s
          = Asum (ar m0 a0 r) (bleft s)
            + (mr m0 r) * (b2n (bright s 0) + b2n (bright s 1)) :=
        Asum_aUp (mr m0 r) (ar m0 a0 r) s
      rw [hAsum] at hA
      have hbleft0 : Asum (ar m0 a0 r) (bleft s) = 0 := by omega
      have hmt : mr m0 r * (b2n (bright s 0) + b2n (bright s 1)) = 0 := by omega
      have htag0 : b2n (bright s 0) + b2n (bright s 1) = 0 := by
        rcases Nat.mul_eq_zero.mp hmt with h | h
        · omega
        · exact h
      have hbl : bleft s = zeros (nr n0 r) := ih (bleft s) hψ hbleft0
      have hbr : bright s = zeros 2 := bright_eq_zeros_of_tag htag0
      calc s = Fin.append (bleft s) (bright s) := (append_bleft_bright s).symm
        _ = Fin.append (zeros (nr n0 r)) (zeros 2) := by rw [hbl, hbr]
        _ = zeros (nr n0 (r + 1)) := (zeros_append).symm

/-- **Top anchor uniqueness:** `1^{n_r}` is the only top support string of integer
subset sum `2m_r-1`. -/
lemma anchor_unique_top (hss : StrongSeed n0 m0 a0)
    (hu1 : ∀ s, ψ1 s ≠ 0 → Asum a0 s = 2 * m0 - 1 → s = ones n0)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) (s : BitString (nr n0 r)) (hs : psr m0 a0 ψ1 true r s ≠ 0)
    (hA : Asum (ar m0 a0 r) s = 2 * mr m0 r - 1) : s = ones (nr n0 r) := by
  induction r with
  | zero => exact hu1 s hs hA
  | succ r ih =>
      have hm2 : 2 ≤ mr m0 r := mr_two_le hss.hm r
      have hw' : liftVec (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r) s ≠ 0 := hs
      rw [liftVec, Bool.xor_true] at hw'
      have hψ : psr m0 a0 ψ1 true r (bleft s) ≠ 0 := left_ne_zero_of_mul hw'
      have hAsum : Asum (ar m0 a0 (r + 1)) s
          = Asum (ar m0 a0 r) (bleft s)
            + (mr m0 r) * (b2n (bright s 0) + b2n (bright s 1)) :=
        Asum_aUp (mr m0 r) (ar m0 a0 r) s
      have hmr1 : mr m0 (r + 1) = 2 * mr m0 r := rfl
      rw [hAsum, hmr1] at hA
      have hblS1 : Asum (ar m0 a0 r) (bleft s) % (mr m0 r) = (mr m0 r - 1) % (mr m0 r) := by
        have := psr_supp1 hss hsupp1 r (bleft s) hψ; rwa [mem_S1] at this
      have hblval :
          Asum (ar m0 a0 r) (bleft s) = mr m0 r - 1 ∨
            Asum (ar m0 a0 r) (bleft s) = 2 * mr m0 r - 1 := by
        rcases two_value (ar m0 a0 r) (mr m0 r - 1) (by omega) (total_lt_ar hss r) (bleft s)
            (by rw [hblS1, Nat.mod_eq_of_lt (by omega)]) with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have htagle : b2n (bright s 0) + b2n (bright s 1) ≤ 2 := by
        have := b2n_le_one (bright s 0); have := b2n_le_one (bright s 1); omega
      have hbltop : Asum (ar m0 a0 r) (bleft s) = 2 * mr m0 r - 1 ∧
          b2n (bright s 0) + b2n (bright s 1) = 2 := by
        rcases hblval with h | h
        · exfalso
          rw [h] at hA
          have hpos : 0 < mr m0 r := by omega
          have hT : mr m0 r * (b2n (bright s 0) + b2n (bright s 1)) = 3 * mr m0 r := by omega
          have htag3 : b2n (bright s 0) + b2n (bright s 1) = 3 :=
            Nat.eq_of_mul_eq_mul_left hpos (hT.trans (mul_comm 3 (mr m0 r)))
          omega
        · refine ⟨h, ?_⟩
          rw [h] at hA
          have hpos : 0 < mr m0 r := by omega
          have hT : mr m0 r * (b2n (bright s 0) + b2n (bright s 1)) = 2 * mr m0 r := by omega
          exact Nat.eq_of_mul_eq_mul_left hpos (hT.trans (mul_comm 2 (mr m0 r)))
      have hbl : bleft s = ones (nr n0 r) := ih (bleft s) hψ hbltop.1
      have hbr : bright s = ones 2 := bright_eq_ones_of_tag hbltop.2
      calc s = Fin.append (bleft s) (bright s) := (append_bleft_bright s).symm
        _ = Fin.append (ones (nr n0 r)) (ones 2) := by rw [hbl, hbr]
        _ = ones (nr n0 (r + 1)) := (ones_append).symm

/-! ## The carry structure of the rung codewords -/

/-- The all-zero string has carry bit `0`. -/
lemma hibit_ar_zeros (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    hibit (mr m0 r) (ar m0 a0 r) (zeros (nr n0 r)) = false := by
  have hm1 : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  rw [hibit, Asum_zeros, Nat.zero_mod]
  exact decide_eq_false_iff_not.mpr (by omega)

/-- The all-one string has carry bit `1`. -/
lemma hibit_ar_ones (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    hibit (mr m0 r) (ar m0 a0 r) (ones (nr n0 r)) = true := by
  have hm2 : 2 ≤ mr m0 r := mr_two_le hss.hm r
  have hsum : Asum (ar m0 a0 r) (ones (nr n0 r)) = 2 * mr m0 r - 1 := by
    rw [Asum_ones]; exact sum_ar hss r
  rw [hibit, hsum, Nat.mod_eq_of_lt (by omega), decide_eq_true_eq]
  omega

/-- **Carry structure (bottom):** the carry-`0` part of the bottom codeword is exactly
the anchor `α_r |0ⁿ⟩`. -/
lemma piece_false_psr_false (hss : StrongSeed n0 m0 a0)
    (hu0 : ∀ s, ψ0 s ≠ 0 → Asum a0 s = 0 → s = zeros n0)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ) :
    piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)
      = (psr m0 a0 ψ0 false r (zeros (nr n0 r))) • ket (zeros (nr n0 r)) := by
  have hm1 : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  have htot := total_lt_ar hss r
  funext s
  simp only [piece, Pi.smul_apply, smul_eq_mul, ket_apply]
  by_cases hz : s = zeros (nr n0 r)
  · subst hz; rw [hibit_ar_zeros hss r]; simp
  · rw [if_neg hz, mul_zero]
    by_cases hps : psr m0 a0 ψ0 false r s = 0
    · simp [hps]
    · have hsS0 : Asum (ar m0 a0 r) s % (mr m0 r) = 0 := by
        have := psr_supp0 hss hsupp0 r s hps; rwa [mem_S0] at this
      have hhib : hibit (mr m0 r) (ar m0 a0 r) s ≠ false := by
        intro h
        have h0 : Asum (ar m0 a0 r) s = 0 :=
          (hibit_false_iff_asum_zero hm1 (ar m0 a0 r) htot hsS0).mp h
        exact hz (anchor_unique_bottom hss hu0 r s hps h0)
      rw [if_neg hhib]

/-- **Carry structure (top):** the carry-`1` part of the top codeword is exactly the
anchor `β_r |1ⁿ⟩`. -/
lemma piece_true_psr_true (hss : StrongSeed n0 m0 a0)
    (hu1 : ∀ s, ψ1 s ≠ 0 → Asum a0 s = 2 * m0 - 1 → s = ones n0)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) :
    piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)
      = (psr m0 a0 ψ1 true r (ones (nr n0 r))) • ket (ones (nr n0 r)) := by
  have hm1 : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  have htot := total_lt_ar hss r
  funext s
  simp only [piece, Pi.smul_apply, smul_eq_mul, ket_apply]
  by_cases hz : s = ones (nr n0 r)
  · subst hz; rw [hibit_ar_ones hss r]; simp
  · rw [if_neg hz, mul_zero]
    by_cases hps : psr m0 a0 ψ1 true r s = 0
    · simp [hps]
    · have hsS1 : Asum (ar m0 a0 r) s % (mr m0 r) = (mr m0 r - 1) % (mr m0 r) := by
        have := psr_supp1 hss hsupp1 r s hps; rwa [mem_S1] at this
      have hhib : hibit (mr m0 r) (ar m0 a0 r) s ≠ true := by
        intro h
        have htop : Asum (ar m0 a0 r) s = 2 * mr m0 r - 1 :=
          (hibit_true_iff_asum_top hm1 (ar m0 a0 r) htot hsS1).mp h
        exact hz (anchor_unique_top hss hu1 hsupp1 r s hps htop)
      rw [if_neg hhib]

/-- The non-anchor part of the bottom codeword is its carry-`1` piece. -/
lemma piece_true_psr_false_eq (r : ℕ) :
    piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)
      = psr m0 a0 ψ0 false r - piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r) := by
  have := piece_add (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ0 false r)
  funext s
  have h := congrFun this s
  simp only [Pi.add_apply] at h
  simp only [Pi.sub_apply]
  exact eq_sub_of_add_eq' h

/-- The non-anchor part of the top codeword is its carry-`0` piece. -/
lemma piece_false_psr_true_eq (r : ℕ) :
    piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)
      = psr m0 a0 ψ1 true r - piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r) := by
  have := piece_add (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ1 true r)
  funext s
  have h := congrFun this s
  simp only [Pi.add_apply] at h
  simp only [Pi.sub_apply]
  exact eq_sub_of_add_eq h

end Seed

end DyadicLifts
