import DyadicLifts.Ladder

/-!
# Self-complementarity and the optional binary-dihedral conclusion

This module formalizes `dyadic_theorem_lean.tex`, Section 4:

* `Definition (Self-complementary SS pair)` — `SelfComp`.
* `Lemma (Complement sends the bottom block to the top block)` — `complement_blocks`.
* The transversal bit-flip `X^{⊗n}` acts by `ψ ↦ (s ↦ ψ(s̄))`, and `X^{⊗2}` fixes the
  Bell flags (`papply_Xstring_bflag`), which is what propagates self-complementarity.

The dyadic distance induction does *not* require this symmetry; it is an optional
enhancement of the cyclic-diagonal conclusion.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-! ## Complement and the tensor split -/

lemma bleft_complement {k : ℕ} (w : BitString (n + k)) :
    bleft (complement w) = complement (bleft w) := by
  funext i
  simp [bleft, complement]

lemma bright_complement {k : ℕ} (w : BitString (n + k)) :
    bright (complement w) = complement (bright w) := by
  funext i
  simp [bright, complement]

/-- `b2n(¬b) + b2n(b) = 1`. -/
lemma b2n_not_add (b : Bool) : b2n (!b) + b2n b = 1 := by cases b <;> rfl

/-- **Complement and the subset sum:** `A_a(s̄) + A_a(s) = A_tot`. -/
lemma Asum_complement_add (a : Fin n → ℕ) (s : BitString n) :
    Asum a (complement s) + Asum a s = ∑ i, a i := by
  simp only [Asum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [complement_apply, ← Nat.mul_add, b2n_not_add, mul_one]

/-- **Lemma (Complement sends the bottom block to the top block).**
If `A_tot ≡ -1 (mod m)`, then `s ∈ S₀ ↔ s̄ ∈ S₁`. -/
lemma complement_blocks {m : ℕ} (a : Fin n → ℕ)
    (htot : Nat.ModEq m (∑ i, a i) (m - 1)) (s : BitString n) :
    s ∈ S0 a m ↔ complement s ∈ S1 a m := by
  have hadd : Asum a (complement s) + Asum a s = ∑ i, a i := Asum_complement_add a s
  rw [mem_S0, mem_S1]
  constructor
  · intro h0
    have e2 : Asum a s ≡ 0 [MOD m] := by simp [Nat.ModEq, h0]
    have e1 : Asum a (complement s) + Asum a s ≡ (∑ i, a i) [MOD m] := by rw [hadd]
    calc Asum a (complement s)
        ≡ Asum a (complement s) + Asum a s [MOD m] := by
            rw [show Asum a (complement s) = Asum a (complement s) + 0 from (Nat.add_zero _).symm]
            exact ((Nat.ModEq.refl _).add e2.symm)
      _ ≡ (∑ i, a i) [MOD m] := e1
      _ ≡ m - 1 [MOD m] := htot
  · intro h1
    have hcompl : Asum a (complement s) ≡ m - 1 [MOD m] := h1
    have hce : Asum a (complement s) ≡ (∑ i, a i) [MOD m] := hcompl.trans htot.symm
    have e1 : Asum a (complement s) + Asum a s ≡ (∑ i, a i) + 0 [MOD m] := by rw [hadd, Nat.add_zero]
    have hgoal : Asum a s ≡ 0 [MOD m] := Nat.ModEq.add_left_cancel hce e1
    simpa [Nat.ModEq] using hgoal

/-! ## The carry bit flips under complement in the strong-sum case -/

lemma hibit_complement_of_strong_sum {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (hsum : (∑ i, a i) = 2 * m - 1) (s : BitString n) :
    hibit m a (complement s) = !(hibit m a s) := by
  have htot : (∑ i, a i) < 2 * m := by
    rw [hsum]
    omega
  have hmods : Asum a s % (2 * m) = Asum a s := asum_mod_two_m a htot s
  have hmodc : Asum a (complement s) % (2 * m) = Asum a (complement s) :=
    asum_mod_two_m a htot (complement s)
  have hadd : Asum a (complement s) + Asum a s = 2 * m - 1 := by
    simpa [hsum] using Asum_complement_add a s
  unfold hibit
  rw [hmods, hmodc]
  by_cases hs : m ≤ Asum a s
  · have hc : ¬ m ≤ Asum a (complement s) := by
      intro hc
      omega
    have hsf : decide (m ≤ Asum a s) = true := decide_eq_true hs
    have hcf : decide (m ≤ Asum a (complement s)) = false :=
      decide_eq_false_iff_not.mpr hc
    rw [hsf, hcf]
    rfl
  · have hc : m ≤ Asum a (complement s) := by
      omega
    have hsf : decide (m ≤ Asum a s) = false := decide_eq_false_iff_not.mpr hs
    have hcf : decide (m ≤ Asum a (complement s)) = true := decide_eq_true hc
    rw [hsf, hcf]
    rfl

/-! ## The transversal bit flip `X^{⊗n}` -/

/-- The all-`X` Pauli string `X^{⊗n}`. -/
def Xstring (n : ℕ) : Fin n → SQ := fun _ => SQ.X

/-- The matrix element of `X^{⊗n}`: nonzero (and `= 1`) exactly between complementary strings. -/
lemma pauliME_Xstring (s t : BitString n) :
    pauliME (Xstring n) s t = if t = complement s then 1 else 0 := by
  unfold pauliME Xstring
  by_cases h : t = complement s
  · subst h
    rw [if_pos rfl]
    refine Finset.prod_eq_one ?_
    intro i _
    cases hsi : s i <;> simp [sqME, complement, hsi]
  · rw [if_neg h]
    have hex : ∃ i, t i = s i := by
      by_contra hc
      push_neg at hc
      apply h
      funext i
      have := hc i
      cases hsi : s i <;> cases hti : t i <;> simp_all [complement]
    obtain ⟨i, hi⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [sqME, hi]

/-- `X^{⊗n}` acts by complementing the index: `(X^{⊗n} ψ)(s) = ψ(s̄)`. -/
lemma papply_Xstring (ψ : Hil n) :
    papply (Xstring n) ψ = fun s => ψ (complement s) := by
  funext s
  simp only [papply, pauliME_Xstring]
  rw [Finset.sum_eq_single (complement s)]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The two-qubit complement swaps the Bell-flag basis strings, fixing the flags. -/
lemma bflag_complement (p : Bool) (uv : BitString 2) :
    bflag p (complement uv) = bflag p uv := by
  have h1 : complement (bket1 p) = bket2 p := by cases p <;> (funext i; fin_cases i <;> rfl)
  have h2 : complement (bket2 p) = bket1 p := by cases p <;> (funext i; fin_cases i <;> rfl)
  have hc1 : (complement uv = bket1 p) ↔ (uv = bket2 p) := by
    constructor
    · intro h; rw [← h1, ← h, complement_complement]
    · intro h; rw [h, h2]
  have hc2 : (complement uv = bket2 p) ↔ (uv = bket1 p) := by
    constructor
    · intro h; rw [← h2, ← h, complement_complement]
    · intro h; rw [h, h1]
  simp only [bflag, Pi.smul_apply, Pi.add_apply, ket_apply, hc1, hc2]
  ring_nf

/-- **`X^{⊗2}` fixes each Bell flag.** -/
lemma papply_Xstring_bflag (p : Bool) :
    papply (Xstring 2) (bflag p) = bflag p := by
  rw [papply_Xstring]
  funext uv
  exact bflag_complement p uv

/-! ## Self-complementary pairs -/

/-- **Definition (Self-complementary SS pair):** `ψ₁ = X^{⊗n} ψ₀`. -/
def SelfComp (ψ₀ ψ₁ : Hil n) : Prop := ∀ s, ψ₁ s = ψ₀ (complement s)

/-- `SelfComp` is exactly `ψ₁ = X^{⊗n} ψ₀`. -/
lemma selfComp_iff (ψ₀ ψ₁ : Hil n) :
    SelfComp ψ₀ ψ₁ ↔ ψ₁ = papply (Xstring n) ψ₀ := by
  rw [papply_Xstring]
  constructor
  · intro h; funext s; exact h s
  · intro h s; rw [h]

/-! ## Self-complementarity is preserved by the dyadic Bell lift -/

lemma liftVec_selfComp {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (hsum : (∑ i, a i) = 2 * m - 1) {ψ₀ ψ₁ : Hil n}
    (hsc : SelfComp ψ₀ ψ₁) :
    SelfComp (liftVec m a false ψ₀) (liftVec m a true ψ₁) := by
  intro w
  rw [liftVec, liftVec, bleft_complement, bright_complement, hsc (bleft w),
    Bool.xor_true, Bool.xor_false, hibit_complement_of_strong_sum hm a hsum (bleft w),
    bflag_complement]

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ₀ ψ₁ : Hil n0}

/-- **Iterated self-complementarity:** if the seed pair is self-complementary, every
rung of the dyadic Bell ladder is self-complementary. -/
theorem psr_selfComp (hss : StrongSeed n0 m0 a0) (hsc : SelfComp ψ₀ ψ₁) (r : ℕ) :
    SelfComp (psr m0 a0 ψ₀ false r) (psr m0 a0 ψ₁ true r) := by
  induction r with
  | zero => exact hsc
  | succ r ih =>
      exact liftVec_selfComp
        (m := mr m0 r) (a := ar m0 a0 r)
        (mr_pos (m0 := m0) (by have := hss.hm; omega) r)
        (sum_ar hss r) ih

end Seed

end DyadicLifts
