import DyadicLifts.Lift
import DyadicLifts.Combinatorics

/-!
# The SS-residue and diagonal action of the dyadic lift

This module formalizes `dyadic_theorem_lean.tex`, Section 3:

* `Lemma (Lifted residue computation)` — `Asum_aUp_append`.
* `Theorem (Dyadic lift gives a doubled SS pair and a doubled diagonal)` — the
  lifted codewords land in the refined residue blocks `S₀(a';2m)`, `S₁(a';2m)`,
  and `U_{2m}(a')` acts as the doubled logical diagonal.

This realizes the *phase-lift template* and the order-doubling corollary.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- The subset sum of the two appended tag qubits. -/
lemma Asum_two (m : ℕ) (uv : BitString 2) :
    Asum ![m, m] uv = m * (b2n (uv 0) + b2n (uv 1)) := by
  simp [Asum, Fin.sum_univ_two, mul_add]

/-- **Lemma (Lifted residue computation).** `A_{a'}(s ++ uv) = A_a(s) + m·(u + v)`. -/
lemma Asum_aUp_append (m : ℕ) (a : Fin n → ℕ) (s : BitString n) (uv : BitString 2) :
    Asum (aUp m a) (Fin.append s uv) = Asum a s + m * (b2n (uv 0) + b2n (uv 1)) := by
  rw [aUp, Asum_append, Asum_two]

/-- The same, phrased through the block projections of a general `w`. -/
lemma Asum_aUp (m : ℕ) (a : Fin n → ℕ) (w : BitString (n + 2)) :
    Asum (aUp m a) w = Asum a (bleft w) + m * (b2n (bright w 0) + b2n (bright w 1)) := by
  conv_lhs => rw [← append_bleft_bright w]
  rw [Asum_aUp_append]

/-- **Lemma (Lifted residue computation), bottom-sector residue clause.**
For `s` with `A_a(s) ≡ 0 (mod m)` and a tag pair `uv` carrying the `k = 0` parity
rule `u ⊕ v = h₀(s)`, the dyadically lifted subset sum is `≡ 0 (mod 2m)`.
Together with `Asum_aUp_append` (the integer identity `A_{a'}(s,u,v)=A_a(s)+m(u+v)`)
this is `lem:lifted-residue-computation` for `k = 0`. -/
lemma Asum_aUp_residue_S0 {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) (s : BitString n) (hs : Asum a s % m = 0)
    (uv : BitString 2) (hpar : xor (uv 0) (uv 1) = hibit m a s) :
    Asum (aUp m a) (Fin.append s uv) % (2 * m) = 0 := by
  have hmod : Asum a s % (2 * m) = Asum a s := asum_mod_two_m a htot s
  have hhib : hibit m a s = decide (m ≤ Asum a s) := by rw [hibit, hmod]
  rcases two_value a 0 (by omega) htot s (by simpa using hs) with hval | hval
  · have hib : hibit m a s = false := by rw [hhib, hval, decide_eq_false_iff_not]; omega
    rw [hib] at hpar
    have hsum : b2n (uv 0) + b2n (uv 1) = 0 ∨ b2n (uv 0) + b2n (uv 1) = 2 := by
      revert hpar; cases uv 0 <;> cases uv 1 <;> simp [b2n] <;> omega
    rcases hsum with h | h
    · have key : Asum (aUp m a) (Fin.append s uv) = 0 := by
        rw [Asum_aUp_append, hval, h]; ring
      rw [key]; exact Nat.zero_mod _
    · have key : Asum (aUp m a) (Fin.append s uv) = 2 * m := by
        rw [Asum_aUp_append, hval, h]; ring
      rw [key]; exact Nat.mod_self _
  · have hib : hibit m a s = true := by rw [hhib, hval, decide_eq_true_eq]; omega
    rw [hib] at hpar
    have hsum : b2n (uv 0) + b2n (uv 1) = 1 := by
      revert hpar; cases uv 0 <;> cases uv 1 <;> simp [b2n] <;> omega
    have key : Asum (aUp m a) (Fin.append s uv) = 2 * m := by
      rw [Asum_aUp_append, hval, hsum]; ring
    rw [key]; exact Nat.mod_self _

/-- **Lemma (Lifted residue computation), top-sector residue clause.**
For `s` with `A_a(s) ≡ m-1 (mod m)` and a tag pair `uv` carrying the `k = 1` parity
rule `u ⊕ v = ¬ h₁(s)`, the dyadically lifted subset sum is `≡ 2m-1 (mod 2m)`. -/
lemma Asum_aUp_residue_S1 {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) (s : BitString n) (hs : Asum a s % m = (m - 1) % m)
    (uv : BitString 2) (hpar : xor (uv 0) (uv 1) = !hibit m a s) :
    Asum (aUp m a) (Fin.append s uv) % (2 * m) = 2 * m - 1 := by
  have hmlt : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
  have hmod : Asum a s % (2 * m) = Asum a s := asum_mod_two_m a htot s
  have hhib : hibit m a s = decide (m ≤ Asum a s) := by rw [hibit, hmod]
  rcases two_value a (m - 1) (by omega) htot s (by rw [hs, hmlt]) with hval | hval
  · have hib : hibit m a s = false := by rw [hhib, hval, decide_eq_false_iff_not]; omega
    rw [hib] at hpar; simp only [Bool.not_false] at hpar
    have hsum : b2n (uv 0) + b2n (uv 1) = 1 := by
      revert hpar; cases uv 0 <;> cases uv 1 <;> simp [b2n] <;> omega
    have key : Asum (aUp m a) (Fin.append s uv) = 2 * m - 1 := by
      rw [Asum_aUp_append, hval, hsum]; omega
    rw [key]; exact Nat.mod_eq_of_lt (by omega)
  · have hib : hibit m a s = true := by rw [hhib, hval, decide_eq_true_eq]; omega
    rw [hib] at hpar; simp only [Bool.not_true] at hpar
    have hsum : b2n (uv 0) + b2n (uv 1) = 0 ∨ b2n (uv 0) + b2n (uv 1) = 2 := by
      revert hpar; cases uv 0 <;> cases uv 1 <;> simp [b2n] <;> omega
    rcases hsum with h | h
    · have key : Asum (aUp m a) (Fin.append s uv) = 2 * m - 1 := by
        rw [Asum_aUp_append, hval, h]; omega
      rw [key]; exact Nat.mod_eq_of_lt (by omega)
    · have key : Asum (aUp m a) (Fin.append s uv) = 2 * m + (2 * m - 1) := by
        rw [Asum_aUp_append, hval, h]; omega
      rw [key, Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)

/-- A nonzero Bell-flag amplitude sits on one of the two flag basis strings. -/
lemma bflag_ne_zero_cases (p : Bool) (uv : BitString 2) (h : bflag p uv ≠ 0) :
    uv = bket1 p ∨ uv = bket2 p := by
  by_contra hc
  push_neg at hc
  apply h
  simp [bflag, Pi.smul_apply, Pi.add_apply, ket_apply, hc.1, hc.2]

/-- The lift of an `S₀`-supported codeword lands in the refined bottom block `S₀(a';2m)`. -/
lemma liftVec_S0_residue {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) (ψ : Hil n) (hsupp : SuppIn ψ (S0 a m)) :
    SuppIn (liftVec m a false ψ) (Sres (aUp m a) (2 * m) 0) := by
  intro w hw
  rw [mem_Sres, Nat.zero_mod]
  rw [liftVec, Bool.xor_false] at hw
  have hψ : ψ (bleft w) ≠ 0 := left_ne_zero_of_mul hw
  have hbf : bflag (hibit m a (bleft w)) (bright w) ≠ 0 := right_ne_zero_of_mul hw
  have hsS0 : Asum a (bleft w) % m = 0 := by
    have := hsupp (bleft w) hψ; rwa [mem_S0] at this
  have hmod : Asum a (bleft w) % (2 * m) = Asum a (bleft w) := asum_mod_two_m a htot _
  have hhib : hibit m a (bleft w) = decide (m ≤ Asum a (bleft w)) := by rw [hibit, hmod]
  rcases two_value a 0 (by omega) htot (bleft w) (by simpa using hsS0) with hval | hval
  · -- carry 0: A_a(s) = 0
    have hp : hibit m a (bleft w) = false := by rw [hhib, hval, decide_eq_false_iff_not]; omega
    rw [hp] at hbf
    rcases bflag_ne_zero_cases false (bright w) hbf with huv | huv
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket1 false) 0) + b2n ((bket1 false) 1) = 0 := by decide
      rw [hT, show Asum a (bleft w) + m * 0 = 0 from by omega, Nat.zero_mod]
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket2 false) 0) + b2n ((bket2 false) 1) = 2 := by decide
      rw [hT, show Asum a (bleft w) + m * 2 = 2 * m from by omega, Nat.mod_self]
  · -- carry 1: A_a(s) = m
    have hp : hibit m a (bleft w) = true := by rw [hhib, hval, decide_eq_true_eq]; omega
    rw [hp] at hbf
    rcases bflag_ne_zero_cases true (bright w) hbf with huv | huv
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket1 true) 0) + b2n ((bket1 true) 1) = 1 := by decide
      rw [hT, show Asum a (bleft w) + m * 1 = 2 * m from by omega, Nat.mod_self]
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket2 true) 0) + b2n ((bket2 true) 1) = 1 := by decide
      rw [hT, show Asum a (bleft w) + m * 1 = 2 * m from by omega, Nat.mod_self]

/-- The lift of an `S₁`-supported codeword lands in the refined top block `S₁(a';2m)`. -/
lemma liftVec_S1_residue {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) (ψ : Hil n) (hsupp : SuppIn ψ (S1 a m)) :
    SuppIn (liftVec m a true ψ) (Sres (aUp m a) (2 * m) (2 * m - 1)) := by
  intro w hw
  rw [mem_Sres]
  rw [liftVec, Bool.xor_true] at hw
  have hψ : ψ (bleft w) ≠ 0 := left_ne_zero_of_mul hw
  have hbf : bflag (!hibit m a (bleft w)) (bright w) ≠ 0 := right_ne_zero_of_mul hw
  have hsS1 : Asum a (bleft w) % m = (m - 1) % m := by
    have := hsupp (bleft w) hψ; rwa [mem_S1] at this
  have hmlt : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
  have hmod : Asum a (bleft w) % (2 * m) = Asum a (bleft w) := asum_mod_two_m a htot _
  have hhib : hibit m a (bleft w) = decide (m ≤ Asum a (bleft w)) := by rw [hibit, hmod]
  rcases two_value a (m - 1) (by omega) htot (bleft w) (by rw [hsS1, hmlt]) with hval | hval
  · -- carry 0: A_a(s) = m-1, flag parity !false = true
    have hp : hibit m a (bleft w) = false := by rw [hhib, hval, decide_eq_false_iff_not]; omega
    rw [hp] at hbf; simp only [Bool.not_false] at hbf
    rcases bflag_ne_zero_cases true (bright w) hbf with huv | huv
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket1 true) 0) + b2n ((bket1 true) 1) = 1 := by decide
      rw [hT, show Asum a (bleft w) + m * 1 = 2 * m - 1 from by omega]
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket2 true) 0) + b2n ((bket2 true) 1) = 1 := by decide
      rw [hT, show Asum a (bleft w) + m * 1 = 2 * m - 1 from by omega]
  · -- carry 1: A_a(s) = 2m-1, flag parity !true = false
    have hp : hibit m a (bleft w) = true := by rw [hhib, hval, decide_eq_true_eq]; omega
    rw [hp] at hbf; simp only [Bool.not_true] at hbf
    rcases bflag_ne_zero_cases false (bright w) hbf with huv | huv
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket1 false) 0) + b2n ((bket1 false) 1) = 0 := by decide
      rw [hT, show Asum a (bleft w) + m * 0 = 2 * m - 1 from by omega]
    · rw [Asum_aUp, huv]
      have hT : b2n ((bket2 false) 0) + b2n ((bket2 false) 1) = 2 := by decide
      rw [hT, show Asum a (bleft w) + m * 2 = 2 * m + (2 * m - 1) from by omega, Nat.add_mod_left]

/-! ## The diagonal action of the lift -/

/-- **Phase-lift template / `dyadic-lift-diagonal` (bottom sector).**
`U_{2m}(a')` fixes the lifted logical-`0` state. -/
theorem Udiag_liftVec_S0 {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) (ψ : Hil n) (hsupp : SuppIn ψ (S0 a m)) :
    Udiag (2 * m) (aUp m a) (liftVec m a false ψ) = liftVec m a false ψ :=
  Udiag_S0 (by omega) (aUp m a) (liftVec m a false ψ)
    (liftVec_S0_residue hm a htot ψ hsupp)

/-- **Phase-lift template / `dyadic-lift-diagonal` (top sector).**
`U_{2m}(a')` scales the lifted logical-`1` state by `e^{-2πi/(2m)}`. -/
theorem Udiag_liftVec_S1 {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ)
    (htot : (∑ i, a i) < 2 * m) (ψ : Hil n) (hsupp : SuppIn ψ (S1 a m)) :
    Udiag (2 * m) (aUp m a) (liftVec m a true ψ)
      = Complex.exp (-(2 * Real.pi * Complex.I / ((2 * m : ℕ) : ℂ))) • liftVec m a true ψ :=
  Udiag_S1 (by omega) (aUp m a) (liftVec m a true ψ)
    (liftVec_S1_residue hm a htot ψ hsupp)

end DyadicLifts
