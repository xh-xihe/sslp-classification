import DyadicLifts.AnchorEq
import DyadicLifts.AnchorLeakage
import DyadicLifts.BellEnum

/-!
# The two-anchor Bell-flag ladder theorem

This module formalizes `dyadic_theorem_lean.tex`, Section 7.

## What is proved completely

* `liftPair_orthonormal` — the dyadic lift sends an orthonormal two-sector SS pair
  to an orthonormal two-sector SS pair.
* `psr_norm0`, `psr_norm1`, `psr_ortho` — every rung codeword is normalized, and the
  two rung codewords are orthogonal.
* `rung_orthonormal_SS` and `rung_diagonal` — **every rung is an orthonormal
  two-sector SS pair carrying the doubled logical diagonal** `diag(1, e^{-2πi/m_r})`.
* `kl_propagation_step` — the full one-step distance-`3` KL propagation, proved by
  the Bell-table split, anchor recursion, buddy uniqueness, and leakage formulas.
* `two_anchor_ladder_KLmat` and `two_anchor_ladder` — the **ladder induction** that
  propagates the distance-`3` KL conditions along every rung.

## Faithful hypotheses

The anchor and positive-phase hypotheses of `Definition (anchor-hypotheses)` are
carried by the structure `AnchorHyp` (with the real anchor coefficients `α₀, β₀`
as explicit positive fields, as the note recommends).  The main theorem
`two_anchor_ladder` takes exactly the paper's hypotheses: strong seed, anchor +
positive phase, normalization, refined SS support, and the seed + first-lift KL
conditions.

The module is fully closed: all matrix-element propagation, including the weight-`≤2`
Bell-table cases, is proved in Lean.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-! ## The lift preserves orthonormal two-sector SS pairs (complete) -/

/-- Orthogonality of the lifted pair: the lifted states sit in disjoint refined blocks. -/
lemma liftPair_ortho {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ) (htot : (∑ i, a i) < 2 * m)
    (ψ₀ ψ₁ : Hil n) (h0 : SuppIn ψ₀ (S0 a m)) (h1 : SuppIn ψ₁ (S1 a m)) :
    ⟪liftVec m a false ψ₀, liftVec m a true ψ₁⟫ = 0 :=
  ss_pair_ortho (m := 2 * m) (by omega)
    (liftVec_S0_residue hm a htot ψ₀ h0) (liftVec_S1_residue hm a htot ψ₁ h1)

/-- **The dyadic lift preserves orthonormal two-sector SS pairs.** -/
theorem liftPair_orthonormal {m : ℕ} (hm : 1 ≤ m) (a : Fin n → ℕ) (htot : (∑ i, a i) < 2 * m)
    (ψ₀ ψ₁ : Hil n) (hn0 : ⟪ψ₀, ψ₀⟫ = 1) (hn1 : ⟪ψ₁, ψ₁⟫ = 1)
    (h0 : SuppIn ψ₀ (S0 a m)) (h1 : SuppIn ψ₁ (S1 a m)) :
    ⟪liftVec m a false ψ₀, liftVec m a false ψ₀⟫ = 1 ∧
      ⟪liftVec m a true ψ₁, liftVec m a true ψ₁⟫ = 1 ∧
      ⟪liftVec m a false ψ₀, liftVec m a true ψ₁⟫ = 0 :=
  ⟨liftVec_norm m a false ψ₀ hn0, liftVec_norm m a true ψ₁ hn1,
    liftPair_ortho hm a htot ψ₀ ψ₁ h0 h1⟩

/-! ## Anchor and positive-phase hypotheses -/

/-- **Definition (Anchor and positive-phase hypotheses).**
The seed `(ψ₀, ψ₁)` has positive real anchor coefficients `α₀, β₀`, with `0ⁿ` the
unique bottom support string of subset sum `0` and `1ⁿ` the unique top support
string of subset sum `2m₀-1`. -/
structure AnchorHyp {n0 : ℕ} (m0 : ℕ) (a0 : Fin n0 → ℕ) (ψ0 ψ1 : Hil n0) where
  α₀ : ℝ
  β₀ : ℝ
  hα : 0 < α₀
  hβ : 0 < β₀
  hcoeff0 : ψ0 (zeros n0) = (α₀ : ℂ)
  hcoeff1 : ψ1 (ones n0) = (β₀ : ℂ)
  hunique0 : ∀ s, ψ0 s ≠ 0 → Asum a0 s = 0 → s = zeros n0
  hunique1 : ∀ s, ψ1 s ≠ 0 → Asum a0 s = 2 * m0 - 1 → s = ones n0

/-! ## First-lift diagonal Bell expansions -/

section AnchorEqTools

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ : Hil n0}

lemma first_lift_II_diag_false :
    mel (psr m0 a0 ψ false 1) (Fin.append (Istr n0) ![SQ.I, SQ.I])
        (psr m0 a0 ψ false 1)
      =
      mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        + mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ) := by
  change
    mel (liftVec m0 a0 false ψ) (Fin.append (Istr n0) ![SQ.I, SQ.I])
        (liftVec m0 a0 false ψ)
      =
      mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        + mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ)
  rw [liftVec_mel_expand]
  simp [mel_II]

lemma first_lift_II_diag_true :
    mel (psr m0 a0 ψ true 1) (Fin.append (Istr n0) ![SQ.I, SQ.I])
        (psr m0 a0 ψ true 1)
      =
      mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        + mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ) := by
  change
    mel (liftVec m0 a0 true ψ) (Fin.append (Istr n0) ![SQ.I, SQ.I])
        (liftVec m0 a0 true ψ)
      =
      mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        + mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ)
  rw [liftVec_mel_expand]
  simp [mel_II]

lemma first_lift_ZZ_diag_false :
    mel (psr m0 a0 ψ false 1) (Fin.append (Istr n0) ![SQ.Z, SQ.Z])
        (psr m0 a0 ψ false 1)
      =
      mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        - mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ) := by
  change
    mel (liftVec m0 a0 false ψ) (Fin.append (Istr n0) ![SQ.Z, SQ.Z])
        (liftVec m0 a0 false ψ)
      =
      mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        - mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ)
  rw [liftVec_mel_expand]
  simp [mel_ZZ]
  ring

lemma first_lift_ZZ_diag_true :
    mel (psr m0 a0 ψ true 1) (Fin.append (Istr n0) ![SQ.Z, SQ.Z])
        (psr m0 a0 ψ true 1)
      =
      - mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        + mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ) := by
  change
    mel (liftVec m0 a0 true ψ) (Fin.append (Istr n0) ![SQ.Z, SQ.Z])
        (liftVec m0 a0 true ψ)
      =
      - mel (piece m0 a0 false ψ) (Istr n0) (piece m0 a0 false ψ)
        + mel (piece m0 a0 true ψ) (Istr n0) (piece m0 a0 true ψ)
  rw [liftVec_mel_expand]
  simp [mel_ZZ]

end AnchorEqTools

section AnchorEquality

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

lemma first_lift_anchor_normsq_eq (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1)) :
    conj ((hanchor.α₀ : ℂ)) * (hanchor.α₀ : ℂ)
      = conj ((hanchor.β₀ : ℂ)) * (hanchor.β₀ : ℂ) := by
  let PII : Fin (n0 + 2) → SQ := Fin.append (Istr n0) ![SQ.I, SQ.I]
  let PZZ : Fin (n0 + 2) → SQ := Fin.append (Istr n0) ![SQ.Z, SQ.Z]
  have hPII : pauliWt PII ≤ 2 := by
    dsimp [PII]
    rw [pauliWt_append, pauliWt_Istr]
    decide
  have hPZZ : pauliWt PZZ ≤ 2 := by
    dsimp [PZZ]
    rw [pauliWt_append, pauliWt_Istr]
    decide
  have hII := KLmat.diag hKL1 (P := PII) hPII
  have hZZ := KLmat.diag hKL1 (P := PZZ) hPZZ
  dsimp [PII, PZZ] at hII hZZ
  rw [first_lift_II_diag_false, first_lift_II_diag_true] at hII
  rw [first_lift_ZZ_diag_false, first_lift_ZZ_diag_true] at hZZ
  set a := mel (piece m0 a0 false ψ0) (Istr n0) (piece m0 a0 false ψ0) with ha
  set b := mel (piece m0 a0 true ψ0) (Istr n0) (piece m0 a0 true ψ0) with hb
  set c := mel (piece m0 a0 false ψ1) (Istr n0) (piece m0 a0 false ψ1) with hc
  set d := mel (piece m0 a0 true ψ1) (Istr n0) (piece m0 a0 true ψ1) with hd
  have had : a = d := by
    have h2 : (2 : ℂ) * a = (2 : ℂ) * d := by
      calc
        (2 : ℂ) * a = (a - b) + (a + b) := by ring
        _ = (-c + d) + (c + d) := by rw [hZZ, hII]
        _ = (2 : ℂ) * d := by ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
  rw [ha, hd] at had
  have hpf : piece m0 a0 false ψ0 = ψ0 (zeros n0) • ket (zeros n0) := by
    simpa [mr, ar, psr] using piece_false_psr_false hss hanchor.hunique0 hsupp0 0
  have hpt : piece m0 a0 true ψ1 = ψ1 (ones n0) • ket (ones n0) := by
    simpa [mr, ar, psr] using piece_true_psr_true hss hanchor.hunique1 hsupp1 0
  rw [hpf, hpt] at had
  rw [mel_Istr, mel_Istr, inn_smul_ket_self, inn_smul_ket_self] at had
  simpa [acoeff0, acoeff1, hanchor.hcoeff0, hanchor.hcoeff1] using had

lemma real_eq_of_complex_normsq_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (h : conj ((α : ℂ)) * (α : ℂ) = conj ((β : ℂ)) * (β : ℂ)) : α = β := by
  have hsq : α ^ 2 = β ^ 2 := by
    have hre := congrArg Complex.re h
    simpa [pow_two] using hre
  nlinarith

lemma first_lift_anchor_eq_real (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1)) :
    hanchor.α₀ = hanchor.β₀ :=
  real_eq_of_complex_normsq_eq hanchor.hα hanchor.hβ
    (first_lift_anchor_normsq_eq hss hanchor hsupp0 hsupp1 hKL1)

lemma acoeff_eq (hss : StrongSeed n0 m0 a0) (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1)) (r : ℕ) :
    acoeff0 m0 a0 ψ0 r = acoeff1 m0 a0 ψ1 r := by
  have hαβ := first_lift_anchor_eq_real hss hanchor hsupp0 hsupp1 hKL1
  induction r with
  | zero =>
      unfold acoeff0 acoeff1
      change ψ0 (zeros n0) = ψ1 (ones n0)
      rw [hanchor.hcoeff0, hanchor.hcoeff1, hαβ]
  | succ r ih =>
      rw [anchor_coeff_succ0 hss r, anchor_coeff_succ1 hss r, ih]

end AnchorEquality

/-! ## Rung-by-rung orthonormality (complete) -/

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

/-- `m_r ≥ 2` along the ladder (from `m₀ ≥ 2`). -/
lemma mr_ge {m0 : ℕ} (hm0 : 2 ≤ m0) (r : ℕ) : 2 ≤ mr m0 r := by
  induction r with
  | zero => exact hm0
  | succ r ih => rw [mr]; omega

/-- Every rung logical-`0` codeword is normalized. -/
lemma psr_norm0 (hn0 : ⟪ψ0, ψ0⟫ = 1) (r : ℕ) :
    ⟪psr m0 a0 ψ0 false r, psr m0 a0 ψ0 false r⟫ = 1 := by
  induction r with
  | zero => exact hn0
  | succ r ih => exact liftVec_norm (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r) ih

/-- Every rung logical-`1` codeword is normalized. -/
lemma psr_norm1 (hn1 : ⟪ψ1, ψ1⟫ = 1) (r : ℕ) :
    ⟪psr m0 a0 ψ1 true r, psr m0 a0 ψ1 true r⟫ = 1 := by
  induction r with
  | zero => exact hn1
  | succ r ih => exact liftVec_norm (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r) ih

/-- The two rung codewords are orthogonal. -/
lemma psr_ortho (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) :
    ⟪psr m0 a0 ψ0 false r, psr m0 a0 ψ1 true r⟫ = 0 :=
  ss_pair_ortho (m := mr m0 r) (mr_ge hss.hm r)
    (psr_supp0 hss hsupp0 r) (psr_supp1 hss hsupp1 r)

/-- **Every rung is an orthonormal two-sector SS pair** for `(m_r, a^{(r)})`. -/
theorem rung_orthonormal_SS (hss : StrongSeed n0 m0 a0)
    (hn0 : ⟪ψ0, ψ0⟫ = 1) (hn1 : ⟪ψ1, ψ1⟫ = 1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) :
    ⟪psr m0 a0 ψ0 false r, psr m0 a0 ψ0 false r⟫ = 1 ∧
      ⟪psr m0 a0 ψ1 true r, psr m0 a0 ψ1 true r⟫ = 1 ∧
      ⟪psr m0 a0 ψ0 false r, psr m0 a0 ψ1 true r⟫ = 0 ∧
      SuppIn (psr m0 a0 ψ0 false r) (S0 (ar m0 a0 r) (mr m0 r)) ∧
      SuppIn (psr m0 a0 ψ1 true r) (S1 (ar m0 a0 r) (mr m0 r)) :=
  ⟨psr_norm0 hn0 r, psr_norm1 hn1 r, psr_ortho hss hsupp0 hsupp1 r,
    psr_supp0 hss hsupp0 r, psr_supp1 hss hsupp1 r⟩

/-- **Every rung carries the doubled logical diagonal** `diag(1, e^{-2πi/m_r})`. -/
theorem rung_diagonal (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) :
    Udiag (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ0 false r) = psr m0 a0 ψ0 false r ∧
      Udiag (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ1 true r)
        = Complex.exp (-(2 * Real.pi * Complex.I / ((mr m0 r : ℕ) : ℂ))) • psr m0 a0 ψ1 true r :=
  ⟨iterated_diagonal_S0 hss hsupp0 r, iterated_diagonal_S1 hss hsupp1 r⟩

/-! ## The distance-`3` KL propagation -/

lemma bottom_anchor_piece (hss : StrongSeed n0 m0 a0) (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ) :
    piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)
      = acoeff0 m0 a0 ψ0 r • ket (zeros (nr n0 r)) := by
  simpa [acoeff0] using piece_false_psr_false hss hanchor.hunique0 hsupp0 r

lemma top_anchor_piece (hss : StrongSeed n0 m0 a0) (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) :
    piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)
      = acoeff1 m0 a0 ψ1 r • ket (ones (nr n0 r)) := by
  simpa [acoeff1] using piece_true_psr_true hss hanchor.hunique1 hsupp1 r

lemma bottom_anchor_to_top_piece_eq_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) (hr : 1 ≤ r) (b : Bool) (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 2) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
      (piece (mr m0 r) (ar m0 a0 r) b (psr m0 a0 ψ1 true r)) = 0 := by
  cases r with
  | zero => omega
  | succ r' =>
      rw [bottom_anchor_piece hss hanchor hsupp0 (r' + 1), mel_smul_left,
        mel_zero_to_top_piece_eq_zero hss hsupp1 r' b A hA]
      simp

lemma bottom_piece_to_top_anchor_eq_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) (hr : 1 ≤ r) (b : Bool) (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 2) :
    mel (piece (mr m0 r) (ar m0 a0 r) b (psr m0 a0 ψ0 false r)) A
      (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) = 0 := by
  cases r with
  | zero => omega
  | succ r' =>
      rw [top_anchor_piece hss hanchor hsupp1 (r' + 1), mel_smul_right,
        mel_bottom_piece_to_one_eq_zero hss hsupp0 r' b A hA]
      simp

lemma bottom_anchor_to_high_eq_zero_wt_le1 (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ) (hr : 1 ≤ r)
    (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 1) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
      (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) = 0 := by
  cases r with
  | zero => omega
  | succ r' =>
      rw [bottom_anchor_piece hss hanchor hsupp0 (r' + 1), mel_smul_left,
        leakage_bottom_wt_le1 hss hsupp0 r' A hA]
      simp

lemma bottom_high_to_anchor_eq_zero_wt_le1 (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ) (hr : 1 ≤ r)
    (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 1) :
    mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
      (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) = 0 := by
  have h :=
    bottom_anchor_to_high_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA
  have hc := mel_conj_symm
      (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
  rw [h, map_zero] at hc
  simpa using hc.symm

lemma top_anchor_to_low_eq_zero_wt_le1 (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) (hr : 1 ≤ r)
    (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 1) :
    mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) A
      (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) = 0 := by
  cases r with
  | zero => omega
  | succ r' =>
      rw [top_anchor_piece hss hanchor hsupp1 (r' + 1), mel_smul_left,
        leakage_top_wt_le1 hss hsupp1 r' A hA]
      simp

lemma top_low_to_anchor_eq_zero_wt_le1 (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) (hr : 1 ≤ r)
    (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 1) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) A
      (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) = 0 := by
  have h :=
    top_anchor_to_low_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA
  have hc := mel_conj_symm
      (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r))
      (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) A
  rw [h, map_zero] at hc
  simpa using hc.symm

lemma anchor_cross_eq_wt_le2 (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) (hr : 1 ≤ r) (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 2) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r))
      + mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      =
        mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r))
      + mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) := by
  cases r with
  | zero => omega
  | succ r' =>
      have hceq :
          acoeff0 m0 a0 ψ0 (r' + 1) = acoeff1 m0 a0 ψ1 (r' + 1) :=
        acoeff_eq hss hanchor hsupp0 hsupp1 hKL1 (r' + 1)
      have hbot := leakage_bottom_wt_le2_formula hss hsupp0 r' A hA
      have htop := leakage_top_wt_le2_formula hss hsupp1 r' A hA
      have hbotR :
          mel (piece (mr m0 (r' + 1)) (ar m0 a0 (r' + 1)) true
              (psr m0 a0 ψ0 false (r' + 1))) A
              (ket (zeros (nr n0 (r' + 1))))
            =
            conj (pauliME A (zeros (nr n0 (r' + 1))) (qbud n0 r')
              * acoeff0 m0 a0 ψ0 (r' + 1)) := by
        have hc := mel_conj_symm
          (ket (zeros (nr n0 (r' + 1))))
          (piece (mr m0 (r' + 1)) (ar m0 a0 (r' + 1)) true
            (psr m0 a0 ψ0 false (r' + 1))) A
        rw [hbot] at hc
        exact hc.symm
      have htopR :
          mel (piece (mr m0 (r' + 1)) (ar m0 a0 (r' + 1)) false
              (psr m0 a0 ψ1 true (r' + 1))) A
              (ket (ones (nr n0 (r' + 1))))
            =
            conj (pauliME A (ones (nr n0 (r' + 1))) (pbud n0 r')
              * acoeff1 m0 a0 ψ1 (r' + 1)) := by
        have hc := mel_conj_symm
          (ket (ones (nr n0 (r' + 1))))
          (piece (mr m0 (r' + 1)) (ar m0 a0 (r' + 1)) false
            (psr m0 a0 ψ1 true (r' + 1))) A
        rw [htop] at hc
        exact hc.symm
      have hcomp := pauliME_ones_pbud_eq_conj_zeros_qbud A hA
      rw [bottom_anchor_piece hss hanchor hsupp0 (r' + 1),
        top_anchor_piece hss hanchor hsupp1 (r' + 1)]
      rw [mel_smul_left, mel_smul_right, mel_smul_right, mel_smul_left]
      rw [hbot, hbotR, htopR, htop, hceq, hcomp]
      simp [map_mul, mul_comm, mul_left_comm, mul_assoc]

lemma offdiag_same_piece_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r))
    (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 2) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r))
      + mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) = 0 := by
  have h := KLmat.offdiag hKL hA
  have hx := piece_add (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ0 false r)
  have hy := piece_add (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ1 true r)
  rw [← hx, ← hy] at h
  simp only [mel_add_left, mel_add_right] at h
  have hz1 := bottom_anchor_to_top_piece_eq_zero hss hanchor hsupp0 hsupp1 r hr false A hA
  have hz2 := bottom_piece_to_top_anchor_eq_zero hss hanchor hsupp0 hsupp1 r hr true A hA
  rw [hz1, hz2] at h
  simpa [add_comm, add_left_comm, add_assoc] using h

lemma anchor_offdiag_eq_zero_wt_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) (hr : 1 ≤ r)
    (A : Fin (nr n0 r) → SQ) (hA0 : pauliWt A = 0) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
      (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) = 0 := by
  have hAid : A = fun _ => SQ.I := (pauliWt_eq_zero_iff A).mp hA0
  rw [bottom_anchor_piece hss hanchor hsupp0 r, top_anchor_piece hss hanchor hsupp1 r,
    hAid, mel_smul_left, mel_smul_right]
  have hne : ones (nr n0 r) ≠ zeros (nr n0 r) := by
    intro h
    have hd : dist (zeros (nr n0 r)) (ones (nr n0 r)) = 0 := by
      rw [h, dist_self]
    rw [dist_zeros_ones] at hd
    have hn0 : 0 < nr n0 r := by
      rw [nr_eq]
      have hn := strongSeed_length hss
      omega
    omega
  rw [mel_ket_ket_gen]
  unfold pauliME
  have hzero :
      (∏ i : Fin (nr n0 r), sqME SQ.I ((zeros (nr n0 r)) i) ((ones (nr n0 r)) i)) = 0 := by
    obtain ⟨i, hi⟩ : ∃ i : Fin (nr n0 r), (zeros (nr n0 r)) i ≠ (ones (nr n0 r)) i := by
      exact Function.ne_iff.mp (Ne.symm hne)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [sqME])
  rw [hzero]
  simp

lemma offdiag_piece_terms_zero_wt_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r))
    (A : Fin (nr n0 r) → SQ) (hA0 : pauliWt A = 0) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) = 0 ∧
      mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) = 0 := by
  have hanchor0 :=
    anchor_offdiag_eq_zero_wt_zero hss hanchor hsupp0 hsupp1 r hr A hA0
  have hsum :=
    offdiag_same_piece_zero hss hanchor hsupp0 hsupp1 r hr hKL A (by omega)
  rw [hanchor0, zero_add] at hsum
  exact ⟨hanchor0, hsum⟩

lemma diag_same_piece_eq (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r))
    (A : Fin (nr n0 r) → SQ) (hA : pauliWt A ≤ 2) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      + mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r))
      =
        mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r))
      + mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) := by
  have h := KLmat.diag hKL hA
  have hx := piece_add (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ0 false r)
  have hy := piece_add (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ1 true r)
  rw [← hx, ← hy] at h
  simp only [mel_add_left, mel_add_right] at h
  have hcross :=
    anchor_cross_eq_wt_le2 hss hanchor hsupp0 hsupp1 hKL1 r hr A hA
  ring_nf at h hcross ⊢
  linear_combination h - hcross

lemma anchor_diag_eq_wt_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) (A : Fin (nr n0 r) → SQ) (hA0 : pauliWt A = 0) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      =
      mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) A
        (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) := by
  have hAid : A = fun _ => SQ.I := (pauliWt_eq_zero_iff A).mp hA0
  have hceq := acoeff_eq hss hanchor hsupp0 hsupp1 hKL1 r
  rw [bottom_anchor_piece hss hanchor hsupp0 r, top_anchor_piece hss hanchor hsupp1 r,
    hAid, mel_smul_left, mel_smul_right, mel_smul_left, mel_smul_right,
    mel_ket_ket_gen, mel_ket_ket_gen, pauliME_identity_self, pauliME_identity_self,
    hceq]

lemma diag_signed_ZZ_piece_eq_wt_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r))
    (A : Fin (nr n0 r) → SQ) (hA0 : pauliWt A = 0) :
    mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      - mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r))
      =
      - mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r))
      + mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) := by
  have hsame :=
    diag_same_piece_eq hss hanchor hsupp0 hsupp1 hKL1 r hr hKL A (by omega)
  have hanch := anchor_diag_eq_wt_zero hss hanchor hsupp0 hsupp1 hKL1 r A hA0
  ring_nf at hsame ⊢
  linear_combination 2 * hanch - hsame

lemma diag_signed_YY_piece_eq_wt_zero (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r))
    (A : Fin (nr n0 r) → SQ) (hA0 : pauliWt A = 0) :
    - mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      + mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r)) A
        (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ0 false r))
      =
      mel (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ1 true r))
      - mel (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) A
          (piece (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) := by
  have hsame :=
    diag_same_piece_eq hss hanchor hsupp0 hsupp1 hKL1 r hr hKL A (by omega)
  have hanch := anchor_diag_eq_wt_zero hss hanchor hsupp0 hsupp1 hKL1 r A hA0
  ring_nf at hsame ⊢
  linear_combination hsame - 2 * hanch

lemma lift_offdiag_zero_for_split (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r))
    (A : Fin (nr n0 r) → SQ) (B : Fin 2 → SQ) (hwt : pauliWt A + pauliWt B ≤ 2) :
    mel (psr m0 a0 ψ0 false (r + 1)) (Fin.append A B)
      (psr m0 a0 ψ1 true (r + 1)) = 0 := by
  have hA2 : pauliWt A ≤ 2 := by omega
  have hsame := offdiag_same_piece_zero hss hanchor hsupp0 hsupp1 r hr hKL A hA2
  have hz1 := bottom_anchor_to_top_piece_eq_zero hss hanchor hsupp0 hsupp1 r hr false A hA2
  have hz2 := bottom_piece_to_top_anchor_eq_zero hss hanchor hsupp0 hsupp1 r hr true A hA2
  change
    mel (liftVec (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      (Fin.append A B)
      (liftVec (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r)) = 0
  rw [liftVec_mel_expand]
  have hwtVec := hwt
  rw [pauli2_eta B] at hwtVec
  rw [pauli2_eta B]
  generalize hB0 : B 0 = B0 at hwtVec ⊢
  generalize hB1 : B 1 = B1 at hwtVec ⊢
  cases B0 <;> cases B1
  · simp [mel_II, hsame]
  · simp [mel_IX, hz1, hz2]
  · simp [mel_IY]
  · simp [mel_IZ]
  · simp [mel_XI, hz1, hz2]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_XX] at hwtVec
      omega
    have hzero := offdiag_piece_terms_zero_wt_zero hss hanchor hsupp0 hsupp1 r hr hKL A hA0
    simp [mel_XX, hzero.1, hzero.2]
  · simp [mel_XY]
  · simp [mel_XZ]
  · simp [mel_YI]
  · simp [mel_YX]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_YY] at hwtVec
      omega
    have hzero := offdiag_piece_terms_zero_wt_zero hss hanchor hsupp0 hsupp1 r hr hKL A hA0
    simp [mel_YY, hzero.1, hzero.2]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_YZ] at hwtVec
      omega
    have hzero := offdiag_piece_terms_zero_wt_zero hss hanchor hsupp0 hsupp1 r hr hKL A hA0
    simp [mel_YZ, hz1, hz2, hzero.1, hzero.2]
  · simp [mel_ZI]
  · simp [mel_ZX]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_ZY] at hwtVec
      omega
    have hzero := offdiag_piece_terms_zero_wt_zero hss hanchor hsupp0 hsupp1 r hr hKL A hA0
    simp [mel_ZY, hz1, hz2, hzero.1, hzero.2]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_ZZ] at hwtVec
      omega
    have hzero := offdiag_piece_terms_zero_wt_zero hss hanchor hsupp0 hsupp1 r hr hKL A hA0
    simp [mel_ZZ, hzero.1, hzero.2]

lemma lift_diag_eq_for_split (hss : StrongSeed n0 m0 a0)
    (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r))
    (A : Fin (nr n0 r) → SQ) (B : Fin 2 → SQ) (hwt : pauliWt A + pauliWt B ≤ 2) :
    mel (psr m0 a0 ψ0 false (r + 1)) (Fin.append A B)
        (psr m0 a0 ψ0 false (r + 1))
      =
      mel (psr m0 a0 ψ1 true (r + 1)) (Fin.append A B)
        (psr m0 a0 ψ1 true (r + 1)) := by
  have hA2 : pauliWt A ≤ 2 := by omega
  have hsame := diag_same_piece_eq hss hanchor hsupp0 hsupp1 hKL1 r hr hKL A hA2
  change
    mel (liftVec (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      (Fin.append A B)
      (liftVec (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r))
      =
    mel (liftVec (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r))
      (Fin.append A B)
      (liftVec (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r))
  rw [liftVec_mel_expand, liftVec_mel_expand]
  have hwtVec := hwt
  rw [pauli2_eta B] at hwtVec
  rw [pauli2_eta B]
  generalize hB0 : B 0 = B0 at hwtVec ⊢
  generalize hB1 : B 1 = B1 at hwtVec ⊢
  cases B0 <;> cases B1
  · simp [mel_II, hsame]
  · have hA1 : pauliWt A ≤ 1 := by
      rw [pauliWt_IX] at hwtVec
      omega
    have hb1 := bottom_anchor_to_high_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have hb2 := bottom_high_to_anchor_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have ht1 := top_low_to_anchor_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    have ht2 := top_anchor_to_low_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    simp [mel_IX, hb1, hb2, ht1, ht2]
  · simp [mel_IY]
  · simp [mel_IZ]
  · have hA1 : pauliWt A ≤ 1 := by
      rw [pauliWt_XI] at hwtVec
      omega
    have hb1 := bottom_anchor_to_high_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have hb2 := bottom_high_to_anchor_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have ht1 := top_low_to_anchor_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    have ht2 := top_anchor_to_low_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    simp [mel_XI, hb1, hb2, ht1, ht2]
  · simp [mel_XX, hsame]
  · simp [mel_XY]
  · simp [mel_XZ]
  · simp [mel_YI]
  · simp [mel_YX]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_YY] at hwtVec
      omega
    have hYY :=
      diag_signed_YY_piece_eq_wt_zero hss hanchor hsupp0 hsupp1 hKL1 r hr hKL A hA0
    simpa [mel_YY, sub_eq_add_neg] using hYY
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_YZ] at hwtVec
      omega
    have hA1 : pauliWt A ≤ 1 := by omega
    have hb1 := bottom_anchor_to_high_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have hb2 := bottom_high_to_anchor_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have ht1 := top_low_to_anchor_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    have ht2 := top_anchor_to_low_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    simp [mel_YZ, hb1, hb2, ht1, ht2]
  · simp [mel_ZI]
  · simp [mel_ZX]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_ZY] at hwtVec
      omega
    have hA1 : pauliWt A ≤ 1 := by omega
    have hb1 := bottom_anchor_to_high_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have hb2 := bottom_high_to_anchor_eq_zero_wt_le1 hss hanchor hsupp0 r hr A hA1
    have ht1 := top_low_to_anchor_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    have ht2 := top_anchor_to_low_eq_zero_wt_le1 hss hanchor hsupp1 r hr A hA1
    simp [mel_ZY, hb1, hb2, ht1, ht2]
  · have hA0 : pauliWt A = 0 := by
      rw [pauliWt_ZZ] at hwtVec
      omega
    have hZZ :=
      diag_signed_ZZ_piece_eq_wt_zero hss hanchor hsupp0 hsupp1 hKL1 r hr hKL A hA0
    simpa [mel_ZZ, sub_eq_add_neg] using hZZ

/-- **Lemma (One-step KL propagation).**
Under the strong-seed, anchor + positive-phase, and first-lift KL hypotheses, if
rung `r ≥ 1` satisfies the weight-`≤2` KL matrix-element conditions, so does rung
`r+1`.

The proof splits the Pauli into its old block and Bell-pair block, dispatches the
six Bell-table cases, and uses the anchor-leakage formula for the only weight-`2`
cross term. -/
theorem kl_propagation_step (hss : StrongSeed n0 m0 a0) (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) (hr : 1 ≤ r)
    (hKL : KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r)) :
    KLmat (psr m0 a0 ψ0 false (r + 1)) (psr m0 a0 ψ1 true (r + 1)) := by
  intro P hP
  let A : Fin (nr n0 r) → SQ := Pl P
  let B : Fin 2 → SQ := Pr P
  have hsplit : Fin.append A B = P := by
    simpa [A, B] using pauliSplit P
  have hwt : pauliWt A + pauliWt B ≤ 2 := by
    have hs := pauliWt_split P
    rw [hs] at hP
    simpa [A, B] using hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsplit]
    exact lift_offdiag_zero_for_split hss hanchor hsupp0 hsupp1 r hr hKL A B hwt
  · rw [← hsplit]
    have h0 := lift_offdiag_zero_for_split hss hanchor hsupp0 hsupp1 r hr hKL A B hwt
    have hc := mel_conj_symm (psr m0 a0 ψ0 false (r + 1))
      (psr m0 a0 ψ1 true (r + 1)) (Fin.append A B)
    rw [h0, map_zero] at hc
    simpa using hc.symm
  · rw [← hsplit]
    exact lift_diag_eq_for_split hss hanchor hsupp0 hsupp1 hKL1 r hr hKL A B hwt

/-- **Two-anchor ladder theorem, KL matrix clause.**
Every rung satisfies the weight-`≤2` KL matrix-element conditions.  This ladder
induction is a genuine proof; it consumes only `kl_propagation_step`. -/
theorem two_anchor_ladder_KLmat (hss : StrongSeed n0 m0 a0) (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL0 : KLmat (psr m0 a0 ψ0 false 0) (psr m0 a0 ψ1 true 0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) :
    KLmat (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r) := by
  induction r with
  | zero => exact hKL0
  | succ r ih =>
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · subst hr0; exact hKL1
      · exact kl_propagation_step hss hanchor hsupp0 hsupp1 hKL1 r hrpos ih

/-- **Theorem (Two-anchor Bell-flag ladder theorem).**
Under the strong-seed, anchor + positive-phase, normalization, refined SS support,
and seed + first-lift KL hypotheses, **every rung satisfies the full distance-`3`
Knill–Laflamme conditions** `KL`.  (The diagonal clause is `rung_diagonal`.) -/
theorem two_anchor_ladder (hss : StrongSeed n0 m0 a0) (hanchor : AnchorHyp m0 a0 ψ0 ψ1)
    (hn0 : ⟪ψ0, ψ0⟫ = 1) (hn1 : ⟪ψ1, ψ1⟫ = 1)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (hKL0 : KLmat (psr m0 a0 ψ0 false 0) (psr m0 a0 ψ1 true 0))
    (hKL1 : KLmat (psr m0 a0 ψ0 false 1) (psr m0 a0 ψ1 true 1))
    (r : ℕ) :
    KL (psr m0 a0 ψ0 false r) (psr m0 a0 ψ1 true r) :=
  ⟨psr_norm0 hn0 r, psr_norm1 hn1 r, psr_ortho hss hsupp0 hsupp1 r,
    two_anchor_ladder_KLmat hss hanchor hsupp0 hsupp1 hKL0 hKL1 r⟩

end Seed

end DyadicLifts
