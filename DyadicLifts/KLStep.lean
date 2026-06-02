import DyadicLifts.BellLift
import DyadicLifts.BellEnum
import DyadicLifts.AnchorRecursion
import DyadicLifts.AnchorCoeff
import DyadicLifts.NoSmallWeight
import DyadicLifts.PauliHerm

/-!
# Matrix-element helpers for the KL propagation (Part 1)

Closed building blocks used by `kl_propagation_step`:

* `mel_ket_left`, `mel_ket_right_sum` — expand a matrix element against a basis ket.
* `mel_ket_left_eq_zero`, `mel_ket_right_eq_zero` — vanishing when no support string is
  within Pauli range.
* `dist_zeros_ones`, `pauliME_zeros_ones` — the two anchors are far apart.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- `mel (ket s) A x = ∑_t ⟨s|A|t⟩ x t`. -/
lemma mel_ket_left (s : BitString n) (A : Fin n → SQ) (x : Hil n) :
    mel (ket s) A x = ∑ t, pauliME A s t * x t := by
  rw [mel, inn_ket_left]; rfl

/-- `mel x A (ket t) = ∑_s conj(x s) ⟨s|A|t⟩`. -/
lemma mel_ket_right_sum (x : Hil n) (A : Fin n → SQ) (t : BitString n) :
    mel x A (ket t) = ∑ s, conj (x s) * pauliME A s t :=
  mel_ket_right x A t

/-- General basis matrix element `⟨r|A|t⟩ = pauliME A r t`. -/
lemma mel_ket_ket_gen (r t : BitString n) (A : Fin n → SQ) :
    mel (ket r) A (ket t) = pauliME A r t := by
  rw [mel_ket_left]
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hu; simp [ket_apply, hu]
  · intro h; exact absurd (Finset.mem_univ t) h

/-- If no support string of `x` is within Pauli range of `s`, then `⟨s|A|x⟩ = 0`. -/
lemma mel_ket_left_eq_zero (s : BitString n) (A : Fin n → SQ) (x : Hil n)
    (h : ∀ t, x t ≠ 0 → dist s t > pauliWt A) : mel (ket s) A x = 0 := by
  rw [mel_ket_left]
  apply Finset.sum_eq_zero
  intro t _
  by_cases hx : x t = 0
  · simp [hx]
  · have hd : dist s t > pauliWt A := h t hx
    have : pauliME A s t = 0 := by
      by_contra hp
      exact absurd (dist_le_pauliWt hp) (by omega)
    simp [this]

/-- If no support string of `x` is within Pauli range of `t`, then `⟨x|A|t⟩ = 0`. -/
lemma mel_ket_right_eq_zero (x : Hil n) (A : Fin n → SQ) (t : BitString n)
    (h : ∀ s, x s ≠ 0 → dist s t > pauliWt A) : mel x A (ket t) = 0 := by
  rw [mel_ket_right_sum]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hx : x s = 0
  · simp [hx]
  · have hd : dist s t > pauliWt A := h s hx
    have : pauliME A s t = 0 := by
      by_contra hp
      exact absurd (dist_le_pauliWt hp) (by omega)
    simp [this]

/-- The two anchors are at distance `n`. -/
lemma dist_zeros_ones : dist (zeros n) (ones n) = n := by
  rw [dist]
  have : bxor (zeros n) (ones n) = ones n := by
    funext i; simp [bxor, zeros, ones]
  rw [this, hammingWt_ones]

/-- A masked (piece) amplitude is nonzero only where the original is. -/
lemma piece_ne_zero {m : ℕ} {a : Fin n → ℕ} {b : Bool} {ψ : Hil n} {t : BitString n}
    (h : piece m a b ψ t ≠ 0) : ψ t ≠ 0 := by
  intro h0; apply h; simp [piece, h0]

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

/-- For `r ≥ 1`, every top-sector rung codeword support string has weight `≥ 3`. -/
lemma supp_psr1_wt_ge3 (hss : StrongSeed n0 m0 a0) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r' : ℕ) {t : BitString (nr n0 (r' + 1))}
    (ht : psr m0 a0 ψ1 true (r' + 1) t ≠ 0) : 3 ≤ hammingWt t := by
  by_contra hc
  push_neg at hc
  have hmem : t ∈ S1 (ar m0 a0 (r' + 1)) (mr m0 (r' + 1)) :=
    psr_supp1 hss hsupp1 (r' + 1) t ht
  exact no_small_S1 hss r' t (by omega) hmem

/-- For `r ≥ 1`, every bottom-sector rung codeword support string is at distance `≥ 3`
from the top anchor. -/
lemma supp_psr0_top_ge3 (hss : StrongSeed n0 m0 a0) (hsupp0 : SuppIn ψ0 (S0 a0 m0))
    (r' : ℕ) {s : BitString (nr n0 (r' + 1))}
    (hs : psr m0 a0 ψ0 false (r' + 1) s ≠ 0) : 3 ≤ dist s (ones (nr n0 (r' + 1))) := by
  by_contra hc
  push_neg at hc
  have hmem : s ∈ S0 (ar m0 a0 (r' + 1)) (mr m0 (r' + 1)) :=
    psr_supp0 hss hsupp0 (r' + 1) s hs
  exact no_small_S0_near_top hss r' s (by omega) hmem

/-- A weight-`≤2` Pauli cannot connect the all-zero anchor to any top-sector piece
on a rung after the first lift. -/
lemma mel_zero_to_top_piece_eq_zero (hss : StrongSeed n0 m0 a0)
    (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r' : ℕ) (b : Bool)
    (A : Fin (nr n0 (r' + 1)) → SQ) (hA : pauliWt A ≤ 2) :
    mel (ket (zeros (nr n0 (r' + 1)))) A
      (piece (mr m0 (r' + 1)) (ar m0 a0 (r' + 1)) b
        (psr m0 a0 ψ1 true (r' + 1))) = 0 := by
  apply mel_ket_left_eq_zero
  intro t ht
  have hψ : psr m0 a0 ψ1 true (r' + 1) t ≠ 0 := piece_ne_zero ht
  have hwt : 3 ≤ hammingWt t := supp_psr1_wt_ge3 hss hsupp1 r' hψ
  have hdist0 : dist (zeros (nr n0 (r' + 1))) t = hammingWt t := by
    rw [dist]
    congr 1
    funext i
    simp [bxor, zeros]
  rw [hdist0]
  omega

/-- A weight-`≤2` Pauli cannot connect any bottom-sector piece to the all-one
anchor on a rung after the first lift. -/
lemma mel_bottom_piece_to_one_eq_zero (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r' : ℕ) (b : Bool)
    (A : Fin (nr n0 (r' + 1)) → SQ) (hA : pauliWt A ≤ 2) :
    mel (piece (mr m0 (r' + 1)) (ar m0 a0 (r' + 1)) b
        (psr m0 a0 ψ0 false (r' + 1))) A
      (ket (ones (nr n0 (r' + 1)))) = 0 := by
  apply mel_ket_right_eq_zero
  intro s hs
  have hψ : psr m0 a0 ψ0 false (r' + 1) s ≠ 0 := piece_ne_zero hs
  have hdist : 3 ≤ dist s (ones (nr n0 (r' + 1))) :=
    supp_psr0_top_ge3 hss hsupp0 r' hψ
  omega

end Seed

end DyadicLifts
