import DyadicLifts
import Examples.D3.BD16v1

/-!
# An unconditional infinite distance-3 family from the BD16 seed (Tier 3)

This file feeds the concrete `((7,2,3))` BD16 code `BD16v1` (angle vector
`(1,2,2,2,2,3,3)`, `m = 8`) into the abstract two-anchor Bell-flag ladder theorem
`DyadicLifts.two_anchor_ladder`, discharging every hypothesis, to obtain an
**unconditional** statement: every rung of the dyadic Bell ladder over this seed
satisfies the distance-3 Knill–Laflamme conditions.

All Knill–Laflamme facts are verified over the decidable exact field `QSqrt235i`
by `native_decide` and transported to `ℂ` along the embedding `ιK` via the bridge
lemmas `KLmat_of_KLmatK` and `liftVec_bridge` of `DyadicLifts.Bridge`.  Consequently
this result depends additionally on `Lean.ofReduceBool`/`Lean.trustCompiler`.
-/

open DyadicLifts SS

namespace BD16Ladder

/-- Integer angle vector of the seed (in `StrongSeed` form, `∑ = 15 = 2·8-1`). -/
def a0 : Fin 7 → ℕ := ![1, 2, 2, 2, 2, 3, 3]

/-- `|0_L⟩` amplitudes of `BD16v1` over the exact field. -/
def ψ0K : BitString 7 → QSqrt235i := BD16v1.code.amp
/-- `|1_L⟩ = X^{⊗7}|0_L⟩`. -/
def ψ1K : BitString 7 → QSqrt235i := fun s => BD16v1.code.amp (complement s)

/-- The two `ℂ`-valued seed codewords. -/
noncomputable def ψ0 : Hil 7 := fun s => ιK (ψ0K s)
noncomputable def ψ1 : Hil 7 := fun s => ιK (ψ1K s)

/-- Support set of the seed (contains the supports of both codewords). -/
def S7 : Finset (BitString 7) := Finset.univ.filter (fun w => ψ0K w ≠ 0 ∨ ψ1K w ≠ 0)

/-- `|0_L⟩` and `|1_L⟩` of the first dyadic lift (rung 1), over the exact field. -/
def ψ0K1 : BitString (7 + 2) → QSqrt235i := liftVecK 8 a0 false ψ0K
def ψ1K1 : BitString (7 + 2) → QSqrt235i := liftVecK 8 a0 true ψ1K

/-- Support set of the first lift. -/
def S9 : Finset (BitString (7 + 2)) := Finset.univ.filter (fun w => ψ0K1 w ≠ 0 ∨ ψ1K1 w ≠ 0)

/-! ## Small embedding helper -/

lemma ιK_ofRat (q : ℚ) : ιK (QSqrt235i.ofRat q) = (q : ℂ) := by
  show ιC23 (QSqrt23i.ofRat q) + ιC23 0 * s5 = (q : ℂ)
  rw [ιC23_zero, zero_mul, add_zero]
  simp only [ιC23, QSqrt23i.ofRat]; push_cast; ring

lemma ne_zero_of_ψ0 {s} (h : ψ0 s ≠ 0) : ψ0K s ≠ 0 := fun hz => h (by simp [ψ0, hz, ιK_zero])
lemma ne_zero_of_ψ1 {s} (h : ψ1 s ≠ 0) : ψ1K s ≠ 0 := fun hz => h (by simp [ψ1, hz, ιK_zero])

/-! ## Support membership facts (decidable, over the exact field) -/

lemma h0_off_S7 : ∀ s, s ∉ S7 → ψ0K s = 0 := fun s hs => by
  by_contra h; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, Or.inl h⟩)
lemma h1_off_S7 : ∀ s, s ∉ S7 → ψ1K s = 0 := fun s hs => by
  by_contra h; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, Or.inr h⟩)
lemma h0_off_S9 : ∀ w, w ∉ S9 → ψ0K1 w = 0 := fun w hw => by
  by_contra h; exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, Or.inl h⟩)
lemma h1_off_S9 : ∀ w, w ∉ S9 → ψ1K1 w = 0 := fun w hw => by
  by_contra h; exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, Or.inr h⟩)

/-! ## Discharging the hypotheses of `two_anchor_ladder` -/

theorem hss : StrongSeed 7 8 a0 := ⟨by decide, by decide, by decide⟩

theorem hsupp0 : SuppIn ψ0 (S0 a0 8) := by
  have hK : ∀ s, ψ0K s ≠ 0 → Asum a0 s % 8 = 0 := by native_decide
  intro s hs; rw [mem_S0]; exact hK s (ne_zero_of_ψ0 hs)

theorem hsupp1 : SuppIn ψ1 (S1 a0 8) := by
  have hK : ∀ s, ψ1K s ≠ 0 → Asum a0 s % 8 = (8 - 1) % 8 := by native_decide
  intro s hs; rw [mem_S1]; exact hK s (ne_zero_of_ψ1 hs)

theorem hn0 : ⟪ψ0, ψ0⟫ = 1 := by
  have hK : melK S7 ψ0K (Istr 7) ψ0K = 1 := by native_decide
  calc ⟪ψ0, ψ0⟫ = mel ψ0 (Istr 7) ψ0 := (mel_Istr ψ0 ψ0).symm
    _ = ιK (melK S7 ψ0K (Istr 7) ψ0K) := (ιK_melK (Istr 7) h0_off_S7 h0_off_S7).symm
    _ = ιK 1 := by rw [hK]
    _ = 1 := ιK_one

theorem hn1 : ⟪ψ1, ψ1⟫ = 1 := by
  have hK : melK S7 ψ1K (Istr 7) ψ1K = 1 := by native_decide
  calc ⟪ψ1, ψ1⟫ = mel ψ1 (Istr 7) ψ1 := (mel_Istr ψ1 ψ1).symm
    _ = ιK (melK S7 ψ1K (Istr 7) ψ1K) := (ιK_melK (Istr 7) h1_off_S7 h1_off_S7).symm
    _ = ιK 1 := by rw [hK]
    _ = 1 := ιK_one

noncomputable def hanchor : AnchorHyp 8 a0 ψ0 ψ1 where
  α₀ := 1 / 4
  β₀ := 1 / 4
  hα := by norm_num
  hβ := by norm_num
  hcoeff0 := by
    have hK : ψ0K (zeros 7) = QSqrt235i.ofRat (1 / 4) := by native_decide
    show ιK (ψ0K (zeros 7)) = _
    rw [hK, ιK_ofRat]; norm_num
  hcoeff1 := by
    have hK : ψ1K (ones 7) = QSqrt235i.ofRat (1 / 4) := by native_decide
    show ιK (ψ1K (ones 7)) = _
    rw [hK, ιK_ofRat]; norm_num
  hunique0 := by
    have hK : ∀ s, ψ0K s ≠ 0 → Asum a0 s = 0 → s = zeros 7 := by native_decide
    intro s hs; exact hK s (ne_zero_of_ψ0 hs)
  hunique1 := by
    have hK : ∀ s, ψ1K s ≠ 0 → Asum a0 s = 2 * 8 - 1 → s = ones 7 := by native_decide
    intro s hs; exact hK s (ne_zero_of_ψ1 hs)

set_option maxHeartbeats 0 in
theorem hKL0 : KLmat (psr 8 a0 ψ0 false 0) (psr 8 a0 ψ1 true 0) := by
  have hK : KLmatK S7 ψ0K ψ1K := by native_decide
  exact KLmat_of_KLmatK h0_off_S7 h1_off_S7 hK

set_option maxHeartbeats 0 in
theorem hKL1 : KLmat (psr 8 a0 ψ0 false 1) (psr 8 a0 ψ1 true 1) := by
  have e0 : psr 8 a0 ψ0 false 1 = fun w => ιK (ψ0K1 w) := by
    show liftVec 8 a0 false ψ0 = fun w => ιK (ψ0K1 w)
    funext w
    simp only [ψ0, liftVec, ψ0K1, liftVecK, ιK_mul, ιK_bflagK]
  have e1 : psr 8 a0 ψ1 true 1 = fun w => ιK (ψ1K1 w) := by
    show liftVec 8 a0 true ψ1 = fun w => ιK (ψ1K1 w)
    funext w
    simp only [ψ1, liftVec, ψ1K1, liftVecK, ιK_mul, ιK_bflagK]
  rw [e0, e1]
  have hK : KLmatK S9 ψ0K1 ψ1K1 := by native_decide
  exact KLmat_of_KLmatK h0_off_S9 h1_off_S9 hK

/-- **Unconditional distance-3 family.** Every rung of the dyadic Bell ladder built
from the concrete BD16v1 seed satisfies the full distance-3 Knill–Laflamme
conditions. -/
theorem exists_distance3_family (r : ℕ) :
    KL (psr 8 a0 ψ0 false r) (psr 8 a0 ψ1 true r) :=
  two_anchor_ladder hss hanchor hn0 hn1 hsupp0 hsupp1 hKL0 hKL1 r

end BD16Ladder
