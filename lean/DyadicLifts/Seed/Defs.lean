import DyadicLifts.Bridge
import SS.ZSeedKL
import SS.PauliSites

/-!
# The seed of the dyadic Bell ladder: definitions

`Examples.D3.BD16Ladder` instantiates the two-anchor ladder theorem on the
`((7,2,3))` code `BD16v1` of arXiv:2504.20847 and closes its finite checks with
`native_decide`, which adds `Lean.ofReduceBool` and `Lean.trustCompiler` to the
axiom set.  This file proves the same statements with no compiled evaluation:
the amplitudes are carried as elements of `ℤ[√2,√3,√5,i]` scaled by a single
rational factor, and every finite check is decided by the kernel on the integer
side and transported back by `SS.ZSeedKL`.

The seed is

```
4·|0_L⟩ = |0000000⟩ + √3|0111100⟩ + √3|1001110⟩ + √2|1010101⟩
        + √2|1011001⟩ + |1110010⟩ + 2i|0100011⟩,
```

with angle vector `a = (1,2,2,2,2,3,3)` and modulus `m = 8`, and
`|1_L⟩ = X^{⊗7}|0_L⟩`.  The scale is `q = 1/4` at the seed and `q = 1/8` after
the lift, which appends a Bell pair carrying a factor `1/√2 = (√2)/2`.

The resulting `exists_distance3_family` has the same statement as the one in
`BD16Ladder` and depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

open DyadicLifts SS SS.ZSqrt235i

namespace BD16Kernel

/-- A seven-bit string written out bit by bit.  Inlined here so that the seed
does not depend on the SSLP verification stack for one helper. -/
def bs7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : BitString 7 :=
  ![b0, b1, b2, b3, b4, b5, b6]

/-! ## The seed over the integer ring -/

/-- Integer angle vector of the seed (`∑ = 15 = 2·8 − 1`). -/
def a0 : Fin 7 → ℕ := ![1, 2, 2, 2, 2, 3, 3]

def zR2 : ZSqrt235i := ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ZSqrt23i.zero⟩
def zR3 : ZSqrt235i := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0⟩, ZSqrt23i.zero⟩
def z2i : ZSqrt235i := ⟨⟨0, 0, 0, 0, 2, 0, 0, 0⟩, ZSqrt23i.zero⟩
def sqrt2Z : ZSqrt235i := ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ZSqrt23i.zero⟩

/-- `4·|0_L⟩`. -/
def ψ0Z : BitString 7 → ZSqrt235i := fun x =>
  if x = bs7 false false false false false false false then one
  else if x = bs7 false true  true  true  true  false false then zR3
  else if x = bs7 true  false false true  true  true  false then zR3
  else if x = bs7 true  false true  false true  false true  then zR2
  else if x = bs7 true  false true  true  false false true  then zR2
  else if x = bs7 true  true  true  false false true  false then one
  else if x = bs7 false true  false false false true  true  then z2i
  else zero

/-- `4·|1_L⟩ = 4·X^{⊗7}|0_L⟩`. -/
def ψ1Z : BitString 7 → ZSqrt235i := fun x => ψ0Z (complement x)

/-- The seed's support set. -/
def S7Z : Finset (BitString 7) :=
  Finset.univ.filter (fun w => ψ0Z w ≠ zero ∨ ψ1Z w ≠ zero)

/-! ## The seed over the exact field, as a scaled integer vector -/

/-- The scale of the seed: `1/4`. -/
def q0 : ℚ := 1 / 4

def ψ0K : BitString 7 → QSqrt235i := fun s => QSqrt235i.smul q0 (toQ (ψ0Z s))
def ψ1K : BitString 7 → QSqrt235i := fun s => QSqrt235i.smul q0 (toQ (ψ1Z s))

lemma ψ0K_def : ψ0K = fun s => QSqrt235i.smul q0 (toQ (ψ0Z s)) := rfl
lemma ψ1K_def : ψ1K = fun s => QSqrt235i.smul q0 (toQ (ψ1Z s)) := rfl

/-- The two `ℂ`-valued seed codewords. -/
noncomputable def ψ0 : Hil 7 := fun s => ιK (ψ0K s)
noncomputable def ψ1 : Hil 7 := fun s => ιK (ψ1K s)

/-! ## The first lift over the integer ring -/

/-- Integer mirror of the Bell parity flag: `bflagK = (1/2)·bflagZ`. -/
def bflagZ (p : Bool) (uv : BitString 2) : ZSqrt235i :=
  mul sqrt2Z
    (add (if uv = bket1 p then one else zero) (if uv = bket2 p then one else zero))

def ψ0Z1 : BitString (7 + 2) → ZSqrt235i := fun w =>
  mulL (ψ0Z (bleft w)) (bflagZ (xor (hibit 8 a0 (bleft w)) false) (bright w))
def ψ1Z1 : BitString (7 + 2) → ZSqrt235i := fun w =>
  mulL (ψ1Z (bleft w)) (bflagZ (xor (hibit 8 a0 (bleft w)) true) (bright w))

/-- The scale after one lift: `(1/4)·(1/2) = 1/8`. -/
def q1 : ℚ := 1 / 8

def S9Z : Finset (BitString (7 + 2)) :=
  Finset.univ.filter (fun w => ψ0Z1 w ≠ zero ∨ ψ1Z1 w ≠ zero)

/-! ## Off-support vanishing (free from the definition of the support sets) -/

lemma z0_off_S7 : ∀ s, s ∉ S7Z → ψ0Z s = zero := fun s hs => by
  by_contra h; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, Or.inl h⟩)
lemma z1_off_S7 : ∀ s, s ∉ S7Z → ψ1Z s = zero := fun s hs => by
  by_contra h; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, Or.inr h⟩)
lemma z0_off_S9 : ∀ w, w ∉ S9Z → ψ0Z1 w = zero := fun w hw => by
  by_contra h; exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, Or.inl h⟩)
lemma z1_off_S9 : ∀ w, w ∉ S9Z → ψ1Z1 w = zero := fun w hw => by
  by_contra h; exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, Or.inr h⟩)

lemma smul_toQ_zero (q : ℚ) : QSqrt235i.smul q (toQ zero) = 0 := by
  rw [toQ_zero]; exact QSqrt235i.smul_zero' q

lemma h0_off_S7 : ∀ s, s ∉ S7Z → ψ0K s = 0 := fun s hs => by
  rw [ψ0K_def]; simp only []; rw [z0_off_S7 s hs]; exact smul_toQ_zero q0
lemma h1_off_S7 : ∀ s, s ∉ S7Z → ψ1K s = 0 := fun s hs => by
  rw [ψ1K_def]; simp only []; rw [z1_off_S7 s hs]; exact smul_toQ_zero q0

/-! ## Nonvanishing transfers between the two sides -/

lemma ne_zero_of_ψ0K {s} (h : ψ0K s ≠ 0) : ψ0Z s ≠ zero := fun hz => by
  apply h; rw [ψ0K_def]; simp only []; rw [hz]; exact smul_toQ_zero q0
lemma ne_zero_of_ψ1K {s} (h : ψ1K s ≠ 0) : ψ1Z s ≠ zero := fun hz => by
  apply h; rw [ψ1K_def]; simp only []; rw [hz]; exact smul_toQ_zero q0

lemma ne_zero_of_ψ0 {s} (h : ψ0 s ≠ 0) : ψ0Z s ≠ zero :=
  ne_zero_of_ψ0K (fun hz => h (by simp [ψ0, hz, ιK_zero]))
lemma ne_zero_of_ψ1 {s} (h : ψ1 s ≠ 0) : ψ1Z s ≠ zero :=
  ne_zero_of_ψ1K (fun hz => h (by simp [ψ1, hz, ιK_zero]))

/-! ## The lift is again a scaled integer vector -/

lemma isqrt2K_eq : isqrt2K = QSqrt235i.smul (1 / 2) (toQ sqrt2Z) := by
  show isqrt2K = _
  simp only [isqrt2K, sqrt2Z, toQ, ZSqrt23i.toQ, ZSqrt23i.zero, QSqrt235i.smul,
    QSqrt23i.smul_def, QSqrt23i.smul, QSqrt23i.zero_eq, QSqrt23i.zero,
    QSqrt235i.mk.injEq, QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | norm_num | ring | trivial | simp)

lemma toQ_ite {c : Prop} [Decidable c] (a b : ZSqrt235i) :
    toQ (if c then a else b) = if c then toQ a else toQ b := by
  split <;> rfl

lemma bflagK_eq (p : Bool) (uv : BitString 2) :
    bflagK p uv = QSqrt235i.smul (1 / 2) (toQ (bflagZ p uv)) := by
  rw [bflagZ, toQ_mul, toQ_add, toQ_ite, toQ_ite, toQ_one, toQ_zero,
    ← QSqrt235i.mul_smul_left, ← isqrt2K_eq]
  rfl

lemma liftK_eq0 :
    liftVecK 8 a0 false ψ0K = fun w => QSqrt235i.smul q1 (toQ (ψ0Z1 w)) := by
  funext w
  rw [liftVecK, ψ0K_def]
  show QSqrt235i.mul (QSqrt235i.smul q0 (toQ (ψ0Z (bleft w)))) _ = _
  rw [bflagK_eq, QSqrt235i.mul_smul_smul, ψ0Z1, mulL_eq, toQ_mul]
  norm_num [q0, q1]

lemma liftK_eq1 :
    liftVecK 8 a0 true ψ1K = fun w => QSqrt235i.smul q1 (toQ (ψ1Z1 w)) := by
  funext w
  rw [liftVecK, ψ1K_def]
  show QSqrt235i.mul (QSqrt235i.smul q0 (toQ (ψ1Z (bleft w)))) _ = _
  rw [bflagK_eq, QSqrt235i.mul_smul_smul, ψ1Z1, mulL_eq, toQ_mul]
  norm_num [q0, q1]

lemma h0_off_S9 : ∀ w, w ∉ S9Z → liftVecK 8 a0 false ψ0K w = 0 := fun w hw => by
  rw [liftK_eq0]; simp only []; rw [z0_off_S9 w hw]; exact smul_toQ_zero q1
lemma h1_off_S9 : ∀ w, w ∉ S9Z → liftVecK 8 a0 true ψ1K w = 0 := fun w hw => by
  rw [liftK_eq1]; simp only []; rw [z1_off_S9 w hw]; exact smul_toQ_zero q1
end BD16Kernel
