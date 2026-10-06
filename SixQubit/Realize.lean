import Mathlib
import SS.HilbertKL
import SS.QSqrt235iC

/-!
# A reusable exact-realization layer

`SixQubit/Orbit36Code.lean` proves that one explicit pair of six-qubit words is
an exact `((6,2,3))` code, by carrying the amplitudes in a ring of algebraic
integers and deciding the Knill--Laflamme constraints there.  Ten further
orbits need exactly the same argument with different tables, so the parts that
do not depend on the table are collected here once.

The ring is `Z[sqrt 2, sqrt 3, i]`, carried as eight integers.  That is enough
for every realization in this development, because each amplitude table is
recorded up to a single real scale:

| words | scale | entries |
| --- | --- | --- |
| sixteen real terms | `1/4` | `+-1` |
| eight real terms | `1/4` | `+-sqrt 2` |
| eleven complex terms | `1/12` | `2 sqrt 3 zeta6^k`, `2 sqrt 6 zeta6^k` |
| twelve complex terms | `1/(2 sqrt 30)` | `2 sqrt 3 zeta6^k`, `2 sqrt 2 zeta6^k` |

Pulling the irrational scale out is what keeps the ring small: `1/sqrt 10` and
`1/sqrt 15` would need `sqrt 5`, but `sqrt 3 / sqrt 30` and `sqrt 2 / sqrt 30`
do not.  Rational amplitudes alone would not suffice, since the phases are
sixth roots of unity.

`decide` does the work, so nothing here uses `native_decide` or `sorry`.
-/

namespace SixQubit.Realize

/-! ## The ring `Z[sqrt 2, sqrt 3, i]` in eight integer coordinates -/

/-- `a0 + a1 r2 + a2 r3 + a3 r6 + i (b0 + b1 r2 + b2 r3 + b3 r6)` with
`r2 = sqrt 2`, `r3 = sqrt 3`, `r6 = sqrt 2 * sqrt 3`. -/
structure ZQ where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  b0 : Int
  b1 : Int
  b2 : Int
  b3 : Int
deriving DecidableEq

/-- Positional constructor for the generated amplitude tables. -/
def z8 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) : ZQ := ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩

namespace ZQ

def zero : ZQ := z8 0 0 0 0 0 0 0 0

def add (x y : ZQ) : ZQ :=
  ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2, x.a3 + y.a3,
   x.b0 + y.b0, x.b1 + y.b1, x.b2 + y.b2, x.b3 + y.b3⟩

def neg (x : ZQ) : ZQ :=
  ⟨-x.a0, -x.a1, -x.a2, -x.a3, -x.b0, -x.b1, -x.b2, -x.b3⟩

def sub (x y : ZQ) : ZQ := add x (neg y)

def conj (x : ZQ) : ZQ :=
  ⟨x.a0, x.a1, x.a2, x.a3, -x.b0, -x.b1, -x.b2, -x.b3⟩

/-- Multiplication.  The two `zero` guards come first, so the kernel never
reaches the sixty-four integer products when an amplitude vanishes. -/
def mul (x y : ZQ) : ZQ :=
  if x = zero then zero else if y = zero then zero else
  ⟨(x.a0*y.a0 + 2*x.a1*y.a1 + 3*x.a2*y.a2 + 6*x.a3*y.a3)
     - (x.b0*y.b0 + 2*x.b1*y.b1 + 3*x.b2*y.b2 + 6*x.b3*y.b3),
   (x.a0*y.a1 + x.a1*y.a0 + 3*x.a2*y.a3 + 3*x.a3*y.a2)
     - (x.b0*y.b1 + x.b1*y.b0 + 3*x.b2*y.b3 + 3*x.b3*y.b2),
   (x.a0*y.a2 + x.a2*y.a0 + 2*x.a1*y.a3 + 2*x.a3*y.a1)
     - (x.b0*y.b2 + x.b2*y.b0 + 2*x.b1*y.b3 + 2*x.b3*y.b1),
   (x.a0*y.a3 + x.a3*y.a0 + x.a1*y.a2 + x.a2*y.a1)
     - (x.b0*y.b3 + x.b3*y.b0 + x.b1*y.b2 + x.b2*y.b1),
   (x.a0*y.b0 + 2*x.a1*y.b1 + 3*x.a2*y.b2 + 6*x.a3*y.b3)
     + (x.b0*y.a0 + 2*x.b1*y.a1 + 3*x.b2*y.a2 + 6*x.b3*y.a3),
   (x.a0*y.b1 + x.a1*y.b0 + 3*x.a2*y.b3 + 3*x.a3*y.b2)
     + (x.b0*y.a1 + x.b1*y.a0 + 3*x.b2*y.a3 + 3*x.b3*y.a2),
   (x.a0*y.b2 + x.a2*y.b0 + 2*x.a1*y.b3 + 2*x.a3*y.b1)
     + (x.b0*y.a2 + x.b2*y.a0 + 2*x.b1*y.a3 + 2*x.b3*y.a1),
   (x.a0*y.b3 + x.a3*y.b0 + x.a1*y.b2 + x.a2*y.b1)
     + (x.b0*y.a3 + x.b3*y.a0 + x.b1*y.a2 + x.b2*y.a1)⟩

/-- Multiply by `(-1)` when the boolean is `true`. -/
def signMul (b : Bool) (x : ZQ) : ZQ := if b then neg x else x

lemma neg_zero : ZQ.neg ZQ.zero = ZQ.zero := by decide

lemma mul_zero_right (x : ZQ) : ZQ.mul x ZQ.zero = ZQ.zero := by
  by_cases h : x = ZQ.zero <;> simp [ZQ.mul, h]

lemma signMul_zero (b : Bool) : ZQ.signMul b ZQ.zero = ZQ.zero := by
  cases b
  · rfl
  · exact neg_zero

end ZQ

/-! ## The embedding into `ℂ` -/

noncomputable section

/-- The real number `a0 + a1 sqrt 2 + a2 sqrt 3 + a3 sqrt 6`. -/
def rz (a0 a1 a2 a3 : Int) : ℝ := SS.rp (a0 : ℚ) (a1 : ℚ) (a2 : ℚ) (a3 : ℚ)

/-- Real part of the embedding. -/
def toCre (x : ZQ) : ℝ := rz x.a0 x.a1 x.a2 x.a3

/-- Imaginary part of the embedding. -/
def toCim (x : ZQ) : ℝ := rz x.b0 x.b1 x.b2 x.b3

/-- The embedding `ZQ → ℂ`. -/
def toC (x : ZQ) : ℂ := ⟨toCre x, toCim x⟩

@[simp] lemma toC_re (x : ZQ) : (toC x).re = toCre x := rfl
@[simp] lemma toC_im (x : ZQ) : (toC x).im = toCim x := rfl

lemma rz_add (a0 a1 a2 a3 c0 c1 c2 c3 : Int) :
    rz (a0 + c0) (a1 + c1) (a2 + c2) (a3 + c3)
      = rz a0 a1 a2 a3 + rz c0 c1 c2 c3 := by
  simp only [rz]; push_cast; exact SS.rp_add _ _ _ _ _ _ _ _

lemma rz_sub (a0 a1 a2 a3 c0 c1 c2 c3 : Int) :
    rz (a0 - c0) (a1 - c1) (a2 - c2) (a3 - c3)
      = rz a0 a1 a2 a3 - rz c0 c1 c2 c3 := by
  simp only [rz]; push_cast; exact SS.rp_sub _ _ _ _ _ _ _ _

lemma rz_neg (a0 a1 a2 a3 : Int) :
    rz (-a0) (-a1) (-a2) (-a3) = -rz a0 a1 a2 a3 := by
  simp only [rz]; push_cast; exact SS.rp_neg _ _ _ _

lemma rz_mul (a0 a1 a2 a3 c0 c1 c2 c3 : Int) :
    rz a0 a1 a2 a3 * rz c0 c1 c2 c3
      = rz (a0*c0 + 2*a1*c1 + 3*a2*c2 + 6*a3*c3)
           (a0*c1 + a1*c0 + 3*a2*c3 + 3*a3*c2)
           (a0*c2 + a2*c0 + 2*a1*c3 + 2*a3*c1)
           (a0*c3 + a3*c0 + a1*c2 + a2*c1) := by
  simp only [rz]; push_cast; exact SS.rp_mul _ _ _ _ _ _ _ _

lemma rz_intCast (a : Int) : rz a 0 0 0 = (a : ℝ) := by
  simp [rz, SS.rp]

@[simp] lemma toC_zero : toC ZQ.zero = 0 := by
  apply Complex.ext <;> simp [toCre, toCim, ZQ.zero, z8, rz, SS.rp]

lemma toC_intCast (a : Int) : toC (z8 a 0 0 0 0 0 0 0) = (a : ℂ) := by
  apply Complex.ext <;> simp [toCre, toCim, z8, rz_intCast]

lemma toC_add (x y : ZQ) : toC (ZQ.add x y) = toC x + toC y := by
  apply Complex.ext <;>
    simp only [toC_re, toC_im, Complex.add_re, Complex.add_im, toCre, toCim,
      ZQ.add] <;>
    exact rz_add _ _ _ _ _ _ _ _

lemma toC_neg (x : ZQ) : toC (ZQ.neg x) = -toC x := by
  apply Complex.ext <;>
    simp only [toC_re, toC_im, Complex.neg_re, Complex.neg_im, toCre, toCim,
      ZQ.neg] <;>
    exact rz_neg _ _ _ _

lemma toC_sub (x y : ZQ) : toC (ZQ.sub x y) = toC x - toC y := by
  rw [ZQ.sub, toC_add, toC_neg]; ring

lemma toC_conj (x : ZQ) : toC (ZQ.conj x) = star (toC x) := by
  apply Complex.ext
  · simp only [toC_re, Complex.star_def, Complex.conj_re, toCre, ZQ.conj]
  · simp only [toC_im, Complex.star_def, Complex.conj_im, toCim, ZQ.conj]
    exact rz_neg _ _ _ _

lemma toC_mul (x y : ZQ) : toC (ZQ.mul x y) = toC x * toC y := by
  by_cases hx : x = ZQ.zero
  · rw [hx, show ZQ.mul ZQ.zero y = ZQ.zero from by simp [ZQ.mul], toC_zero,
      zero_mul]
  by_cases hy : y = ZQ.zero
  · rw [hy, ZQ.mul_zero_right, toC_zero, mul_zero]
  apply Complex.ext
  · simp only [toC_re, toC_im, Complex.mul_re, toCre, toCim, ZQ.mul, if_neg hx,
      if_neg hy]
    rw [rz_mul, rz_mul, ← rz_sub]
  · simp only [toC_re, toC_im, Complex.mul_im, toCre, toCim, ZQ.mul, if_neg hx,
      if_neg hy]
    rw [rz_mul, rz_mul, ← rz_add]

lemma toC_signMul (b : Bool) (x : ZQ) :
    toC (ZQ.signMul b x) = SS.signC b (toC x) := by
  cases b
  · rfl
  · exact toC_neg x

end

/-! ## Masks -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

/-- The integer mask of a bitstring: coordinate `i` is bit `i`. -/
def num (x : SS.BitString 6) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0)
    + (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0)

/-- The bitstring of an integer mask. -/
def nbit (m : Nat) : SS.BitString 6 := fun i => Nat.testBit m i.val

theorem nbit_num : ∀ x : SS.BitString 6, nbit (num x) = x := by decide

theorem num_lt : ∀ x : SS.BitString 6, num x < 64 := by decide

/-! ## The exact matrix-element sums -/

/-- One term of a matrix-element sum: `(-1)^{z.s} conj (cj (s xor x)) * ck s`. -/
def zterm (cj ck : SS.BitString 6 → ZQ) (x z s : SS.BitString 6) : ZQ :=
  ZQ.signMul (SS.bdot z s) (ZQ.mul (ZQ.conj (cj (SS.bxor s x))) (ck s))

/-- Exact sum of a `ZQ`-valued function over a list of bitstrings. -/
def zsum (L : List (SS.BitString 6)) (f : SS.BitString 6 → ZQ) : ZQ :=
  (L.map f).foldr ZQ.add ZQ.zero

/-- The exact matrix element `<psi_j| P(x,z) |psi_k>` without the `i^{#Y}`
prefactor; `Lk` is a support list for `ck`. -/
def zmat (cj ck : SS.BitString 6 → ZQ) (Lk : List (SS.BitString 6))
    (x z : SS.BitString 6) : ZQ :=
  zsum Lk (zterm cj ck x z)

/-! ## The finite certificate

Exactly the three conditions `HasDistance` needs: the two diagonal elements
agree and both off-diagonal elements vanish.  Which Paulis carry a nonzero
diagonal scalar is extra information, useful for enumerators but not for being
a code, so it is deliberately not part of this certificate. -/

def checkKL (c0z c1z : SS.BitString 6 → ZQ) (L0 L1 : List (SS.BitString 6))
    (x z : SS.BitString 6) : Bool :=
  decide (ZQ.sub (zmat c0z c0z L0 x z) (zmat c1z c1z L1 x z) = ZQ.zero)
    && decide (zmat c0z c1z L1 x z = ZQ.zero)
    && decide (zmat c1z c0z L0 x z = ZQ.zero)

/-- Transport of the mask-indexed certificate to an arbitrary Pauli. -/
theorem checkKL_of_wt {c0z c1z : SS.BitString 6 → ZQ}
    {L0 L1 : List (SS.BitString 6)}
    (hchk : ∀ m < 64, ∀ k < 64,
      (⟨nbit m, nbit k⟩ : SS.PauliString 6).wt ≤ 2 →
      checkKL c0z c1z L0 L1 (nbit m) (nbit k) = true)
    (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    checkKL c0z c1z L0 L1 P.x P.z = true := by
  have hx := nbit_num P.x
  have hz := nbit_num P.z
  have h := hchk (num P.x) (num_lt _) (num P.z) (num_lt _) (by rw [hx, hz]; exact hw)
  rwa [hx, hz] at h

/-! ## Transport to genuine complex matrix elements -/

noncomputable section

/-- The complex state attached to exact amplitudes and a real scale. -/
def stC (sc : ℂ) (c : SS.BitString 6 → ZQ) : SS.State 6 ℂ := fun s => sc * toC (c s)

/-- `toC` turns a `zsum` into an ordinary sum over the list. -/
lemma toC_zsum (L : List (SS.BitString 6)) (f : SS.BitString 6 → ZQ) :
    toC (zsum L f) = (L.map (fun s => toC (f s))).sum := by
  unfold zsum
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons, toC_add, ih]

lemma zterm_eq_zero {cj ck : SS.BitString 6 → ZQ} {x z s : SS.BitString 6}
    (h : ck s = ZQ.zero) : zterm cj ck x z s = ZQ.zero := by
  unfold zterm
  rw [h, ZQ.mul_zero_right, ZQ.signMul_zero]

/-- **The exact sums are the true Knill--Laflamme matrix elements.** -/
theorem matElt_eq (sc : ℂ) (cj ck : SS.BitString 6 → ZQ)
    (Lk : List (SS.BitString 6)) (hnd : Lk.Nodup)
    (hk : ∀ s, s ∉ Lk → ck s = ZQ.zero) (P : SS.PauliString 6) :
    SS.innerC (stC sc cj) (SS.pauliAct P (stC sc ck))
      = star sc * sc * (Complex.I ^ P.numY) * toC (zmat cj ck Lk P.x P.z) := by
  classical
  have hcong : ∀ s : SS.BitString 6,
      SS.signC (SS.bdot P.z s) (star (stC sc cj (SS.bxor s P.x)) * stC sc ck s)
        = star sc * sc * toC (zterm cj ck P.x P.z s) := by
    intro s
    unfold zterm stC
    rw [toC_signMul, toC_mul, toC_conj]
    cases SS.bdot P.z s <;>
      simp only [SS.signC_true, SS.signC_false, star_mul'] <;> ring
  have hsub : ∑ s : SS.BitString 6, toC (zterm cj ck P.x P.z s)
      = ∑ s ∈ Lk.toFinset, toC (zterm cj ck P.x P.z s) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro s _ hs
    rw [zterm_eq_zero (hk s (by simpa using hs)), toC_zero]
  have hkey : ∑ s : SS.BitString 6,
      SS.signC (SS.bdot P.z s) (star (stC sc cj (SS.bxor s P.x)) * stC sc ck s)
        = star sc * sc * toC (zmat cj ck Lk P.x P.z) := by
    rw [Finset.sum_congr rfl (fun s _ => hcong s), ← Finset.mul_sum, hsub,
      List.sum_toFinset _ hnd, ← toC_zsum, zmat]
  rw [SS.innerC_pauliAct, hkey]
  ring

/-- **The reusable realization theorem.**

Given exact amplitude tables vanishing off their support lists, and the finite
certificate decided over all mask pairs, the scaled complex pair is an exact
`((6,2,3))` code.  The scale is arbitrary: it cancels out of the off-diagonal
equations and appears symmetrically in the diagonal one. -/
theorem is_code_of_check (sc : ℂ) (c0z c1z : SS.BitString 6 → ZQ)
    (L0 L1 : List (SS.BitString 6)) (h0nd : L0.Nodup) (h1nd : L1.Nodup)
    (h0v : ∀ s, s ∉ L0 → c0z s = ZQ.zero) (h1v : ∀ s, s ∉ L1 → c1z s = ZQ.zero)
    (hchk : ∀ m < 64, ∀ k < 64,
      (⟨nbit m, nbit k⟩ : SS.PauliString 6).wt ≤ 2 →
      checkKL c0z c1z L0 L1 (nbit m) (nbit k) = true) :
    SS.HasDistance ![stC sc c0z, stC sc c1z] 3 := by
  intro P hw
  have hw2 : P.wt ≤ 2 := hw
  have h := checkKL_of_wt hchk P hw2
  simp only [checkKL, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨SS.innerC (stC sc c0z) (SS.pauliAct P (stC sc c0z)), ?_⟩
  intro j k
  fin_cases j <;> fin_cases k
  · show SS.innerC (stC sc c0z) (SS.pauliAct P (stC sc c0z)) = _
    rw [if_pos rfl]
  · show SS.innerC (stC sc c0z) (SS.pauliAct P (stC sc c1z)) = _
    rw [if_neg (by decide)]
    rw [matElt_eq sc c0z c1z L1 h1nd h1v P, h.1.2, toC_zero, mul_zero]
  · show SS.innerC (stC sc c1z) (SS.pauliAct P (stC sc c0z)) = _
    rw [if_neg (by decide)]
    rw [matElt_eq sc c1z c0z L0 h0nd h0v P, h.2, toC_zero, mul_zero]
  · show SS.innerC (stC sc c1z) (SS.pauliAct P (stC sc c1z)) = _
    rw [if_pos rfl]
    have h0 : toC (ZQ.sub (zmat c0z c0z L0 P.x P.z) (zmat c1z c1z L1 P.x P.z)) = 0 := by
      rw [h.1.1, toC_zero]
    rw [toC_sub] at h0
    rw [matElt_eq sc c0z c0z L0 h0nd h0v P, matElt_eq sc c1z c1z L1 h1nd h1v P]
    linear_combination (-(star sc * sc * (Complex.I ^ P.numY))) * h0

/-- Normalization from the exact squared norm and the scale. -/
theorem normalized_of (sc : ℂ) (c : SS.BitString 6 → ZQ)
    (L : List (SS.BitString 6)) (hnd : L.Nodup)
    (hv : ∀ s, s ∉ L → c s = ZQ.zero) (N : Int)
    (hz : zmat c c L (fun _ => false) (fun _ => false) = z8 N 0 0 0 0 0 0 0)
    (hn : star sc * sc * (N : ℂ) = 1) :
    SS.innerC (stC sc c) (stC sc c) = 1 := by
  have hP : (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6).numY = 0 := by decide
  have hid : SS.pauliAct (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6)
      (stC sc c) = stC sc c := by
    funext t
    simp only [SS.pauliAct, hP, pow_zero, one_mul, SS.bxor_zero]
    rw [show SS.bdot (fun _ => false) t = false from by simp [SS.bdot],
      SS.signC_false]
  have := matElt_eq sc c c L hnd hv (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6)
  rw [hid, hP, pow_zero, mul_one, hz, toC_intCast] at this
  rw [this, hn]

/-- Amplitudes vanish off the support list. -/
theorem stC_vanishes (sc : ℂ) (c : SS.BitString 6 → ZQ)
    (L : List (SS.BitString 6)) (hv : ∀ s, s ∉ L → c s = ZQ.zero)
    (s : SS.BitString 6) (hs : s ∉ L) : stC sc c s = 0 := by
  unfold stC
  rw [hv s hs, toC_zero, mul_zero]

end

end SixQubit.Realize
