import SS.ZSqrt235i
import DyadicLifts.Bridge

/-!
# Integer mirror of the Knill--Laflamme evaluator

`DyadicLifts.Bridge` evaluates a code's KL matrix elements over `QSqrt235i`,
sixteen rationals.  The kernel cannot reduce `Rat` --- `Rat.normalize` calls
`Nat.gcd`, which is defined by well-founded recursion --- so those checks were
closed by `native_decide`.  This module mirrors the evaluator over `ZSqrt235i`
and transports the result back.

## The scale

A code's amplitudes lie in `(1/D)·ℤ[√2,√3,√5,i]`, not in the ring itself.  Every
matrix element is quadratic in the amplitudes, so replacing `ψ` by `q·ψ`
rescales all of them by `q²`.  For `q ≠ 0` that changes neither which of them
vanish nor which of them agree, which is all the KL conditions ask.  The scale
is therefore carried symbolically (`melK_smul`) and never evaluated.

## The cost

The naive mirror is far too slow: the double sum runs over `|S|²` pairs, each
term is a product of `n` per-qubit factors, and one kernel multiplication in
this ring costs about 23 ms.  Almost all of that work is spent computing zeros.
For a Pauli `P` of weight `≤ 2`,

* `sqMEZ (P i) a b = 0` unless `a` and `b` are related as `P i` dictates, so
  `pauliMEZ P s t` vanishes for all but one `t` per `s`;
* at the `n - 2` or more positions where `P i = I` and `s i = t i`, the factor
  is `1`;
* and the amplitude vanishes off the code's support, which is a small part
  of `S`.

`mulL` and `mulR` below inspect one argument before touching the other and
return early on `0` and on `1`.  Because the kernel does not evaluate an
argument it never reaches, a vanishing term costs a few structure comparisons
and no ring multiplication at all; a surviving term costs at most two.  `mulL`
guards the left argument (used where the left one is cheap: a per-qubit factor,
or a conjugated amplitude) and `mulR` the right (used where the right one is
the amplitude and the left is an unevaluated product).

No `sorry`, no `native_decide`.
-/

/-! ### Literals as named constants

The `Zero` and `One` instances are the named constants.  Saying so lets `simp`
turn a bare `0` or `1` into a constructor application, which is what
`mk.injEq` needs in order to split a structure equation into coefficients. -/

namespace SS.QSqrt23i
lemma zero_eq : (0 : QSqrt23i) = zero := rfl
lemma one_eq : (1 : QSqrt23i) = one := rfl
end SS.QSqrt23i

namespace SS.QSqrt235i
lemma zero_eq' : (0 : QSqrt235i) = zero := rfl
lemma one_eq' : (1 : QSqrt235i) = one := rfl
end SS.QSqrt235i

namespace SS.QSqrt23i

lemma smul_def (q : ℚ) (x : QSqrt23i) : q • x = smul q x := rfl
lemma add_def (x y : QSqrt23i) : x + y = add x y := rfl
lemma mul_def (x y : QSqrt23i) : x * y = mul x y := rfl

lemma smul_add_smul (q : ℚ) (a b : QSqrt23i) :
    add (smul q a) (smul q b) = smul q (add a b) := by
  simp only [add, smul, mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma conj_smul (q : ℚ) (a : QSqrt23i) : conj (smul q a) = smul q (conj a) := by
  simp only [conj, smul, mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma smul_smul (p q : ℚ) (x : QSqrt23i) : smul p (smul q x) = smul (p * q) x := by
  simp only [smul, mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma mul_smul_smul (p q : ℚ) (a b : QSqrt23i) :
    mul (smul p a) (smul q b) = smul (p * q) (mul a b) := by
  simp only [mul, smul, mulReal, mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma one_smul' (x : QSqrt23i) : smul 1 x = x := by
  simp only [smul, mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma smul_zero' (q : ℚ) : smul q zero = zero := by
  simp only [smul, zero, mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

end SS.QSqrt23i

namespace SS.QSqrt235i

open SS.QSqrt23i (smul_def add_def mul_def)

lemma smul_def' (q : ℚ) (x : QSqrt235i) : q • x = smul q x := rfl
lemma add_def' (x y : QSqrt235i) : x + y = add x y := rfl
lemma mul_def' (x y : QSqrt235i) : x * y = mul x y := rfl

lemma smul_add_smul (q : ℚ) (a b : QSqrt235i) :
    add (smul q a) (smul q b) = smul q (add a b) := by
  simp only [add, smul, mk.injEq, smul_def, add_def, QSqrt23i.add, QSqrt23i.smul,
    QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma conj_smul (q : ℚ) (a : QSqrt235i) : conj (smul q a) = smul q (conj a) := by
  simp only [conj, smul, mk.injEq, smul_def, QSqrt23i.conj, QSqrt23i.smul,
    QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma mul_smul_smul (p q : ℚ) (a b : QSqrt235i) :
    mul (smul p a) (smul q b) = smul (p * q) (mul a b) := by
  simp only [mul, smul, mk.injEq, smul_def, add_def, mul_def, QSqrt23i.mul,
    QSqrt23i.add, QSqrt23i.smul, QSqrt23i.mulReal, QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

lemma one_smul' (x : QSqrt235i) : smul 1 x = x := by
  cases x with
  | mk u v =>
    simp only [smul, smul_def, mk.injEq]
    exact ⟨QSqrt23i.one_smul' u, QSqrt23i.one_smul' v⟩

lemma smul_zero' (q : ℚ) : smul q zero = (0 : QSqrt235i) := by
  show smul q ⟨0, 0⟩ = ⟨0, 0⟩
  simp only [smul, mk.injEq, smul_def]
  exact ⟨QSqrt23i.smul_zero' q, QSqrt23i.smul_zero' q⟩

lemma mul_smul_right (q : ℚ) (x y : QSqrt235i) :
    mul x (smul q y) = smul q (mul x y) := by
  conv_lhs => rw [← one_smul' x]
  rw [mul_smul_smul, one_mul]

lemma smul_one_ofRat (q : ℚ) : smul q 1 = ofRat q := by
  simp only [smul, one_eq', one, ofRat, QSqrt23i.smul_def, QSqrt23i.smul,
    QSqrt23i.one_eq, QSqrt23i.zero_eq, QSqrt23i.one, QSqrt23i.zero, QSqrt23i.ofRat,
    mk.injEq, QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | norm_num | ring | trivial)

lemma smul_ofRat (q r : ℚ) : smul q (ofRat r) = ofRat (q * r) := by
  simp only [smul, ofRat, QSqrt23i.smul_def, QSqrt23i.smul, QSqrt23i.ofRat,
    QSqrt23i.zero_eq, QSqrt23i.zero, mk.injEq, QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | norm_num | ring | trivial)

lemma ofRat_one : ofRat 1 = 1 := by
  simp only [ofRat, one_eq', one, QSqrt23i.ofRat, QSqrt23i.one_eq, QSqrt23i.one,
    QSqrt23i.zero_eq, QSqrt23i.zero, mk.injEq, QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | norm_num | ring | trivial)

lemma mul_smul_left (q : ℚ) (x y : QSqrt235i) :
    mul (smul q x) y = smul q (mul x y) := by
  conv_lhs => rw [← one_smul' y]
  rw [mul_smul_smul, mul_one]

end SS.QSqrt235i

namespace SS.ZSqrt235i

/-- The unit of the integer ring. -/
def one : ZSqrt235i := ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ZSqrt23i.zero⟩

@[simp] lemma toQ_one : toQ one = (1 : QSqrt235i) := by
  show toQ one = QSqrt235i.one
  simp only [toQ, one, QSqrt235i.one, ZSqrt23i.toQ, ZSqrt23i.zero, QSqrt235i.mk.injEq]
  refine ⟨?_, ?_⟩
  · show (⟨((1 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ),
      ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ)⟩ : QSqrt23i)
      = QSqrt23i.one
    simp [QSqrt23i.one]
  · show (⟨((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ),
      ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ)⟩ : QSqrt23i)
      = 0
    simp; rfl

instance : Std.Commutative (α := ZSqrt235i) add where
  comm x y := by
    simp only [add, ZSqrt23i.add, ZSqrt235i.mk.injEq, ZSqrt23i.mk.injEq]
    all_goals (repeat' apply And.intro)
    all_goals (first | rfl | ring | trivial | simp)

instance : Std.Associative (α := ZSqrt235i) add where
  assoc x y z := by
    simp only [add, ZSqrt23i.add, ZSqrt235i.mk.injEq, ZSqrt23i.mk.injEq]
    all_goals (repeat' apply And.intro)
    all_goals (first | rfl | ring | trivial | simp)

/-! ### The annihilation and unit laws that make the short circuits sound -/

@[simp] lemma zero_mul' (y : ZSqrt235i) : mul zero y = zero := by
  simp only [mul, zero, ZSqrt23i.mul, ZSqrt23i.add, ZSqrt23i.smulInt, ZSqrt23i.mulRealZ,
    ZSqrt23i.zero, ZSqrt235i.mk.injEq, ZSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

@[simp] lemma mul_zero' (x : ZSqrt235i) : mul x zero = zero := by
  simp only [mul, zero, ZSqrt23i.mul, ZSqrt23i.add, ZSqrt23i.smulInt, ZSqrt23i.mulRealZ,
    ZSqrt23i.zero, ZSqrt235i.mk.injEq, ZSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

@[simp] lemma one_mul' (y : ZSqrt235i) : mul one y = y := by
  simp only [mul, one, ZSqrt23i.mul, ZSqrt23i.add, ZSqrt23i.smulInt, ZSqrt23i.mulRealZ,
    ZSqrt23i.zero, ZSqrt235i.mk.injEq, ZSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

@[simp] lemma mul_one' (x : ZSqrt235i) : mul x one = x := by
  simp only [mul, one, ZSqrt23i.mul, ZSqrt23i.add, ZSqrt23i.smulInt, ZSqrt23i.mulRealZ,
    ZSqrt23i.zero, ZSqrt235i.mk.injEq, ZSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | ring | trivial | simp)

/-- The integer `k` as an element of the ring. -/
def intZ (k : Int) : ZSqrt235i := ⟨⟨k, 0, 0, 0, 0, 0, 0, 0⟩, ZSqrt23i.zero⟩

@[simp] lemma toQ_intZ (k : Int) : toQ (intZ k) = QSqrt235i.ofRat (k : ℚ) := by
  show toQ (intZ k) = QSqrt235i.ofRat (k : ℚ)
  simp only [toQ, intZ, ZSqrt23i.toQ, ZSqrt23i.zero, QSqrt235i.ofRat, QSqrt23i.ofRat,
    QSqrt23i.zero_eq, QSqrt23i.zero, QSqrt235i.mk.injEq, QSqrt23i.mk.injEq]
  all_goals (repeat' apply And.intro)
  all_goals (first | rfl | norm_num | ring | trivial)

/-- Multiplication that inspects its **left** argument first and returns without
reading the right one when the left is `0` or `1`. -/
def mulL (x y : ZSqrt235i) : ZSqrt235i :=
  if x = zero then zero else if x = one then y else mul x y

/-- Multiplication that inspects its **right** argument first. -/
def mulR (x y : ZSqrt235i) : ZSqrt235i :=
  if y = zero then zero else if y = one then x else mul x y

lemma mulL_eq (x y : ZSqrt235i) : mulL x y = mul x y := by
  unfold mulL
  split
  · rename_i h; rw [h, zero_mul']
  · split
    · rename_i h; rw [h, one_mul']
    · rfl

lemma mulR_eq (x y : ZSqrt235i) : mulR x y = mul x y := by
  unfold mulR
  split
  · rename_i h; rw [h, mul_zero']
  · split
    · rename_i h; rw [h, mul_one']
    · rfl

end SS.ZSqrt235i

namespace DyadicLifts

open SS SS.ZSqrt235i

variable {n : ℕ}

/-! ## The evaluator over the integers -/

/-- The imaginary unit of the integer ring. -/
def iZ : ZSqrt235i := ⟨⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ZSqrt23i.zero⟩

/-- The single-qubit Pauli matrix element, integer mirror of `sqMEK`. -/
def sqMEZ : SQ → Bool → Bool → ZSqrt235i
  | SQ.I, a, b => if a = b then one else zero
  | SQ.X, a, b => if a = b then zero else one
  | SQ.Z, a, b => if a = b then (if b then neg one else one) else zero
  | SQ.Y, a, b => if a = b then zero else (if b then neg iZ else iZ)

@[simp] lemma toQ_iZ : toQ iZ = QSqrt235i.I := by
  show toQ iZ = QSqrt235i.I
  simp only [toQ, iZ, QSqrt235i.I, ZSqrt23i.toQ, ZSqrt23i.zero, QSqrt235i.mk.injEq]
  refine ⟨?_, ?_⟩
  · show (⟨((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ),
      ((1 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ)⟩ : QSqrt23i)
      = QSqrt23i.I
    simp [QSqrt23i.I]
  · show (⟨((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ),
      ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ), ((0 : Int) : ℚ)⟩ : QSqrt23i)
      = 0
    simp; rfl

@[simp] lemma toQ_sqMEZ (P : SQ) (a b : Bool) : toQ (sqMEZ P a b) = sqMEK P a b := by
  cases P <;> cases a <;> cases b <;>
    simp only [sqMEZ, sqMEK, toQ_zero, toQ_one, toQ_neg, toQ_iZ, if_true, if_false,
      reduceIte, Bool.false_eq_true, reduceCtorEq] <;> rfl

/-- The per-Pauli product.  `mulL` short-circuits on the factor, so a zero
factor ends the product without the remaining ones being evaluated, and an
identity factor --- which is what all but at most two positions contribute for a
weight-`≤ 2` Pauli --- costs no multiplication. -/
def pauliMEZ (P : Fin n → SQ) (s t : BitString n) : ZSqrt235i :=
  (List.finRange n).foldr (fun i acc => mulL (sqMEZ (P i) (s i) (t i)) acc) one

@[simp] lemma toQ_pauliMEZ (P : Fin n → SQ) (s t : BitString n) :
    toQ (pauliMEZ P s t) = pauliMEK P s t := by
  rw [pauliMEZ, pauliMEK]
  induction (List.finRange n) with
  | nil => simp
  | cons i is ih =>
      simp only [List.foldr_cons]
      rw [mulL_eq, toQ_mul, ih, toQ_sqMEZ]
      rfl

/-- The integer sum over a support set. -/
def foldSumZ (S : Finset (BitString n)) (f : BitString n → ZSqrt235i) : ZSqrt235i :=
  S.fold add zero f

lemma toQ_foldSumZ (S : Finset (BitString n)) (f : BitString n → ZSqrt235i) :
    toQ (foldSumZ S f) = SS.foldSum S (fun x => toQ (f x)) := by
  classical
  induction S using Finset.induction with
  | empty => simp only [foldSumZ, SS.foldSum, Finset.fold_empty]; exact toQ_zero
  | @insert a S ha ih =>
      have h1 : foldSumZ (insert a S) f = ZSqrt235i.add (f a) (foldSumZ S f) := by
        rw [foldSumZ, Finset.fold_insert ha]; rfl
      have h2 : SS.foldSum (insert a S) (fun x => toQ (f x))
          = QSqrt235i.add (toQ (f a)) (SS.foldSum S (fun x => toQ (f x))) := by
        rw [SS.foldSum, Finset.fold_insert ha]; rfl
      rw [h1, h2, ← ih, toQ_add]

/-- The KL matrix element over the integer mirror.  `mulR` on the inner term
kills it from the amplitude alone, without evaluating the Pauli product; `mulL`
on the outer term kills it from the conjugated amplitude, without evaluating the
inner sum at all. -/
def melZ (S : Finset (BitString n)) (ψ0Z : BitString n → ZSqrt235i) (P : Fin n → SQ)
    (ψ1Z : BitString n → ZSqrt235i) : ZSqrt235i :=
  foldSumZ S fun s =>
    mulL (conj (ψ0Z s)) (foldSumZ S fun t => mulR (pauliMEZ P s t) (ψ1Z t))

lemma toQ_melZ (S : Finset (BitString n)) (ψ0Z ψ1Z : BitString n → ZSqrt235i)
    (P : Fin n → SQ) :
    toQ (melZ S ψ0Z P ψ1Z) = melK S (fun s => toQ (ψ0Z s)) P (fun s => toQ (ψ1Z s)) := by
  rw [melZ, melK, toQ_foldSumZ]
  refine Finset.fold_congr (fun s _ => ?_)
  rw [mulL_eq, toQ_mul, toQ_conj, toQ_foldSumZ]
  refine congrArg _ (Finset.fold_congr (fun t _ => ?_))
  rw [mulR_eq, toQ_mul, toQ_pauliMEZ]
  rfl

/-! ## The global scale is invisible to the conditions -/

lemma foldSum_smul (S : Finset (BitString n)) (f : BitString n → QSqrt235i) (q : ℚ) :
    SS.foldSum S (fun s => QSqrt235i.smul q (f s))
      = QSqrt235i.smul q (SS.foldSum S f) := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [SS.foldSum, Finset.fold_empty]
      exact (QSqrt235i.smul_zero' q).symm
  | @insert a S ha ih =>
      have h1 : SS.foldSum (insert a S) (fun s => QSqrt235i.smul q (f s))
          = QSqrt235i.add (QSqrt235i.smul q (f a))
              (SS.foldSum S fun s => QSqrt235i.smul q (f s)) := by
        rw [SS.foldSum, Finset.fold_insert ha]; rfl
      have h2 : SS.foldSum (insert a S) f
          = QSqrt235i.add (f a) (SS.foldSum S f) := by
        rw [SS.foldSum, Finset.fold_insert ha]; rfl
      rw [h1, h2, ih, QSqrt235i.smul_add_smul]

lemma melK_smul (S : Finset (BitString n)) (f g : BitString n → QSqrt235i) (q : ℚ)
    (P : Fin n → SQ) :
    melK S (fun s => QSqrt235i.smul q (f s)) P (fun s => QSqrt235i.smul q (g s))
      = QSqrt235i.smul (q * q) (melK S f P g) := by
  rw [melK, melK, ← foldSum_smul]
  refine Finset.fold_congr (fun s _ => ?_)
  show QSqrt235i.mul _ _ = QSqrt235i.smul (q * q) (QSqrt235i.mul _ _)
  rw [QSqrt235i.conj_smul]
  have hin : SS.foldSum S (fun t => pauliMEK P s t * QSqrt235i.smul q (g t))
      = QSqrt235i.smul q (SS.foldSum S fun t => pauliMEK P s t * g t) := by
    rw [← foldSum_smul]
    exact Finset.fold_congr (fun t _ => QSqrt235i.mul_smul_right q _ _)
  rw [hin, QSqrt235i.mul_smul_smul]

/-- The scaled integer matrix element **is** the rational one. -/
lemma melK_of_melZ {S : Finset (BitString n)} {ψ0Z ψ1Z : BitString n → ZSqrt235i}
    (q : ℚ) (P : Fin n → SQ) :
    melK S (fun s => QSqrt235i.smul q (toQ (ψ0Z s))) P
          (fun s => QSqrt235i.smul q (toQ (ψ1Z s)))
      = QSqrt235i.smul (q * q) (toQ (melZ S ψ0Z P ψ1Z)) := by
  rw [melK_smul, toQ_melZ]

/-! ## The Knill--Laflamme conditions, as one boolean per Pauli -/

/-- The three conditions at one Pauli, folded into a boolean.  Keeping the
result in `Bool` rather than `Prop` means the kernel evaluates arithmetic
instead of building `Decidable` instances. -/
def klAtZ (S : Finset (BitString n)) (ψ0Z ψ1Z : BitString n → ZSqrt235i)
    (P : Fin n → SQ) : Bool :=
  (melZ S ψ0Z P ψ1Z == zero)
    && (melZ S ψ1Z P ψ0Z == zero)
    && (melZ S ψ0Z P ψ0Z == melZ S ψ1Z P ψ1Z)

lemma klAtZ_spec {S : Finset (BitString n)} {ψ0Z ψ1Z : BitString n → ZSqrt235i}
    {P : Fin n → SQ} (h : klAtZ S ψ0Z ψ1Z P = true) :
    melZ S ψ0Z P ψ1Z = zero ∧ melZ S ψ1Z P ψ0Z = zero
      ∧ melZ S ψ0Z P ψ0Z = melZ S ψ1Z P ψ1Z := by
  rw [klAtZ, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1.1, by simpa using h.1.2, by simpa using h.2⟩

/-- **The transport.**  A code whose amplitudes are `q` times integer ring
elements satisfies the exact-field KL conditions as soon as its integer mirror
does, for every Pauli of weight at most two.  The hypothesis is a single
decidable statement over the integers. -/
theorem KLmatK_of_int {S : Finset (BitString n)} {ψ0Z ψ1Z : BitString n → ZSqrt235i}
    (q : ℚ) (h : ∀ P : Fin n → SQ, pauliWt P ≤ 2 → klAtZ S ψ0Z ψ1Z P = true) :
    KLmatK S (fun s => QSqrt235i.smul q (toQ (ψ0Z s)))
            (fun s => QSqrt235i.smul q (toQ (ψ1Z s))) := by
  intro P hP
  obtain ⟨h01, h10, hd⟩ := klAtZ_spec (h P hP)
  refine ⟨?_, ?_, ?_⟩
  · rw [melK_of_melZ q P, h01, toQ_zero]; exact QSqrt235i.smul_zero' _
  · rw [melK_of_melZ q P, h10, toQ_zero]; exact QSqrt235i.smul_zero' _
  · rw [melK_of_melZ q P, melK_of_melZ q P, hd]

end DyadicLifts
