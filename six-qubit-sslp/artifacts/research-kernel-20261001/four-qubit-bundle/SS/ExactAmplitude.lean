import SS.QSqrt235iC

/-! Exact integer amplitude arithmetic, extracted from the established Orbit36Code
implementation. No canonical code or classification theorem is imported. -/

namespace SS.ExactAmplitude

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


end SS.ExactAmplitude
