import Mathlib
import SS.HilbertKL
import SixQubit.BEnumerator
import SixQubit.Orbit8Real

/-!
# Orbit 8: the excitation-rotation attainment family

This file turns the continuous construction in the supplementary material into
an exact kernel certificate.  Starting with `Orbit8Real`, we rotate qubits 4
and 0 by the real excitation-preserving matrix

```
|10> |-> C |10> - S |01>,       C^2 + S^2 = 1,
```

and leave `|00>` and `|11>` fixed.  The original realization has qubit 4
fixed to one, so every new amplitude is a linear polynomial in `C,S` with
coefficients in `Z[sqrt 2,sqrt 3,i]`.

The Knill--Laflamme and low-weight trace calculations below are not numerical
sampling.  `QuadZ` records all six coefficients of the resulting quadratic
polynomial.  Kernel `decide` checks the coefficient identities for every Pauli
mask; `eval_zero_of_circle` is the proof that the sole relation
`C^2+S^2=1` transports those identities to genuine complex amplitudes.
-/

namespace SixQubit.Orbit8Family

open scoped BigOperators
open SixQubit.Realize SixQubit.Orbit8Real
open SS.MacWilliams

/-! ## Linear and quadratic exact coefficient records -/

/-- `k + c*C + s*S`, with exact algebraic-integer coefficients. -/
structure LinZ where
  k : ZQ
  c : ZQ
  s : ZQ
deriving DecidableEq

namespace LinZ

def zero : LinZ := ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩

end LinZ

/-- `k + c*C + s*S + cc*C^2 + cs*C*S + ss*S^2`. -/
structure QuadZ where
  k : ZQ
  c : ZQ
  s : ZQ
  cc : ZQ
  cs : ZQ
  ss : ZQ
deriving DecidableEq

namespace QuadZ

def zero : QuadZ :=
  ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero⟩

def const (a : Int) : QuadZ :=
  ⟨z8 a 0 0 0 0 0 0 0, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero⟩

def add (p q : QuadZ) : QuadZ :=
  ⟨ZQ.add p.k q.k, ZQ.add p.c q.c, ZQ.add p.s q.s,
   ZQ.add p.cc q.cc, ZQ.add p.cs q.cs, ZQ.add p.ss q.ss⟩

def neg (p : QuadZ) : QuadZ :=
  ⟨ZQ.neg p.k, ZQ.neg p.c, ZQ.neg p.s,
   ZQ.neg p.cc, ZQ.neg p.cs, ZQ.neg p.ss⟩

def sub (p q : QuadZ) : QuadZ := add p (neg q)

def signMul (b : Bool) (p : QuadZ) : QuadZ := if b then neg p else p

/-- Coefficients of `conj(eval u) * eval v`. -/
def mulConj (u v : LinZ) : QuadZ :=
  ⟨ZQ.mul (ZQ.conj u.k) v.k,
   ZQ.add (ZQ.mul (ZQ.conj u.k) v.c) (ZQ.mul (ZQ.conj u.c) v.k),
   ZQ.add (ZQ.mul (ZQ.conj u.k) v.s) (ZQ.mul (ZQ.conj u.s) v.k),
   ZQ.mul (ZQ.conj u.c) v.c,
   ZQ.add (ZQ.mul (ZQ.conj u.c) v.s) (ZQ.mul (ZQ.conj u.s) v.c),
   ZQ.mul (ZQ.conj u.s) v.s⟩

lemma mulConj_zero_right (u : LinZ) : mulConj u LinZ.zero = zero := by
  unfold mulConj LinZ.zero
  simp only [ZQ.mul_zero_right]
  rfl

lemma signMul_zero (b : Bool) : signMul b zero = zero := by
  cases b <;> decide

end QuadZ

/-! ## The rotated exact amplitude tables -/

/-- Toggle the two rotated coordinates, 0 and 4. -/
def flip40 : SS.BitString 6 := bs true false false false true false

/-- The exact coefficient record after rotating a table whose input support
has coordinate 4 fixed to one. -/
def rotateCoeff (f : SS.BitString 6 → ZQ) (x : SS.BitString 6) : LinZ :=
  if x 4 then
    if x 0 then ⟨f x, ZQ.zero, ZQ.zero⟩
    else ⟨ZQ.zero, f x, ZQ.zero⟩
  else if x 0 then
    ⟨ZQ.zero, ZQ.zero, ZQ.neg (f (SS.bxor x flip40))⟩
  else LinZ.zero

def c0q : SS.BitString 6 → LinZ := rotateCoeff c0z
def c1q : SS.BitString 6 → LinZ := rotateCoeff c1z

/-- New support positions created from input words with coordinate 0 zero. -/
def moved (L : List (SS.BitString 6)) : List (SS.BitString 6) :=
  (L.filter (fun x => !(x 0))).map (fun x => SS.bxor x flip40)

def F0 : List (SS.BitString 6) := L0 ++ moved L0
def F1 : List (SS.BitString 6) := L1 ++ moved L1

theorem F0_nodup : F0.Nodup := by decide
theorem F1_nodup : F1.Nodup := by decide

theorem c0q_vanishes : ∀ x : SS.BitString 6, x ∉ F0 → c0q x = LinZ.zero := by decide
theorem c1q_vanishes : ∀ x : SS.BitString 6, x ∉ F1 → c1q x = LinZ.zero := by decide

/-- The rotation preserves the all-ones residue, now on the complete output
support rather than merely on the eleven input positions. -/
theorem F0_in_fiber : ∀ x ∈ F0, SS.weight av x = 0 := by decide
theorem F1_in_fiber : ∀ x ∈ F1, SS.weight av x = 1 := by decide

/-! ## Evaluation in genuine complex amplitudes -/

noncomputable section

def evalLin (C S : ℝ) (u : LinZ) : ℂ :=
  toC u.k + (C : ℂ) * toC u.c + (S : ℂ) * toC u.s

def evalQuad (C S : ℝ) (q : QuadZ) : ℂ :=
  toC q.k + (C : ℂ) * toC q.c + (S : ℂ) * toC q.s
    + (C : ℂ)^2 * toC q.cc + (C : ℂ) * (S : ℂ) * toC q.cs
    + (S : ℂ)^2 * toC q.ss

@[simp] lemma evalLin_zero (C S : ℝ) : evalLin C S LinZ.zero = 0 := by
  simp [evalLin, LinZ.zero]

@[simp] lemma evalQuad_zero (C S : ℝ) : evalQuad C S QuadZ.zero = 0 := by
  simp [evalQuad, QuadZ.zero]

lemma evalQuad_add (C S : ℝ) (p q : QuadZ) :
    evalQuad C S (QuadZ.add p q) = evalQuad C S p + evalQuad C S q := by
  simp only [evalQuad, QuadZ.add, toC_add]
  ring

lemma evalQuad_neg (C S : ℝ) (p : QuadZ) :
    evalQuad C S (QuadZ.neg p) = -evalQuad C S p := by
  simp only [evalQuad, QuadZ.neg, toC_neg]
  ring

lemma evalQuad_sub (C S : ℝ) (p q : QuadZ) :
    evalQuad C S (QuadZ.sub p q) = evalQuad C S p - evalQuad C S q := by
  rw [QuadZ.sub, evalQuad_add, evalQuad_neg]
  ring

lemma evalQuad_signMul (C S : ℝ) (b : Bool) (p : QuadZ) :
    evalQuad C S (QuadZ.signMul b p) = SS.signC b (evalQuad C S p) := by
  cases b
  · rfl
  · exact evalQuad_neg C S p

lemma evalQuad_mulConj (C S : ℝ) (u v : LinZ) :
    evalQuad C S (QuadZ.mulConj u v) = star (evalLin C S u) * evalLin C S v := by
  simp only [evalQuad, evalLin, QuadZ.mulConj, toC_mul, toC_conj, toC_add,
    map_add, map_mul, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The two genuine logical words of the rotated family. -/
def w0 (C S : ℝ) : SS.State 6 ℂ := fun x => sc * evalLin C S (c0q x)
def w1 (C S : ℝ) : SS.State 6 ℂ := fun x => sc * evalLin C S (c1q x)

def code (C S : ℝ) : Fin 2 → SS.State 6 ℂ := ![w0 C S, w1 C S]

theorem w0_vanishes (C S : ℝ) (x : SS.BitString 6) (hx : x ∉ F0) :
    w0 C S x = 0 := by
  rw [w0, c0q_vanishes x hx, evalLin_zero, mul_zero]

theorem w1_vanishes (C S : ℝ) (x : SS.BitString 6) (hx : x ∉ F1) :
    w1 C S x = 0 := by
  rw [w1, c1q_vanishes x hx, evalLin_zero, mul_zero]

/-- Full-fiber support statement for the bottom logical word. -/
theorem w0_full_fiber (C S : ℝ) (x : SS.BitString 6)
    (hx : SS.weight av x ≠ 0) : w0 C S x = 0 := by
  apply w0_vanishes
  intro hmem
  exact hx (F0_in_fiber x hmem)

/-- Full-fiber support statement for the top logical word. -/
theorem w1_full_fiber (C S : ℝ) (x : SS.BitString 6)
    (hx : SS.weight av x ≠ 1) : w1 C S x = 0 := by
  apply w1_vanishes
  intro hmem
  exact hx (F1_in_fiber x hmem)

/-! ## Symbolic matrix elements and the KL certificate -/

def qterm (cj ck : SS.BitString 6 → LinZ) (x z t : SS.BitString 6) : QuadZ :=
  QuadZ.signMul (SS.bdot z t) (QuadZ.mulConj (cj (SS.bxor t x)) (ck t))

def qsum (L : List (SS.BitString 6)) (f : SS.BitString 6 → QuadZ) : QuadZ :=
  (L.map f).foldr QuadZ.add QuadZ.zero

def qmat (cj ck : SS.BitString 6 → LinZ) (L : List (SS.BitString 6))
    (x z : SS.BitString 6) : QuadZ := qsum L (qterm cj ck x z)

lemma eval_qsum (C S : ℝ) (L : List (SS.BitString 6))
    (f : SS.BitString 6 → QuadZ) :
    evalQuad C S (qsum L f) = (L.map (fun x => evalQuad C S (f x))).sum := by
  unfold qsum
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons, evalQuad_add, ih]

lemma qterm_eq_zero {cj ck : SS.BitString 6 → LinZ} {x z t : SS.BitString 6}
    (h : ck t = LinZ.zero) : qterm cj ck x z t = QuadZ.zero := by
  unfold qterm
  rw [h]
  rw [QuadZ.mulConj_zero_right, QuadZ.signMul_zero]

/-- The symbolic sum evaluates to the genuine Hilbert-space matrix element. -/
theorem innerC_pauli_eq (C S : ℝ) (cj ck : SS.BitString 6 → LinZ)
    (L : List (SS.BitString 6)) (hnd : L.Nodup)
    (hv : ∀ t, t ∉ L → ck t = LinZ.zero) (P : SS.PauliString 6) :
    SS.innerC (fun x => sc * evalLin C S (cj x))
        (SS.pauliAct P (fun x => sc * evalLin C S (ck x)))
      = star sc * sc * (Complex.I ^ P.numY) * evalQuad C S (qmat cj ck L P.x P.z) := by
  classical
  have hcong : ∀ t : SS.BitString 6,
      SS.signC (SS.bdot P.z t)
          (star (sc * evalLin C S (cj (SS.bxor t P.x))) *
            (sc * evalLin C S (ck t)))
        = star sc * sc * evalQuad C S (qterm cj ck P.x P.z t) := by
    intro t
    rw [qterm, evalQuad_signMul, evalQuad_mulConj]
    cases SS.bdot P.z t <;>
      simp only [SS.signC_true, SS.signC_false, star_mul'] <;> ring
  have hsub : ∑ t : SS.BitString 6, evalQuad C S (qterm cj ck P.x P.z t)
      = ∑ t ∈ L.toFinset, evalQuad C S (qterm cj ck P.x P.z t) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro t _ ht
    rw [qterm_eq_zero (hv t (by simpa using ht)), evalQuad_zero]
  have hkey : ∑ t : SS.BitString 6,
      SS.signC (SS.bdot P.z t)
          (star (sc * evalLin C S (cj (SS.bxor t P.x))) *
            (sc * evalLin C S (ck t)))
        = star sc * sc * evalQuad C S (qmat cj ck L P.x P.z) := by
    rw [Finset.sum_congr rfl (fun t _ => hcong t), ← Finset.mul_sum, hsub,
      List.sum_toFinset _ hnd, ← eval_qsum, qmat]
  rw [SS.innerC_pauliAct, hkey]
  ring

/-- Canonical zero modulo `C^2+S^2=1`. -/
def CircleZero (q : QuadZ) : Prop :=
  q.c = ZQ.zero ∧ q.s = ZQ.zero ∧ q.cs = ZQ.zero ∧
    q.cc = q.ss ∧ q.k = ZQ.neg q.ss

instance (q : QuadZ) : Decidable (CircleZero q) := by
  unfold CircleZero
  infer_instance

lemma eval_zero_of_circle (C S : ℝ) (hCS : C^2 + S^2 = 1)
    (q : QuadZ) (hq : CircleZero q) : evalQuad C S q = 0 := by
  rcases hq with ⟨hc, hs, hcs, hcc, hk⟩
  rw [evalQuad, hc, hs, hcs, hcc, hk, toC_zero, toC_neg]
  have hCSc : (C : ℂ)^2 + (S : ℂ)^2 = 1 := by exact_mod_cast hCS
  linear_combination (toC q.ss) * hCSc

def checkKLQ (x z : SS.BitString 6) : Prop :=
  CircleZero (QuadZ.sub (qmat c0q c0q F0 x z) (qmat c1q c1q F1 x z)) ∧
    CircleZero (qmat c0q c1q F1 x z) ∧
    CircleZero (qmat c1q c0q F0 x z)

instance (x z : SS.BitString 6) : Decidable (checkKLQ x z) := by
  unfold checkKLQ
  infer_instance

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 50000 in
/-- Exhaustive exact quadratic KL certificate for all masks of weight at most
two. -/
theorem check_all : ∀ m < 64, ∀ k < 64,
    (⟨nbit m, nbit k⟩ : SS.PauliString 6).wt ≤ 2 →
      checkKLQ (nbit m) (nbit k) := by decide

theorem check_of_wt (P : SS.PauliString 6) (hP : P.wt ≤ 2) :
    checkKLQ P.x P.z := by
  have hx := nbit_num P.x
  have hz := nbit_num P.z
  have h := check_all (num P.x) (num_lt _) (num P.z) (num_lt _)
    (by rw [hx, hz]; exact hP)
  rwa [hx, hz] at h

/-- The rotated pair is a genuine distance-three code for every point of the
unit circle. -/
theorem is_code (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    SS.HasDistance (code C S) 3 := by
  change SS.HasDistance ![w0 C S, w1 C S] 3
  intro P hP
  have hchk := check_of_wt P hP
  rcases hchk with ⟨hdiag, h01, h10⟩
  refine ⟨SS.innerC (w0 C S) (SS.pauliAct P (w0 C S)), ?_⟩
  intro j k
  fin_cases j <;> fin_cases k
  · change SS.innerC (w0 C S) (SS.pauliAct P (w0 C S)) = _
    rw [if_pos rfl]
  · change SS.innerC (w0 C S) (SS.pauliAct P (w1 C S)) = _
    rw [if_neg (by decide)]
    change SS.innerC (fun x => sc * evalLin C S (c0q x))
      (SS.pauliAct P (fun x => sc * evalLin C S (c1q x))) = 0
    rw [innerC_pauli_eq C S c0q c1q F1 F1_nodup c1q_vanishes P,
      eval_zero_of_circle C S hCS _ h01, mul_zero]
  · change SS.innerC (w1 C S) (SS.pauliAct P (w0 C S)) = _
    rw [if_neg (by decide)]
    change SS.innerC (fun x => sc * evalLin C S (c1q x))
      (SS.pauliAct P (fun x => sc * evalLin C S (c0q x))) = 0
    rw [innerC_pauli_eq C S c1q c0q F0 F0_nodup c0q_vanishes P,
      eval_zero_of_circle C S hCS _ h10, mul_zero]
  · change SS.innerC (w1 C S) (SS.pauliAct P (w1 C S)) = _
    rw [if_pos rfl]
    change SS.innerC (fun x => sc * evalLin C S (c1q x))
        (SS.pauliAct P (fun x => sc * evalLin C S (c1q x))) =
      SS.innerC (fun x => sc * evalLin C S (c0q x))
        (SS.pauliAct P (fun x => sc * evalLin C S (c0q x)))
    rw [innerC_pauli_eq C S c0q c0q F0 F0_nodup c0q_vanishes P,
      innerC_pauli_eq C S c1q c1q F1 F1_nodup c1q_vanishes P]
    have hz := eval_zero_of_circle C S hCS _ hdiag
    rw [evalQuad_sub] at hz
    have heq : evalQuad C S (qmat c0q c0q F0 P.x P.z) =
        evalQuad C S (qmat c1q c1q F1 P.x P.z) := sub_eq_zero.mp hz
    rw [heq]

end

end SixQubit.Orbit8Family
