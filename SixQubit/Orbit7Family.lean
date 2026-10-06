import SixQubit.Orbit7Real
import SixQubit.Orbit8Family

/-!
# Orbit 7: an exact circle family

This module gives the exact attainment family used for orbit 7.  Starting
from `Orbit7Real`, replace each logical word `f` by

```
    C f + S X_0 f,                 C^2 + S^2 = 1.
```

The original support has `x_0 != x_2`, whereas its `X_0` translate has
`x_0 = x_2`; consequently the two summands have disjoint support.  Since the
zeroth angle is zero, the translate remains in the same complete residue
fiber.

The proof is coefficient exact.  We reuse the generic linear/quadratic
records from `Orbit8Family`: every matrix element is a quadratic polynomial
over `Z[sqrt 2,sqrt 3,i]`, and kernel `decide` checks its coefficients modulo
the sole relation `C^2+S^2=1`.  No numerical sampling is used.
-/

namespace SixQubit.Orbit7Family

open SixQubit.Realize SixQubit.Orbit7Real
open SixQubit.Orbit8Family

/-! ## Exact amplitude tables -/

/-- The bit flip on coordinate zero. -/
def e0 : SS.BitString 6 := bs true false false false false false

/-- Coefficients of `C*f(x) + S*f(x xor e0)`. -/
def mixCoeff (f : SS.BitString 6 -> ZQ) (x : SS.BitString 6) : LinZ :=
  ⟨ZQ.zero, f x, f (SS.bxor x e0)⟩

def c0q : SS.BitString 6 -> LinZ := mixCoeff c0z
def c1q : SS.BitString 6 -> LinZ := mixCoeff c1z

def moved (L : List (SS.BitString 6)) : List (SS.BitString 6) :=
  L.map (fun x => SS.bxor x e0)

def F0 : List (SS.BitString 6) := L0 ++ moved L0
def F1 : List (SS.BitString 6) := L1 ++ moved L1

theorem F0_nodup : F0.Nodup := by decide
theorem F1_nodup : F1.Nodup := by decide

theorem c0q_vanishes : ∀ x : SS.BitString 6, x ∉ F0 -> c0q x = LinZ.zero := by
  decide

theorem c1q_vanishes : ∀ x : SS.BitString 6, x ∉ F1 -> c1q x = LinZ.zero := by
  decide

theorem F0_in_fiber : ∀ x ∈ F0, SS.weight av x = 0 := by decide
theorem F1_in_fiber : ∀ x ∈ F1, SS.weight av x = 1 := by decide

/-! ## Genuine complex states -/

noncomputable section

/-- The scale is definitionally the same `1/12` used by `Orbit7Real`.  It is
spelled with the orbit-8 name solely because the generic quadratic matrix
element lemma currently lives in that module. -/
private lemma scales_eq : SixQubit.Orbit8Real.sc = sc := by rfl

def w0 (C S : ℝ) : SS.State 6 ℂ :=
  fun x => sc * evalLin C S (c0q x)

def w1 (C S : ℝ) : SS.State 6 ℂ :=
  fun x => sc * evalLin C S (c1q x)

def code (C S : ℝ) : Fin 2 -> SS.State 6 ℂ := ![w0 C S, w1 C S]

theorem w0_vanishes (C S : ℝ) (x : SS.BitString 6) (hx : x ∉ F0) :
    w0 C S x = 0 := by
  rw [w0, c0q_vanishes x hx, evalLin_zero, mul_zero]

theorem w1_vanishes (C S : ℝ) (x : SS.BitString 6) (hx : x ∉ F1) :
    w1 C S x = 0 := by
  rw [w1, c1q_vanishes x hx, evalLin_zero, mul_zero]

theorem w0_full_fiber (C S : ℝ) (x : SS.BitString 6)
    (hx : SS.weight av x ≠ 0) : w0 C S x = 0 := by
  apply w0_vanishes
  intro hmem
  exact hx (F0_in_fiber x hmem)

theorem w1_full_fiber (C S : ℝ) (x : SS.BitString 6)
    (hx : SS.weight av x ≠ 1) : w1 C S x = 0 := by
  apply w1_vanishes
  intro hmem
  exact hx (F1_in_fiber x hmem)

/-! ## Exact quadratic KL certificate -/

def checkKLQ (x z : SS.BitString 6) : Prop :=
  CircleZero (QuadZ.sub
    (qmat c0q c0q F0 x z) (qmat c1q c1q F1 x z)) ∧
  CircleZero (qmat c0q c1q F1 x z) ∧
  CircleZero (qmat c1q c0q F0 x z)

instance (x z : SS.BitString 6) : Decidable (checkKLQ x z) := by
  unfold checkKLQ
  infer_instance

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 50000 in
/-- All Pauli KL equations through weight two, coefficient by coefficient. -/
theorem check_all : ∀ m < 64, ∀ k < 64,
    (⟨nbit m, nbit k⟩ : SS.PauliString 6).wt ≤ 2 ->
      checkKLQ (nbit m) (nbit k) := by
  decide

theorem check_of_wt (P : SS.PauliString 6) (hP : P.wt ≤ 2) :
    checkKLQ P.x P.z := by
  have hx := nbit_num P.x
  have hz := nbit_num P.z
  have h := check_all (num P.x) (num_lt _) (num P.z) (num_lt _)
    (by rw [hx, hz]; exact hP)
  rwa [hx, hz] at h

theorem innerC_pauli_eq (C S : ℝ)
    (cj ck : SS.BitString 6 -> LinZ) (L : List (SS.BitString 6))
    (hnd : L.Nodup) (hv : ∀ t, t ∉ L -> ck t = LinZ.zero)
    (P : SS.PauliString 6) :
    SS.innerC (fun x => sc * evalLin C S (cj x))
        (SS.pauliAct P (fun x => sc * evalLin C S (ck x))) =
      star sc * sc * (Complex.I ^ P.numY) *
        evalQuad C S (qmat cj ck L P.x P.z) := by
  simpa [scales_eq] using
    (SixQubit.Orbit8Family.innerC_pauli_eq C S cj ck L hnd hv P)

/-- Every member of the circle family is a genuine distance-three code. -/
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
    rw [sub_eq_zero.mp hz]

end

end SixQubit.Orbit7Family
