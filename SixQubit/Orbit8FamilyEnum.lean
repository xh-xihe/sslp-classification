import SixQubit.Orbit8Family
import SixQubit.Shadow

/-!
# Orbit 8 family: normalization and weight enumerators

This second layer consumes the exact symbolic KL certificate from
`Orbit8Family` and computes the complete Shor--Laflamme image of the rotated
family.
-/

namespace SixQubit.Orbit8Family

open scoped BigOperators
open SixQubit.Realize SixQubit.Orbit8Real
open SS.MacWilliams

def qtrace (x z : SS.BitString 6) : QuadZ :=
  QuadZ.add (qmat c0q c0q F0 x z) (qmat c1q c1q F1 x z)

def z0 : SS.BitString 6 := fun _ => false
def e0 : SS.BitString 6 := bs true false false false false false
def e4 : SS.BitString 6 := bs false false false false true false
def e04 : SS.BitString 6 := bs true false false false true false

def PZ0 : SS.PauliString 6 := ⟨z0, e0⟩
def PZ4 : SS.PauliString 6 := ⟨z0, e4⟩
def PXX : SS.PauliString 6 := ⟨e04, z0⟩
def PYY : SS.PauliString 6 := ⟨e04, e04⟩
def PId : SS.PauliString 6 := ⟨z0, z0⟩

def qZ0 : QuadZ :=
  ⟨z8 (-144) 0 0 0 0 0 0 0, ZQ.zero, ZQ.zero,
   z8 144 0 0 0 0 0 0 0, ZQ.zero, z8 (-144) 0 0 0 0 0 0 0⟩

def qZ4 : QuadZ :=
  ⟨z8 (-144) 0 0 0 0 0 0 0, ZQ.zero, ZQ.zero,
   z8 (-144) 0 0 0 0 0 0 0, ZQ.zero, z8 144 0 0 0 0 0 0 0⟩

def qXX : QuadZ :=
  ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero,
   z8 (-288) 0 0 0 0 0 0 0, ZQ.zero⟩

def qYY : QuadZ :=
  ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero,
   z8 288 0 0 0 0 0 0 0, ZQ.zero⟩

theorem qtrace_Z0 : qtrace PZ0.x PZ0.z = qZ0 := by decide
theorem qtrace_Z4 : qtrace PZ4.x PZ4.z = qZ4 := by decide
theorem qtrace_XX : qtrace PXX.x PXX.z = qXX := by decide
theorem qtrace_YY : qtrace PYY.x PYY.z = qYY := by decide

theorem norm0_exact :
    CircleZero (QuadZ.sub (qmat c0q c0q F0 z0 z0) (QuadZ.const 144)) := by decide

theorem norm1_exact :
    CircleZero (QuadZ.sub (qmat c1q c1q F1 z0 z0) (QuadZ.const 144)) := by decide

def circleZeroB (q : QuadZ) : Bool :=
  decide (q.c = ZQ.zero) && decide (q.s = ZQ.zero) && decide (q.cs = ZQ.zero) &&
    decide (q.cc = q.ss) && decide (q.k = ZQ.neg q.ss)

lemma circleZeroB_iff (q : QuadZ) : circleZeroB q = true ↔ CircleZero q := by
  simp [circleZeroB, CircleZero]
  tauto

def specialMask (m k : Nat) : Bool :=
  decide ((m = 0 ∧ k = 0) ∨ (m = 0 ∧ k = 1) ∨ (m = 0 ∧ k = 16) ∨
    (m = 17 ∧ k = 0) ∨ (m = 17 ∧ k = 17))

def qtraceOK (m k : Nat) : Bool :=
  let P : SS.PauliString 6 := ⟨nbit m, nbit k⟩
  if decide (P.wt ≤ 2) then
    if specialMask m k then true else circleZeroB (qtrace P.x P.z)
  else true

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 50000 in
/-- Apart from the four displayed Paulis, every projector trace of weight at
most three is zero modulo the circle relation. -/
theorem qtrace_check_all : ∀ m < 64, ∀ k < 64,
    qtraceOK m k = true := by decide

lemma num_injective : Function.Injective num := by
  intro x y h
  rw [← nbit_num x, ← nbit_num y, h]

lemma pauli_eq_of_nums (P Q : SS.PauliString 6)
    (hx : num P.x = num Q.x) (hz : num P.z = num Q.z) : P = Q := by
  cases P with
  | mk px pz =>
    cases Q with
    | mk qx qz =>
      simp only [SS.PauliString.mk.injEq]
      exact ⟨num_injective hx, num_injective hz⟩

theorem qtrace_sparse_of_wt (P : SS.PauliString 6) (hwt : P.wt ≤ 2)
    (hi : P ≠ PId) (h0 : P ≠ PZ0) (h4 : P ≠ PZ4)
    (hx : P ≠ PXX) (hy : P ≠ PYY) :
    CircleZero (qtrace P.x P.z) := by
  have h := qtrace_check_all (num P.x) (num_lt _) (num P.z) (num_lt _)
  have hspecial : ¬ ((num P.x = 0 ∧ num P.z = 0) ∨
      (num P.x = 0 ∧ num P.z = 1) ∨
      (num P.x = 0 ∧ num P.z = 16) ∨
      (num P.x = 17 ∧ num P.z = 0) ∨
      (num P.x = 17 ∧ num P.z = 17)) := by
    intro hs
    rcases hs with hs | hs | hs | hs | hs
    · exact hi (pauli_eq_of_nums P PId hs.1 (by simpa [PId, z0] using hs.2))
    · exact h0 (pauli_eq_of_nums P PZ0 hs.1 (by simpa [PZ0, z0, e0] using hs.2))
    · exact h4 (pauli_eq_of_nums P PZ4 hs.1 (by simpa [PZ4, z0, e4] using hs.2))
    · exact hx (pauli_eq_of_nums P PXX
        (by simpa [PXX, e04, z0] using hs.1) hs.2)
    · exact hy (pauli_eq_of_nums P PYY
        (by simpa [PYY, e04] using hs.1) (by simpa [PYY, e04] using hs.2))
  have hxb := nbit_num P.x
  have hzb := nbit_num P.z
  have hmk : (⟨P.x, P.z⟩ : SS.PauliString 6) = P := by cases P; rfl
  simp only [qtraceOK] at h
  simp [specialMask, hspecial] at h
  rw [hxb, hzb] at h
  rcases h with hlarge | hzero
  · rw [hmk] at hlarge
    omega
  · exact (circleZeroB_iff _).mp hzero

noncomputable section

lemma sc_sq : star sc * sc = (1/144 : ℂ) := by
  rw [sc]
  norm_num [Complex.star_def, Complex.conj_ofNat]

lemma eval_const (C S : ℝ) (a : Int) :
    evalQuad C S (QuadZ.const a) = (a : ℂ) := by
  simp [evalQuad, QuadZ.const, toC_intCast]

lemma eval_eq_const_of_rel (C S : ℝ) (hCS : C^2 + S^2 = 1)
    (q : QuadZ) (a : Int) (h : CircleZero (QuadZ.sub q (QuadZ.const a))) :
    evalQuad C S q = (a : ℂ) := by
  have hz := eval_zero_of_circle C S hCS _ h
  rw [evalQuad_sub, eval_const] at hz
  exact sub_eq_zero.mp hz

theorem w0_normalized (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    SS.innerC (w0 C S) (w0 C S) = 1 := by
  let I0 : SS.PauliString 6 := ⟨z0, z0⟩
  have hP : I0.numY = 0 := by decide
  let u : SS.State 6 ℂ := fun x => sc * evalLin C S (c0q x)
  have hx : ∀ t, SS.bxor t I0.x = t := by
    intro t
    exact SS.bxor_zero t
  have hz : ∀ t, SS.bdot I0.z t = false := by
    intro t
    simp [I0, z0, SS.bdot]
  have hact : SS.pauliAct I0 u = u := by
    funext t
    simp only [SS.pauliAct, hP, pow_zero, one_mul]
    rw [hx t, hz t, SS.signC_false]
  have hm := innerC_pauli_eq C S c0q c0q F0 F0_nodup c0q_vanishes I0
  change SS.innerC u (SS.pauliAct I0 u) = _ at hm
  rw [hact] at hm
  dsimp [I0] at hm
  rw [hP, pow_zero, mul_one] at hm
  change SS.innerC u u = 1
  rw [hm]
  have he := eval_eq_const_of_rel C S hCS _ 144 norm0_exact
  rw [he, show (starRingEnd ℂ) sc * sc = (1/144 : ℂ) from sc_sq]
  norm_num

theorem w1_normalized (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    SS.innerC (w1 C S) (w1 C S) = 1 := by
  let I0 : SS.PauliString 6 := ⟨z0, z0⟩
  have hP : I0.numY = 0 := by decide
  let u : SS.State 6 ℂ := fun x => sc * evalLin C S (c1q x)
  have hx : ∀ t, SS.bxor t I0.x = t := by
    intro t
    exact SS.bxor_zero t
  have hz : ∀ t, SS.bdot I0.z t = false := by
    intro t
    simp [I0, z0, SS.bdot]
  have hact : SS.pauliAct I0 u = u := by
    funext t
    simp only [SS.pauliAct, hP, pow_zero, one_mul]
    rw [hx t, hz t, SS.signC_false]
  have hm := innerC_pauli_eq C S c1q c1q F1 F1_nodup c1q_vanishes I0
  change SS.innerC u (SS.pauliAct I0 u) = _ at hm
  rw [hact] at hm
  dsimp [I0] at hm
  rw [hP, pow_zero, mul_one] at hm
  change SS.innerC u u = 1
  have he := eval_eq_const_of_rel C S hCS _ 144 norm1_exact
  rw [hm, he, show (starRingEnd ℂ) sc * sc = (1/144 : ℂ) from sc_sq]
  norm_num

theorem trProj_eq_qtrace (C S : ℝ) (P : SS.PauliString 6) :
    trProj (code C S) P =
      star sc * sc * (Complex.I ^ P.numY) * evalQuad C S (qtrace P.x P.z) := by
  rw [trProj, Fin.sum_univ_two]
  change SS.innerC (fun x => sc * evalLin C S (c0q x))
      (SS.pauliAct P (fun x => sc * evalLin C S (c0q x))) +
    SS.innerC (fun x => sc * evalLin C S (c1q x))
      (SS.pauliAct P (fun x => sc * evalLin C S (c1q x))) = _
  rw [innerC_pauli_eq C S c0q c0q F0 F0_nodup c0q_vanishes P,
    innerC_pauli_eq C S c1q c1q F1 F1_nodup c1q_vanishes P,
    qtrace, evalQuad_add]
  ring

lemma eval_qZ0 (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    evalQuad C S qZ0 = (-288 * S^2 : ℝ) := by
  simp only [evalQuad, qZ0, toC_intCast, toC_zero]
  have hCSc : (C : ℂ)^2 + (S : ℂ)^2 = 1 := by exact_mod_cast hCS
  push_cast
  linear_combination (144 : ℂ) * hCSc

lemma eval_qZ4 (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    evalQuad C S qZ4 = (-288 * C^2 : ℝ) := by
  simp only [evalQuad, qZ4, toC_intCast, toC_zero]
  have hCSc : (C : ℂ)^2 + (S : ℂ)^2 = 1 := by exact_mod_cast hCS
  push_cast
  linear_combination (144 : ℂ) * hCSc

lemma eval_qXX (C S : ℝ) : evalQuad C S qXX = (-288 * C * S : ℝ) := by
  simp [evalQuad, qXX, toC_intCast]
  ring

lemma eval_qYY (C S : ℝ) : evalQuad C S qYY = (288 * C * S : ℝ) := by
  simp [evalQuad, qYY, toC_intCast]
  ring

theorem trProj_Z0 (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    trProj (code C S) PZ0 = ((-2 * S^2 : ℝ) : ℂ) := by
  rw [trProj_eq_qtrace, qtrace_Z0, eval_qZ0 C S hCS, sc_sq]
  have hn : PZ0.numY = 0 := by decide
  rw [hn, pow_zero]
  norm_num
  ring

theorem trProj_Z4 (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    trProj (code C S) PZ4 = ((-2 * C^2 : ℝ) : ℂ) := by
  rw [trProj_eq_qtrace, qtrace_Z4, eval_qZ4 C S hCS, sc_sq]
  have hn : PZ4.numY = 0 := by decide
  rw [hn, pow_zero]
  norm_num
  ring

theorem trProj_XX (C S : ℝ) :
    trProj (code C S) PXX = ((-2 * C * S : ℝ) : ℂ) := by
  rw [trProj_eq_qtrace, qtrace_XX, eval_qXX, sc_sq]
  have hn : PXX.numY = 0 := by decide
  rw [hn, pow_zero]
  norm_num
  ring

theorem trProj_YY (C S : ℝ) :
    trProj (code C S) PYY = ((-2 * C * S : ℝ) : ℂ) := by
  rw [trProj_eq_qtrace, qtrace_YY, eval_qYY, sc_sq]
  have hn : PYY.numY = 2 := by decide
  rw [hn, pow_two, Complex.I_mul_I]
  norm_num
  ring

theorem trProj_sparse (C S : ℝ) (hCS : C^2 + S^2 = 1)
    (P : SS.PauliString 6) (hwt : P.wt ≤ 2)
    (hi : P ≠ PId) (h0 : P ≠ PZ0) (h4 : P ≠ PZ4)
    (hx : P ≠ PXX) (hy : P ≠ PYY) :
    trProj (code C S) P = 0 := by
  rw [trProj_eq_qtrace,
    eval_zero_of_circle C S hCS _ (qtrace_sparse_of_wt P hwt hi h0 h4 hx hy), mul_zero]

end

end SixQubit.Orbit8Family
