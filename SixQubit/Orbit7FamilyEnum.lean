import SixQubit.Orbit7Family
import SixQubit.Orbit8FamilyEnum
import SixQubit.Shadow

/-!
# Orbit 7 circle family: exact low-weight projector traces

For the circle family of `Orbit7Family`, the only nonzero projector traces
through Pauli weight two are

```
    tr(P X_0)       =  4 C S,
    tr(P Z_0 Z_2)   = -2 (C^2-S^2).
```

This file proves the sparsity statement by an exhaustive coefficient check
over all Pauli masks.  It also proves normalization from the exact quadratic
tables.  These are raw Shor--Laflamme conventions, so their squared norms
give `A_1=16 C^2 S^2` and `A_2=4(C^2-S^2)^2`.
-/

namespace SixQubit.Orbit7Family

open scoped BigOperators
open SixQubit.Realize SixQubit.Orbit7Real
open SixQubit.Orbit8Family
open SS.MacWilliams

def qtrace (x z : SS.BitString 6) : QuadZ :=
  QuadZ.add (qmat c0q c0q F0 x z) (qmat c1q c1q F1 x z)

def z0 : SS.BitString 6 := fun _ => false
def e2 : SS.BitString 6 := bs false false true false false false
def e02 : SS.BitString 6 := bs true false true false false false

def PId : SS.PauliString 6 := ⟨z0, z0⟩
def PX0 : SS.PauliString 6 := ⟨e0, z0⟩
def PZ02 : SS.PauliString 6 := ⟨z0, e02⟩

def qX0 : QuadZ :=
  ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero,
    z8 576 0 0 0 0 0 0 0, ZQ.zero⟩

def qZ02 : QuadZ :=
  ⟨ZQ.zero, ZQ.zero, ZQ.zero,
    z8 (-288) 0 0 0 0 0 0 0, ZQ.zero,
    z8 288 0 0 0 0 0 0 0⟩

theorem qtrace_X0 : qtrace PX0.x PX0.z = qX0 := by decide
theorem qtrace_Z02 : qtrace PZ02.x PZ02.z = qZ02 := by decide

theorem norm0_exact :
    CircleZero (QuadZ.sub (qmat c0q c0q F0 z0 z0) (QuadZ.const 144)) := by
  decide

theorem norm1_exact :
    CircleZero (QuadZ.sub (qmat c1q c1q F1 z0 z0) (QuadZ.const 144)) := by
  decide

def specialMask (m k : Nat) : Bool :=
  decide ((m = 0 ∧ k = 0) ∨ (m = 1 ∧ k = 0) ∨ (m = 0 ∧ k = 5))

def qtraceOK (m k : Nat) : Bool :=
  let P : SS.PauliString 6 := ⟨nbit m, nbit k⟩
  if decide (P.wt ≤ 2) then
    if specialMask m k then true
    else SixQubit.Orbit8Family.circleZeroB (qtrace P.x P.z)
  else true

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 50000 in
/-- The coefficient-level sparsity check for all low-weight Pauli masks. -/
theorem qtrace_check_all : ∀ m < 64, ∀ k < 64, qtraceOK m k = true := by
  decide

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
    (hi : P ≠ PId) (hx : P ≠ PX0) (hz02 : P ≠ PZ02) :
    CircleZero (qtrace P.x P.z) := by
  have h := qtrace_check_all (num P.x) (num_lt _) (num P.z) (num_lt _)
  have hspecial : ¬ ((num P.x = 0 ∧ num P.z = 0) ∨
      (num P.x = 1 ∧ num P.z = 0) ∨
      (num P.x = 0 ∧ num P.z = 5)) := by
    intro hs
    rcases hs with hs | hs | hs
    · exact hi (pauli_eq_of_nums P PId hs.1 (by simpa [PId, z0] using hs.2))
    · exact hx (pauli_eq_of_nums P PX0
        (by simpa [PX0, e0] using hs.1) (by simpa [PX0, z0] using hs.2))
    · exact hz02 (pauli_eq_of_nums P PZ02 hs.1
        (by simpa [PZ02, e02] using hs.2))
  have hxb := nbit_num P.x
  have hzb := nbit_num P.z
  have hmk : (⟨P.x, P.z⟩ : SS.PauliString 6) = P := by cases P; rfl
  simp only [qtraceOK] at h
  simp [specialMask, hspecial] at h
  rw [hxb, hzb] at h
  rcases h with hlarge | hzero
  · rw [hmk] at hlarge
    omega
  · exact (SixQubit.Orbit8Family.circleZeroB_iff _).mp hzero

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
  rw [he, show (starRingEnd ℂ sc * sc = (1/144 : ℂ)) from sc_sq]
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
  rw [hm]
  have he := eval_eq_const_of_rel C S hCS _ 144 norm1_exact
  rw [he, show (starRingEnd ℂ sc * sc = (1/144 : ℂ)) from sc_sq]
  norm_num

theorem normalized (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    ∀ k, SS.innerC (code C S k) (code C S k) = 1 := by
  intro k
  fin_cases k
  · exact w0_normalized C S hCS
  · exact w1_normalized C S hCS

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

lemma eval_qX0 (C S : ℝ) : evalQuad C S qX0 = (576*C*S : ℂ) := by
  simp [evalQuad, qX0, toC_intCast]
  ring

lemma eval_qZ02 (C S : ℝ) :
    evalQuad C S qZ02 = (-288*(C^2-S^2) : ℂ) := by
  simp [evalQuad, qZ02, toC_intCast]
  ring

theorem trProj_X0 (C S : ℝ) :
    trProj (code C S) PX0 = ((4*C*S : ℝ) : ℂ) := by
  rw [trProj_eq_qtrace, qtrace_X0, eval_qX0, sc_sq]
  have hn : PX0.numY = 0 := by decide
  rw [hn, pow_zero]
  norm_num
  ring

theorem trProj_Z02 (C S : ℝ) :
    trProj (code C S) PZ02 = ((-2*(C^2-S^2) : ℝ) : ℂ) := by
  rw [trProj_eq_qtrace, qtrace_Z02, eval_qZ02, sc_sq]
  have hn : PZ02.numY = 0 := by decide
  rw [hn, pow_zero]
  norm_num
  ring

theorem trProj_sparse (C S : ℝ) (hCS : C^2 + S^2 = 1)
    (P : SS.PauliString 6) (hwt : P.wt ≤ 2)
    (hi : P ≠ PId) (hx : P ≠ PX0) (hz02 : P ≠ PZ02) :
    trProj (code C S) P = 0 := by
  rw [trProj_eq_qtrace,
    eval_zero_of_circle C S hCS _ (qtrace_sparse_of_wt P hwt hi hx hz02), mul_zero]

end

end SixQubit.Orbit7Family
