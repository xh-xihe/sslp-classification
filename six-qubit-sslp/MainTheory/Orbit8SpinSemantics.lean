import SixQubit.Orbit8OperatorQP
import MainTheory.PauliWordBridge

set_option autoImplicit false

namespace MainTheory.Orbit8SpinSemantics

open SixQubit.Orbit8Universal
open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.PauliTransferTwo MainTheory.PauliTensorTransfer

def allY : SS.PauliString 6 := ⟨ones6,ones6⟩

theorem xor_ones (x : SS.BitString 6) : SS.bxor x ones6 = SS.complement x := by
  ext j
  simp [SS.bxor,ones6,SS.complement]

theorem spin_sign_table : ∀ x : SS.BitString 6,
    (if SS.bdot ones6 (SS.bxor x ones6) then (1 : ℤ) else -1)=spinSign x := by decide

theorem spinSign_power : ∀ x : SS.BitString 6,
    spinSign x=(-1 : ℤ)^(SS.hammingWt x+1) := by decide

theorem spinJ_pauli (f : SS.State 6 ℂ) :
    spinJ f = SS.pauliAct allY (fun x => star (f x)) := by
  funext x
  have hs := spin_sign_table x
  have hnum : allY.numY=6 := by decide
  simp only [SS.pauliAct]
  rw [hnum]
  simp only [allY]
  have hi : Complex.I^6 = -1 := by
    calc
      _ = (Complex.I^2)^3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [hi]
  unfold spinJ
  rw [← xor_ones x,← hs]
  cases SS.bdot ones6 (SS.bxor x ones6) <;> simp [SS.signC]

theorem spinJ_tensor (f : SS.State 6 ℂ) :
    spinJ f = (tensorKernel (fun _ : Fin 6 => pauli 2)).mulVec (fun x => star (f x)) := by
  have ht : tensorKernel (fun _ : Fin 6 => pauli 2)=
      MainTheory.PauliKernelTrace.pauliKernel allY :=
    MainTheory.PauliWordBridge.wordKernel_pauliWordEquiv allY
  rw [ht,spinJ_pauli]
  exact (MainTheory.PauliKernelTrace.kernelAction_pauliKernel allY _).symm

noncomputable def ket (x : SS.BitString 6) : SS.State 6 ℂ :=
  fun y => if y=x then 1 else 0

theorem complement_eq_iff (x y : SS.BitString 6) :
    SS.complement y=x ↔ y=SS.complement x := by
  constructor <;> intro h
  · rw [← h,SS.complement_complement]
  · rw [h,SS.complement_complement]

theorem spinJ_basis (x : SS.BitString 6) :
    spinJ (ket x) = (spinSign x : ℂ) • ket (SS.complement x) := by
  funext y
  simp only [spinJ,ket,Pi.smul_apply,smul_eq_mul,complement_eq_iff]
  by_cases h : y=SS.complement x
  · simp [h,spinSign_complement]
  · simp [h]

theorem normalized_ladder (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) (b : ℝ) (hb : ball c=(b : ℂ)) :
    (raise (u d) (spinJ c) = fun x => -(b : ℂ)*d x) ∧
    (raise (u d) (spinJ d) = fun x => (b : ℂ)*c x) := by
  constructor
  · simpa [hb] using ladder01 c d hc hd hcode
  · simpa [hb] using ladder10 c d hc hd hnc hnd hcode

end MainTheory.Orbit8SpinSemantics
