import MainTheory.FamilyKernelCovariance
import MainTheory.DiagonalLocalKernel
import MainTheory.FiniteGateAsPhase
import SixQubit.Orbit21Cert

set_option autoImplicit false

namespace MainTheory.Orbit21PhysicalGate

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel MainTheory.PauliKernelTrace
open MainTheory.FiniteGateAsPhase MainTheory.DiagonalLocalKernel MainTheory.PairPartialTrace

noncomputable def phases : LocalPhase 6 := phaseOfAngle Complex.I Complex.I_pow_four SixQubit.Orbit21Cert.av
noncomputable def D : OperatorKernel 6 := tensorKernel (localMatrix phases)
def G : SS.PauliString 6 := ⟨fun _ => false,![true,true,true,false,false,true]⟩
def S : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,Complex.I]
def Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]

theorem local_factors : localMatrix phases=![S,S,S,Z,Z,S.conjTranspose] := by
  have h1 : (1 : ZMod 4).val=1 := by decide
  have h2 : (2 : ZMod 4).val=2 := by decide
  have h3 : (3 : ZMod 4).val=3 := by decide
  funext j
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [localMatrix,phases,phaseOfAngle,rootPower,S,Z,SixQubit.Orbit21Cert.av,
      Complex.I_pow_three,Complex.I_sq,h1,h2,h3]

theorem displayed_tensor : D=tensorKernel ![S,S,S,Z,Z,S.conjTranspose] := by
  rw [D,local_factors]

theorem action (f : SS.State 6 ℂ) (x : SS.BitString 6) :
    D.mulVec f x=Complex.I^(SS.weight SixQubit.Orbit21Cert.av x).val*f x := by
  have h := congrFun (MainTheory.DiagonalLocalKernel.action phases f) x
  simpa only [phases,diagonalAction,diagonalValue_phaseOfAngle] using h

theorem square : D*D=pauliKernel G := by
  have hlocal (j : Fin 6) : localMatrix phases j*localMatrix phases j=
      MainTheory.PauliTransferTwo.pauli (MainTheory.PauliWordBridge.pauliWordEquiv G j) := by
    rw [local_factors]
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [S,Z,G,Matrix.mul_apply,Fin.sum_univ_two,MainTheory.PauliTransferTwo.pauli,
        MainTheory.PauliWordBridge.pauliWordEquiv,MainTheory.PauliWordBridge.label] <;> rfl
  rw [D,← tensorKernel_mul]
  simp_rw [hlocal]
  exact MainTheory.PauliWordBridge.wordKernel_pauliWordEquiv G

theorem eigenvectors (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → d x=0) :
    D.mulVec c=c ∧ D.mulVec d= -d := by
  constructor <;> funext x
  · rw [action]
    by_cases hx : SS.weight SixQubit.Orbit21Cert.av x=0
    · simp [hx]
    · simp [hc x hx]
  · rw [action]
    by_cases hx : SS.weight SixQubit.Orbit21Cert.av x=2
    · norm_num [hx,Complex.I_sq,show (2 : ZMod 4).val=2 from by decide]
    · simp [hd x hx]

theorem preserves_projector (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → d x=0) :
    D*familyKernel ![c,d]*D.conjTranspose=familyKernel ![c,d] := by
  obtain ⟨h0,h1⟩ := eigenvectors c d hc hd
  apply MainTheory.FamilyKernelCovariance.eigen_preservation D ![c,d] ![1,-1]
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i
    · simpa using h0
    · simpa using h1

theorem forced_projector (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → d x=0) :
    pauliKernel G*familyKernel ![c,d]=familyKernel ![c,d] := by
  obtain ⟨h0,h1⟩ := eigenvectors c d hc hd
  apply MainTheory.FamilyKernelCovariance.fixed_left
  intro i
  rw [← square,← Matrix.mulVec_mulVec]
  fin_cases i
  · change D.mulVec (D.mulVec c)=c
    rw [h0,h0]
  · change D.mulVec (D.mulVec d)=d
    rw [h1,Matrix.mulVec_neg,h1,neg_neg]

end MainTheory.Orbit21PhysicalGate
