import MainTheory.Orbit21LiteralScalars
import MainTheory.Orbit21PhysicalGate
import MainTheory.Orbit21EnumeratorDisplays
import MainTheory.WImageIntrinsicBridge
import MainTheory.KLCodeBridge

set_option autoImplicit false

namespace MainTheory.Orbit21WitnessDisplays

open MainTheory.Orbit21LiteralWitness MainTheory.PairPartialTrace MainTheory.PauliKernelTrace
open MainTheory.WImageIntrinsicBridge

theorem gate_eigenvectors : MainTheory.Orbit21PhysicalGate.D.mulVec w0=w0 ∧
    MainTheory.Orbit21PhysicalGate.D.mulVec w1= -w1 :=
  MainTheory.Orbit21PhysicalGate.eigenvectors w0 w1 fibers.1 fibers.2

theorem projector_kl (E : SS.PauliString 6) (hE : E.wt ≤ 2) : ∃ lam : ℂ,
    familyKernel ![w0,w1]*pauliKernel E*familyKernel ![w0,w1]=lam • familyKernel ![w0,w1] := by
  let C := exactCodeOfPair w0 w1 normalized.1 normalized.2 is_code
  obtain ⟨lam,hlam⟩ := MainTheory.KLTensorSupport.pauli_mem_detectedOperators C E (by omega)
  have h := (MainTheory.KLCodeBridge.projector_compression_iff C.frame (pauliKernel E) lam).2 hlam
  exact ⟨lam,h⟩

def zz (i j : Fin 6) : SS.PauliString 6 :=
  ⟨fun _ => false,SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩

theorem scalar_labels : MainTheory.Orbit21LiteralScalars.pauli=
    ![zz 4 5,zz 2 4,zz 1 4,zz 0 4] := by
  funext j
  have hext (P Q : SS.PauliString 6) (hx : P.x=Q.x) (hz : P.z=Q.z) : P=Q := by
    cases P
    cases Q
    cases hx
    cases hz
    rfl
  apply hext
  · funext i; fin_cases j <;> fin_cases i <;> rfl
  · funext i; fin_cases j <;> fin_cases i <;> rfl

theorem A2_value : SS.MacWilliams.Aco ![w0,w1] 2/4=4*(1/2 : ℝ)^2 ∧
    4*(1/2 : ℝ)^2=1 := by
  have h := MainTheory.Orbit21EnumeratorDisplays.first_three w0 w1
    fibers.1 fibers.2 normalized.1 normalized.2 is_code
  constructor <;> norm_num [h.2.1]

end MainTheory.Orbit21WitnessDisplays
