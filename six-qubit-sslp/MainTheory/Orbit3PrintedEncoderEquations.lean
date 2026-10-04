import MainTheory.OrderTwoHomogeneousEncoders
import MainTheory.ConjugateStateExpectation
import MainTheory.MixedFamilyTrace

/-! The displayed diagonal and one off-diagonal equations are exactly full KL. -/

namespace MainTheory.Orbit3PrintedEncoderEquations
noncomputable section
open MainTheory.ClassificationLevels MainTheory.PauliKernelTrace
open MainTheory.OrderTwoHomogeneousEncoders
open scoped BigOperators

theorem inner_star (v w : SS.State 6 ℂ) :
    star (SS.innerC v w)=SS.innerC w v := by
  simp only [SS.innerC,star_sum,star_mul,star_star]

theorem compression_star (v w : SS.State 6 ℂ) (P : SS.PauliString 6) :
    SS.innerC w (SS.pauliAct P v)=star (SS.innerC v (SS.pauliAct P w)) := by
  have h := MainTheory.ConjugateStateExpectation.inner_adjoint (pauliKernel P) v w
  change SS.innerC (kernelAction (pauliKernel P) v) w=
    SS.innerC v (kernelAction ((pauliKernel P).conjTranspose) w) at h
  rw [MainTheory.MixedFamilyTrace.pauli_self_adjoint] at h
  simp only [kernelAction_pauliKernel] at h
  rw [← h,inner_star]

theorem full_KL_iff (ψ : Fin 2 → SS.State 6 ℂ) : SS.HasDistance ψ 3 ↔
    ∀ P : SS.PauliString 6, P.wt≤2 →
      SS.innerC (ψ 0) (SS.pauliAct P (ψ 0))=
        SS.innerC (ψ 1) (SS.pauliAct P (ψ 1)) ∧
      SS.innerC (ψ 0) (SS.pauliAct P (ψ 1))=0 := by
  constructor
  · intro h P hw
    obtain ⟨c,hc⟩ := h P (by omega)
    constructor
    · rw [hc,hc]; rfl
    · rw [hc]; simp
  · intro h P hw
    obtain ⟨hd,ho⟩ := h P (by omega)
    refine ⟨SS.innerC (ψ 0) (SS.pauliAct P (ψ 0)),?_⟩
    intro j k
    fin_cases j <;> fin_cases k
    · simp
    · simpa using ho
    · have hs := compression_star (ψ 0) (ψ 1) P
      rw [ho,star_zero] at hs
      simpa using hs
    · simpa using hd.symm

def raw (ψ : Fin 2 → SS.State 6 ℂ) (N : ℝ) (hN : 0 < N)
    (hn : ∀ k, SS.innerC (ψ k) (ψ k)=(N : ℂ))
    (hp : SixQubit.ParityPauliScalars.ParityPair MainTheory.OrderTwoScalarBridge.orbit3Mask ψ)
    (he : ∀ P : SS.PauliString 6, P.wt≤2 →
      SS.innerC (ψ 0) (SS.pauliAct P (ψ 0))=
        SS.innerC (ψ 1) (SS.pauliAct P (ψ 1)) ∧
      SS.innerC (ψ 0) (SS.pauliAct P (ψ 1))=0) :=
  orbit3 ψ N hN hn hp ((full_KL_iff ψ).mpr he)

theorem printed_A3_zero (ψ : Fin 2 → SS.State 6 ℂ) (N : ℝ) (hN : 0 < N)
    (hn : ∀ k, SS.innerC (ψ k) (ψ k)=(N : ℂ))
    (hp : SixQubit.ParityPauliScalars.ParityPair MainTheory.OrderTwoScalarBridge.orbit3Mask ψ)
    (he : ∀ P : SS.PauliString 6, P.wt≤2 →
      SS.innerC (ψ 0) (SS.pauliAct P (ψ 0))=
        SS.innerC (ψ 1) (SS.pauliAct P (ψ 1)) ∧
      SS.innerC (ψ 0) (SS.pauliAct P (ψ 1))=0) :
    SS.MacWilliams.Aco ψ 3=0 := orbit3_A3_zero (raw ψ N hN hn hp he)

end
end MainTheory.Orbit3PrintedEncoderEquations
