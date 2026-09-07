import MainTheory.KnillLaflammeRecovery
import MainTheory.KLCodeBridge
import MainTheory.KrausAmplification

/-! # Paper-facing exact quantum error correction, from actual KL equations -/

namespace MainTheory.QuantumRecovery

open CodeSpec ClassificationLevels PauliKernelBTrace PauliKernelTrace
open FiniteKrausChannel KnillLaflammeRecovery KLCodeBridge
open scoped ComplexOrder

noncomputable section

variable {n K d t : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- The manuscript's literal `P Eᵢ† Eⱼ P = cᵢⱼ P` equations are equivalent
to a genuine finite Kraus CPTP recovery of all encoded operators. -/
theorem projector_kl_iff_recovery (F : OrthonormalFrame n K) (hK : 0 < K)
    (E : I → OperatorKernel n) (hE : TracePreserving E) :
    ProjectorKnillLaflamme F E ↔
      ∃ R : Option I → OperatorKernel n, TracePreserving R ∧ Recovers (frameMatrix F) E R := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact (projectorKnillLaflamme_iff F E).trans
    (knillLaflamme_iff_recovery (frameMatrix F) (frameMatrix_gram F) E hE)

/-- The same iff with the explicitly Hermitian matrix required in the
paper.  Hermiticity is proved from the physical error Gram matrix. -/
theorem hermitian_projector_kl_iff_recovery (F : OrthonormalFrame n K) (hK : 0 < K)
    (E : I → OperatorKernel n) (hE : TracePreserving E) :
    (∃ c : Matrix I I ℂ, c.IsHermitian ∧ ∀ i j,
      (CodeProjector.ofFrame F).kernel * (E i).conjTranspose * E j *
        (CodeProjector.ofFrame F).kernel = c i j • (CodeProjector.ofFrame F).kernel) ↔
      ∃ R : Option I → OperatorKernel n, TracePreserving R ∧ Recovers (frameMatrix F) E R := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  rw [← projector_kl_iff_recovery F hK E hE]
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩
  · intro h
    obtain ⟨c, hpos, hc⟩ := knillLaflamme_has_positive_gram (frameMatrix F) E
      ((projectorKnillLaflamme_iff F E).1 h)
    refine ⟨c, hpos.isHermitian, fun i j => ?_⟩
    simpa only [Matrix.mul_assoc] using
      (projector_compression_iff F ((E i).conjTranspose * E j) (c i j)).2
        (by simpa only [Matrix.mul_assoc] using hc i j)

/-- Genuine distance corrects every normalized finite channel whose errors
are arbitrary linear combinations of weight-at-most-`t` Paulis, if `2t<d`. -/
theorem recovery_of_distance (C : ExactCode n K d) (E : I → OperatorKernel n)
    (hE : TracePreserving E) (ht : 2 * t < d)
    (hspan : ∀ i, E i ∈ pauliErrorSpace n t) :
    ∃ R : Option I → OperatorKernel n, TracePreserving R ∧
      Recovers (frameMatrix C.frame) E R := by
  letI : Nonempty (Fin K) := ⟨⟨0, C.positiveRank⟩⟩
  exact KLSufficiency.exists_recovery_of_knillLaflamme (frameMatrix C.frame)
    (frameMatrix_gram C.frame) E hE (knillLaflamme_of_error_span C E ht hspan)

/-- The usual `floor((d−1)/2)` correction radius. -/
theorem recovery_of_half_distance (C : ExactCode n K d) (hd : 0 < d)
    (E : I → OperatorKernel n) (hE : TracePreserving E)
    (hspan : ∀ i, E i ∈ pauliErrorSpace n ((d - 1) / 2)) :
    ∃ R : Option I → OperatorKernel n, TracePreserving R ∧
      Recovers (frameMatrix C.frame) E R :=
  recovery_of_distance C E hE (by omega) hspan

/-- One fixed recovery for all channels spanned by the full low-weight
Pauli error set, rather than a separate choice for every channel. -/
theorem common_recovery_of_distance (C : ExactCode n K d) (ht : 2 * t < d) :
    ∃ R : Option {P : SS.PauliString n // P.wt ≤ t} → OperatorKernel n,
      TracePreserving R ∧
      ∀ (m : ℕ) (a : Fin m → {P : SS.PauliString n // P.wt ≤ t} → ℂ),
        TracePreserving (fun j => ∑ P, a j P • pauliKernel P.val) →
          Recovers (frameMatrix C.frame) (fun j => ∑ P, a j P • pauliKernel P.val) R := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0, C.positiveRank⟩⟩
  let E : {P : SS.PauliString n // P.wt ≤ t} → OperatorKernel n := fun P => pauliKernel P.val
  apply finite_error_set_recovery (frameMatrix C.frame) (frameMatrix_gram C.frame) E
  apply knillLaflamme_of_error_span C E ht
  intro P
  exact Submodule.subset_span ⟨P.val, P.property, rfl⟩

end

end MainTheory.QuantumRecovery
