import MainTheory.PhaseSectorBridge

/-!
# The induced two-dimensional logical action

This file makes concrete progress on the remaining spectral-extraction step.
For a code-preserving linear operation it constructs the actual `2 × 2`
logical endomorphism in coordinates of the stored orthonormal frame.  Synthesis
and analysis are proved inverse on logical coordinates, and preservation is
used to prove that logical action followed by synthesis is exactly the
physical action on the code.

Since `ℂ` is algebraically closed, the induced endomorphism has a nonzero
eigenvector.  The final theorem transports that eigenpair back to a genuine
nonzero physical code state.  No spectral or sector object is assumed here.
Constructing the second orthogonal eigenvector from unitarity is left to the
next layer.
-/

namespace MainTheory.D3LogicalAction

open MainTheory
open scoped BigOperators

noncomputable section

/-- The coefficient functional `psi ↦ ⟨F_i, psi⟩`. -/
def coordinateFunctional (F : CodeSpec.OrthonormalFrame 6 2) (i : Fin 2) :
    (SS.State 6 ℂ) →ₗ[ℂ] ℂ where
  toFun psi := SS.innerC (F.vec i) psi
  map_add' psi chi := CodeSpec.innerC_add_right (F.vec i) psi chi
  map_smul' a psi := by
    simpa [smul_eq_mul] using
      CodeSpec.innerC_smul_right a (F.vec i) psi

/-- Synthesis of a physical state from its two logical coordinates. -/
def synthesisLinear (F : CodeSpec.OrthonormalFrame 6 2) :
    (Fin 2 → ℂ) →ₗ[ℂ] SS.State 6 ℂ where
  toFun v := ∑ k, v k • F.vec k
  map_add' v w := by
    funext x
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  map_smul' a v := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [RingHom.id_apply]
    ring

/-- Analysis of a physical state in the stored logical frame. -/
def analysisLinear (F : CodeSpec.OrthonormalFrame 6 2) :
    (SS.State 6 ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun psi := fun i ↦ coordinateFunctional F i psi
  map_add' psi chi := by
    funext i
    exact (coordinateFunctional F i).map_add psi chi
  map_smul' a psi := by
    funext i
    exact (coordinateFunctional F i).map_smul a psi

/-- Analysis is a left inverse to synthesis, by frame orthonormality. -/
@[simp] theorem analysis_synthesis
    (F : CodeSpec.OrthonormalFrame 6 2) (v : Fin 2 → ℂ) :
    analysisLinear F (synthesisLinear F v) = v := by
  funext i
  change coordinateFunctional F i (∑ k, v k • F.vec k) = v i
  rw [map_sum]
  simp [coordinateFunctional, F.orthonormal]

/-- In particular, synthesis is injective. -/
theorem synthesis_injective (F : CodeSpec.OrthonormalFrame 6 2) :
    Function.Injective (synthesisLinear F) := by
  intro v w hvw
  have := congrArg (analysisLinear F) hvw
  simpa using this

/-- Synthesizing the frame coefficients of a state is exactly the frame
projector. -/
theorem synthesis_analysis_eq_projectorAction
    (F : CodeSpec.OrthonormalFrame 6 2) (psi : SS.State 6 ℂ) :
    synthesisLinear F (analysisLinear F psi) =
      CodeSpec.projectorAction F psi := by
  funext x
  change (∑ k, SS.innerC (F.vec k) psi • F.vec k) x = _
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Every synthesized state belongs to the actual code span. -/
theorem synthesis_mem_codeSpan
    (F : CodeSpec.OrthonormalFrame 6 2) (v : Fin 2 → ℂ) :
    synthesisLinear F v ∈ CodeSpec.codeSpan F := by
  change (∑ k, v k • F.vec k) ∈ CodeSpec.codeSpan F
  apply Submodule.sum_mem
  intro k _
  exact (CodeSpec.codeSpan F).smul_mem (v k)
    (Submodule.subset_span (Set.mem_range_self k))

/-- The concrete induced `2 × 2` logical endomorphism in frame
coordinates. -/
def logicalAction (F : CodeSpec.OrthonormalFrame 6 2)
    (U : Module.End ℂ (SS.State 6 ℂ)) : Module.End ℂ (Fin 2 → ℂ) :=
  (analysisLinear F).comp (U.comp (synthesisLinear F))

/-- On a preserved code, the induced logical action and the physical action
commute exactly with synthesis. -/
theorem synthesis_logicalAction
    (F : CodeSpec.OrthonormalFrame 6 2)
    (U : Module.End ℂ (SS.State 6 ℂ))
    (hpres : CodeSpec.CodePreserving F U) (v : Fin 2 → ℂ) :
    synthesisLinear F (logicalAction F U v) = U (synthesisLinear F v) := by
  have hmem : U (synthesisLinear F v) ∈ CodeSpec.codeSpan F :=
    hpres _ (synthesis_mem_codeSpan F v)
  calc
    synthesisLinear F (logicalAction F U v) =
        CodeSpec.projectorAction F (U (synthesisLinear F v)) := by
      simpa [logicalAction, LinearMap.comp_apply] using
        synthesis_analysis_eq_projectorAction F (U (synthesisLinear F v))
    _ = U (synthesisLinear F v) :=
      (CodeSpec.mem_codeSpan_iff_projectorAction_eq F _).1 hmem

/-- The algebraically closed field theorem supplies a nonzero logical
eigenvector of the induced two-dimensional endomorphism. -/
theorem exists_logical_eigenvector
    (F : CodeSpec.OrthonormalFrame 6 2)
    (U : Module.End ℂ (SS.State 6 ℂ)) :
    ∃ (mu : ℂ) (v : Fin 2 → ℂ),
      v ≠ 0 ∧ logicalAction F U v = mu • v := by
  obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue (logicalAction F U)
  obtain ⟨v, hv⟩ := hmu.exists_hasEigenvector
  exact ⟨mu, v, hv.2, hv.apply_eq_smul⟩

/-- A preserving operation therefore has a genuine nonzero eigenstate in the
actual physical code.  This is the first half of the two-dimensional spectral
extraction, proved without an extraction premise. -/
theorem exists_physical_code_eigenvector
    (F : CodeSpec.OrthonormalFrame 6 2)
    (U : Module.End ℂ (SS.State 6 ℂ))
    (hpres : CodeSpec.CodePreserving F U) :
    ∃ (mu : ℂ) (v : Fin 2 → ℂ),
      v ≠ 0 ∧
      synthesisLinear F v ≠ 0 ∧
      U (synthesisLinear F v) = mu • synthesisLinear F v := by
  obtain ⟨mu, v, hv, heigen⟩ := exists_logical_eigenvector F U
  have hphysical : synthesisLinear F v ≠ 0 := by
    intro hzero
    have hsynth : synthesisLinear F v = synthesisLinear F 0 := by
      simpa using hzero
    exact hv (synthesis_injective F hsynth)
  refine ⟨mu, v, hv, hphysical, ?_⟩
  calc
    U (synthesisLinear F v) = synthesisLinear F (logicalAction F U v) :=
      (synthesis_logicalAction F U hpres v).symm
    _ = synthesisLinear F (mu • v) := by rw [heigen]
    _ = mu • synthesisLinear F v := by rw [map_smul]

end

end MainTheory.D3LogicalAction
