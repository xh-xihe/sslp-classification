import MainTheory.StateEuclidean
import MainTheory.CodeSpec
import MainTheory.PhaseSectorFull
import MainTheory.UnitarySpectral
import MainTheory.PhaseSectorBridge

/-!
# General-rank spectral extraction, part one: the Euclidean setting

`PhaseSectorBridge.SpectralExtractionPrinciple n K d` asks for a complete
eigen-decomposition of a code-preserving diagonal operation, for arbitrary `n`,
`K` and `d`.  The repository proves it only at `(6, 2, 3)`, by an argument
special to rank two.

`UnitarySpectral.directSum_isInternal` now supplies the general spectral input,
but it lives on a Mathlib `InnerProductSpace`, while the code span lives in
`SS.State n ℂ`, which carries no norm.  This file moves the data across: the
canonical module isomorphism with `EuclideanSpace`, the image of the code span
under it, and the gate as a unitary operator preserving that image.
-/

namespace MainTheory.GeneralSpectral

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open MainTheory.StateEuclidean

variable {n K d : ℕ}

/-- The canonical module isomorphism between the state space and the Euclidean
space on the same index. -/
def stateEquiv (n : ℕ) :
    SS.State n ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (SS.BitString n) :=
  (WithLp.linearEquiv 2 ℂ (SS.BitString n → ℂ)).symm

@[simp] theorem stateEquiv_apply (psi : SS.State n ℂ) :
    stateEquiv n psi = StateEuclidean.toEuclidean psi := rfl

@[simp] theorem stateEquiv_symm_apply (psi : EuclideanSpace ℂ (SS.BitString n)) :
    (stateEquiv n).symm psi = StateEuclidean.ofEuclidean psi := rfl

/-- The code span, carried into the Euclidean space. -/
noncomputable def euclideanCodeSpan (F : CodeSpec.OrthonormalFrame n K) :
    Submodule ℂ (EuclideanSpace ℂ (SS.BitString n)) :=
  (CodeSpec.codeSpan F).map (stateEquiv n).toLinearMap

theorem mem_euclideanCodeSpan_iff (F : CodeSpec.OrthonormalFrame n K)
    (psi : EuclideanSpace ℂ (SS.BitString n)) :
    psi ∈ euclideanCodeSpan F ↔ StateEuclidean.ofEuclidean psi ∈ CodeSpec.codeSpan F := by
  constructor
  · rintro ⟨phi, hphi, rfl⟩
    exact hphi
  · intro h
    exact ⟨StateEuclidean.ofEuclidean psi, h, rfl⟩

/-! ## The gate on the Euclidean space -/

/-- The real diagonal gate, transported to the Euclidean space. -/
noncomputable def euclideanGate (theta : Fin n → ℝ) :
    EuclideanSpace ℂ (SS.BitString n) →ₗ[ℂ] EuclideanSpace ℂ (SS.BitString n) :=
  ((stateEquiv n).toLinearMap.comp
    (PhaseSectorBridge.realGateEnd theta)).comp (stateEquiv n).symm.toLinearMap

@[simp] theorem euclideanGate_apply (theta : Fin n → ℝ)
    (psi : EuclideanSpace ℂ (SS.BitString n)) :
    euclideanGate theta psi = StateEuclidean.toEuclidean
      (MainTheory.RealGate.realGate theta (StateEuclidean.ofEuclidean psi)) := rfl

/-- **The transported gate is unitary.** -/
theorem isUnitaryOn_euclideanGate (theta : Fin n → ℝ) :
    UnitarySpectral.IsUnitaryOn (euclideanGate theta) := by
  intro x y
  rw [euclideanGate_apply, euclideanGate_apply,
    ← StateEuclidean.innerC_eq_inner,
    StateEuclidean.innerC_realGate,
    StateEuclidean.innerC_eq_inner]
  simp only [StateEuclidean.toEuclidean_ofEuclidean]

/-- Code preservation transports to the Euclidean image. -/
theorem euclideanGate_mem (F : CodeSpec.OrthonormalFrame n K)
    {theta : Fin n → ℝ}
    (hpres : CodeSpec.CodePreserving F (PhaseSectorBridge.realGateEnd theta))
    {psi : EuclideanSpace ℂ (SS.BitString n)}
    (hpsi : psi ∈ euclideanCodeSpan F) :
    euclideanGate theta psi ∈ euclideanCodeSpan F := by
  rw [mem_euclideanCodeSpan_iff] at hpsi ⊢
  rw [euclideanGate_apply]
  simpa using hpres _ hpsi

end MainTheory.GeneralSpectral
