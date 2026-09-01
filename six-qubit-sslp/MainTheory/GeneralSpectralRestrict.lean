import MainTheory.GeneralSpectral

/-!
# General-rank spectral extraction, part two: the restriction to the code

The gate restricted to the code subspace is a unitary operator on a
finite-dimensional complex inner product space, so
`UnitarySpectral.directSum_isInternal` decomposes that subspace into its
eigenspaces -- for arbitrary `n` and arbitrary rank `K`.

This is separated from part one only because the submodule inner-product
instances resolve against an imported `euclideanCodeSpan` but not against one
being defined in the same file.
-/

namespace MainTheory.GeneralSpectral

open MainTheory.StateEuclidean

variable {n K : ℕ}

/-! ## Instances

Searching for these through unification runs into the submodule/`PiLp`
instance diamond and times out at `isDefEq`.  Naming them makes the search
pick them directly. -/

noncomputable instance codeNormedAddCommGroup
    (F : CodeSpec.OrthonormalFrame n K) :
    NormedAddCommGroup (euclideanCodeSpan F) := inferInstance

noncomputable instance codeInnerProductSpace
    (F : CodeSpec.OrthonormalFrame n K) :
    InnerProductSpace ℂ (euclideanCodeSpan F) := inferInstance

/-! ## The restriction to the code, and its spectral decomposition -/

variable {F : CodeSpec.OrthonormalFrame n K} {theta : Fin n → ℝ}

/-- The gate restricted to the code, as an operator on the code subspace. -/
noncomputable def restrictedGate
    (hpres : CodeSpec.CodePreserving F (PhaseSectorBridge.realGateEnd theta)) :
    euclideanCodeSpan F →ₗ[ℂ] euclideanCodeSpan F :=
  (euclideanGate theta).restrict (fun _ hv => euclideanGate_mem F hpres hv)

@[simp] theorem restrictedGate_coe
    (hpres : CodeSpec.CodePreserving F (PhaseSectorBridge.realGateEnd theta))
    (v : euclideanCodeSpan F) :
    ((restrictedGate hpres v : euclideanCodeSpan F)
      : EuclideanSpace ℂ (SS.BitString n))
      = euclideanGate theta (v : EuclideanSpace ℂ (SS.BitString n)) := rfl

/-- **The restriction is unitary on the code subspace.** -/
theorem isUnitaryOn_restrictedGate
    (hpres : CodeSpec.CodePreserving F (PhaseSectorBridge.realGateEnd theta)) :
    UnitarySpectral.IsUnitaryOn (restrictedGate hpres) := by
  intro x y
  have h := isUnitaryOn_euclideanGate (n := n) theta
    (x : EuclideanSpace ℂ (SS.BitString n))
    (y : EuclideanSpace ℂ (SS.BitString n))
  simpa [Submodule.coe_inner, restrictedGate_coe] using h

/-- **The code subspace is the orthogonal direct sum of the gate's
eigenspaces**, for arbitrary `n` and arbitrary rank `K`.

This is the general-rank statement that `SpectralExtractionPrinciple` needs and
that the rank-two argument in the repository could not provide. -/
theorem directSum_isInternal_restricted
    (hpres : CodeSpec.CodePreserving F (PhaseSectorBridge.realGateEnd theta)) :
    DirectSum.IsInternal fun mu : Module.End.Eigenvalues (restrictedGate hpres) =>
      Module.End.eigenspace (restrictedGate hpres) mu :=
  UnitarySpectral.directSum_isInternal (isUnitaryOn_restrictedGate hpres)

/-! ## The code subspace has dimension K -/

/-- The frame, carried into the Euclidean space, is orthonormal in Mathlib's
sense. -/
theorem orthonormal_euclideanFrame (F : CodeSpec.OrthonormalFrame n K) :
    Orthonormal ℂ (fun k => StateEuclidean.toEuclidean (F.vec k)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [← StateEuclidean.innerC_eq_inner]
  exact F.orthonormal i j

theorem euclideanCodeSpan_eq_span (F : CodeSpec.OrthonormalFrame n K) :
    euclideanCodeSpan F
      = Submodule.span ℂ
        (Set.range fun k => StateEuclidean.toEuclidean (F.vec k)) := by
  rw [euclideanCodeSpan, CodeSpec.codeSpan, Submodule.map_span,
    ← Set.range_comp]
  rfl

/-- **The code subspace has dimension `K`.** -/
theorem finrank_euclideanCodeSpan (F : CodeSpec.OrthonormalFrame n K) :
    Module.finrank ℂ (euclideanCodeSpan F) = K := by
  rw [euclideanCodeSpan_eq_span]
  have hli : LinearIndependent ℂ (fun k => StateEuclidean.toEuclidean (F.vec k)) :=
    (orthonormal_euclideanFrame F).linearIndependent
  rw [finrank_span_eq_card hli, Fintype.card_fin]

end MainTheory.GeneralSpectral
