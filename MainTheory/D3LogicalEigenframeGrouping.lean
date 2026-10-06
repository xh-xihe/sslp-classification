import MainTheory.D3LogicalEigenframeSectors

/-!
# Grouping a two-dimensional logical eigenframe into sectors

For two logical dimensions there are exactly two multiplicity patterns.  If
the two eigenvalues coincide, this file constructs one rank-two sector.  If
they differ, it constructs two rank-one sectors.  Both constructions include
an explicit equivalence between `Fin 2` and the flattened sigma index and an
equality of the resulting eigenframe span with the actual code span.

Thus the conversion from a raw orthonormal logical eigenframe to
`PhaseSectorBridge.LogicalSectorResolution` is kernel mathematics, not part of
the remaining spectral assumption.
-/

namespace MainTheory.D3LogicalEigenframeGrouping

open MainTheory
open MainTheory.PhaseSectorFull
open MainTheory.D3LogicalEigenframeSectors

noncomputable section

/-- Reindex two vectors as the unique rank-two sector. -/
def oneSectorReindex :
    Fin 2 ≃ (Σ _ : Fin 1, Fin 2) where
  toFun k := ⟨0, k⟩
  invFun u := u.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨alpha, k⟩
    fin_cases alpha
    rfl

/-- Reindex two vectors as two rank-one sectors. -/
def twoSectorReindex :
    Fin 2 ≃ (Σ _ : Fin 2, Fin 1) :=
  (Equiv.sigmaUnique (Fin 2) (fun _ ↦ Fin 1)).symm

/-- Pointwise equality of a reindexed sector frame with a supplied frame
implies equality of their linear spans. -/
theorem codeSpan_reindexedSectorFrame_eq
    {n K t : ℕ} {theta : Fin n → ℝ}
    (D : SectorDecomposition n t theta)
    (e : Fin K ≃ D.Index)
    (F : CodeSpec.OrthonormalFrame n K)
    (hvec : ∀ k, (FiniteLift.reindexedSectorFrame D e).vec k = F.vec k) :
    CodeSpec.codeSpan (FiniteLift.reindexedSectorFrame D e) =
      CodeSpec.codeSpan F := by
  unfold CodeSpec.codeSpan
  apply congrArg (Submodule.span ℂ)
  ext psi
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hvec k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, hvec k⟩

theorem LogicalEigenframe.eigenvalue_eq_zero_of_eq
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta)
    (heq : E.eigenvalue 0 = E.eigenvalue 1) (k : Fin 2) :
    E.eigenvalue k = E.eigenvalue 0 := by
  fin_cases k
  · rfl
  · exact heq.symm

/-- The coincident-eigenvalue case: one sector of rank two. -/
def oneSectorDecomposition
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta)
    (heq : E.eigenvalue 0 = E.eigenvalue 1) :
    SectorDecomposition 6 1 theta where
  sectorCount_pos := by decide
  rank := fun _ ↦ 2
  rank_pos := by
    intro _
    decide
  vec := fun u ↦ E.frame.vec (oneSectorReindex.symm u)
  orthonormal := by
    intro u v
    rw [E.frame.orthonormal]
    simp only [oneSectorReindex.symm.injective.eq_iff]
  phase := fun _ ↦ E.logicalPhase 0
  phaseDistinct := by
    intro alpha beta _
    exact Subsingleton.elim alpha beta
  eigen := by
    intro u
    calc
      MainTheory.RealGate.realGate theta
          (E.frame.vec (oneSectorReindex.symm u)) =
          fun x ↦ E.eigenvalue (oneSectorReindex.symm u) *
            E.frame.vec (oneSectorReindex.symm u) x :=
        E.eigen (oneSectorReindex.symm u)
      _ = fun x ↦ phaseExp (E.logicalPhase 0) *
          E.frame.vec (oneSectorReindex.symm u) x := by
        funext x
        rw [E.phaseExp_logicalPhase]
        obtain ⟨i, j⟩ := u
        fin_cases i
        fin_cases j
        · change E.eigenvalue 0 * E.frame.vec 0 x =
            E.eigenvalue 0 * E.frame.vec 0 x
          rfl
        · change E.eigenvalue 1 * E.frame.vec 1 x =
            E.eigenvalue 0 * E.frame.vec 1 x
          rw [heq]

@[simp] theorem oneSectorDecomposition_vec_reindex
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta)
    (heq : E.eigenvalue 0 = E.eigenvalue 1) (k : Fin 2) :
    (oneSectorDecomposition E heq).vec (oneSectorReindex k) =
      E.frame.vec k := by
  simp [oneSectorDecomposition]

/-- Complete logical sector resolution in the coincident-eigenvalue case. -/
def oneSectorResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta)
    (heq : E.eigenvalue 0 = E.eigenvalue 1) :
    PhaseSectorBridge.LogicalSectorResolution C theta where
  sectorCount := 1
  sectors := oneSectorDecomposition E heq
  link :=
    { reindex := oneSectorReindex
      span_eq := E.span_eq.trans
        (codeSpan_reindexedSectorFrame_eq
          (oneSectorDecomposition E heq) oneSectorReindex E.frame
          (oneSectorDecomposition_vec_reindex E heq)).symm }

/-- The distinct-eigenvalue case: two sectors of rank one. -/
def twoSectorDecomposition
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta)
    (hne : E.eigenvalue 0 ≠ E.eigenvalue 1) :
    SectorDecomposition 6 2 theta where
  sectorCount_pos := by decide
  rank := fun _ ↦ 1
  rank_pos := by
    intro _
    decide
  vec := fun u ↦ E.frame.vec (twoSectorReindex.symm u)
  orthonormal := by
    intro u v
    rw [E.frame.orthonormal]
    simp only [twoSectorReindex.symm.injective.eq_iff]
  phase := E.logicalPhase
  phaseDistinct := by
    intro alpha beta hphase
    have heigen : E.eigenvalue alpha = E.eigenvalue beta := by
      rw [← E.phaseExp_logicalPhase alpha,
        ← E.phaseExp_logicalPhase beta]
      exact hphase
    fin_cases alpha <;> fin_cases beta
    · rfl
    · exact (hne heigen).elim
    · exact (hne heigen.symm).elim
    · rfl
  eigen := by
    intro u
    have hindex : twoSectorReindex.symm u = u.1 := by
      exact Equiv.sigmaUnique_apply u
    calc
      MainTheory.RealGate.realGate theta
          (E.frame.vec (twoSectorReindex.symm u)) =
          fun x ↦ E.eigenvalue (twoSectorReindex.symm u) *
            E.frame.vec (twoSectorReindex.symm u) x :=
        E.eigen (twoSectorReindex.symm u)
      _ = fun x ↦ phaseExp (E.logicalPhase u.1) *
          E.frame.vec (twoSectorReindex.symm u) x := by
        funext x
        rw [hindex, E.phaseExp_logicalPhase]

@[simp] theorem twoSectorDecomposition_vec_reindex
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta)
    (hne : E.eigenvalue 0 ≠ E.eigenvalue 1) (k : Fin 2) :
    (twoSectorDecomposition E hne).vec (twoSectorReindex k) =
      E.frame.vec k := by
  simp [twoSectorDecomposition]

/-- Complete logical sector resolution in the distinct-eigenvalue case. -/
def twoSectorResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta)
    (hne : E.eigenvalue 0 ≠ E.eigenvalue 1) :
    PhaseSectorBridge.LogicalSectorResolution C theta where
  sectorCount := 2
  sectors := twoSectorDecomposition E hne
  link :=
    { reindex := twoSectorReindex
      span_eq := E.span_eq.trans
        (codeSpan_reindexedSectorFrame_eq
          (twoSectorDecomposition E hne) twoSectorReindex E.frame
          (twoSectorDecomposition_vec_reindex E hne)).symm }

/-- Automatic grouping of a raw two-dimensional logical eigenframe. -/
def LogicalEigenframe.toLogicalSectorResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta) :
    PhaseSectorBridge.LogicalSectorResolution C theta :=
  if heq : E.eigenvalue 0 = E.eigenvalue 1 then
    oneSectorResolution E heq
  else
    twoSectorResolution E heq

/-- The remaining spectral input can now be stated as a plain orthonormal
eigenframe theorem on the invariant two-dimensional code. -/
def LogicalEigenframeExtractionPrinciple : Prop :=
  ∀ (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ),
    CodeSpec.CodePreserving C.frame
        (PhaseSectorBridge.realGateEnd theta) →
      Nonempty (LogicalEigenframe C theta)

/-- A raw logical eigenframe extraction theorem implies the repository's
full phase-sector extraction interface; phase representatives, multiplicity
grouping, sigma indices, and the code-span link are all constructed above. -/
theorem spectralExtraction_of_logicalEigenframeExtraction
    (hextract : LogicalEigenframeExtractionPrinciple) :
    PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3 := by
  intro C theta hpres
  obtain ⟨E⟩ := hextract C theta hpres
  exact ⟨MainTheory.D3LogicalEigenframeGrouping.LogicalEigenframe.toLogicalSectorResolution E⟩

end

end MainTheory.D3LogicalEigenframeGrouping
