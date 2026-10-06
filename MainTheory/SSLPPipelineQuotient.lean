import MainTheory.SSLPCompletedProjectors
import MainTheory.SSLPFiniteAudit

/-! End-to-end exactness of the completed-projector quotient and finite audit. -/

namespace MainTheory.SSLPPipelineQuotient

open CodeSpec ClassificationLevels GlobalClassificationBridge SSLPCompleteness
open SSLPCompletedProjectors IntrinsicTransport BoundedRepresentation

noncomputable section

/-- A chosen code equivalence must allow the normalization moves used in
the outer enumeration. No identification of unrelated projectors is assumed. -/
def NormalizationCompatible {n : ℕ} (R : Setoid (CodeProjector n)) : Prop :=
  (∀ (F : OrthonormalFrame n 2) (x : SS.BitString n),
    R.r (CodeProjector.ofFrame F) (CodeProjector.ofFrame (shiftFrame F x))) ∧
  (∀ (F : OrthonormalFrame n 2) (p : Equiv.Perm (Fin n)),
    R.r (CodeProjector.ofFrame F) (CodeProjector.ofFrame (PermutationFrameBridge.permFrame F p)))

theorem lu_normalization_compatible (n : ℕ) : NormalizationCompatible (luSetoid n) :=
  ⟨GeneralNormalFormLU.shiftFrame_luEquivalent, PermutationFrameBridge.permFrame_luEquivalent⟩

theorem normalForm_equivalent {n d : ℕ} (R : Setoid (CodeProjector n))
    (hR : NormalizationCompatible R) {C : ExactCode n 2 d}
    (S : SortedForm.SortedNormalForm C) :
    R.r (CodeProjector.ofFrame C.frame) (CodeProjector.ofFrame S.frame) := by
  have hspan : CodeProjector.ofFrame C.frame = CodeProjector.ofFrame S.source :=
    SpanProjectorBridge.ofFrame_eq_of_codeSpan_eq _ _ S.source_span
  have he : S.frame = PermutationFrameBridge.permFrame (shiftFrame S.source S.x0) S.perm := by
    apply frame_ext
    funext k t
    exact S.frame_eq k t
  rw [hspan, he]
  exact R.iseqv.trans (hR.1 S.source S.x0) (hR.2 _ S.perm)

theorem completion_covers_equivalence {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (R : Setoid (CodeProjector n)) (hR : NormalizationCompatible R)
    (C : ExactCode n 2 d) (hC : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ W : Completion n d (outerCutoff B1 Bn d),
      R.r (CodeProjector.ofFrame C.frame) W.projector := by
  by_cases he : d = 2
  · obtain ⟨S, _, hq, _⟩ := completeness_of_nontrivial_two
      (B1 := B1) (Bn := Bn) he (Nat.le_refl d) beta1 C hC
    exact ⟨ofSorted S hq S.hasDistance, normalForm_equivalent R hR S⟩
  · have h3 : 3 ≤ d := by omega
    obtain ⟨S, _, hq, _, _, _, _, _, _, hdist⟩ := completeness_of_nontrivial_three
      (B1 := B1) (Bn := Bn) h3 (Nat.le_refl d) betan C hC
    exact ⟨ofSorted S hq hdist, normalForm_equivalent R hR S⟩

def outputClasses {n d B : ℕ} (R : Setoid (CodeProjector n)) : Set (Quotient R) :=
  {y | ∃ W : Completion n d B, Quotient.mk R W.projector = y}

def targetClasses {n d : ℕ} (R : Setoid (CodeProjector n)) : Set (Quotient R) :=
  {y | ∃ C : ExactCode n 2 d, (∃ g : IntrinsicGroup C, g ≠ 1) ∧
    Quotient.mk R (CodeProjector.ofFrame C.frame) = y}

theorem outputClasses_eq_targetClasses {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (R : Setoid (CodeProjector n)) (hR : NormalizationCompatible R) :
    outputClasses (d := d) (B := outerCutoff B1 Bn d) R = targetClasses (d := d) R := by
  ext y
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W.toCode, W.nontrivial, hW⟩
  · rintro ⟨C, hC, hy⟩
    obtain ⟨W, hW⟩ := completion_covers_equivalence hd beta1 betan R hR C hC
    exact ⟨W, (Quotient.sound hW).symm.trans hy⟩

/-- **`thm:sslp-completeness`**, including the actual projector quotient and
the finite audit of every intrinsic class, at the selected distance cutoff. -/
theorem pipeline_exact {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (hB1 : 0 < B1) (hBn : 0 < Bn)
    (R : Setoid (CodeProjector n)) (hR : NormalizationCompatible R) :
    (outputClasses (d := d) (B := outerCutoff B1 Bn d) R = targetClasses (d := d) R) ∧
      ∀ W : Completion n d (outerCutoff B1 Bn d),
        Finite (IntrinsicGroup W.toCode) ∧
        Function.Surjective (actionOfLabel (B := outerCutoff B1 Bn d) W.toCode) := by
  refine ⟨outputClasses_eq_targetClasses hd beta1 betan R hR, fun W => ?_⟩
  have h := SSLPFiniteAudit.representation_at_cutoff hd beta1 betan hB1 hBn W.toCode
  exact ⟨finite_of_representation h, (coverOfRepresentation h).covers⟩

/-- The unconditional semantic beta constants instantiate the general
pipeline; separate numerical certificates specialize its finite ranges. -/
theorem pipeline_exact_beta {n d : ℕ} (hd : 2 ≤ d)
    (R : Setoid (CodeProjector n)) (hR : NormalizationCompatible R) :
    (outputClasses (d := d)
        (B := outerCutoff (BetaExists.betaOf (n+1)) (BetaExists.betaOf n) d) R =
      targetClasses (d := d) R) ∧
      ∀ W : Completion n d (outerCutoff (BetaExists.betaOf (n+1)) (BetaExists.betaOf n) d),
        Finite (IntrinsicGroup W.toCode) ∧
        Function.Surjective
          (actionOfLabel (B := outerCutoff (BetaExists.betaOf (n+1)) (BetaExists.betaOf n) d) W.toCode) :=
  pipeline_exact hd (BetaExists.betaBound_betaOf _) (BetaExists.betaBound_betaOf _)
    (BetaExists.betaOf_pos _) (BetaExists.betaOf_pos _) R hR

end
end MainTheory.SSLPPipelineQuotient
