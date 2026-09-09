import MainTheory.IntrinsicTransport
import MainTheory.SortedNormalForm
import MainTheory.SpanProjectorBridge
import MainTheory.LocalMonomialFrameBridge
import MainTheory.PermutationFrameBridge

/-! Projector-level normalization at arbitrary block length. -/

namespace MainTheory.GeneralNormalFormLU

open ClassificationLevels CodeSpec IntrinsicTransport LocalMonomialFrameBridge

noncomputable section

theorem shiftFrame_luEquivalent {n K : ℕ} (F : OrthonormalFrame n K)
    (x : SS.BitString n) :
    LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame (shiftFrame F x)) := by
  classical
  have hs (s : Finset (Fin n)) :
      LUEquivalent (CodeProjector.ofFrame F)
        (CodeProjector.ofFrame (shiftFrame F (fun j => if j ∈ s then x j else false))) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : shiftFrame F (fun j => if j ∈ (∅ : Finset (Fin n)) then x j else false) = F := by
        apply frame_ext
        funext k t
        simp
      rw [he]
      exact luEquivalent_equivalence.refl _
    | @insert i s hi ih =>
      let G := shiftFrame F (fun j => if j ∈ s then x j else false)
      let H := oneSiteFrame G i (x i) 1 1 (by simp) (by simp)
      have hGH : LUEquivalent (CodeProjector.ofFrame G) (CodeProjector.ofFrame H) :=
        oneSiteFrame_luEquivalent G i (x i) 1 1 (by simp) (by simp)
      have he : H = shiftFrame F (fun j => if j ∈ insert i s then x j else false) := by
        apply frame_ext
        funext k t
        change (if t i then (1 : ℂ) else 1) *
          F.vec k (SS.bxor (LocalMonomialActionBridge.oneSiteInput i (x i) t)
            (fun j => if j ∈ s then x j else false)) = _
        rw [ite_self, one_mul, oneSiteInput_eq_bxor]
        change F.vec k _ = F.vec k _
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          simp [SS.bxor, oneSiteMask, hi]
        · simp [SS.bxor, oneSiteMask, hji]
      rw [he] at hGH
      exact luEquivalent_equivalence.trans ih hGH
  simpa using hs Finset.univ

theorem luEquivalent_ofFrame_normalForm {n d : ℕ} {C : ExactCode n 2 d}
    (S : SortedForm.SortedNormalForm C) :
    LUEquivalent (CodeProjector.ofFrame C.frame) (CodeProjector.ofFrame S.frame) := by
  have hspan : CodeProjector.ofFrame C.frame = CodeProjector.ofFrame S.source :=
    SpanProjectorBridge.ofFrame_eq_of_codeSpan_eq _ _ S.source_span
  have he : S.frame =
      PermutationFrameBridge.permFrame (shiftFrame S.source S.x0) S.perm := by
    apply frame_ext
    funext k t
    exact S.frame_eq k t
  rw [hspan, he]
  exact luEquivalent_equivalence.trans (shiftFrame_luEquivalent S.source S.x0)
    (PermutationFrameBridge.permFrame_luEquivalent _ S.perm)

end
end MainTheory.GeneralNormalFormLU
