import MainTheory.SSLPPipelineExact
import MainTheory.GeneralNormalFormLU

/-! The pipeline's independent completion records and actual projectors.
No source code or prior realizability witness is a field of a completion. -/

namespace MainTheory.SSLPCompletedProjectors

open CodeSpec ClassificationLevels GlobalClassificationBridge SSLPCompleteness

noncomputable section

structure Completion (n d B : ℕ) where
  q : ℕ
  q_ne : NeZero q
  two_le_q : 2 ≤ q
  q_le_bound : q ≤ B
  m : ℕ
  two_le_m : 2 ≤ m
  m_dvd_q : m ∣ q
  angle : Fin n → ZMod q
  sorted : Monotone fun j => (angle j).val
  primitive : Gate.Primitive q angle
  zeta : ℂ
  primitiveRoot : IsPrimitiveRoot zeta q
  frame : OrthonormalFrame n 2
  hasDistance : SS.HasDistance frame.vec d
  leftFiber : SS.SSConditionState angle 0 (frame.vec 0)
  rightFiber : SS.SSConditionState angle (((q/m : ℕ) : ZMod q)) (frame.vec 1)

attribute [instance] Completion.q_ne

def Completion.toCode {n d B : ℕ} (W : Completion n d B) : ExactCode n 2 d :=
  SSLPConverse.codeOfPair W.frame W.hasDistance

def Completion.projector {n d B : ℕ} (W : Completion n d B) : CodeProjector n :=
  CodeProjector.ofFrame W.frame

theorem Completion.nontrivial {n d B : ℕ} (W : Completion n d B) :
    ∃ g : IntrinsicGroup W.toCode, g ≠ 1 :=
  SSLPConverse.nontrivial_intrinsicGroup_of_pair W.primitiveRoot W.primitive
    W.m_dvd_q W.two_le_m W.frame W.hasDistance W.leftFiber W.rightFiber

theorem Completion.logical_order {n d B : ℕ} (W : Completion n d B) :
    ∃ g : IntrinsicGroup W.toCode, orderOf g = W.m := by
  refine ⟨(SSLPConverse.resolutionOfPair W.primitiveRoot W.primitive W.m_dvd_q
    W.two_le_m W.frame W.hasDistance W.leftFiber W.rightFiber).intrinsicClass, ?_⟩
  exact SSLPConverse.orderOf_intrinsicClass_resolutionOfPair W.primitiveRoot W.primitive
    W.m_dvd_q W.two_le_m W.frame W.hasDistance W.leftFiber W.rightFiber

def ofSorted {n d d' B : ℕ} {C : ExactCode n 2 d}
    (S : SortedForm.SortedNormalForm C) (hB : S.q ≤ B)
    (hd : SS.HasDistance S.frame.vec d') : Completion n d' B where
  q := S.q
  q_ne := S.q_ne
  two_le_q := S.two_le_q
  q_le_bound := hB
  m := S.m
  two_le_m := S.two_le_m
  m_dvd_q := S.m_dvd_q
  angle := S.angle
  sorted := S.sorted
  primitive := S.primitive
  zeta := S.zeta
  primitiveRoot := S.primitiveRoot
  frame := S.frame
  hasDistance := hd
  leftFiber := S.leftFiber
  rightFiber := S.rightFiber

theorem completion_covers_projector {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (C : ExactCode n 2 d) (hC : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ W : Completion n d (outerCutoff B1 Bn d),
      LUEquivalent (CodeProjector.ofFrame C.frame) W.projector := by
  by_cases he : d = 2
  · obtain ⟨S, _, hq, _⟩ := completeness_of_nontrivial_two
      (B1 := B1) (Bn := Bn) he (Nat.le_refl d) beta1 C hC
    exact ⟨ofSorted S hq S.hasDistance, GeneralNormalFormLU.luEquivalent_ofFrame_normalForm S⟩
  · have h3 : 3 ≤ d := by omega
    obtain ⟨S, _, hq, _, _, _, _, _, _, hdist⟩ := completeness_of_nontrivial_three
      (B1 := B1) (Bn := Bn) h3 (Nat.le_refl d) betan C hC
    exact ⟨ofSorted S hq hdist, GeneralNormalFormLU.luEquivalent_ofFrame_normalForm S⟩

/-- Exact image equality for every projector invariant preserved by the
normalizing physical LU moves. This covers selected invariant-level output. -/
theorem invariant_output_exact {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    {X : Type*} (f : CodeProjector n → X)
    (hf : ∀ P Q, LUEquivalent P Q → f P = f Q) (y : X) :
    (∃ W : Completion n d (outerCutoff B1 Bn d), f W.projector = y) ↔
      ∃ C : ExactCode n 2 d, (∃ g : IntrinsicGroup C, g ≠ 1) ∧
        f (CodeProjector.ofFrame C.frame) = y := by
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W.toCode, W.nontrivial, hW⟩
  · rintro ⟨C, hC, hy⟩
    obtain ⟨W, hW⟩ := completion_covers_projector hd beta1 betan C hC
    exact ⟨W, (hf _ _ hW).symm.trans hy⟩

/-- The output quotient has precisely the classes of the target codes.
The relation is on actual projectors; it can identify further classes. -/
theorem quotient_output_exact {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (R : Setoid (CodeProjector n))
    (hR : ∀ P Q, LUEquivalent P Q → R.r P Q) (y : Quotient R) :
    (∃ W : Completion n d (outerCutoff B1 Bn d), Quotient.mk R W.projector = y) ↔
      ∃ C : ExactCode n 2 d, (∃ g : IntrinsicGroup C, g ≠ 1) ∧
        Quotient.mk R (CodeProjector.ofFrame C.frame) = y :=
  invariant_output_exact hd beta1 betan (Quotient.mk R)
    (fun P Q h => Quotient.sound (hR P Q h)) y

/-- In particular the full local-unitary quotient is covered without
asserting that distinct support keys are distinct LU classes. -/
theorem lu_output_exact {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (y : LocalUnitaryCodeClass n) :
    (∃ W : Completion n d (outerCutoff B1 Bn d), Quotient.mk (luSetoid n) W.projector = y) ↔
      ∃ C : ExactCode n 2 d, (∃ g : IntrinsicGroup C, g ≠ 1) ∧
        Quotient.mk (luSetoid n) (CodeProjector.ofFrame C.frame) = y :=
  quotient_output_exact hd beta1 betan (luSetoid n) (fun _ _ h => h) y

end
end MainTheory.SSLPCompletedProjectors
