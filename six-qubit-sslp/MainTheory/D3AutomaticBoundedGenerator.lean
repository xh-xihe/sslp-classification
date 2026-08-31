import MainTheory.D3NormalizedFiniteToReal
import MainTheory.D3FreshGenerator

/-!
# Automatic bounded generator from finite two-fibre data

For a genuine primitive finite generator on an exact six-qubit
distance-three code, the preceding modules now construct a fresh sparse phase
with no additional semantic premise.  This file packages that phase as a new
primitive finite generator on the explicitly local-`X`-normalized exact code.

The new order is the fresh least denominator and is bounded by nine.  We do
not identify the normalized code with the original code: transporting this
result back along local `X` is a separate equivalence theorem.
-/

namespace MainTheory.D3AutomaticBoundedGenerator

open MainTheory
open MainTheory.SixQubitSemanticEntrance
open MainTheory.D3FreshSparseAssembly
open MainTheory.D3NormalizedFreshPhase
open MainTheory.D3NormalizedFiniteToReal

noncomputable section

/-- Eigenvalues of the normalized finite/real action on its two logical
states. -/
def normalizedEigenvalue
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) : Fin 2 → ℂ :=
  ![1, Cyclic.chi G.zeta (((q / T.logicalOrder : ℕ) : ZMod q))]

/-- The right normalized eigenvalue is not one.  This is derived from the
proved projective-order characterization and `2 <= logicalOrder`. -/
theorem normalizedRightEigenvalue_ne_one
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    Cyclic.chi G.zeta (((q / T.logicalOrder : ℕ) : ZMod q)) ≠ 1 := by
  intro hchi
  have hpow :
      Cyclic.chi G.zeta
          (((q / T.logicalOrder : ℕ) : ZMod q)) ^ 1 = 1 := by
    rw [hchi]
    simp
  have hdiv : T.logicalOrder ∣ 1 :=
    (T.normalizedProjectiveOrder 1).1 hpow
  have hm : T.logicalOrder = 1 := Nat.dvd_one.mp hdiv
  have hm2 : 2 ≤ T.logicalOrder := T.two_le_logicalOrder
  omega

theorem normalizedEigenvalue_nontrivial
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    normalizedEigenvalue T 0 ≠ normalizedEigenvalue T 1 := by
  intro heq
  apply normalizedRightEigenvalue_ne_one T
  simpa [normalizedEigenvalue] using heq.symm

/-- The exact real representative has the displayed normalized eigenframe and
the two eigenvalues above. -/
theorem normalizedRealPhase_eigen
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) (k : Fin 2) :
    MainTheory.RealGate.realGate (normalizedRealPhase T)
        ((normalizedFrame T).vec k) =
      fun x ↦ normalizedEigenvalue T k * (normalizedFrame T).vec k x := by
  fin_cases k
  · simpa [normalizedFrame, normalizedEigenvalue] using
      normalizedRealPhase_leftEigen T
  · simpa [normalizedFrame, normalizedEigenvalue] using
      normalizedRealPhase_rightEigen T

/-- The automatic fresh phase with its state parameters written through the
normalized frame.  This small typed adapter prevents downstream elaboration
from unfolding the entire sparse construction merely to see that
`normalizedFrame.vec = normalizedState`. -/
def frameFreshSparsePhase
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    FreshSparsePhase
      ((normalizedFrame T).vec 0) ((normalizedFrame T).vec 1)
      (normalizedRealPhase T) := by
  exact automaticFreshSparsePhase T

/-- Explicit span equality used by the packaging constructor. -/
theorem normalizedCode_span_eq_normalizedFrame
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    CodeSpec.codeSpan (normalizedCode T).frame =
      CodeSpec.codeSpan (normalizedFrame T) := by
  change CodeSpec.codeSpan (normalizedFrame T) =
    CodeSpec.codeSpan (normalizedFrame T)
  rfl

/-- Canonical local instance for the fresh least denominator. -/
def frameFreshOrderNeZero
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    NeZero (frameFreshSparsePhase T).data.order :=
  ⟨(frameFreshSparsePhase T).data.order_pos.ne'⟩

/-- Fresh primitive finite generator at the internally constructed sparse
denominator. -/
def automaticFreshGenerator
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    @RankTwoGlobal.FiniteGeneratorResolution 6 3 (normalizedCode T)
      (frameFreshSparsePhase T).data.order
      (frameFreshOrderNeZero T) :=
  D3FreshGenerator.ofFreshSparsePhase
    (C := normalizedCode T)
    (normalizedRealPhase T)
    (normalizedFrame T)
    (normalizedCode_span_eq_normalizedFrame T)
    (normalizedEigenvalue T)
    (normalizedRealPhase_eigen T)
    (normalizedEigenvalue_nontrivial T)
    (frameFreshSparsePhase T)

/-- The new generator's physical order satisfies the sharp six-qubit bound. -/
theorem automaticFreshGenerator_order_le_nine
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    (frameFreshSparsePhase T).data.order ≤ 9 :=
  (frameFreshSparsePhase T).order_le_nine betaSix

/-- The fresh finite gate exposed without a dependent `NeZero` premise in its
type.  Positivity of the fresh denominator installs the instance internally. -/
def freshFiniteGateEnd
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    Module.End ℂ (SS.State 6 ℂ) := by
  letI : NeZero (frameFreshSparsePhase T).data.order :=
    frameFreshOrderNeZero T
  exact RankTwoGlobal.finiteGateEnd
    (automaticFreshGenerator T).zeta
    (automaticFreshGenerator T).angle

/-- The freshly packaged finite generator has exactly the same projective
action as the exact real representative on the normalized code. -/
theorem automaticFreshGenerator_sameProjective_real
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    CodeSpec.SameProjectiveOnCode (normalizedCode T).frame
      (freshFiniteGateEnd T)
      (PhaseSectorBridge.realGateEnd (normalizedRealPhase T)) := by
  letI : NeZero (frameFreshSparsePhase T).data.order :=
    frameFreshOrderNeZero T
  change CodeSpec.SameProjectiveOnCode (normalizedCode T).frame
    (RankTwoGlobal.finiteGateEnd
      (automaticFreshGenerator T).zeta
      (automaticFreshGenerator T).angle)
    (PhaseSectorBridge.realGateEnd (normalizedRealPhase T))
  simpa [automaticFreshGenerator] using
    D3FreshGenerator.ofFreshSparsePhase_sameProjective
      (C := normalizedCode T)
      (normalizedRealPhase T)
      (normalizedFrame T)
      (normalizedCode_span_eq_normalizedFrame T)
      (normalizedEigenvalue T)
      (normalizedRealPhase_eigen T)
      (normalizedEigenvalue_nontrivial T)
      (frameFreshSparsePhase T)

/-- The original normalized finite action and its exact real representative
are equal as linear endomorphisms of the full physical space. -/
theorem normalizedFiniteGateEnd_eq_realGateEnd
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    RankTwoGlobal.finiteGateEnd G.zeta (normalizedFiniteAngle G T) =
      PhaseSectorBridge.realGateEnd (normalizedRealPhase T) := by
  apply LinearMap.ext
  intro psi
  exact congrFun (normalizedGate_eq_realGate T) psi

/-- Consequently the fresh bounded generator and the original normalized
finite generator have the same projective action on the normalized exact
code. -/
theorem automaticFreshGenerator_sameProjective_normalizedFinite
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    CodeSpec.SameProjectiveOnCode (normalizedCode T).frame
      (freshFiniteGateEnd T)
      (RankTwoGlobal.finiteGateEnd G.zeta (normalizedFiniteAngle G T)) := by
  rw [normalizedFiniteGateEnd_eq_realGateEnd T]
  exact automaticFreshGenerator_sameProjective_real T

/-- Generator-only form: the proved canonical two-fibre certificate is chosen
internally, so no normal-form object is an external assumption. -/
def automaticFreshGeneratorOfGenerator
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :=
  automaticFreshGenerator (canonicalTwoFiber G)

theorem automaticFreshGeneratorOfGenerator_order_le_nine
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    (frameFreshSparsePhase (canonicalTwoFiber G)).data.order ≤ 9 :=
  automaticFreshGenerator_order_le_nine betaSix (canonicalTwoFiber G)

end

end MainTheory.D3AutomaticBoundedGenerator
