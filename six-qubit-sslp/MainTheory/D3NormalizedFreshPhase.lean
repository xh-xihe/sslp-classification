import MainTheory.D3FreshSparseAssembly

/-!
# Fresh sparse phase from a normalized two-fibre eigenframe

This module removes another semantic input from the distance-three sparse
construction.  A `RankTwoGlobal.TwoFiberCertificate` already contains the
local-`X`-normalized orthonormal frame, its exact distance-three KL predicate,
and the nonzero right residue.  We package that frame as an actual
`ExactCode 6 2 3`, derive its common affine span, and feed all of those facts
to `assembleFreshSparsePhase_of_normalizedEigen`.

The only real-phase premise left by the final constructor is stated literally:
the supplied real diagonal phase fixes the normalized left state.  A later
finite-to-real transcription may discharge it; this file does not identify a
real vector with a modular angle merely because their names look related.
-/

namespace MainTheory.D3NormalizedFreshPhase

open MainTheory
open MainTheory.SixQubitSemanticEntrance
open MainTheory.D3FreshSparseAssembly

noncomputable section

/-- The two logical states after the local-`X` normalization carried by a
two-fibre certificate, exposed independently of the older pivot interface. -/
def normalizedState
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) (k : Fin 2) :
    SS.State 6 ℂ :=
  fun s ↦ G.eigenFrame.vec k (SS.bxor s T.x0)

/-- The normalized states form a genuine orthonormal frame. -/
def normalizedFrame
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    CodeSpec.OrthonormalFrame 6 2 where
  vec := normalizedState T
  orthonormal := by
    intro i j
    exact T.normalizedOrthonormal i j

/-- Local `X` normalization produces another exact distance-three code, not
merely two arbitrary amplitude vectors. -/
def normalizedCode
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    CodeSpec.ExactCode 6 2 3 where
  positiveRank := by decide
  frame := normalizedFrame T
  hasDistance := by
    exact T.normalizedHasDistance

/-- The common-affine-span lemma is applied to the actual normalized code
constructed above; it is not an extra certificate supplied by the caller. -/
theorem normalizedCommonAffineSpan
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    CodeAffineSpanBridge.CommonAffineSpanCertificate
      (normalizedState T 0) (normalizedState T 1) := by
  exact CodeAffineSpanBridge.commonAffineSpan_of_exactCode
    (normalizedCode T) (by decide)

/-- The canonical right residue `q / m` is nonzero.  This is derived from the
stored nonzero gap and the unit normalization, so the positive-rank argument
does not depend on an unverified arithmetic side condition. -/
theorem normalizedRightResidue_ne_zero
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    (((q / T.logicalOrder : ℕ) : ZMod q)) ≠ 0 := by
  rw [← T.unit_normalizes_gap]
  intro hzero
  apply T.gap_ne_zero
  calc
    T.gap = ((↑(T.unit⁻¹) : ZMod q) * (T.unit : ZMod q)) * T.gap := by
      simp
    _ = (↑(T.unit⁻¹) : ZMod q) *
          ((T.unit : ZMod q) * T.gap) := by
      rw [mul_assoc]
    _ = 0 := by
      rw [hzero, mul_zero]

/-- Fully automatic sparse assembly from a normalized two-fibre certificate
and an eigenvalue-one real phase equation.  The supported basis, binary minor,
integer right-hand side, common affine geometry, and rank positivity are all
constructed or proved internally. -/
noncomputable def freshSparsePhase
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G)
    (theta : Fin 6 → ℝ)
    (heigen : MainTheory.RealGate.realGate theta
      (normalizedState T 0) = normalizedState T 0) :
    FreshSparsePhase (normalizedState T 0) (normalizedState T 1) theta :=
  assembleFreshSparsePhase_of_normalizedEigen
    (normalizedCommonAffineSpan T)
    (normalizedFiniteAngle G T)
    (((q / T.logicalOrder : ℕ) : ZMod q))
    (by
      simpa [normalizedState, normalizedFiniteAngle] using T.normalizedRight)
    (normalizedRightResidue_ne_zero T)
    theta heigen

/-- A supplied primitive finite generator has a kernel-constructed normalized
two-fibre certificate.  This is a noncomputable choice from a proved
`Nonempty`; it introduces no new axiom or semantic assumption. -/
def canonicalTwoFiber
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    RankTwoGlobal.TwoFiberCertificate G :=
  Classical.choice (RankTwoGlobal.finiteGenerator_twoFiber G)

/-- Generator-facing convenience wrapper.  Everything except the literal
real eigenvalue-one equation is now derived from the generator and the exact
code. -/
noncomputable def freshSparsePhaseOfGenerator
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (theta : Fin 6 → ℝ)
    (heigen : MainTheory.RealGate.realGate theta
      (normalizedState (canonicalTwoFiber G) 0) =
        normalizedState (canonicalTwoFiber G) 0) :
    FreshSparsePhase
      (normalizedState (canonicalTwoFiber G) 0)
      (normalizedState (canonicalTwoFiber G) 1) theta :=
  freshSparsePhase (canonicalTwoFiber G) theta heigen

end

end MainTheory.D3NormalizedFreshPhase
