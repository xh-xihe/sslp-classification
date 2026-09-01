import MainTheory.SortedNormalForm
import MainTheory.FlipSemanticTransport

/-!
# `thm:d3-sslp-classification`: the sharper `beta_n` cutoff at distance three

`thm:d2-sslp-classification` puts every exact `((n,2,d))` code with `d >= 2` in
a sorted two-fibre normal form of modulus at most `beta_{n+1}`, the coloured
system having `n + 1` unknowns.  At `d >= 3` the paper replaces `beta_{n+1}` by
`beta_n`: the common affine span of the two logical supports lets one cut a
square *binary simplex* of size `r <= n` out of actual supported vertices, so
the pivot is smaller.

That sparse construction is `D3FreshSparseAssembly`, and
`D3AutomaticBoundedGenerator.automaticFreshGenerator` already packages it as a
finite generator with order at most `beta_n`.  The one thing missing was that
this generator lives on the *normalized* code -- the one obtained from the
original by the local `X` string `T.x0` -- so it could not be handed to the
normal-form construction, which expects a generator on the code itself.

`FlipSemanticTransport` supplies the missing step, and `boundedGenerator`
applies it: flipping the fresh generator back by the same `x0` lands it on the
original code, with the same modulus.
-/

namespace MainTheory.D3BoundedNormalForm

open MainTheory
open MainTheory.IntrinsicTransport
open MainTheory.D3NormalizedFreshPhase
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.SectionTwoGeneral

noncomputable section

variable {n : ℕ}

/-- Flipping the normalized frame back by the same string recovers the
generator's own eigenframe. -/
theorem shiftFrame_normalizedFrame {C : CodeSpec.ExactCode n 2 3} {q : ℕ}
    [NeZero q] {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    shiftFrame (normalizedCode T).frame T.x0 = G.eigenFrame := by
  refine frame_ext ?_
  funext k s
  show (normalizedCode T).frame.vec k (SS.bxor s T.x0) = G.eigenFrame.vec k s
  show G.eigenFrame.vec k (SS.bxor (SS.bxor s T.x0) T.x0) = G.eigenFrame.vec k s
  rw [SS.bxor_bxor_cancel]

/-- The span hypothesis the flip transport needs, stated on a frame rather
than on a generator so that no modulus instance appears in it. -/
theorem codeSpan_shift_of_span {C : CodeSpec.ExactCode n 2 3} {q : ℕ}
    [NeZero q] {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G)
    (F : CodeSpec.OrthonormalFrame n 2)
    (hF : CodeSpec.codeSpan (normalizedCode T).frame = CodeSpec.codeSpan F) :
    CodeSpec.codeSpan C.frame = CodeSpec.codeSpan (shiftFrame F T.x0) := by
  have hmap := congrArg (Submodule.map (shiftEquiv T.x0).toLinearMap) hF
  rw [← codeSpan_shiftFrame, ← codeSpan_shiftFrame] at hmap
  rw [shiftFrame_normalizedFrame T] at hmap
  rw [G.span_eq]
  exact hmap

/-- **The bounded generator, on the original code.**

The fresh sparse generator flipped back by the local `X` string it was built
against.  Its modulus is the sparse one, hence at most `beta_n`. -/
def boundedGenerator {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    @RankTwoGlobal.FiniteGeneratorResolution n 3 C
      (frameFreshSparsePhase T).data.order (frameFreshOrderNeZero T) := by
  letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
  exact FlipSemanticTransport.flipFiniteGeneratorResolution
    (C' := C) (automaticFreshGenerator T) T.x0
    (codeSpan_shift_of_span T _ (automaticFreshGenerator T).span_eq)

/-- **`thm:d3-sslp-classification`.**

At distance three the sorted two-fibre normal form can be chosen with modulus
at most `beta_n`, replacing the `beta_{n+1}` of `thm:d2-sslp-classification`. -/
theorem exists_sortedNormalForm_le_betaN {B : ℕ}
    (beta : BinaryBeta.BetaBound n B)
    (C : CodeSpec.ExactCode n 2 3) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedForm.SortedNormalForm C, S.q ≤ B := by
  letI : NeZero (rationalLift C GeneralFiniteness.two_le_three theta hpres).order :=
    ⟨(rationalLift C GeneralFiniteness.two_le_three theta hpres).order_pos.ne'⟩
  set G := finiteGenerator C GeneralFiniteness.two_le_three theta hpres hnt
    with hG
  set T := canonicalTwoFiber G with hT
  letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
  obtain ⟨S, hS⟩ :=
    SortedForm.exists_sortedNormalForm_of_generator C (boundedGenerator T)
  refine ⟨S, ?_⟩
  rw [hS]
  exact automaticFreshGenerator_order_le beta T

/-- **The six-qubit cutoff, unconditionally.**  `beta_6 = 9` is a kernel
theorem, so the six-qubit sorted normal form has modulus at most nine with no
hypothesis at all. -/
theorem exists_sortedNormalForm_le_nine
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedForm.SortedNormalForm C, S.q ≤ 9 :=
  exists_sortedNormalForm_le_betaN
    MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper C theta hpres hnt

end

end MainTheory.D3BoundedNormalForm
