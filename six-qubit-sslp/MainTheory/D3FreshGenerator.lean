import MainTheory.D3FreshFiniteGateAction
import MainTheory.RankTwoGlobal
import MainTheory.PhaseSectorBridge

/-!
# Packaging a fresh sparse phase as a finite generator

This module performs the packaging step which must remain separate from the
denominator bound.  Given genuine real-gate eigenframe data for the actual
code and a `FreshSparsePhase` for those two logical states, it constructs a
new `FiniteGeneratorResolution` whose modulus is the fresh least denominator.
-/

namespace MainTheory.D3FreshGenerator

variable {n : ℕ}

open MainTheory
open MainTheory.D3FreshSparseAssembly

noncomputable section

/-- The freshly bounded rational phase, expressed as a genuine primitive
finite generator spanning the actual code. -/
noncomputable def ofFreshSparsePhase
    {C : CodeSpec.ExactCode n 2 3}
    (theta : Fin n → ℝ)
    (eigenFrame : CodeSpec.OrthonormalFrame n 2)
    (span_eq : CodeSpec.codeSpan C.frame =
      CodeSpec.codeSpan eigenFrame)
    (eigenvalue : Fin 2 → ℂ)
    (eigen : ∀ k,
      MainTheory.RealGate.realGate theta (eigenFrame.vec k) =
        fun x => eigenvalue k * eigenFrame.vec k x)
    (projectively_nontrivial : eigenvalue 0 ≠ eigenvalue 1)
    (F : FreshSparsePhase
      (eigenFrame.vec 0) (eigenFrame.vec 1) theta) :
    @RankTwoGlobal.FiniteGeneratorResolution n 3 C F.data.order
      ⟨F.data.order_pos.ne'⟩ := by
  letI : NeZero F.data.order := ⟨F.data.order_pos.ne'⟩
  refine
    { zeta := D3FreshFiniteGate.standardRoot F.data
      primitiveRoot := D3FreshFiniteGate.standardRoot_primitive F.data
      angle := F.data.angle
      primitive := F.data.angle_primitive
      eigenFrame := eigenFrame
      span_eq := span_eq
      eigenvalue := eigenvalue
      eigen := ?_
      projectively_nontrivial := projectively_nontrivial }
  intro k
  calc
    Gate.gate (D3FreshFiniteGate.standardRoot F.data) F.data.angle
        (eigenFrame.vec k) =
        D3FreshFiniteGateAction.freshGate F.data
          (eigenFrame.vec k) :=
      congrFun (D3FreshFiniteGateAction.gate_eq_freshGate F.data)
        (eigenFrame.vec k)
    _ = MainTheory.RealGate.realGate F.data.fullSolutionReal
        (eigenFrame.vec k) :=
      congrFun (D3FreshFiniteGateAction.freshGate_eq_realGate F.data)
        (eigenFrame.vec k)
    _ = MainTheory.RealGate.realGate theta (eigenFrame.vec k) := by
      fin_cases k
      · exact F.realGate_eq_left
      · exact F.realGate_eq_right
    _ = fun x => eigenvalue k * eigenFrame.vec k x := eigen k

/-- The new finite generator and the original real gate induce exactly the
same projective action on the actual code.  In fact the scalar is one; the
projective formulation is the interface consumed by the semantic entrance. -/
theorem ofFreshSparsePhase_sameProjective
    {C : CodeSpec.ExactCode n 2 3}
    (theta : Fin n → ℝ)
    (eigenFrame : CodeSpec.OrthonormalFrame n 2)
    (span_eq : CodeSpec.codeSpan C.frame =
      CodeSpec.codeSpan eigenFrame)
    (eigenvalue : Fin 2 → ℂ)
    (eigen : ∀ k,
      MainTheory.RealGate.realGate theta (eigenFrame.vec k) =
        fun x => eigenvalue k * eigenFrame.vec k x)
    (projectively_nontrivial : eigenvalue 0 ≠ eigenvalue 1)
    (F : FreshSparsePhase
      (eigenFrame.vec 0) (eigenFrame.vec 1) theta) :
    CodeSpec.SameProjectiveOnCode C.frame
      (@RankTwoGlobal.finiteGateEnd n F.data.order
        ⟨F.data.order_pos.ne'⟩
        (D3FreshFiniteGate.standardRoot F.data) F.data.angle)
      (PhaseSectorBridge.realGateEnd theta) := by
  letI : NeZero F.data.order := ⟨F.data.order_pos.ne'⟩
  let G := ofFreshSparsePhase theta eigenFrame span_eq eigenvalue
    eigen projectively_nontrivial F
  have hframe : CodeSpec.SameProjectiveOnCode eigenFrame
      (RankTwoGlobal.finiteGateEnd G.zeta G.angle)
      (PhaseSectorBridge.realGateEnd theta) := by
    apply (CodeSpec.sameProjectiveOnCode_iff_frame eigenFrame _ _).2
    refine ⟨1, one_ne_zero, ?_⟩
    intro k
    simp only [one_smul]
    calc
      RankTwoGlobal.finiteGateEnd G.zeta G.angle
          (eigenFrame.vec k) =
          Gate.gate G.zeta G.angle (eigenFrame.vec k) := rfl
      _ = fun x => eigenvalue k * eigenFrame.vec k x := G.eigen k
      _ = MainTheory.RealGate.realGate theta
          (eigenFrame.vec k) := (eigen k).symm
      _ = PhaseSectorBridge.realGateEnd theta
          (eigenFrame.vec k) := rfl
  unfold CodeSpec.SameProjectiveOnCode at hframe ⊢
  rw [span_eq]
  simpa [G] using hframe

end

end MainTheory.D3FreshGenerator
