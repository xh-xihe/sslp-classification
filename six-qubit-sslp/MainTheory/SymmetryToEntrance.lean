import MainTheory.LocalPhaseAngle
import MainTheory.PhaseSectorBridge
import MainTheory.GlobalClassificationBridge
import MainTheory.SixQubitSemanticEntrance
import MainTheory.LabelledGates

/-!
# From a diagonal symmetry to the entrance's hypotheses

`D3CertifiedSpectralOuterEntrance.arbitrary_code_enters_outer` takes a real
angle vector `theta`, a proof that `realGateEnd theta` preserves the code, and
projective nontriviality.  The intrinsic group is built from `LocalPhase`.  This
file converts one into the other, so that any element of the group can be fed to
the entrance.

`MainTheory/LocalPhaseAngle.lean` supplies the angle vector; what is added here
is the operator-level identity and the two hypotheses in the shape the entrance
asks for.
-/

namespace MainTheory.SymmetryToEntrance

variable {n d : ℕ}

open MainTheory.ClassificationLevels

/-- **The real gate of a matching angle vector is the diagonal action.** -/
theorem realGateEnd_eq_diagonalAction (u : LocalPhase n) (theta : Fin n → ℝ)
    (h : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ))
      = ((u j : ℂ)))
    (phi : SS.State n ℂ) :
    PhaseSectorBridge.realGateEnd theta phi = diagonalAction u phi := by
  funext s
  rw [PhaseSectorBridge.realGateEnd]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MainTheory.RealGate.realGate,
    diagonalAction]
  rw [LocalPhaseAngle.diagonalValue_eq_exp u theta h s]

/-- A diagonal symmetry gives the entrance's preservation hypothesis.

Stated at arbitrary rank: nothing in the argument sees the number of logical
states, and `GeneralLiftOrder` needs it at general `K`. -/
theorem codePreserving_of_symmetry {K : ℕ} (F : CodeSpec.OrthonormalFrame n K)
    (u : LocalPhase n)
    (hu : u ∈ diagonalSymmetryGroup (CodeProjector.ofFrame F))
    (theta : Fin n → ℝ)
    (h : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ))
      = ((u j : ℂ))) :
    CodeSpec.CodePreserving F (PhaseSectorBridge.realGateEnd theta) := by
  intro phi hphi
  rw [realGateEnd_eq_diagonalAction u theta h]
  have := hu.1 phi ((GlobalClassificationBridge.inProjectorRange_ofFrame_iff F phi).2 hphi)
  exact (GlobalClassificationBridge.inProjectorRange_ofFrame_iff F _).1 this

/-! ## Triviality matches on both sides

The entrance's `ProjectivelyNontrivialReal` says the real gate is not a nonzero
scalar on the code; the intrinsic group quotients by exactly the symmetries that
are.  So the dichotomy the assembly needs -- either the class is the identity, or
the entrance applies -- is the same dichotomy on both sides. -/

/-- If the real gate is projectively trivial, so is the symmetry. -/
theorem isProjectivelyTrivial_of_sameProjective (F : CodeSpec.OrthonormalFrame n 2)
    (u : LocalPhase n)
    (hu : u ∈ diagonalSymmetryGroup (CodeProjector.ofFrame F))
    (theta : Fin n → ℝ)
    (h : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ))
      = ((u j : ℂ)))
    (htriv : CodeSpec.SameProjectiveOnCode F
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    IsProjectivelyTrivial (CodeProjector.ofFrame F) ⟨u, hu⟩ := by
  obtain ⟨lam, hlam, hact⟩ := htriv
  refine ⟨lam, hlam, fun phi hphi => ?_⟩
  have hmem : phi ∈ CodeSpec.codeSpan F :=
    (GlobalClassificationBridge.inProjectorRange_ofFrame_iff F phi).1 hphi
  have hh := hact phi hmem
  rw [realGateEnd_eq_diagonalAction u theta h] at hh
  simpa using hh

/-- Hence a nonidentity class supplies the entrance's nontriviality. -/
theorem projectivelyNontrivialReal_of_class_ne_one
    (C : CodeSpec.ExactCode n 2 d)
    (u : LocalPhase n)
    (hu : u ∈ diagonalSymmetryGroup (CodeProjector.ofFrame C.frame))
    (theta : Fin n → ℝ)
    (h : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ))
      = ((u j : ℂ)))
    (hne : intrinsicClass (CodeProjector.ofFrame C.frame) ⟨u, hu⟩ ≠ 1) :
    ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id := by
  intro htriv
  apply hne
  rw [intrinsicClass, QuotientGroup.eq_one_iff]
  exact isProjectivelyTrivial_of_sameProjective C.frame u hu theta h htriv

/-! ## The identity class is bounded

The trivial branch of the assembly, complete: the identity class is represented
by the identity symmetry, which is the gate of `trivialLabel`. -/

/-- The identity local phase is a diagonal symmetry of every code. -/
theorem one_mem_symmetryGroup (F : CodeSpec.OrthonormalFrame n 2) :
    (1 : LocalPhase n) ∈ diagonalSymmetryGroup (CodeProjector.ofFrame F) :=
  Subgroup.one_mem _

/-- **The identity class has a bounded label.** -/
theorem exists_label_of_class_one (C : CodeSpec.ExactCode n 2 d) (hB : 0 < B) :
    ∃ (lbl : ProjectiveGroupFinite.BoundedPhaseLabel n B)
      (u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)),
      intrinsicClass (CodeProjector.ofFrame C.frame) u = 1 ∧
        (u : LocalPhase n) = BoundedRepresentation.gateOfLabel lbl := by
  refine ⟨LabelledGates.trivialLabel hB,
    ⟨1, one_mem_symmetryGroup C.frame⟩, ?_, ?_⟩
  · rw [intrinsicClass]
    exact QuotientGroup.mk_one _
  · rw [LabelledGates.gateOfLabel_trivial]

end MainTheory.SymmetryToEntrance
