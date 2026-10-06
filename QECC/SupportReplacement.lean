import QECC.ProjectorSupport

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- If a physical phase is constant on the actual computational support of
the code, then it acts projectively as that scalar on the code. -/
theorem actsAsScalar_of_constant_on_actualCodeSupport [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (theta : PhaseVector n) (c : LocalPhase)
    (hconstant : ∀ x ∈ C.actualCodeSupport a,
      supportPhase theta x = c) :
    C.ActsAsScalar theta := by
  refine ⟨c, fun x y hxy => ?_⟩
  apply hconstant x
  by_contra hx
  let e : State n := computationalBasisState y
  let psi : C.CodeSpace := ⟨C.proj.mulVec e, ⟨e, rfl⟩⟩
  have hvanish := C.codeSpace_vanishes_off_actualSupport
    hq a hpres psi x hx
  have heval : psi.1 x = C.proj x y := by
    simp [psi, e, Matrix.mulVec, dotProduct, computationalBasisState]
  exact hxy (heval.symm.trans hvanish)

/-- It is enough to prove constancy separately on every active sector's
actual support. -/
theorem actsAsScalar_of_constant_on_actualSectorSupports [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (theta : PhaseVector n) (c : LocalPhase)
    (hconstant : ∀ (b : C.ActiveResidue a) x,
      x ∈ C.actualSectorSupport a b → supportPhase theta x = c) :
    C.ActsAsScalar theta := by
  apply C.actsAsScalar_of_constant_on_actualCodeSupport hq a hpres theta c
  rintro x ⟨b, hx⟩
  exact hconstant b x hx

end CodeProjector

end

end QECC
