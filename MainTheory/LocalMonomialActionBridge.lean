import MainTheory.LocalMonomialElementary

/-!
# One-site `CodeEquiv.monAct` as an explicit LU kernel

This module identifies the amplitude-level diagonal/antidiagonal action at
one physical coordinate with `ClassificationLevels.oneQubitKernel`.  Together
with `PhysicalProjectorBridge`, it turns that action on every vector of a
frame into one genuine level-(iv) LU step.
-/

namespace MainTheory.LocalMonomialActionBridge

noncomputable section

/-- Replace one Boolean coordinate and leave all other coordinates fixed. -/
def replaceBit {n : Nat} (j : Fin n) (b : Bool) (s : SS.BitString n) :
    SS.BitString n :=
  fun k => if k = j then b else s k

/-- Input basis word selected by a diagonal (`flip=false`) or antidiagonal
(`flip=true`) one-site matrix. -/
def oneSiteInput {n : Nat} (j : Fin n) (flip : Bool)
    (s : SS.BitString n) : SS.BitString n :=
  replaceBit j (xor (s j) flip) s

@[simp] theorem oneSiteInput_apply_self {n : Nat} (j : Fin n)
    (flip : Bool) (s : SS.BitString n) :
    oneSiteInput j flip s j = xor (s j) flip := by
  simp [oneSiteInput, replaceBit]

theorem oneSiteInput_apply_ne {n : Nat} (j k : Fin n) (hkj : k ≠ j)
    (flip : Bool) (s : SS.BitString n) :
    oneSiteInput j flip s k = s k := by
  simp [oneSiteInput, replaceBit, hkj]

private theorem eq_oneSiteInput_iff {n : Nat} (j : Fin n)
    (flip : Bool) (x y : SS.BitString n) :
    y = oneSiteInput j flip x ↔
      y j = xor (x j) flip ∧ ∀ k, k ≠ j → x k = y k := by
  constructor
  · intro h
    subst y
    constructor
    · exact oneSiteInput_apply_self j flip x
    · intro k hkj
      exact (oneSiteInput_apply_ne j k hkj flip x).symm
  · rintro ⟨hj, hout⟩
    funext k
    by_cases hkj : k = j
    · subst k
      simpa using hj
    · rw [oneSiteInput_apply_ne j k hkj]
      exact (hout k hkj).symm

/-- Sparse global kernel of the one-site monomial factor. -/
def oneSiteMonomialKernel {n : Nat} (j : Fin n) (flip : Bool)
    (al be : ℂ) : MainTheory.ClassificationLevels.OperatorKernel n :=
  fun x y =>
    if y = oneSiteInput j flip x then (if x j then be else al) else 0

/-- The sparse global kernel is definitionally the same physical operator as
the generic one-qubit-kernel construction applied to `monomialMatrix`. -/
theorem oneQubitKernel_monomialMatrix {n : Nat} (j : Fin n)
    (flip : Bool) (al be : ℂ) :
    MainTheory.ClassificationLevels.oneQubitKernel j
        (MainTheory.LocalMonomialElementary.monomialMatrix flip al be) =
      oneSiteMonomialKernel j flip al be := by
  funext x y
  unfold oneSiteMonomialKernel
  by_cases htarget : y = oneSiteInput j flip x
  · subst y
    cases hflip : flip <;>
      cases hx : x j <;>
      simp [MainTheory.ClassificationLevels.oneQubitKernel,
        MainTheory.ClassificationLevels.bitIndex,
        MainTheory.LocalMonomialElementary.monomialMatrix,
        oneSiteInput, replaceBit, hx]
  · by_cases hout : ∀ k, k ≠ j → x k = y k
    · have hbit : y j ≠ xor (x j) flip := by
        intro hbit
        exact htarget ((eq_oneSiteInput_iff j flip x y).2 ⟨hbit, hout⟩)
      cases hflip : flip <;>
        cases hx : x j <;>
        cases hy : y j <;>
        simp [MainTheory.ClassificationLevels.oneQubitKernel,
          MainTheory.ClassificationLevels.bitIndex,
          MainTheory.LocalMonomialElementary.monomialMatrix,
          hflip, hx, hy] at hbit ⊢ <;>
          intro heq <;>
          exfalso <;>
          apply htarget <;>
          simpa only [hflip] using heq
    · cases hflip : flip <;>
        cases hx : x j <;>
        cases hy : y j <;>
        simp [MainTheory.ClassificationLevels.oneQubitKernel, hout] <;>
          intro heq <;>
          exfalso <;>
          apply htarget <;>
          simpa only [hflip] using heq

/-- Matrix action of the one-qubit kernel, in the exact amplitude convention
used by `CodeEquiv.monAct`. -/
theorem kernelAction_monomialMatrix {n : Nat} (j : Fin n)
    (flip : Bool) (al be : ℂ) (psi : SS.State n ℂ) :
    MainTheory.ClassificationLevels.kernelAction
        (MainTheory.ClassificationLevels.oneQubitKernel j
          (MainTheory.LocalMonomialElementary.monomialMatrix flip al be)) psi =
      fun s => (if s j then be else al) * psi (oneSiteInput j flip s) := by
  rw [oneQubitKernel_monomialMatrix]
  funext s
  simp [MainTheory.ClassificationLevels.kernelAction,
    oneSiteMonomialKernel]

/-- Applying one local monomial factor to every vector of a frame is one
explicit `LUEquivalent` step. -/
theorem luEquivalent_of_oneSiteMonomial_frames {n K : Nat}
    (F G : MainTheory.CodeSpec.OrthonormalFrame n K)
    (j : Fin n) (flip : Bool) (al be : ℂ)
    (hal : Complex.normSq al = 1) (hbe : Complex.normSq be = 1)
    (hvec : ∀ k, G.vec k =
      fun s => (if s j then be else al) *
        F.vec k (oneSiteInput j flip s)) :
    MainTheory.ClassificationLevels.LUEquivalent
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame F)
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame G) := by
  apply MainTheory.PhysicalProjectorBridge.luEquivalent_of_oneQubit_frames
    F G j (MainTheory.LocalMonomialElementary.monomialMatrix flip al be)
    (MainTheory.LocalMonomialElementary.monomialMatrix_unitary
      flip al be hal hbe)
  intro k
  rw [hvec k]
  exact (kernelAction_monomialMatrix j flip al be (F.vec k)).symm

end

end MainTheory.LocalMonomialActionBridge
