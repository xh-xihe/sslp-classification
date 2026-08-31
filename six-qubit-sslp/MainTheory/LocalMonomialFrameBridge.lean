import MainTheory.LocalMonomialActionBridge

/-!
# Orthonormal-frame closure under one local monomial factor

The preceding action bridge compares a supplied pair of frames.  For chaining
the six physical sites we also need the intermediate frames themselves.  This
leaf proves directly that the one-site amplitude action preserves the complex
inner product, constructs the transformed orthonormal frame, and certifies its
projector as one LU step from the original frame projector.
-/

namespace MainTheory.LocalMonomialFrameBridge

open scoped BigOperators ComplexConjugate

noncomputable section

def oneSiteMask {n : Nat} (j : Fin n) (flip : Bool) : SS.BitString n :=
  fun k => if k = j then flip else false

theorem oneSiteInput_eq_bxor {n : Nat} (j : Fin n) (flip : Bool)
    (s : SS.BitString n) :
    MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s =
      SS.bxor s (oneSiteMask j flip) := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [MainTheory.LocalMonomialActionBridge.oneSiteInput,
      MainTheory.LocalMonomialActionBridge.replaceBit,
      oneSiteMask, SS.bxor]
  · simp [MainTheory.LocalMonomialActionBridge.oneSiteInput,
      MainTheory.LocalMonomialActionBridge.replaceBit,
      oneSiteMask, SS.bxor, hkj]

theorem oneSiteInput_involutive {n : Nat} (j : Fin n) (flip : Bool)
    (s : SS.BitString n) :
    MainTheory.LocalMonomialActionBridge.oneSiteInput j flip
        (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s) = s := by
  simp only [oneSiteInput_eq_bxor, SS.bxor_bxor_cancel]

def oneSiteInputEquiv {n : Nat} (j : Fin n) (flip : Bool) :
    SS.BitString n ≃ SS.BitString n where
  toFun := MainTheory.LocalMonomialActionBridge.oneSiteInput j flip
  invFun := MainTheory.LocalMonomialActionBridge.oneSiteInput j flip
  left_inv := oneSiteInput_involutive j flip
  right_inv := oneSiteInput_involutive j flip

def oneSiteAct {n : Nat} (j : Fin n) (flip : Bool) (al be : ℂ)
    (psi : SS.State n ℂ) : SS.State n ℂ :=
  fun s => (if s j then be else al) *
    psi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s)

/-- A unitary diagonal/antidiagonal factor preserves the full state inner
product, not merely normalization of a particular codeword. -/
theorem innerC_oneSiteAct {n : Nat} (j : Fin n) (flip : Bool)
    (al be : ℂ) (hal : Complex.normSq al = 1)
    (hbe : Complex.normSq be = 1) (psi phi : SS.State n ℂ) :
    SS.innerC (oneSiteAct j flip al be psi)
        (oneSiteAct j flip al be phi) = SS.innerC psi phi := by
  have halL : star al * al = 1 :=
    SixQubit.CodeEquiv.unit_of_normSq hal
  have hbeL : star be * be = 1 :=
    SixQubit.CodeEquiv.unit_of_normSq hbe
  have hcoeff : ∀ s : SS.BitString n,
      star (if s j then be else al) * (if s j then be else al) = 1 := by
    intro s
    cases hs : s j
    · simpa [hs] using halL
    · simpa [hs] using hbeL
  unfold SS.innerC oneSiteAct
  calc
    (∑ s, star
          ((if s j then be else al) *
            psi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s)) *
        ((if s j then be else al) *
          phi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s))) =
      ∑ s,
        star (psi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s)) *
          phi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s) := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [star_mul']
      calc
        (star (if s j then be else al) *
            star (psi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s))) *
            ((if s j then be else al) *
              phi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s)) =
          (star (if s j then be else al) *
              (if s j then be else al)) *
            (star (psi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s)) *
              phi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s)) := by
                ring
        _ = star (psi
              (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s)) *
            phi (MainTheory.LocalMonomialActionBridge.oneSiteInput j flip s) := by
              rw [hcoeff s, one_mul]
    _ = ∑ s, star (psi s) * phi s := by
      exact Equiv.sum_comp (oneSiteInputEquiv j flip)
        (fun s => star (psi s) * phi s)

/-- The intermediate orthonormal frame after one physical monomial factor. -/
def oneSiteFrame {n K : Nat} (F : MainTheory.CodeSpec.OrthonormalFrame n K)
    (j : Fin n) (flip : Bool) (al be : ℂ)
    (hal : Complex.normSq al = 1) (hbe : Complex.normSq be = 1) :
    MainTheory.CodeSpec.OrthonormalFrame n K where
  vec k := oneSiteAct j flip al be (F.vec k)
  orthonormal := by
    intro k l
    rw [innerC_oneSiteAct j flip al be hal hbe]
    exact F.orthonormal k l

/-- The constructed intermediate frame is connected to the original by one
kernel-visible LU step. -/
theorem oneSiteFrame_luEquivalent {n K : Nat}
    (F : MainTheory.CodeSpec.OrthonormalFrame n K)
    (j : Fin n) (flip : Bool) (al be : ℂ)
    (hal : Complex.normSq al = 1) (hbe : Complex.normSq be = 1) :
    MainTheory.ClassificationLevels.LUEquivalent
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame F)
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame
        (oneSiteFrame F j flip al be hal hbe)) := by
  apply MainTheory.LocalMonomialActionBridge.luEquivalent_of_oneSiteMonomial_frames
      F (oneSiteFrame F j flip al be hal hbe) j flip al be hal hbe
  intro k
  rfl

end

end MainTheory.LocalMonomialFrameBridge
