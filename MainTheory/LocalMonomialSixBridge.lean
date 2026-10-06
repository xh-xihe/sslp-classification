import MainTheory.CodeEquivProjectorBridge
import MainTheory.LocalMonomialFrameBridge
import MainTheory.PermutationFrameBridge

/-!
# Six-qubit `CodeEquiv.Equivalent` implies projector LU equivalence

This is the fixed-six-qubit physical glue omitted by the amplitude-level
classification.  A `LocalMonomial` is expanded into one physical-qubit
permutation followed by six certified one-qubit diagonal/antidiagonal gates.
Logical rephasing and interchange are then removed by exact equality of frame
projectors.

No tensor-product unitary is postulated: every physical step is an inhabitant
of `ClassificationLevels.ElementaryLU`, and the final statement uses only its
equivalence closure.
-/

namespace MainTheory.LocalMonomialSixBridge

noncomputable section

open MainTheory.ClassificationLevels

abbrev LM6 := SixQubit.CodeEquiv.LocalMonomial 6

/-- The coefficient contributed by the factor at one physical site. -/
def siteCoeff (U : LM6) (i : Fin 6) (s : SS.BitString 6) : ℂ :=
  if s i then U.be i else U.al i

/-! Staged input words.  Keeping each layer named prevents weak-head
reduction from expanding all six coordinate replacements at once. -/

def input0 (U : LM6) (s : SS.BitString 6) : SS.BitString 6 :=
  MainTheory.LocalMonomialActionBridge.oneSiteInput 0 (U.flip 0) s

def input1 (U : LM6) (s : SS.BitString 6) : SS.BitString 6 :=
  input0 U (MainTheory.LocalMonomialActionBridge.oneSiteInput 1 (U.flip 1) s)

def input2 (U : LM6) (s : SS.BitString 6) : SS.BitString 6 :=
  input1 U (MainTheory.LocalMonomialActionBridge.oneSiteInput 2 (U.flip 2) s)

def input3 (U : LM6) (s : SS.BitString 6) : SS.BitString 6 :=
  input2 U (MainTheory.LocalMonomialActionBridge.oneSiteInput 3 (U.flip 3) s)

def input4 (U : LM6) (s : SS.BitString 6) : SS.BitString 6 :=
  input3 U (MainTheory.LocalMonomialActionBridge.oneSiteInput 4 (U.flip 4) s)

def input5 (U : LM6) (s : SS.BitString 6) : SS.BitString 6 :=
  input4 U (MainTheory.LocalMonomialActionBridge.oneSiteInput 5 (U.flip 5) s)

/-! Staged state actions. -/

def site0Act (U : LM6) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  MainTheory.LocalMonomialFrameBridge.oneSiteAct 0
    (U.flip 0) (U.al 0) (U.be 0) psi

def site1Act (U : LM6) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  MainTheory.LocalMonomialFrameBridge.oneSiteAct 1
    (U.flip 1) (U.al 1) (U.be 1) (site0Act U psi)

def site2Act (U : LM6) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  MainTheory.LocalMonomialFrameBridge.oneSiteAct 2
    (U.flip 2) (U.al 2) (U.be 2) (site1Act U psi)

def site3Act (U : LM6) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  MainTheory.LocalMonomialFrameBridge.oneSiteAct 3
    (U.flip 3) (U.al 3) (U.be 3) (site2Act U psi)

def site4Act (U : LM6) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  MainTheory.LocalMonomialFrameBridge.oneSiteAct 4
    (U.flip 4) (U.al 4) (U.be 4) (site3Act U psi)

def site5Act (U : LM6) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  MainTheory.LocalMonomialFrameBridge.oneSiteAct 5
    (U.flip 5) (U.al 5) (U.be 5) (site4Act U psi)

/-- The state action obtained by applying the six one-site factors in the
fixed coordinate order `0,1,2,3,4,5`. -/
def sixSiteAct (U : LM6) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  site5Act U psi

theorem site0Act_apply (U : LM6) (psi : SS.State 6 ℂ)
    (s : SS.BitString 6) :
    site0Act U psi s = siteCoeff U 0 s * psi (input0 U s) := by
  rfl

theorem site1Act_apply (U : LM6) (psi : SS.State 6 ℂ)
    (s : SS.BitString 6) :
    site1Act U psi s =
      siteCoeff U 1 s * (siteCoeff U 0 s * psi (input1 U s)) := by
  unfold site1Act MainTheory.LocalMonomialFrameBridge.oneSiteAct
  rw [site0Act_apply]
  simp [siteCoeff, input1,
    MainTheory.LocalMonomialActionBridge.oneSiteInput,
    MainTheory.LocalMonomialActionBridge.replaceBit]

theorem site2Act_apply (U : LM6) (psi : SS.State 6 ℂ)
    (s : SS.BitString 6) :
    site2Act U psi s = siteCoeff U 2 s *
      (siteCoeff U 1 s * (siteCoeff U 0 s * psi (input2 U s))) := by
  unfold site2Act MainTheory.LocalMonomialFrameBridge.oneSiteAct
  rw [site1Act_apply]
  simp [siteCoeff, input2,
    MainTheory.LocalMonomialActionBridge.oneSiteInput,
    MainTheory.LocalMonomialActionBridge.replaceBit]

theorem site3Act_apply (U : LM6) (psi : SS.State 6 ℂ)
    (s : SS.BitString 6) :
    site3Act U psi s = siteCoeff U 3 s * (siteCoeff U 2 s *
      (siteCoeff U 1 s * (siteCoeff U 0 s * psi (input3 U s)))) := by
  unfold site3Act MainTheory.LocalMonomialFrameBridge.oneSiteAct
  rw [site2Act_apply]
  simp [siteCoeff, input3,
    MainTheory.LocalMonomialActionBridge.oneSiteInput,
    MainTheory.LocalMonomialActionBridge.replaceBit]

theorem site4Act_apply (U : LM6) (psi : SS.State 6 ℂ)
    (s : SS.BitString 6) :
    site4Act U psi s = siteCoeff U 4 s * (siteCoeff U 3 s *
      (siteCoeff U 2 s * (siteCoeff U 1 s *
        (siteCoeff U 0 s * psi (input4 U s))))) := by
  unfold site4Act MainTheory.LocalMonomialFrameBridge.oneSiteAct
  rw [site3Act_apply]
  simp [siteCoeff, input4,
    MainTheory.LocalMonomialActionBridge.oneSiteInput,
    MainTheory.LocalMonomialActionBridge.replaceBit]

theorem site5Act_apply (U : LM6) (psi : SS.State 6 ℂ)
    (s : SS.BitString 6) :
    site5Act U psi s = siteCoeff U 5 s * (siteCoeff U 4 s *
      (siteCoeff U 3 s * (siteCoeff U 2 s * (siteCoeff U 1 s *
        (siteCoeff U 0 s * psi (input5 U s)))))) := by
  unfold site5Act MainTheory.LocalMonomialFrameBridge.oneSiteAct
  rw [site4Act_apply]
  simp [siteCoeff, input5,
    MainTheory.LocalMonomialActionBridge.oneSiteInput,
    MainTheory.LocalMonomialActionBridge.replaceBit]

theorem input5_eq_bxor (U : LM6) (s : SS.BitString 6) :
    input5 U s = SS.bxor s U.flip := by
  funext i
  fin_cases i <;>
    simp [input5, input4, input3, input2, input1, input0,
      MainTheory.LocalMonomialActionBridge.oneSiteInput,
      MainTheory.LocalMonomialActionBridge.replaceBit, SS.bxor]

/-- The six sparse one-site actions are exactly `CodeEquiv.monAct`, including
the coefficient product and the full XOR input word. -/
theorem sixSiteAct_eq_monAct (U : LM6) (psi : SS.State 6 ℂ) :
    sixSiteAct U psi =
      SixQubit.CodeEquiv.monAct U.flip U.al U.be psi := by
  funext s
  change site5Act U psi s = _
  rw [site5Act_apply, input5_eq_bxor]
  change siteCoeff U 5 s * (siteCoeff U 4 s *
      (siteCoeff U 3 s * (siteCoeff U 2 s * (siteCoeff U 1 s *
        (siteCoeff U 0 s * psi (SS.bxor s U.flip)))))) =
    (∏ i : Fin 6, siteCoeff U i s) * psi (SS.bxor s U.flip)
  have hprod : (∏ i : Fin 6, siteCoeff U i s) =
      siteCoeff U 0 s * (siteCoeff U 1 s * (siteCoeff U 2 s *
        (siteCoeff U 3 s * (siteCoeff U 4 s * siteCoeff U 5 s)))) := by
    have h1 : Fin.succ (0 : Fin 5) = (1 : Fin 6) := Fin.ext (by rfl)
    have h2 : Fin.succ (Fin.succ (0 : Fin 4)) = (2 : Fin 6) :=
      Fin.ext (by rfl)
    have h3 : Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))) = (3 : Fin 6) :=
      Fin.ext (by rfl)
    have h4 :
        Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))) =
          (4 : Fin 6) := Fin.ext (by rfl)
    have h5 :
        Fin.succ (Fin.succ (Fin.succ (Fin.succ
          (Fin.succ (0 : Fin 1))))) = (5 : Fin 6) := Fin.ext (by rfl)
    have hempty :
        (∏ i : Fin 0, siteCoeff U i.succ.succ.succ.succ.succ.succ s) = 1 := by
      simp
    simp only [Fin.prod_univ_succ]
    rw [h1, h2, h3, h4, h5, hempty, mul_one]
  rw [hprod]
  ring

def permutedFrame (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 :=
  MainTheory.PermutationFrameBridge.permFrame F U.perm

def afterSite0 (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 :=
  MainTheory.LocalMonomialFrameBridge.oneSiteFrame (permutedFrame F U)
    0 (U.flip 0) (U.al 0) (U.be 0) (U.al_unit 0) (U.be_unit 0)

def afterSite1 (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 :=
  MainTheory.LocalMonomialFrameBridge.oneSiteFrame (afterSite0 F U)
    1 (U.flip 1) (U.al 1) (U.be 1) (U.al_unit 1) (U.be_unit 1)

def afterSite2 (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 :=
  MainTheory.LocalMonomialFrameBridge.oneSiteFrame (afterSite1 F U)
    2 (U.flip 2) (U.al 2) (U.be 2) (U.al_unit 2) (U.be_unit 2)

def afterSite3 (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 :=
  MainTheory.LocalMonomialFrameBridge.oneSiteFrame (afterSite2 F U)
    3 (U.flip 3) (U.al 3) (U.be 3) (U.al_unit 3) (U.be_unit 3)

def afterSite4 (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 :=
  MainTheory.LocalMonomialFrameBridge.oneSiteFrame (afterSite3 F U)
    4 (U.flip 4) (U.al 4) (U.be 4) (U.al_unit 4) (U.be_unit 4)

/-- The concrete intermediate frame after the permutation and all six local
factors. -/
def localMonomialFrame (F : MainTheory.CodeSpec.OrthonormalFrame 6 2)
    (U : LM6) : MainTheory.CodeSpec.OrthonormalFrame 6 2 :=
  MainTheory.LocalMonomialFrameBridge.oneSiteFrame (afterSite4 F U)
    5 (U.flip 5) (U.al 5) (U.be 5) (U.al_unit 5) (U.be_unit 5)

theorem permutedFrame_vec
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) (k : Fin 2) :
    (permutedFrame F U).vec k =
      SixQubit.CodeEquiv.permAct U.perm (F.vec k) := by
  rfl

theorem afterSite0_vec
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) (k : Fin 2) :
    (afterSite0 F U).vec k = site0Act U
      (SixQubit.CodeEquiv.permAct U.perm (F.vec k)) := by
  change MainTheory.LocalMonomialFrameBridge.oneSiteAct 0
      (U.flip 0) (U.al 0) (U.be 0) ((permutedFrame F U).vec k) = _
  rw [permutedFrame_vec]
  rfl

theorem afterSite1_vec
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) (k : Fin 2) :
    (afterSite1 F U).vec k = site1Act U
      (SixQubit.CodeEquiv.permAct U.perm (F.vec k)) := by
  change MainTheory.LocalMonomialFrameBridge.oneSiteAct 1
      (U.flip 1) (U.al 1) (U.be 1) ((afterSite0 F U).vec k) = _
  rw [afterSite0_vec]
  rfl

theorem afterSite2_vec
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) (k : Fin 2) :
    (afterSite2 F U).vec k = site2Act U
      (SixQubit.CodeEquiv.permAct U.perm (F.vec k)) := by
  change MainTheory.LocalMonomialFrameBridge.oneSiteAct 2
      (U.flip 2) (U.al 2) (U.be 2) ((afterSite1 F U).vec k) = _
  rw [afterSite1_vec]
  rfl

theorem afterSite3_vec
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) (k : Fin 2) :
    (afterSite3 F U).vec k = site3Act U
      (SixQubit.CodeEquiv.permAct U.perm (F.vec k)) := by
  change MainTheory.LocalMonomialFrameBridge.oneSiteAct 3
      (U.flip 3) (U.al 3) (U.be 3) ((afterSite2 F U).vec k) = _
  rw [afterSite2_vec]
  rfl

theorem afterSite4_vec
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) (k : Fin 2) :
    (afterSite4 F U).vec k = site4Act U
      (SixQubit.CodeEquiv.permAct U.perm (F.vec k)) := by
  change MainTheory.LocalMonomialFrameBridge.oneSiteAct 4
      (U.flip 4) (U.al 4) (U.be 4) ((afterSite3 F U).vec k) = _
  rw [afterSite3_vec]
  rfl

theorem localMonomialFrame_vec
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) (k : Fin 2) :
    (localMonomialFrame F U).vec k = U.act (F.vec k) := by
  change MainTheory.LocalMonomialFrameBridge.oneSiteAct 5
      (U.flip 5) (U.al 5) (U.be 5) ((afterSite4 F U).vec k) = _
  rw [afterSite4_vec]
  change sixSiteAct U
    (SixQubit.CodeEquiv.permAct U.perm (F.vec k)) = U.act (F.vec k)
  rw [sixSiteAct_eq_monAct]
  rfl

/-- A complete six-qubit local monomial, including its physical-qubit
permutation, is a finite chain of seven kernel-visible elementary LU steps. -/
theorem localMonomialFrame_luEquivalent
    (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) (U : LM6) :
    LUEquivalent (CodeProjector.ofFrame F)
      (CodeProjector.ofFrame (localMonomialFrame F U)) := by
  have hp := MainTheory.PermutationFrameBridge.permFrame_luEquivalent F U.perm
  have h0 := MainTheory.LocalMonomialFrameBridge.oneSiteFrame_luEquivalent
    (permutedFrame F U) 0 (U.flip 0) (U.al 0) (U.be 0)
      (U.al_unit 0) (U.be_unit 0)
  have h1 := MainTheory.LocalMonomialFrameBridge.oneSiteFrame_luEquivalent
    (afterSite0 F U) 1 (U.flip 1) (U.al 1) (U.be 1)
      (U.al_unit 1) (U.be_unit 1)
  have h2 := MainTheory.LocalMonomialFrameBridge.oneSiteFrame_luEquivalent
    (afterSite1 F U) 2 (U.flip 2) (U.al 2) (U.be 2)
      (U.al_unit 2) (U.be_unit 2)
  have h3 := MainTheory.LocalMonomialFrameBridge.oneSiteFrame_luEquivalent
    (afterSite2 F U) 3 (U.flip 3) (U.al 3) (U.be 3)
      (U.al_unit 3) (U.be_unit 3)
  have h4 := MainTheory.LocalMonomialFrameBridge.oneSiteFrame_luEquivalent
    (afterSite3 F U) 4 (U.flip 4) (U.al 4) (U.be 4)
      (U.al_unit 4) (U.be_unit 4)
  have h5 := MainTheory.LocalMonomialFrameBridge.oneSiteFrame_luEquivalent
    (afterSite4 F U) 5 (U.flip 5) (U.al 5) (U.be 5)
      (U.al_unit 5) (U.be_unit 5)
  exact luEquivalent_equivalence.trans hp
    (luEquivalent_equivalence.trans h0
      (luEquivalent_equivalence.trans h1
        (luEquivalent_equivalence.trans h2
          (luEquivalent_equivalence.trans h3
            (luEquivalent_equivalence.trans h4 h5)))))

/-- The amplitude-level six-qubit equivalence used by the finite
classification really implies equality of level-(iv) LU code classes for
orthonormal frames. -/
theorem luEquivalent_of_codeEquivalent
    (F G : MainTheory.CodeSpec.OrthonormalFrame 6 2)
    (hE : SixQubit.CodeEquiv.Equivalent F.vec G.vec) :
    LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame G) := by
  obtain ⟨U, lam, sw, hlam, hvec⟩ := hE
  let H := localMonomialFrame F U
  have hphysical : LUEquivalent (CodeProjector.ofFrame F)
      (CodeProjector.ofFrame H) := by
    exact localMonomialFrame_luEquivalent F U
  have hgauge : CodeProjector.ofFrame G = CodeProjector.ofFrame H := by
    apply MainTheory.CodeEquivProjectorBridge.ofFrame_eq_of_logicalGauge
      H G lam sw hlam
    intro k
    calc
      G.vec k = SixQubit.CodeEquiv.scal (lam k)
          (U.act (F.vec (SixQubit.CodeEquiv.swapIdx sw k))) := hvec k
      _ = SixQubit.CodeEquiv.scal (lam k)
          (H.vec (SixQubit.CodeEquiv.swapIdx sw k)) := by
            rw [localMonomialFrame_vec]
  rw [hgauge]
  exact hphysical

end

end MainTheory.LocalMonomialSixBridge
