import MainTheory.WImageNoGo51
import MainTheory.WImages
import MainTheory.WImageOrbit36

/-!
# The 62 paper orbits whose weight-enumerator images are settled

This is a deliberately paper-facing aggregation leaf.  It packages the 51
empty images proved in `MainTheory.WImageNoGo51` together with the exact image
theorems for the eleven realized orbits 7, 8, 9, 10, 11, 16, 21, 22, 23, 36
and 45.  The remaining paper IDs are exactly 1, 2, 3 and 4.

This file does not claim the still-separate generated-directory transport from
the 66 canonical orbit representatives.  Its content is the conjunction of
the concrete paper-representative `WImage` theorems imported above, plus a
kernel-checked audit of the paper-ID partition.
-/

namespace MainTheory.WImageSettled62

/-- One proposition containing all eleven exact, nonempty image descriptions. -/
structure Realized11Statement : Prop where
  orbit7 :
    MainTheory.Levels.WImage SixQubit.Orbit7Real.av 0 1 =
      MainTheory.WImages.FI '' Set.Icc 0 1
  orbit8 :
    MainTheory.Levels.WImage SixQubit.Orbit8Real.av 0 1 =
      MainTheory.WImages.FI '' Set.Icc (1 / 2) 1
  orbit9 :
    MainTheory.Levels.WImage SixQubit.Orbit9Real.av 0 1 =
      {MainTheory.Levels.E2A}
  orbit10 :
    MainTheory.Levels.WImage SixQubit.Orbit10Real.av 0 2 =
      {MainTheory.Levels.E2A}
  orbit11 :
    MainTheory.Levels.WImage SixQubit.Orbit11Real.av 0 2 =
      {MainTheory.WImages.E1A}
  orbit16 :
    MainTheory.Levels.WImage SixQubit.Orbit16Real.av 0 2 =
      {MainTheory.Levels.E2A}
  orbit21 :
    MainTheory.Levels.WImage SixQubit.Orbit21Cert.av 0 2 =
      {MainTheory.Levels.E2A}
  orbit22 :
    MainTheory.Levels.WImage SixQubit.Orbit22Real.av 0 2 =
      {MainTheory.Levels.E2A}
  orbit23 :
    MainTheory.Levels.WImage SixQubit.Orbit23Real.av 0 2 =
      {MainTheory.WImages.E1A}
  orbit36 :
    MainTheory.Levels.WImage SixQubit.Orbit36Transport.originalAv 0 1 =
      {MainTheory.WImages.R5A}
  orbit45 :
    MainTheory.Levels.WImage SixQubit.Orbit45Support.av 0 3 =
      MainTheory.WImages.FII '' Set.Icc (2 / 3) 1

/-- The existing orbit-specific proofs inhabit the eleven-orbit package. -/
theorem all_11_realized_WImages : Realized11Statement where
  orbit7 := MainTheory.WImages.WImage_orbit7
  orbit8 := MainTheory.WImages.WImage_orbit8
  orbit9 := MainTheory.WImages.WImage_orbit9
  orbit10 := MainTheory.WImages.WImage_orbit10
  orbit11 := MainTheory.WImages.WImage_orbit11
  orbit16 := MainTheory.WImages.WImage_orbit16
  orbit21 := MainTheory.Levels.WImage_orbit21
  orbit22 := MainTheory.WImages.WImage_orbit22
  orbit23 := MainTheory.WImages.WImage_orbit23
  orbit36 := MainTheory.WImages.WImage_orbit36
  orbit45 := MainTheory.WImages.WImage_orbit45

/-- The exact proposition proved by the aggregate 51-no-go theorem. -/
def NoGo51Statement : Prop :=
  MainTheory.WImageNoGo51.Q3NoGoStatement ∧
  MainTheory.WImageNoGo51.Q4NoGoStatement ∧
  MainTheory.WImageNoGo51.Q5NoGoStatement ∧
  MainTheory.WImageNoGo51.Q6NoGoStatement ∧
  MainTheory.WImageNoGo51.Q7NoGoStatement ∧
  MainTheory.WImageNoGo51.Q8NoGoStatement ∧
  MainTheory.WImageNoGo51.Q9NoGoStatement

/-- Fifty-one exact empty images and eleven exact realized images. -/
def Settled62Statement : Prop := NoGo51Statement ∧ Realized11Statement

/-- A single kernel term packaging all 62 settled paper-facing images. -/
theorem all_62_settled_WImages : Settled62Statement := by
  exact ⟨MainTheory.WImageNoGo51.all_51_no_go_WImages,
    all_11_realized_WImages⟩

def realizedOrbitIds : List Nat := [7, 8, 9, 10, 11, 16, 21, 22, 23, 36, 45]

def openOrbitIds : List Nat := [1, 2, 3, 4]

def settledOrbitIds : List Nat :=
  MainTheory.WImageNoGo51.noGoOrbitIds ++ realizedOrbitIds

def statusOrbitIds : List Nat := settledOrbitIds ++ openOrbitIds

def paperOrbitIds : Finset Nat := Finset.Icc 1 66

theorem realizedOrbitIds_length : realizedOrbitIds.length = 11 := by decide
theorem realizedOrbitIds_nodup : realizedOrbitIds.Nodup := by decide
theorem openOrbitIds_length : openOrbitIds.length = 4 := by decide
theorem settledOrbitIds_length : settledOrbitIds.length = 62 := by decide
theorem statusOrbitIds_length : statusOrbitIds.length = 66 := by decide
theorem statusOrbitIds_nodup : statusOrbitIds.Nodup := by decide

/-- The 51 no-go, 11 realized and 4 open lists cover paper IDs 1 through 66
exactly once. -/
theorem statusOrbitIds_cover : statusOrbitIds.toFinset = paperOrbitIds := by decide

end MainTheory.WImageSettled62
