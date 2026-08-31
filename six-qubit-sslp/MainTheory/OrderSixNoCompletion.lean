import MainTheory.CubeCompletionTransport
import MainTheory.Generated.FiniteOrbitWitnessShard162
import MainTheory.Generated.FiniteOrbitWitnessShard163
import MainTheory.Generated.FiniteOrbitWitnessShard164
import MainTheory.Generated.FiniteOrbitWitnessShard166
import MainTheory.WImageNoGo51

/-!
# The generated logical-order-six keys are no-gos

Each of the four generated payloads is bound to its paper support pair by an
exact mask equality and its stored, kernel-checked cube action.  The numerical
paper-orbit table is used only after these payload-level identifications.
-/

namespace MainTheory.OrderSixNoCompletion

open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline

namespace Base
abbrev input162 := MainTheory.Generated.FiniteOrbitBase.input162
abbrev input163 := MainTheory.Generated.FiniteOrbitBase.input163
abbrev input164 := MainTheory.Generated.FiniteOrbitBase.input164
abbrev input166 := MainTheory.Generated.FiniteOrbitBase.input166
abbrev key52 := MainTheory.Generated.FiniteOrbitBase.key52
abbrev key53 := MainTheory.Generated.FiniteOrbitBase.key53
abbrev key54 := MainTheory.Generated.FiniteOrbitBase.key54
abbrev key55 := MainTheory.Generated.FiniteOrbitBase.key55
end Base

def paper53Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit53.S0
  | true => SixQubit.Orbit53.S1

def paper54Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit54.S0
  | true => SixQubit.Orbit54.S1

def paper55Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit55.S0
  | true => SixQubit.Orbit55.S1

def paper56Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit56.S0
  | true => SixQubit.Orbit56.S1

theorem input162_fibers_eq_paper53 : fibersOfPair Base.input162 = paper53Fibers := by
  funext c
  cases c <;> decide

theorem input163_fibers_eq_paper54 : fibersOfPair Base.input163 = paper54Fibers := by
  funext c
  cases c <;> decide

theorem input164_fibers_eq_paper55 : fibersOfPair Base.input164 = paper55Fibers := by
  funext c
  cases c <;> decide

theorem input166_fibers_eq_paper56 : fibersOfPair Base.input166 = paper56Fibers := by
  funext c
  cases c <;> decide

theorem paper53_equivalent_key53 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 6 paper53Fibers 6 6 Base.key53.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input162.q Base.input162.m paper53Fibers
      Base.key53.q Base.key53.m Base.key53.fibers
  rw [← input162_fibers_eq_paper53]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard162.witness_validFor

theorem paper54_equivalent_key52 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 6 paper54Fibers 6 6 Base.key52.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input163.q Base.input163.m paper54Fibers
      Base.key52.q Base.key52.m Base.key52.fibers
  rw [← input163_fibers_eq_paper54]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard163.witness_validFor

theorem paper55_equivalent_key54 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 6 paper55Fibers 6 6 Base.key54.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input164.q Base.input164.m paper55Fibers
      Base.key54.q Base.key54.m Base.key54.fibers
  rw [← input164_fibers_eq_paper55]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard164.witness_validFor

theorem paper56_equivalent_key55 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 6 paper56Fibers 6 6 Base.key55.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input166.q Base.input166.m paper56Fibers
      Base.key55.q Base.key55.m Base.key55.fibers
  rw [← input166_fibers_eq_paper56]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard166.witness_validFor

theorem paper53_noCompletion : NoCompletion paper53Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit53.av 0 1 paper53Fibers
  · simpa [paper53Fibers] using SixQubit.Orbit53.S0_eq_fiber
  · simpa [paper53Fibers] using SixQubit.Orbit53.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit53_empty

theorem paper54_noCompletion : NoCompletion paper54Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit54.av 0 1 paper54Fibers
  · simpa [paper54Fibers] using SixQubit.Orbit54.S0_eq_fiber
  · simpa [paper54Fibers] using SixQubit.Orbit54.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit54_empty

theorem paper55_noCompletion : NoCompletion paper55Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit55.av 0 1 paper55Fibers
  · simpa [paper55Fibers] using SixQubit.Orbit55.S0_eq_fiber
  · simpa [paper55Fibers] using SixQubit.Orbit55.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit55_empty

theorem paper56_noCompletion : NoCompletion paper56Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit56.av 0 1 paper56Fibers
  · simpa [paper56Fibers] using SixQubit.Orbit56.S0_eq_fiber
  · simpa [paper56Fibers] using SixQubit.Orbit56.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit56_empty

theorem key52_noCompletion : NoCompletion Base.key52.fibers :=
  not_completion_of_fiberEquivalent paper54_noCompletion paper54_equivalent_key52.2.2

theorem key53_noCompletion : NoCompletion Base.key53.fibers :=
  not_completion_of_fiberEquivalent paper53_noCompletion paper53_equivalent_key53.2.2

theorem key54_noCompletion : NoCompletion Base.key54.fibers :=
  not_completion_of_fiberEquivalent paper55_noCompletion paper55_equivalent_key54.2.2

theorem key55_noCompletion : NoCompletion Base.key55.fibers :=
  not_completion_of_fiberEquivalent paper56_noCompletion paper56_equivalent_key55.2.2

theorem keyAt52_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 52 = Base.key52 := by decide
theorem keyAt53_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 53 = Base.key53 := by decide
theorem keyAt54_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 54 = Base.key54 := by decide
theorem keyAt55_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 55 = Base.key55 := by decide

theorem paperOrbitId52_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 52 = 54 := by decide
theorem paperOrbitId53_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 53 = 53 := by decide
theorem paperOrbitId54_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 54 = 55 := by decide
theorem paperOrbitId55_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 55 = 56 := by decide

theorem directoryKey52_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 52).fibers := by
  simpa only [keyAt52_eq] using key52_noCompletion

theorem directoryKey53_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 53).fibers := by
  simpa only [keyAt53_eq] using key53_noCompletion

theorem directoryKey54_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 54).fibers := by
  simpa only [keyAt54_eq] using key54_noCompletion

theorem directoryKey55_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 55).fibers := by
  simpa only [keyAt55_eq] using key55_noCompletion

theorem key_m_eq_six_iff (k : Fin 66) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 6 ↔
      k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 := by
  fin_cases k <;> decide

theorem noCompletion_of_orderSix (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 6) :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  rcases (key_m_eq_six_iff k).1 hm with h | h | h | h
  · subst k; exact directoryKey52_noCompletion
  · subst k; exact directoryKey53_noCompletion
  · subst k; exact directoryKey54_noCompletion
  · subst k; exact directoryKey55_noCompletion

end MainTheory.OrderSixNoCompletion
