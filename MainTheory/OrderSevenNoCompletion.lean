import MainTheory.CubeCompletionTransport
import MainTheory.Generated.FiniteOrbitWitnessShard175
import MainTheory.Generated.FiniteOrbitWitnessShard176
import MainTheory.Generated.FiniteOrbitWitnessShard177
import MainTheory.Generated.FiniteOrbitWitnessShard179
import MainTheory.Generated.FiniteOrbitWitnessShard180
import MainTheory.WImageNoGo51

/-!
# The generated logical-order-7 keys are no-gos

There are 5 of them, and they had no layer of their own: orders 5,
6, 8 and 9 did, but orders 4 and 7 -- fifteen of the sixty-six keys
between them -- did not, so nothing connected their paper no-gos to
the directory and `M_3(6) = 5` could not be stated.

Each key is bound to its paper support pair by an exact mask equality
and its stored, kernel-checked cube action.  The numerical
paper-orbit table is consulted only after those payload-level
identifications.
-/

namespace MainTheory.OrderSevenNoCompletion

open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline

namespace Base
abbrev input177 := MainTheory.Generated.FiniteOrbitBase.input177
abbrev input175 := MainTheory.Generated.FiniteOrbitBase.input175
abbrev input180 := MainTheory.Generated.FiniteOrbitBase.input180
abbrev input176 := MainTheory.Generated.FiniteOrbitBase.input176
abbrev input179 := MainTheory.Generated.FiniteOrbitBase.input179
abbrev key56 := MainTheory.Generated.FiniteOrbitBase.key56
abbrev key57 := MainTheory.Generated.FiniteOrbitBase.key57
abbrev key58 := MainTheory.Generated.FiniteOrbitBase.key58
abbrev key59 := MainTheory.Generated.FiniteOrbitBase.key59
abbrev key60 := MainTheory.Generated.FiniteOrbitBase.key60
end Base

def paper59Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit59.S0
  | true => SixQubit.Orbit59.S1

theorem input177_fibers_eq_paper59 :
    fibersOfPair Base.input177 = paper59Fibers := by
  funext c
  cases c <;> decide

theorem paper59_equivalent_key56 :
    MainTheory.DistanceSignature.LabeledEquivalent
      7 7 paper59Fibers 7 7 Base.key56.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input177.q Base.input177.m paper59Fibers
      Base.key56.q Base.key56.m Base.key56.fibers
  rw [← input177_fibers_eq_paper59]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard177.witness_validFor

theorem paper59_noCompletion : NoCompletion paper59Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit59.av 0 1
    paper59Fibers
  · simpa [paper59Fibers] using SixQubit.Orbit59.S0_eq_fiber
  · simpa [paper59Fibers] using SixQubit.Orbit59.S1_residue
  · exact MainTheory.WImageNoGo51.WImage_orbit59_empty

theorem key56_noCompletion : NoCompletion Base.key56.fibers :=
  not_completion_of_fiberEquivalent paper59_noCompletion
    paper59_equivalent_key56.2.2

theorem keyAt56_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 56 = Base.key56 := by decide

theorem paperOrbitId56_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 56 = 59 := by decide

theorem directoryKey56_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 56).fibers := by
  simpa only [keyAt56_eq] using key56_noCompletion

def paper57Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit57.S0
  | true => SixQubit.Orbit57.S1

theorem input175_fibers_eq_paper57 :
    fibersOfPair Base.input175 = paper57Fibers := by
  funext c
  cases c <;> decide

theorem paper57_equivalent_key57 :
    MainTheory.DistanceSignature.LabeledEquivalent
      7 7 paper57Fibers 7 7 Base.key57.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input175.q Base.input175.m paper57Fibers
      Base.key57.q Base.key57.m Base.key57.fibers
  rw [← input175_fibers_eq_paper57]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard175.witness_validFor

theorem paper57_noCompletion : NoCompletion paper57Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit57.av 0 1
    paper57Fibers
  · simpa [paper57Fibers] using SixQubit.Orbit57.S0_eq_fiber
  · simpa [paper57Fibers] using SixQubit.Orbit57.S1_residue
  · exact MainTheory.WImageNoGo51.WImage_orbit57_empty

theorem key57_noCompletion : NoCompletion Base.key57.fibers :=
  not_completion_of_fiberEquivalent paper57_noCompletion
    paper57_equivalent_key57.2.2

theorem keyAt57_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 57 = Base.key57 := by decide

theorem paperOrbitId57_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 57 = 57 := by decide

theorem directoryKey57_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 57).fibers := by
  simpa only [keyAt57_eq] using key57_noCompletion

def paper61Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit61.S0
  | true => SixQubit.Orbit61.S1

theorem input180_fibers_eq_paper61 :
    fibersOfPair Base.input180 = paper61Fibers := by
  funext c
  cases c <;> decide

theorem paper61_equivalent_key58 :
    MainTheory.DistanceSignature.LabeledEquivalent
      7 7 paper61Fibers 7 7 Base.key58.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input180.q Base.input180.m paper61Fibers
      Base.key58.q Base.key58.m Base.key58.fibers
  rw [← input180_fibers_eq_paper61]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard180.witness_validFor

theorem paper61_noCompletion : NoCompletion paper61Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit61.av 0 1
    paper61Fibers
  · simpa [paper61Fibers] using SixQubit.Orbit61.S0_eq_fiber
  · simpa [paper61Fibers] using SixQubit.Orbit61.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit61_empty

theorem key58_noCompletion : NoCompletion Base.key58.fibers :=
  not_completion_of_fiberEquivalent paper61_noCompletion
    paper61_equivalent_key58.2.2

theorem keyAt58_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 58 = Base.key58 := by decide

theorem paperOrbitId58_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 58 = 61 := by decide

theorem directoryKey58_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 58).fibers := by
  simpa only [keyAt58_eq] using key58_noCompletion

def paper58Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit58.S0
  | true => SixQubit.Orbit58.S1

theorem input176_fibers_eq_paper58 :
    fibersOfPair Base.input176 = paper58Fibers := by
  funext c
  cases c <;> decide

theorem paper58_equivalent_key59 :
    MainTheory.DistanceSignature.LabeledEquivalent
      7 7 paper58Fibers 7 7 Base.key59.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input176.q Base.input176.m paper58Fibers
      Base.key59.q Base.key59.m Base.key59.fibers
  rw [← input176_fibers_eq_paper58]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard176.witness_validFor

theorem paper58_noCompletion : NoCompletion paper58Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit58.av 0 1
    paper58Fibers
  · simpa [paper58Fibers] using SixQubit.Orbit58.S0_eq_fiber
  · simpa [paper58Fibers] using SixQubit.Orbit58.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit58_empty

theorem key59_noCompletion : NoCompletion Base.key59.fibers :=
  not_completion_of_fiberEquivalent paper58_noCompletion
    paper58_equivalent_key59.2.2

theorem keyAt59_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 59 = Base.key59 := by decide

theorem paperOrbitId59_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 59 = 58 := by decide

theorem directoryKey59_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 59).fibers := by
  simpa only [keyAt59_eq] using key59_noCompletion

def paper60Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit60.S0
  | true => SixQubit.Orbit60.S1

theorem input179_fibers_eq_paper60 :
    fibersOfPair Base.input179 = paper60Fibers := by
  funext c
  cases c <;> decide

theorem paper60_equivalent_key60 :
    MainTheory.DistanceSignature.LabeledEquivalent
      7 7 paper60Fibers 7 7 Base.key60.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input179.q Base.input179.m paper60Fibers
      Base.key60.q Base.key60.m Base.key60.fibers
  rw [← input179_fibers_eq_paper60]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard179.witness_validFor

theorem paper60_noCompletion : NoCompletion paper60Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit60.av 0 1
    paper60Fibers
  · simpa [paper60Fibers] using SixQubit.Orbit60.S0_eq_fiber
  · simpa [paper60Fibers] using SixQubit.Orbit60.S1_residue
  · exact MainTheory.WImageNoGo51.WImage_orbit60_empty

theorem key60_noCompletion : NoCompletion Base.key60.fibers :=
  not_completion_of_fiberEquivalent paper60_noCompletion
    paper60_equivalent_key60.2.2

theorem keyAt60_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 60 = Base.key60 := by decide

theorem paperOrbitId60_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 60 = 60 := by decide

theorem directoryKey60_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 60).fibers := by
  simpa only [keyAt60_eq] using key60_noCompletion

/-- Exactly these keys carry logical order 7. -/
theorem key_m_eq_seven_iff (k : Fin 66) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 7 ↔
      k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 := by
  fin_cases k <;> decide

/-- **No exact distance-three code completes a logical-order-7
orbit.** -/
theorem noCompletion_of_orderSeven (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 7) :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  rcases (key_m_eq_seven_iff k).1 hm with h | h | h | h | h
  · subst k; exact directoryKey56_noCompletion
  · subst k; exact directoryKey57_noCompletion
  · subst k; exact directoryKey58_noCompletion
  · subst k; exact directoryKey59_noCompletion
  · subst k; exact directoryKey60_noCompletion

end MainTheory.OrderSevenNoCompletion
