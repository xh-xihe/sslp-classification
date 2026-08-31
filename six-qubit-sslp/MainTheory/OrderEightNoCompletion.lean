import MainTheory.CubeCompletionTransport
import MainTheory.Generated.FiniteOrbitWitnessShard201
import MainTheory.Generated.FiniteOrbitWitnessShard202
import MainTheory.WImageNoGo51

/-!
# The generated logical-order-eight keys are no-gos

The two directory keys are connected to paper orbits 64 and 65 through their
literal support masks and the two stored cube actions.  Numeric paper ids are
not used as substitutes for these support-level identifications.
-/

namespace MainTheory.OrderEightNoCompletion

open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline

namespace Base
abbrev input201 := MainTheory.Generated.FiniteOrbitBase.input201
abbrev input202 := MainTheory.Generated.FiniteOrbitBase.input202
abbrev key63 := MainTheory.Generated.FiniteOrbitBase.key63
abbrev key64 := MainTheory.Generated.FiniteOrbitBase.key64
end Base

def paper64Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit64.S0
  | true => SixQubit.Orbit64.S1

def paper65Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit65.S0
  | true => SixQubit.Orbit65.S1

theorem input201_fibers_eq_paper64 :
    fibersOfPair Base.input201 = paper64Fibers := by
  funext c
  cases c <;> decide

theorem input202_fibers_eq_paper65 :
    fibersOfPair Base.input202 = paper65Fibers := by
  funext c
  cases c <;> decide

theorem paper64_equivalent_key63 :
    MainTheory.DistanceSignature.LabeledEquivalent
      8 8 paper64Fibers 8 8 Base.key63.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input201.q Base.input201.m paper64Fibers
      Base.key63.q Base.key63.m Base.key63.fibers
  rw [← input201_fibers_eq_paper64]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard201.witness_validFor

theorem paper65_equivalent_key64 :
    MainTheory.DistanceSignature.LabeledEquivalent
      8 8 paper65Fibers 8 8 Base.key64.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input202.q Base.input202.m paper65Fibers
      Base.key64.q Base.key64.m Base.key64.fibers
  rw [← input202_fibers_eq_paper65]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard202.witness_validFor

theorem paper64_noCompletion : NoCompletion paper64Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit64.av 0 1 paper64Fibers
  · simpa [paper64Fibers] using SixQubit.Orbit64.S0_eq_fiber
  · simpa [paper64Fibers] using SixQubit.Orbit64.S1_residue
  · exact MainTheory.WImageNoGo51.WImage_orbit64_empty

theorem paper65_noCompletion : NoCompletion paper65Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit65.av 0 1 paper65Fibers
  · simpa [paper65Fibers] using SixQubit.Orbit65.S0_eq_fiber
  · simpa [paper65Fibers] using SixQubit.Orbit65.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit65_empty

theorem key63_noCompletion : NoCompletion Base.key63.fibers :=
  not_completion_of_fiberEquivalent paper64_noCompletion
    paper64_equivalent_key63.2.2

theorem key64_noCompletion : NoCompletion Base.key64.fibers :=
  not_completion_of_fiberEquivalent paper65_noCompletion
    paper65_equivalent_key64.2.2

theorem keyAt63_eq :
    MainTheory.Generated.FiniteOrbitBase.keyAt 63 = Base.key63 := by
  decide

theorem keyAt64_eq :
    MainTheory.Generated.FiniteOrbitBase.keyAt 64 = Base.key64 := by
  decide

theorem paperOrbitId63_eq :
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 63 = 64 := by
  decide

theorem paperOrbitId64_eq :
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 64 = 65 := by
  decide

theorem directoryKey63_noCompletion :
    NoCompletion
      (MainTheory.Generated.FiniteOrbitBase.keyAt 63).fibers := by
  simpa only [keyAt63_eq] using key63_noCompletion

theorem directoryKey64_noCompletion :
    NoCompletion
      (MainTheory.Generated.FiniteOrbitBase.keyAt 64).fibers := by
  simpa only [keyAt64_eq] using key64_noCompletion

theorem key_m_eq_eight_iff (k : Fin 66) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 8 ↔
      k = 63 ∨ k = 64 := by
  fin_cases k <;> decide

theorem noCompletion_of_orderEight (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 8) :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  rcases (key_m_eq_eight_iff k).1 hm with h | h
  · subst k
    exact directoryKey63_noCompletion
  · subst k
    exact directoryKey64_noCompletion

/-- Paper-facing metadata after the two actual support identifications. -/
theorem paperOrbitId_of_orderEight (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 8) :
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId k = 64 ∨
      MainTheory.Generated.FiniteOrbitBase.paperOrbitId k = 65 := by
  rcases (key_m_eq_eight_iff k).1 hm with h | h
  · subst k
    exact Or.inl paperOrbitId63_eq
  · subst k
    exact Or.inr paperOrbitId64_eq

end MainTheory.OrderEightNoCompletion
