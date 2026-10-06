import MainTheory.CubeCompletionTransport
import MainTheory.Generated.FiniteOrbitWitnessShard058
import MainTheory.Generated.FiniteOrbitWitnessShard059
import MainTheory.Generated.FiniteOrbitWitnessShard062
import MainTheory.Generated.FiniteOrbitWitnessShard063
import MainTheory.Generated.FiniteOrbitWitnessShard065
import MainTheory.Generated.FiniteOrbitWitnessShard066
import MainTheory.Generated.FiniteOrbitWitnessShard067
import MainTheory.Generated.FiniteOrbitWitnessShard070
import MainTheory.Generated.FiniteOrbitWitnessShard193
import MainTheory.Generated.FiniteOrbitWitnessShard194
import MainTheory.WImageNoGo51

/-!
# The generated logical-order-4 keys are no-gos

There are 10 of them, and they had no layer of their own: orders 5,
6, 8 and 9 did, but orders 4 and 7 -- fifteen of the sixty-six keys
between them -- did not, so nothing connected their paper no-gos to
the directory and `M_3(6) = 5` could not be stated.

Each key is bound to its paper support pair by an exact mask equality
and its stored, kernel-checked cube action.  The numerical
paper-orbit table is consulted only after those payload-level
identifications.
-/

namespace MainTheory.OrderFourNoCompletion

open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline

namespace Base
abbrev input058 := MainTheory.Generated.FiniteOrbitBase.input058
abbrev input059 := MainTheory.Generated.FiniteOrbitBase.input059
abbrev input067 := MainTheory.Generated.FiniteOrbitBase.input067
abbrev input070 := MainTheory.Generated.FiniteOrbitBase.input070
abbrev input063 := MainTheory.Generated.FiniteOrbitBase.input063
abbrev input066 := MainTheory.Generated.FiniteOrbitBase.input066
abbrev input062 := MainTheory.Generated.FiniteOrbitBase.input062
abbrev input065 := MainTheory.Generated.FiniteOrbitBase.input065
abbrev input193 := MainTheory.Generated.FiniteOrbitBase.input193
abbrev input194 := MainTheory.Generated.FiniteOrbitBase.input194
abbrev key24 := MainTheory.Generated.FiniteOrbitBase.key24
abbrev key25 := MainTheory.Generated.FiniteOrbitBase.key25
abbrev key26 := MainTheory.Generated.FiniteOrbitBase.key26
abbrev key27 := MainTheory.Generated.FiniteOrbitBase.key27
abbrev key28 := MainTheory.Generated.FiniteOrbitBase.key28
abbrev key29 := MainTheory.Generated.FiniteOrbitBase.key29
abbrev key30 := MainTheory.Generated.FiniteOrbitBase.key30
abbrev key31 := MainTheory.Generated.FiniteOrbitBase.key31
abbrev key61 := MainTheory.Generated.FiniteOrbitBase.key61
abbrev key62 := MainTheory.Generated.FiniteOrbitBase.key62
end Base

def paper25Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit25.S0
  | true => SixQubit.Orbit25.S1

theorem input058_fibers_eq_paper25 :
    fibersOfPair Base.input058 = paper25Fibers := by
  funext c
  cases c <;> decide

theorem paper25_equivalent_key24 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper25Fibers 4 4 Base.key24.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input058.q Base.input058.m paper25Fibers
      Base.key24.q Base.key24.m Base.key24.fibers
  rw [← input058_fibers_eq_paper25]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard058.witness_validFor

theorem paper25_noCompletion : NoCompletion paper25Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit25.av 0 1
    paper25Fibers
  · simpa [paper25Fibers] using SixQubit.Orbit25.S0_eq_fiber
  · simpa [paper25Fibers] using SixQubit.Orbit25.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit25_empty

theorem key24_noCompletion : NoCompletion Base.key24.fibers :=
  not_completion_of_fiberEquivalent paper25_noCompletion
    paper25_equivalent_key24.2.2

theorem keyAt24_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 24 = Base.key24 := by decide

theorem paperOrbitId24_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 24 = 25 := by decide

theorem directoryKey24_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 24).fibers := by
  simpa only [keyAt24_eq] using key24_noCompletion

def paper26Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit26.S0
  | true => SixQubit.Orbit26.S1

theorem input059_fibers_eq_paper26 :
    fibersOfPair Base.input059 = paper26Fibers := by
  funext c
  cases c <;> decide

theorem paper26_equivalent_key25 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper26Fibers 4 4 Base.key25.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input059.q Base.input059.m paper26Fibers
      Base.key25.q Base.key25.m Base.key25.fibers
  rw [← input059_fibers_eq_paper26]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard059.witness_validFor

theorem paper26_noCompletion : NoCompletion paper26Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit26.av 0 1
    paper26Fibers
  · simpa [paper26Fibers] using SixQubit.Orbit26.S0_eq_fiber
  · simpa [paper26Fibers] using SixQubit.Orbit26.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit26_empty

theorem key25_noCompletion : NoCompletion Base.key25.fibers :=
  not_completion_of_fiberEquivalent paper26_noCompletion
    paper26_equivalent_key25.2.2

theorem keyAt25_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 25 = Base.key25 := by decide

theorem paperOrbitId25_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 25 = 26 := by decide

theorem directoryKey25_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 25).fibers := by
  simpa only [keyAt25_eq] using key25_noCompletion

def paper31Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit31.S0
  | true => SixQubit.Orbit31.S1

theorem input067_fibers_eq_paper31 :
    fibersOfPair Base.input067 = paper31Fibers := by
  funext c
  cases c <;> decide

theorem paper31_equivalent_key26 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper31Fibers 4 4 Base.key26.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input067.q Base.input067.m paper31Fibers
      Base.key26.q Base.key26.m Base.key26.fibers
  rw [← input067_fibers_eq_paper31]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard067.witness_validFor

theorem paper31_noCompletion : NoCompletion paper31Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit31.av 0 1
    paper31Fibers
  · simpa [paper31Fibers] using SixQubit.Orbit31.S0_eq_fiber
  · simpa [paper31Fibers] using SixQubit.Orbit31.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit31_empty

theorem key26_noCompletion : NoCompletion Base.key26.fibers :=
  not_completion_of_fiberEquivalent paper31_noCompletion
    paper31_equivalent_key26.2.2

theorem keyAt26_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 26 = Base.key26 := by decide

theorem paperOrbitId26_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 26 = 31 := by decide

theorem directoryKey26_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 26).fibers := by
  simpa only [keyAt26_eq] using key26_noCompletion

def paper32Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit32.S0
  | true => SixQubit.Orbit32.S1

theorem input070_fibers_eq_paper32 :
    fibersOfPair Base.input070 = paper32Fibers := by
  funext c
  cases c <;> decide

theorem paper32_equivalent_key27 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper32Fibers 4 4 Base.key27.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input070.q Base.input070.m paper32Fibers
      Base.key27.q Base.key27.m Base.key27.fibers
  rw [← input070_fibers_eq_paper32]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard070.witness_validFor

theorem paper32_noCompletion : NoCompletion paper32Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit32.av 0 1
    paper32Fibers
  · simpa [paper32Fibers] using SixQubit.Orbit32.S0_eq_fiber
  · simpa [paper32Fibers] using SixQubit.Orbit32.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit32_empty

theorem key27_noCompletion : NoCompletion Base.key27.fibers :=
  not_completion_of_fiberEquivalent paper32_noCompletion
    paper32_equivalent_key27.2.2

theorem keyAt27_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 27 = Base.key27 := by decide

theorem paperOrbitId27_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 27 = 32 := by decide

theorem directoryKey27_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 27).fibers := by
  simpa only [keyAt27_eq] using key27_noCompletion

def paper28Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit28.S0
  | true => SixQubit.Orbit28.S1

theorem input063_fibers_eq_paper28 :
    fibersOfPair Base.input063 = paper28Fibers := by
  funext c
  cases c <;> decide

theorem paper28_equivalent_key28 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper28Fibers 4 4 Base.key28.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input063.q Base.input063.m paper28Fibers
      Base.key28.q Base.key28.m Base.key28.fibers
  rw [← input063_fibers_eq_paper28]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard063.witness_validFor

theorem paper28_noCompletion : NoCompletion paper28Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit28.av 0 1
    paper28Fibers
  · simpa [paper28Fibers] using SixQubit.Orbit28.S0_eq_fiber
  · simpa [paper28Fibers] using SixQubit.Orbit28.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit28_empty

theorem key28_noCompletion : NoCompletion Base.key28.fibers :=
  not_completion_of_fiberEquivalent paper28_noCompletion
    paper28_equivalent_key28.2.2

theorem keyAt28_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 28 = Base.key28 := by decide

theorem paperOrbitId28_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 28 = 28 := by decide

theorem directoryKey28_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 28).fibers := by
  simpa only [keyAt28_eq] using key28_noCompletion

def paper30Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit30.S0
  | true => SixQubit.Orbit30.S1

theorem input066_fibers_eq_paper30 :
    fibersOfPair Base.input066 = paper30Fibers := by
  funext c
  cases c <;> decide

theorem paper30_equivalent_key29 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper30Fibers 4 4 Base.key29.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input066.q Base.input066.m paper30Fibers
      Base.key29.q Base.key29.m Base.key29.fibers
  rw [← input066_fibers_eq_paper30]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard066.witness_validFor

theorem paper30_noCompletion : NoCompletion paper30Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit30.av 0 1
    paper30Fibers
  · simpa [paper30Fibers] using SixQubit.Orbit30.S0_eq_fiber
  · simpa [paper30Fibers] using SixQubit.Orbit30.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit30_empty

theorem key29_noCompletion : NoCompletion Base.key29.fibers :=
  not_completion_of_fiberEquivalent paper30_noCompletion
    paper30_equivalent_key29.2.2

theorem keyAt29_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 29 = Base.key29 := by decide

theorem paperOrbitId29_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 29 = 30 := by decide

theorem directoryKey29_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 29).fibers := by
  simpa only [keyAt29_eq] using key29_noCompletion

def paper27Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit27.S0
  | true => SixQubit.Orbit27.S1

theorem input062_fibers_eq_paper27 :
    fibersOfPair Base.input062 = paper27Fibers := by
  funext c
  cases c <;> decide

theorem paper27_equivalent_key30 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper27Fibers 4 4 Base.key30.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input062.q Base.input062.m paper27Fibers
      Base.key30.q Base.key30.m Base.key30.fibers
  rw [← input062_fibers_eq_paper27]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard062.witness_validFor

theorem paper27_noCompletion : NoCompletion paper27Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit27.av 0 1
    paper27Fibers
  · simpa [paper27Fibers] using SixQubit.Orbit27.S0_eq_fiber
  · simpa [paper27Fibers] using SixQubit.Orbit27.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit27_empty

theorem key30_noCompletion : NoCompletion Base.key30.fibers :=
  not_completion_of_fiberEquivalent paper27_noCompletion
    paper27_equivalent_key30.2.2

theorem keyAt30_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 30 = Base.key30 := by decide

theorem paperOrbitId30_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 30 = 27 := by decide

theorem directoryKey30_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 30).fibers := by
  simpa only [keyAt30_eq] using key30_noCompletion

def paper29Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit29.S0
  | true => SixQubit.Orbit29.S1

theorem input065_fibers_eq_paper29 :
    fibersOfPair Base.input065 = paper29Fibers := by
  funext c
  cases c <;> decide

theorem paper29_equivalent_key31 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 4 paper29Fibers 4 4 Base.key31.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input065.q Base.input065.m paper29Fibers
      Base.key31.q Base.key31.m Base.key31.fibers
  rw [← input065_fibers_eq_paper29]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard065.witness_validFor

theorem paper29_noCompletion : NoCompletion paper29Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit29.av 0 1
    paper29Fibers
  · simpa [paper29Fibers] using SixQubit.Orbit29.S0_eq_fiber
  · simpa [paper29Fibers] using SixQubit.Orbit29.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit29_empty

theorem key31_noCompletion : NoCompletion Base.key31.fibers :=
  not_completion_of_fiberEquivalent paper29_noCompletion
    paper29_equivalent_key31.2.2

theorem keyAt31_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 31 = Base.key31 := by decide

theorem paperOrbitId31_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 31 = 29 := by decide

theorem directoryKey31_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 31).fibers := by
  simpa only [keyAt31_eq] using key31_noCompletion

def paper62Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit62.S0
  | true => SixQubit.Orbit62.S1

theorem input193_fibers_eq_paper62 :
    fibersOfPair Base.input193 = paper62Fibers := by
  funext c
  cases c <;> decide

theorem paper62_equivalent_key61 :
    MainTheory.DistanceSignature.LabeledEquivalent
      8 4 paper62Fibers 8 4 Base.key61.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input193.q Base.input193.m paper62Fibers
      Base.key61.q Base.key61.m Base.key61.fibers
  rw [← input193_fibers_eq_paper62]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard193.witness_validFor

theorem paper62_noCompletion : NoCompletion paper62Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit62.av 0 2
    paper62Fibers
  · simpa [paper62Fibers] using SixQubit.Orbit62.S0_eq_fiber
  · simpa [paper62Fibers] using SixQubit.Orbit62.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit62_empty

theorem key61_noCompletion : NoCompletion Base.key61.fibers :=
  not_completion_of_fiberEquivalent paper62_noCompletion
    paper62_equivalent_key61.2.2

theorem keyAt61_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 61 = Base.key61 := by decide

theorem paperOrbitId61_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 61 = 62 := by decide

theorem directoryKey61_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 61).fibers := by
  simpa only [keyAt61_eq] using key61_noCompletion

def paper63Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit63.S0
  | true => SixQubit.Orbit63.S1

theorem input194_fibers_eq_paper63 :
    fibersOfPair Base.input194 = paper63Fibers := by
  funext c
  cases c <;> decide

theorem paper63_equivalent_key62 :
    MainTheory.DistanceSignature.LabeledEquivalent
      8 4 paper63Fibers 8 4 Base.key62.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input194.q Base.input194.m paper63Fibers
      Base.key62.q Base.key62.m Base.key62.fibers
  rw [← input194_fibers_eq_paper63]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard194.witness_validFor

theorem paper63_noCompletion : NoCompletion paper63Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit63.av 0 2
    paper63Fibers
  · simpa [paper63Fibers] using SixQubit.Orbit63.S0_eq_fiber
  · simpa [paper63Fibers] using SixQubit.Orbit63.S1_residue
  · exact MainTheory.WImageNoGo51.WImage_orbit63_empty

theorem key62_noCompletion : NoCompletion Base.key62.fibers :=
  not_completion_of_fiberEquivalent paper63_noCompletion
    paper63_equivalent_key62.2.2

theorem keyAt62_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 62 = Base.key62 := by decide

theorem paperOrbitId62_eq : MainTheory.Generated.FiniteOrbitBase.paperOrbitId 62 = 63 := by decide

theorem directoryKey62_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 62).fibers := by
  simpa only [keyAt62_eq] using key62_noCompletion

/-- Exactly these keys carry logical order 4. -/
theorem key_m_eq_four_iff (k : Fin 66) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 4 ↔
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 61 ∨ k = 62 := by
  fin_cases k <;> decide

/-- **No exact distance-three code completes a logical-order-4
orbit.** -/
theorem noCompletion_of_orderFour (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 4) :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  rcases (key_m_eq_four_iff k).1 hm with h | h | h | h | h | h | h | h | h | h
  · subst k; exact directoryKey24_noCompletion
  · subst k; exact directoryKey25_noCompletion
  · subst k; exact directoryKey26_noCompletion
  · subst k; exact directoryKey27_noCompletion
  · subst k; exact directoryKey28_noCompletion
  · subst k; exact directoryKey29_noCompletion
  · subst k; exact directoryKey30_noCompletion
  · subst k; exact directoryKey31_noCompletion
  · subst k; exact directoryKey61_noCompletion
  · subst k; exact directoryKey62_noCompletion

end MainTheory.OrderFourNoCompletion
