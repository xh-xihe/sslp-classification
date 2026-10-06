import MainTheory.Generated.FiniteOrbitWitnessShard081
import MainTheory.Generated.FiniteOrbitWitnessShard084
import MainTheory.Generated.FiniteOrbitWitnessShard085
import MainTheory.Generated.FiniteOrbitWitnessShard086
import MainTheory.Generated.FiniteOrbitWitnessShard087
import MainTheory.Generated.FiniteOrbitWitnessShard089
import MainTheory.Generated.FiniteOrbitWitnessShard091
import MainTheory.Generated.FiniteOrbitWitnessShard095
import SixQubit.Orbit33
import SixQubit.Orbit34
import SixQubit.Orbit35
import SixQubit.Orbit36Transport
import SixQubit.Orbit37
import SixQubit.Orbit38
import SixQubit.Orbit39
import SixQubit.Orbit40

/-!
# Kernel identification of the eight order-five directory keys

The generated 66-key directory is ordered lexicographically by
`(q,m,mask0,mask1)`.  It is **not** ordered by the paper's orbit numbers.
This module closes that provenance gap for the only eight keys with
`q = m = 5`.

For every paper orbit 33--40 we check two independent pieces of data:

* the concrete generated input pair is pointwise equal to the paper support
  pair (both colours are checked as finite sets of six-bit strings); and
* the stored generated cube-action witness maps that exact input pair to the
  stated generated key.

Thus the lookup facts below do not merely compare integer ids.  They bind the
paper supports, actual `FiberPair` payloads, and actual cube actions in Lean.
-/

namespace MainTheory.OrderFivePaperIdentification

open MainTheory.FiniteOrbitPipeline

namespace Base
abbrev input081 := MainTheory.Generated.FiniteOrbitBase.input081
abbrev input084 := MainTheory.Generated.FiniteOrbitBase.input084
abbrev input085 := MainTheory.Generated.FiniteOrbitBase.input085
abbrev input086 := MainTheory.Generated.FiniteOrbitBase.input086
abbrev input087 := MainTheory.Generated.FiniteOrbitBase.input087
abbrev input089 := MainTheory.Generated.FiniteOrbitBase.input089
abbrev input091 := MainTheory.Generated.FiniteOrbitBase.input091
abbrev input095 := MainTheory.Generated.FiniteOrbitBase.input095
abbrev key32 := MainTheory.Generated.FiniteOrbitBase.key32
abbrev key33 := MainTheory.Generated.FiniteOrbitBase.key33
abbrev key34 := MainTheory.Generated.FiniteOrbitBase.key34
abbrev key35 := MainTheory.Generated.FiniteOrbitBase.key35
abbrev key36 := MainTheory.Generated.FiniteOrbitBase.key36
abbrev key37 := MainTheory.Generated.FiniteOrbitBase.key37
abbrev key38 := MainTheory.Generated.FiniteOrbitBase.key38
abbrev key39 := MainTheory.Generated.FiniteOrbitBase.key39
end Base

/-! ## Exact paper support pairs -/

def paper33Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit33.S0
  | true => SixQubit.Orbit33.S1

def paper34Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit34.S0
  | true => SixQubit.Orbit34.S1

def paper35Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit35.S0
  | true => SixQubit.Orbit35.S1

/-- Orbit 36 is identified with the representative printed in the paper,
not merely the symmetric gauge used internally by its rigidity proof. -/
def paper36Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit36Transport.originalS0
  | true => SixQubit.Orbit36Transport.originalS1

def paper37Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit37.S0
  | true => SixQubit.Orbit37.S1

def paper38Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit38.S0
  | true => SixQubit.Orbit38.S1

def paper39Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit39.S0
  | true => SixQubit.Orbit39.S1

def paper40Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Orbit40.S0
  | true => SixQubit.Orbit40.S1

/-! ## Paper payloads equal the concrete generated inputs -/

theorem input081_fibers_eq_paper33 :
    fibersOfPair Base.input081 = paper33Fibers := by
  funext c
  cases c <;> decide

theorem input084_fibers_eq_paper34 :
    fibersOfPair Base.input084 = paper34Fibers := by
  funext c
  cases c <;> decide

theorem input085_fibers_eq_paper35 :
    fibersOfPair Base.input085 = paper35Fibers := by
  funext c
  cases c <;> decide

theorem input086_fibers_eq_paper36 :
    fibersOfPair Base.input086 = paper36Fibers := by
  funext c
  cases c <;> decide

theorem input087_fibers_eq_paper37 :
    fibersOfPair Base.input087 = paper37Fibers := by
  funext c
  cases c <;> decide

theorem input089_fibers_eq_paper38 :
    fibersOfPair Base.input089 = paper38Fibers := by
  funext c
  cases c <;> decide

theorem input091_fibers_eq_paper39 :
    fibersOfPair Base.input091 = paper39Fibers := by
  funext c
  cases c <;> decide

theorem input095_fibers_eq_paper40 :
    fibersOfPair Base.input095 = paper40Fibers := by
  funext c
  cases c <;> decide

/-! ## Actual cube-action identifications -/

theorem paper33_equivalent_key37 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper33Fibers 5 5 Base.key37.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input081.q Base.input081.m paper33Fibers
      Base.key37.q Base.key37.m Base.key37.fibers
  rw [← input081_fibers_eq_paper33]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard081.witness_validFor

theorem paper34_equivalent_key32 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper34Fibers 5 5 Base.key32.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input084.q Base.input084.m paper34Fibers
      Base.key32.q Base.key32.m Base.key32.fibers
  rw [← input084_fibers_eq_paper34]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard084.witness_validFor

theorem paper35_equivalent_key38 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper35Fibers 5 5 Base.key38.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input085.q Base.input085.m paper35Fibers
      Base.key38.q Base.key38.m Base.key38.fibers
  rw [← input085_fibers_eq_paper35]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard085.witness_validFor

theorem paper36_equivalent_key34 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper36Fibers 5 5 Base.key34.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input086.q Base.input086.m paper36Fibers
      Base.key34.q Base.key34.m Base.key34.fibers
  rw [← input086_fibers_eq_paper36]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard086.witness_validFor

theorem paper37_equivalent_key39 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper37Fibers 5 5 Base.key39.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input087.q Base.input087.m paper37Fibers
      Base.key39.q Base.key39.m Base.key39.fibers
  rw [← input087_fibers_eq_paper37]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard087.witness_validFor

theorem paper38_equivalent_key36 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper38Fibers 5 5 Base.key36.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input089.q Base.input089.m paper38Fibers
      Base.key36.q Base.key36.m Base.key36.fibers
  rw [← input089_fibers_eq_paper38]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard089.witness_validFor

theorem paper39_equivalent_key33 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper39Fibers 5 5 Base.key33.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input091.q Base.input091.m paper39Fibers
      Base.key33.q Base.key33.m Base.key33.fibers
  rw [← input091_fibers_eq_paper39]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard091.witness_validFor

theorem paper40_equivalent_key35 :
    MainTheory.DistanceSignature.LabeledEquivalent
      5 5 paper40Fibers 5 5 Base.key35.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input095.q Base.input095.m paper40Fibers
      Base.key35.q Base.key35.m Base.key35.fibers
  rw [← input095_fibers_eq_paper40]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard095.witness_validFor

/-! ## Binding to the public directory indices and paper ids -/

theorem orderFive_key_payloads :
    MainTheory.Generated.FiniteOrbitBase.keyAt 32 = Base.key32 ∧
    MainTheory.Generated.FiniteOrbitBase.keyAt 33 = Base.key33 ∧
    MainTheory.Generated.FiniteOrbitBase.keyAt 34 = Base.key34 ∧
    MainTheory.Generated.FiniteOrbitBase.keyAt 35 = Base.key35 ∧
    MainTheory.Generated.FiniteOrbitBase.keyAt 36 = Base.key36 ∧
    MainTheory.Generated.FiniteOrbitBase.keyAt 37 = Base.key37 ∧
    MainTheory.Generated.FiniteOrbitBase.keyAt 38 = Base.key38 ∧
    MainTheory.Generated.FiniteOrbitBase.keyAt 39 = Base.key39 := by
  decide

theorem orderFive_paper_ids :
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 32 = 34 ∧
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 33 = 39 ∧
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 34 = 36 ∧
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 35 = 40 ∧
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 36 = 38 ∧
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 37 = 33 ∧
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 38 = 35 ∧
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 39 = 37 := by
  decide

theorem paper33_equivalent_directoryKey37 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper33Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 37).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.2.1] using paper33_equivalent_key37

theorem paper34_equivalent_directoryKey32 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper34Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 32).fibers := by
  simpa only [orderFive_key_payloads.1] using paper34_equivalent_key32

theorem paper35_equivalent_directoryKey38 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper35Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 38).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.2.2.1] using paper35_equivalent_key38

theorem paper36_equivalent_directoryKey34 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper36Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 34).fibers := by
  simpa only [orderFive_key_payloads.2.2.1] using paper36_equivalent_key34

theorem paper37_equivalent_directoryKey39 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper37Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 39).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.2.2.2] using paper37_equivalent_key39

theorem paper38_equivalent_directoryKey36 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper38Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 36).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.1] using paper38_equivalent_key36

theorem paper39_equivalent_directoryKey33 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper39Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 33).fibers := by
  simpa only [orderFive_key_payloads.2.1] using paper39_equivalent_key33

theorem paper40_equivalent_directoryKey35 :
    MainTheory.DistanceSignature.LabeledEquivalent 5 5 paper40Fibers 5 5
      (MainTheory.Generated.FiniteOrbitBase.keyAt 35).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.1] using paper40_equivalent_key35

end MainTheory.OrderFivePaperIdentification
