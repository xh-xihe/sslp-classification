import MainTheory.OrderRange
import MainTheory.WImageSettled62
import MainTheory.Generated.FiniteOrbitWitnessShard004
import MainTheory.Generated.FiniteOrbitWitnessShard006
import MainTheory.Generated.FiniteOrbitWitnessShard012
import MainTheory.Generated.FiniteOrbitWitnessShard013
import MainTheory.Generated.FiniteOrbitWitnessShard019
import MainTheory.Generated.FiniteOrbitWitnessShard023
import MainTheory.Generated.FiniteOrbitWitnessShard024
import MainTheory.Generated.FiniteOrbitWitnessShard025
import MainTheory.Generated.FiniteOrbitWitnessShard028
import MainTheory.Generated.FiniteOrbitWitnessShard029
import MainTheory.Generated.FiniteOrbitWitnessShard035
import MainTheory.Generated.FiniteOrbitWitnessShard036
import MainTheory.Generated.FiniteOrbitWitnessShard037
import MainTheory.Generated.FiniteOrbitWitnessShard040
import MainTheory.Generated.FiniteOrbitWitnessShard041
import MainTheory.Generated.FiniteOrbitWitnessShard043
import MainTheory.Generated.FiniteOrbitWitnessShard048
import MainTheory.Generated.FiniteOrbitWitnessShard049
import MainTheory.Generated.FiniteOrbitWitnessShard111
import MainTheory.Generated.FiniteOrbitWitnessShard112
import MainTheory.Generated.FiniteOrbitWitnessShard113
import MainTheory.Generated.FiniteOrbitWitnessShard117
import MainTheory.Generated.FiniteOrbitWitnessShard121
import MainTheory.Generated.FiniteOrbitWitnessShard141
import MainTheory.Generated.FiniteOrbitWitnessShard142
import MainTheory.Generated.FiniteOrbitWitnessShard143
import MainTheory.Generated.FiniteOrbitWitnessShard144
import MainTheory.Generated.FiniteOrbitWitnessShard148
import MainTheory.Generated.FiniteOrbitWitnessShard151

/-!
# The completion status of all 66 directory keys

`WImageSettled62` proves the 51 empty weight-enumerator images and
the 11 exact nonempty ones, but about *paper representatives*: an
angle vector `SixQubit.OrbitNN.av` and its two residue fibres.  Its
own docstring records the gap --

> This file does not claim the still-separate generated-directory
> transport from the 66 canonical orbit representatives.

-- and `thm:six-WE-status` is a statement about the 66 orbits, so
that gap was the whole distance between the theorem and what was
proved.  The `Order*NoCompletion` modules close it for logical orders
4 through 9, `OrderRange` for four more keys, and this file for the
remaining twenty-nine, all of logical order two or three.

Every one is the same three steps: identify the generated fibre pair
with the paper orbit's two residue fibres by an exact mask
computation, transport the no-go (or the completion) along the
stored, kernel-checked cube action, and only then consult the
numeric paper-orbit table.

The census at the end is `thm:six-WE-status` at the directory level:
51 keys admit no exact normalized distance-three completion, 11 do,
and the remaining four are exactly the paper's open orbits
`W_1, W_2, W_3, W_4`.
-/

namespace MainTheory.DirectoryOrbitStatus

open MainTheory.CubeAction
open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline
open MainTheory.Generated.FiniteOrbitBase

set_option maxRecDepth 100000

def paper5Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit5.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit5.av x = 1

theorem input004_fibers_eq_paper5 :
    fibersOfPair input004 = paper5Fibers := by
  funext c
  cases c <;> decide

theorem paper5_equivalent_key04 :
    MainTheory.DistanceSignature.LabeledEquivalent
      3 3 paper5Fibers 3 3 key04.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input004.q input004.m paper5Fibers
      key04.q key04.m key04.fibers
  rw [← input004_fibers_eq_paper5]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard004.witness_validFor

theorem keyAt04_eq : keyAt 4 = key04 := by decide

theorem paper5_noCompletion : NoCompletion paper5Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit5.av 0 1 paper5Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit5_empty

theorem directoryKey04_noCompletion :
    NoCompletion (keyAt 4).fibers := by
  rw [keyAt04_eq]
  exact not_completion_of_fiberEquivalent paper5_noCompletion
    paper5_equivalent_key04.2.2

def paper6Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit6.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit6.av x = 1

theorem input006_fibers_eq_paper6 :
    fibersOfPair input006 = paper6Fibers := by
  funext c
  cases c <;> decide

theorem paper6_equivalent_key05 :
    MainTheory.DistanceSignature.LabeledEquivalent
      3 3 paper6Fibers 3 3 key05.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input006.q input006.m paper6Fibers
      key05.q key05.m key05.fibers
  rw [← input006_fibers_eq_paper6]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard006.witness_validFor

theorem keyAt05_eq : keyAt 5 = key05 := by decide

theorem paper6_noCompletion : NoCompletion paper6Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit6.av 0 1 paper6Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit6_empty

theorem directoryKey05_noCompletion :
    NoCompletion (keyAt 5).fibers := by
  rw [keyAt05_eq]
  exact not_completion_of_fiberEquivalent paper6_noCompletion
    paper6_equivalent_key05.2.2

def paper9Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit9Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit9Real.av x = 1

theorem input013_fibers_eq_paper9 :
    fibersOfPair input013 = paper9Fibers := by
  funext c
  cases c <;> decide

theorem paper9_equivalent_key07 :
    MainTheory.DistanceSignature.LabeledEquivalent
      3 3 paper9Fibers 3 3 key07.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input013.q input013.m paper9Fibers
      key07.q key07.m key07.fibers
  rw [← input013_fibers_eq_paper9]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard013.witness_validFor

theorem keyAt07_eq : keyAt 7 = key07 := by decide

theorem paper9_hasCompletion : HasCompletion paper9Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit9Real.av 0 1 paper9Fibers rfl rfl
    (A := MainTheory.Levels.E2A)
  rw [MainTheory.WImages.WImage_orbit9]
  rfl

theorem directoryKey07_hasCompletion :
    HasCompletion (keyAt 7).fibers := by
  rw [keyAt07_eq]
  exact completion_of_fiberEquivalent paper9_hasCompletion
    paper9_equivalent_key07.2.2

def paper8Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit8Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit8Real.av x = 1

theorem input012_fibers_eq_paper8 :
    fibersOfPair input012 = paper8Fibers := by
  funext c
  cases c <;> decide

theorem paper8_equivalent_key08 :
    MainTheory.DistanceSignature.LabeledEquivalent
      3 3 paper8Fibers 3 3 key08.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input012.q input012.m paper8Fibers
      key08.q key08.m key08.fibers
  rw [← input012_fibers_eq_paper8]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard012.witness_validFor

theorem keyAt08_eq : keyAt 8 = key08 := by decide

theorem paper8_hasCompletion : HasCompletion paper8Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit8Real.av 0 1 paper8Fibers rfl rfl
    (A := MainTheory.WImages.FI 1)
  rw [MainTheory.WImages.WImage_orbit8]
  exact ⟨1, by norm_num, rfl⟩

theorem directoryKey08_hasCompletion :
    HasCompletion (keyAt 8).fibers := by
  rw [keyAt08_eq]
  exact completion_of_fiberEquivalent paper8_hasCompletion
    paper8_equivalent_key08.2.2

def paper15Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit15.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit15.av x = 2

theorem input028_fibers_eq_paper15 :
    fibersOfPair input028 = paper15Fibers := by
  funext c
  cases c <;> decide

theorem paper15_equivalent_key10 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper15Fibers 4 2 key10.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input028.q input028.m paper15Fibers
      key10.q key10.m key10.fibers
  rw [← input028_fibers_eq_paper15]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard028.witness_validFor

theorem keyAt10_eq : keyAt 10 = key10 := by decide

theorem paper15_noCompletion : NoCompletion paper15Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit15.av 0 2 paper15Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit15_empty

theorem directoryKey10_noCompletion :
    NoCompletion (keyAt 10).fibers := by
  rw [keyAt10_eq]
  exact not_completion_of_fiberEquivalent paper15_noCompletion
    paper15_equivalent_key10.2.2

def paper23Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit23Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit23Real.av x = 2

theorem input048_fibers_eq_paper23 :
    fibersOfPair input048 = paper23Fibers := by
  funext c
  cases c <;> decide

theorem paper23_equivalent_key11 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper23Fibers 4 2 key11.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input048.q input048.m paper23Fibers
      key11.q key11.m key11.fibers
  rw [← input048_fibers_eq_paper23]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard048.witness_validFor

theorem keyAt11_eq : keyAt 11 = key11 := by decide

theorem paper23_hasCompletion : HasCompletion paper23Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit23Real.av 0 2 paper23Fibers rfl rfl
    (A := MainTheory.WImages.E1A)
  rw [MainTheory.WImages.WImage_orbit23]
  rfl

theorem directoryKey11_hasCompletion :
    HasCompletion (keyAt 11).fibers := by
  rw [keyAt11_eq]
  exact completion_of_fiberEquivalent paper23_hasCompletion
    paper23_equivalent_key11.2.2

def paper10Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit10Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit10Real.av x = 2

theorem input019_fibers_eq_paper10 :
    fibersOfPair input019 = paper10Fibers := by
  funext c
  cases c <;> decide

theorem paper10_equivalent_key12 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper10Fibers 4 2 key12.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input019.q input019.m paper10Fibers
      key12.q key12.m key12.fibers
  rw [← input019_fibers_eq_paper10]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard019.witness_validFor

theorem keyAt12_eq : keyAt 12 = key12 := by decide

theorem paper10_hasCompletion : HasCompletion paper10Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit10Real.av 0 2 paper10Fibers rfl rfl
    (A := MainTheory.Levels.E2A)
  rw [MainTheory.WImages.WImage_orbit10]
  rfl

theorem directoryKey12_hasCompletion :
    HasCompletion (keyAt 12).fibers := by
  rw [keyAt12_eq]
  exact completion_of_fiberEquivalent paper10_hasCompletion
    paper10_equivalent_key12.2.2

def paper16Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit16Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit16Real.av x = 2

theorem input029_fibers_eq_paper16 :
    fibersOfPair input029 = paper16Fibers := by
  funext c
  cases c <;> decide

theorem paper16_equivalent_key13 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper16Fibers 4 2 key13.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input029.q input029.m paper16Fibers
      key13.q key13.m key13.fibers
  rw [← input029_fibers_eq_paper16]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard029.witness_validFor

theorem keyAt13_eq : keyAt 13 = key13 := by decide

theorem paper16_hasCompletion : HasCompletion paper16Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit16Real.av 0 2 paper16Fibers rfl rfl
    (A := MainTheory.Levels.E2A)
  rw [MainTheory.WImages.WImage_orbit16]
  rfl

theorem directoryKey13_hasCompletion :
    HasCompletion (keyAt 13).fibers := by
  rw [keyAt13_eq]
  exact completion_of_fiberEquivalent paper16_hasCompletion
    paper16_equivalent_key13.2.2

def paper14Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit14.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit14.av x = 2

theorem input025_fibers_eq_paper14 :
    fibersOfPair input025 = paper14Fibers := by
  funext c
  cases c <;> decide

theorem paper14_equivalent_key14 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper14Fibers 4 2 key14.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input025.q input025.m paper14Fibers
      key14.q key14.m key14.fibers
  rw [← input025_fibers_eq_paper14]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard025.witness_validFor

theorem keyAt14_eq : keyAt 14 = key14 := by decide

theorem paper14_noCompletion : NoCompletion paper14Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit14.av 0 2 paper14Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit14_empty

theorem directoryKey14_noCompletion :
    NoCompletion (keyAt 14).fibers := by
  rw [keyAt14_eq]
  exact not_completion_of_fiberEquivalent paper14_noCompletion
    paper14_equivalent_key14.2.2

def paper24Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit24.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit24.av x = 2

theorem input049_fibers_eq_paper24 :
    fibersOfPair input049 = paper24Fibers := by
  funext c
  cases c <;> decide

theorem paper24_equivalent_key15 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper24Fibers 4 2 key15.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input049.q input049.m paper24Fibers
      key15.q key15.m key15.fibers
  rw [← input049_fibers_eq_paper24]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard049.witness_validFor

theorem keyAt15_eq : keyAt 15 = key15 := by decide

theorem paper24_noCompletion : NoCompletion paper24Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit24.av 0 2 paper24Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit24_empty

theorem directoryKey15_noCompletion :
    NoCompletion (keyAt 15).fibers := by
  rw [keyAt15_eq]
  exact not_completion_of_fiberEquivalent paper24_noCompletion
    paper24_equivalent_key15.2.2

def paper22Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit22Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit22Real.av x = 2

theorem input043_fibers_eq_paper22 :
    fibersOfPair input043 = paper22Fibers := by
  funext c
  cases c <;> decide

theorem paper22_equivalent_key16 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper22Fibers 4 2 key16.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input043.q input043.m paper22Fibers
      key16.q key16.m key16.fibers
  rw [← input043_fibers_eq_paper22]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard043.witness_validFor

theorem keyAt16_eq : keyAt 16 = key16 := by decide

theorem paper22_hasCompletion : HasCompletion paper22Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit22Real.av 0 2 paper22Fibers rfl rfl
    (A := MainTheory.Levels.E2A)
  rw [MainTheory.WImages.WImage_orbit22]
  rfl

theorem directoryKey16_hasCompletion :
    HasCompletion (keyAt 16).fibers := by
  rw [keyAt16_eq]
  exact completion_of_fiberEquivalent paper22_hasCompletion
    paper22_equivalent_key16.2.2

def paper13Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit13.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit13.av x = 2

theorem input024_fibers_eq_paper13 :
    fibersOfPair input024 = paper13Fibers := by
  funext c
  cases c <;> decide

theorem paper13_equivalent_key17 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper13Fibers 4 2 key17.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input024.q input024.m paper13Fibers
      key17.q key17.m key17.fibers
  rw [← input024_fibers_eq_paper13]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard024.witness_validFor

theorem keyAt17_eq : keyAt 17 = key17 := by decide

theorem paper13_noCompletion : NoCompletion paper13Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit13.av 0 2 paper13Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit13_empty

theorem directoryKey17_noCompletion :
    NoCompletion (keyAt 17).fibers := by
  rw [keyAt17_eq]
  exact not_completion_of_fiberEquivalent paper13_noCompletion
    paper13_equivalent_key17.2.2

def paper12Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit12.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit12.av x = 2

theorem input023_fibers_eq_paper12 :
    fibersOfPair input023 = paper12Fibers := by
  funext c
  cases c <;> decide

theorem paper12_equivalent_key18 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper12Fibers 4 2 key18.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input023.q input023.m paper12Fibers
      key18.q key18.m key18.fibers
  rw [← input023_fibers_eq_paper12]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard023.witness_validFor

theorem keyAt18_eq : keyAt 18 = key18 := by decide

theorem paper12_noCompletion : NoCompletion paper12Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit12.av 0 2 paper12Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit12_empty

theorem directoryKey18_noCompletion :
    NoCompletion (keyAt 18).fibers := by
  rw [keyAt18_eq]
  exact not_completion_of_fiberEquivalent paper12_noCompletion
    paper12_equivalent_key18.2.2

def paper20Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit20.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit20.av x = 2

theorem input040_fibers_eq_paper20 :
    fibersOfPair input040 = paper20Fibers := by
  funext c
  cases c <;> decide

theorem paper20_equivalent_key19 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper20Fibers 4 2 key19.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input040.q input040.m paper20Fibers
      key19.q key19.m key19.fibers
  rw [← input040_fibers_eq_paper20]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard040.witness_validFor

theorem keyAt19_eq : keyAt 19 = key19 := by decide

theorem paper20_noCompletion : NoCompletion paper20Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit20.av 0 2 paper20Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit20_empty

theorem directoryKey19_noCompletion :
    NoCompletion (keyAt 19).fibers := by
  rw [keyAt19_eq]
  exact not_completion_of_fiberEquivalent paper20_noCompletion
    paper20_equivalent_key19.2.2

def paper18Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit18.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit18.av x = 2

theorem input036_fibers_eq_paper18 :
    fibersOfPair input036 = paper18Fibers := by
  funext c
  cases c <;> decide

theorem paper18_equivalent_key20 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper18Fibers 4 2 key20.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input036.q input036.m paper18Fibers
      key20.q key20.m key20.fibers
  rw [← input036_fibers_eq_paper18]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard036.witness_validFor

theorem keyAt20_eq : keyAt 20 = key20 := by decide

theorem paper18_noCompletion : NoCompletion paper18Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit18.av 0 2 paper18Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit18_empty

theorem directoryKey20_noCompletion :
    NoCompletion (keyAt 20).fibers := by
  rw [keyAt20_eq]
  exact not_completion_of_fiberEquivalent paper18_noCompletion
    paper18_equivalent_key20.2.2

def paper17Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit17.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit17.av x = 2

theorem input035_fibers_eq_paper17 :
    fibersOfPair input035 = paper17Fibers := by
  funext c
  cases c <;> decide

theorem paper17_equivalent_key21 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper17Fibers 4 2 key21.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input035.q input035.m paper17Fibers
      key21.q key21.m key21.fibers
  rw [← input035_fibers_eq_paper17]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard035.witness_validFor

theorem keyAt21_eq : keyAt 21 = key21 := by decide

theorem paper17_noCompletion : NoCompletion paper17Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit17.av 0 2 paper17Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit17_empty

theorem directoryKey21_noCompletion :
    NoCompletion (keyAt 21).fibers := by
  rw [keyAt21_eq]
  exact not_completion_of_fiberEquivalent paper17_noCompletion
    paper17_equivalent_key21.2.2

def paper21Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit21Cert.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit21Cert.av x = 2

theorem input041_fibers_eq_paper21 :
    fibersOfPair input041 = paper21Fibers := by
  funext c
  cases c <;> decide

theorem paper21_equivalent_key22 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper21Fibers 4 2 key22.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input041.q input041.m paper21Fibers
      key22.q key22.m key22.fibers
  rw [← input041_fibers_eq_paper21]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard041.witness_validFor

theorem keyAt22_eq : keyAt 22 = key22 := by decide

theorem paper21_hasCompletion : HasCompletion paper21Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit21Cert.av 0 2 paper21Fibers rfl rfl
    (A := MainTheory.Levels.E2A)
  rw [MainTheory.Levels.WImage_orbit21]
  rfl

theorem directoryKey22_hasCompletion :
    HasCompletion (keyAt 22).fibers := by
  rw [keyAt22_eq]
  exact completion_of_fiberEquivalent paper21_hasCompletion
    paper21_equivalent_key22.2.2

def paper19Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit19.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit19.av x = 2

theorem input037_fibers_eq_paper19 :
    fibersOfPair input037 = paper19Fibers := by
  funext c
  cases c <;> decide

theorem paper19_equivalent_key23 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper19Fibers 4 2 key23.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input037.q input037.m paper19Fibers
      key23.q key23.m key23.fibers
  rw [← input037_fibers_eq_paper19]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard037.witness_validFor

theorem keyAt23_eq : keyAt 23 = key23 := by decide

theorem paper19_noCompletion : NoCompletion paper19Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit19.av 0 2 paper19Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit19_empty

theorem directoryKey23_noCompletion :
    NoCompletion (keyAt 23).fibers := by
  rw [keyAt23_eq]
  exact not_completion_of_fiberEquivalent paper19_noCompletion
    paper19_equivalent_key23.2.2

def paper43Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit43.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit43.av x = 3

theorem input113_fibers_eq_paper43 :
    fibersOfPair input113 = paper43Fibers := by
  funext c
  cases c <;> decide

theorem paper43_equivalent_key40 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 2 paper43Fibers 6 2 key40.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input113.q input113.m paper43Fibers
      key40.q key40.m key40.fibers
  rw [← input113_fibers_eq_paper43]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard113.witness_validFor

theorem keyAt40_eq : keyAt 40 = key40 := by decide

theorem paper43_noCompletion : NoCompletion paper43Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit43.av 0 3 paper43Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit43_empty

theorem directoryKey40_noCompletion :
    NoCompletion (keyAt 40).fibers := by
  rw [keyAt40_eq]
  exact not_completion_of_fiberEquivalent paper43_noCompletion
    paper43_equivalent_key40.2.2

def paper41Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit41.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit41.av x = 3

theorem input111_fibers_eq_paper41 :
    fibersOfPair input111 = paper41Fibers := by
  funext c
  cases c <;> decide

theorem paper41_equivalent_key41 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 2 paper41Fibers 6 2 key41.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input111.q input111.m paper41Fibers
      key41.q key41.m key41.fibers
  rw [← input111_fibers_eq_paper41]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard111.witness_validFor

theorem keyAt41_eq : keyAt 41 = key41 := by decide

theorem paper41_noCompletion : NoCompletion paper41Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit41.av 0 3 paper41Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit41_empty

theorem directoryKey41_noCompletion :
    NoCompletion (keyAt 41).fibers := by
  rw [keyAt41_eq]
  exact not_completion_of_fiberEquivalent paper41_noCompletion
    paper41_equivalent_key41.2.2

def paper42Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit42.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit42.av x = 3

theorem input112_fibers_eq_paper42 :
    fibersOfPair input112 = paper42Fibers := by
  funext c
  cases c <;> decide

theorem paper42_equivalent_key42 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 2 paper42Fibers 6 2 key42.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input112.q input112.m paper42Fibers
      key42.q key42.m key42.fibers
  rw [← input112_fibers_eq_paper42]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard112.witness_validFor

theorem keyAt42_eq : keyAt 42 = key42 := by decide

theorem paper42_noCompletion : NoCompletion paper42Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit42.av 0 3 paper42Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit42_empty

theorem directoryKey42_noCompletion :
    NoCompletion (keyAt 42).fibers := by
  rw [keyAt42_eq]
  exact not_completion_of_fiberEquivalent paper42_noCompletion
    paper42_equivalent_key42.2.2

def paper46Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit46.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit46.av x = 3

theorem input121_fibers_eq_paper46 :
    fibersOfPair input121 = paper46Fibers := by
  funext c
  cases c <;> decide

theorem paper46_equivalent_key43 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 2 paper46Fibers 6 2 key43.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input121.q input121.m paper46Fibers
      key43.q key43.m key43.fibers
  rw [← input121_fibers_eq_paper46]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard121.witness_validFor

theorem keyAt43_eq : keyAt 43 = key43 := by decide

theorem paper46_noCompletion : NoCompletion paper46Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit46.av 0 3 paper46Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit46_empty

theorem directoryKey43_noCompletion :
    NoCompletion (keyAt 43).fibers := by
  rw [keyAt43_eq]
  exact not_completion_of_fiberEquivalent paper46_noCompletion
    paper46_equivalent_key43.2.2

def paper44Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit44.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit44.av x = 3

theorem input117_fibers_eq_paper44 :
    fibersOfPair input117 = paper44Fibers := by
  funext c
  cases c <;> decide

theorem paper44_equivalent_key44 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 2 paper44Fibers 6 2 key44.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input117.q input117.m paper44Fibers
      key44.q key44.m key44.fibers
  rw [← input117_fibers_eq_paper44]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard117.witness_validFor

theorem keyAt44_eq : keyAt 44 = key44 := by decide

theorem paper44_noCompletion : NoCompletion paper44Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit44.av 0 3 paper44Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit44_empty

theorem directoryKey44_noCompletion :
    NoCompletion (keyAt 44).fibers := by
  rw [keyAt44_eq]
  exact not_completion_of_fiberEquivalent paper44_noCompletion
    paper44_equivalent_key44.2.2

def paper48Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit48.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit48.av x = 2

theorem input142_fibers_eq_paper48 :
    fibersOfPair input142 = paper48Fibers := by
  funext c
  cases c <;> decide

theorem paper48_equivalent_key46 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 3 paper48Fibers 6 3 key46.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input142.q input142.m paper48Fibers
      key46.q key46.m key46.fibers
  rw [← input142_fibers_eq_paper48]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard142.witness_validFor

theorem keyAt46_eq : keyAt 46 = key46 := by decide

theorem paper48_noCompletion : NoCompletion paper48Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit48.av 0 2 paper48Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit48_empty

theorem directoryKey46_noCompletion :
    NoCompletion (keyAt 46).fibers := by
  rw [keyAt46_eq]
  exact not_completion_of_fiberEquivalent paper48_noCompletion
    paper48_equivalent_key46.2.2

def paper47Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit47.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit47.av x = 2

theorem input141_fibers_eq_paper47 :
    fibersOfPair input141 = paper47Fibers := by
  funext c
  cases c <;> decide

theorem paper47_equivalent_key47 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 3 paper47Fibers 6 3 key47.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input141.q input141.m paper47Fibers
      key47.q key47.m key47.fibers
  rw [← input141_fibers_eq_paper47]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard141.witness_validFor

theorem keyAt47_eq : keyAt 47 = key47 := by decide

theorem paper47_noCompletion : NoCompletion paper47Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit47.av 0 2 paper47Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit47_empty

theorem directoryKey47_noCompletion :
    NoCompletion (keyAt 47).fibers := by
  rw [keyAt47_eq]
  exact not_completion_of_fiberEquivalent paper47_noCompletion
    paper47_equivalent_key47.2.2

def paper50Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit50.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit50.av x = 2

theorem input144_fibers_eq_paper50 :
    fibersOfPair input144 = paper50Fibers := by
  funext c
  cases c <;> decide

theorem paper50_equivalent_key48 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 3 paper50Fibers 6 3 key48.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input144.q input144.m paper50Fibers
      key48.q key48.m key48.fibers
  rw [← input144_fibers_eq_paper50]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard144.witness_validFor

theorem keyAt48_eq : keyAt 48 = key48 := by decide

theorem paper50_noCompletion : NoCompletion paper50Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit50.av 0 2 paper50Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit50_empty

theorem directoryKey48_noCompletion :
    NoCompletion (keyAt 48).fibers := by
  rw [keyAt48_eq]
  exact not_completion_of_fiberEquivalent paper50_noCompletion
    paper50_equivalent_key48.2.2

def paper49Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit49.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit49.av x = 2

theorem input143_fibers_eq_paper49 :
    fibersOfPair input143 = paper49Fibers := by
  funext c
  cases c <;> decide

theorem paper49_equivalent_key49 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 3 paper49Fibers 6 3 key49.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input143.q input143.m paper49Fibers
      key49.q key49.m key49.fibers
  rw [← input143_fibers_eq_paper49]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard143.witness_validFor

theorem keyAt49_eq : keyAt 49 = key49 := by decide

theorem paper49_noCompletion : NoCompletion paper49Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit49.av 0 2 paper49Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit49_empty

theorem directoryKey49_noCompletion :
    NoCompletion (keyAt 49).fibers := by
  rw [keyAt49_eq]
  exact not_completion_of_fiberEquivalent paper49_noCompletion
    paper49_equivalent_key49.2.2

def paper52Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit52.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit52.av x = 2

theorem input151_fibers_eq_paper52 :
    fibersOfPair input151 = paper52Fibers := by
  funext c
  cases c <;> decide

theorem paper52_equivalent_key50 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 3 paper52Fibers 6 3 key50.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input151.q input151.m paper52Fibers
      key50.q key50.m key50.fibers
  rw [← input151_fibers_eq_paper52]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard151.witness_validFor

theorem keyAt50_eq : keyAt 50 = key50 := by decide

theorem paper52_noCompletion : NoCompletion paper52Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit52.av 0 2 paper52Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit52_empty

theorem directoryKey50_noCompletion :
    NoCompletion (keyAt 50).fibers := by
  rw [keyAt50_eq]
  exact not_completion_of_fiberEquivalent paper52_noCompletion
    paper52_equivalent_key50.2.2

def paper51Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit51.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit51.av x = 2

theorem input148_fibers_eq_paper51 :
    fibersOfPair input148 = paper51Fibers := by
  funext c
  cases c <;> decide

theorem paper51_equivalent_key51 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 3 paper51Fibers 6 3 key51.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    input148.q input148.m paper51Fibers
      key51.q key51.m key51.fibers
  rw [← input148_fibers_eq_paper51]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard148.witness_validFor

theorem keyAt51_eq : keyAt 51 = key51 := by decide

theorem paper51_noCompletion : NoCompletion paper51Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit51.av 0 2 paper51Fibers
    rfl rfl
  exact MainTheory.WImageNoGo51.WImage_orbit51_empty

theorem directoryKey51_noCompletion :
    NoCompletion (keyAt 51).fibers := by
  rw [keyAt51_eq]
  exact not_completion_of_fiberEquivalent paper51_noCompletion
    paper51_equivalent_key51.2.2

/-! ## The census -/

/-- The 51 keys the no-go analysis rules out. -/
def noGoKeys : List (Fin 66) := [4, 5, 10, 14, 15, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65]

/-- The 11 keys an exact code realizes. -/
def realizedKeys : List (Fin 66) := [6, 7, 8, 9, 11, 12, 13, 16, 22, 34, 45]

/-- The four keys `main.tex` leaves open: `W_1` through `W_4`. -/
def openKeys : List (Fin 66) := [0, 1, 2, 3]

theorem noGoKeys_length : noGoKeys.length = 51 := by decide
theorem realizedKeys_length : realizedKeys.length = 11 := by decide
theorem openKeys_length : openKeys.length = 4 := by decide

/-- The three lists partition the sixty-six keys. -/
theorem keys_partition :
    (noGoKeys ++ realizedKeys ++ openKeys).toFinset = (Finset.univ : Finset (Fin 66)) := by decide

theorem keys_nodup : (noGoKeys ++ realizedKeys ++ openKeys).Nodup := by decide

/-- The open keys are exactly the paper's orbits 1, 2, 3 and 4. -/
theorem openKeys_paperIds :
    openKeys.map paperOrbitId = [1, 2, 3, 4] := by decide

/-! The three lists are read off the generated paper-orbit table,
so they are cross-checked against the paper-facing lists in
`WImageNoGo51` and `WImageSettled62` rather than trusted.  Without
this a transcription slip in that table would silently move a key
from one census column to another. -/

theorem noGoKeys_paperIds :
    (noGoKeys.map paperOrbitId).toFinset =
      MainTheory.WImageNoGo51.noGoOrbitIds.toFinset := by decide

theorem realizedKeys_paperIds :
    (realizedKeys.map paperOrbitId).toFinset =
      MainTheory.WImageSettled62.realizedOrbitIds.toFinset := by decide

theorem openKeys_paperIds_eq :
    (openKeys.map paperOrbitId).toFinset =
      MainTheory.WImageSettled62.openOrbitIds.toFinset := by decide

/-- **No key on the no-go list admits an exact normalized
distance-three completion.** -/
theorem noCompletion_of_mem_noGoKeys (k : Fin 66) (h : k ∈ noGoKeys) :
    NoCompletion (keyAt k).fibers := by
  fin_cases k
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact directoryKey04_noCompletion
  · exact directoryKey05_noCompletion
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact directoryKey10_noCompletion
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact directoryKey14_noCompletion
  · exact directoryKey15_noCompletion
  · exact absurd h (by decide)
  · exact directoryKey17_noCompletion
  · exact directoryKey18_noCompletion
  · exact directoryKey19_noCompletion
  · exact directoryKey20_noCompletion
  · exact directoryKey21_noCompletion
  · exact absurd h (by decide)
  · exact directoryKey23_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey24_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey25_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey26_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey27_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey28_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey29_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey30_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey31_noCompletion
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey32_noCompletion
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey33_noCompletion
  · exact absurd h (by decide)
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey35_noCompletion
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey36_noCompletion
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey37_noCompletion
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey38_noCompletion
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey39_noCompletion
  · exact directoryKey40_noCompletion
  · exact directoryKey41_noCompletion
  · exact directoryKey42_noCompletion
  · exact directoryKey43_noCompletion
  · exact directoryKey44_noCompletion
  · exact absurd h (by decide)
  · exact directoryKey46_noCompletion
  · exact directoryKey47_noCompletion
  · exact directoryKey48_noCompletion
  · exact directoryKey49_noCompletion
  · exact directoryKey50_noCompletion
  · exact directoryKey51_noCompletion
  · exact MainTheory.OrderSixNoCompletion.directoryKey52_noCompletion
  · exact MainTheory.OrderSixNoCompletion.directoryKey53_noCompletion
  · exact MainTheory.OrderSixNoCompletion.directoryKey54_noCompletion
  · exact MainTheory.OrderSixNoCompletion.directoryKey55_noCompletion
  · exact MainTheory.OrderSevenNoCompletion.directoryKey56_noCompletion
  · exact MainTheory.OrderSevenNoCompletion.directoryKey57_noCompletion
  · exact MainTheory.OrderSevenNoCompletion.directoryKey58_noCompletion
  · exact MainTheory.OrderSevenNoCompletion.directoryKey59_noCompletion
  · exact MainTheory.OrderSevenNoCompletion.directoryKey60_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey61_noCompletion
  · exact MainTheory.OrderFourNoCompletion.directoryKey62_noCompletion
  · exact MainTheory.OrderEightNoCompletion.directoryKey63_noCompletion
  · exact MainTheory.OrderEightNoCompletion.directoryKey64_noCompletion
  · exact MainTheory.OrderNineNoCompletion.directoryKey65_noCompletion

/-- **Every key on the realized list is realized by an actual exact
code.** -/
theorem hasCompletion_of_mem_realizedKeys (k : Fin 66) (h : k ∈ realizedKeys) :
    HasCompletion (keyAt k).fibers := by
  fin_cases k
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact MainTheory.OrderRange.key06_hasCompletion
  · exact directoryKey07_hasCompletion
  · exact directoryKey08_hasCompletion
  · exact MainTheory.OrderRange.key09_hasCompletion
  · exact absurd h (by decide)
  · exact directoryKey11_hasCompletion
  · exact directoryKey12_hasCompletion
  · exact directoryKey13_hasCompletion
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact directoryKey16_hasCompletion
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact directoryKey22_hasCompletion
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact MainTheory.OrderFiveUniqueCompletion.directoryKey34_hasCompletion
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact MainTheory.OrderRange.key45_hasCompletion
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **`thm:six-WE-status` at the directory level.**  Every key is
settled one way or the other except the four the paper boxes as
open. -/
theorem settled_or_open (k : Fin 66) :
    NoCompletion (keyAt k).fibers ∨
      HasCompletion (keyAt k).fibers ∨ k ∈ openKeys := by
  by_cases hn : k ∈ noGoKeys
  · exact Or.inl (noCompletion_of_mem_noGoKeys k hn)
  by_cases hr : k ∈ realizedKeys
  · exact Or.inr (Or.inl (hasCompletion_of_mem_realizedKeys k hr))
  refine Or.inr (Or.inr ?_)
  revert hn hr
  revert k
  decide

end MainTheory.DirectoryOrbitStatus
