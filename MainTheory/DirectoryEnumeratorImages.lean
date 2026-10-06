import MainTheory.EnumeratorOrbitTransport
import MainTheory.OrbitNumberingBridge
import MainTheory.DirectoryOrbitStatus
import MainTheory.OrderFivePaperIdentification
import MainTheory.WImageOrbit36
import MainTheory.WImageOpenL
import MainTheory.Generated.FiniteOrbitWitnessShard000
import MainTheory.Generated.FiniteOrbitWitnessShard001
import MainTheory.Generated.FiniteOrbitWitnessShard002
import MainTheory.Generated.FiniteOrbitWitnessShard003

/-! # The eleven literal image descriptions on the generated orbit directory

Every equality below transports actual normalized states and their complete
KL predicate. The fifty-one empty images likewise follow from the actual
no-completion theorems, not from stored status labels.
-/

namespace MainTheory.DirectoryEnumeratorImages

open MainTheory MainTheory.EnumeratorOrbitTransport
open MainTheory.Generated.FiniteOrbitBase

noncomputable section

set_option maxRecDepth 100000

def angleFibers (a : Fin 6 → ZMod 2) : MainTheory.CubeAction.FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight a x = 0
  | true => Finset.univ.filter fun x => SS.weight a x = 1

theorem orbit1_fibers :
    MainTheory.CubeAction.FiberEquivalent (angleFibers SixQubit.OpenLOrbit1.angle)
      (keyAt 0).fibers := by
  have h : MainTheory.FiniteOrbitPipeline.fibersOfPair input000 =
      angleFibers SixQubit.OpenLOrbit1.angle := by
    funext c
    cases c <;> decide
  have he := MainTheory.FiniteOrbitPipeline.OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard000.witness_validFor
  rw [h] at he
  exact he.2.2

theorem orbit2_fibers :
    MainTheory.CubeAction.FiberEquivalent (angleFibers SixQubit.OpenLOrbit2.angle)
      (keyAt 1).fibers := by
  have h : MainTheory.FiniteOrbitPipeline.fibersOfPair input001 =
      angleFibers SixQubit.OpenLOrbit2.angle := by
    funext c
    cases c <;> decide
  have he := MainTheory.FiniteOrbitPipeline.OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard001.witness_validFor
  rw [h] at he
  exact he.2.2

theorem orbit3_fibers :
    MainTheory.CubeAction.FiberEquivalent (angleFibers SixQubit.OpenLOrbit3.angle)
      (keyAt 2).fibers := by
  have h : MainTheory.FiniteOrbitPipeline.fibersOfPair input002 =
      angleFibers SixQubit.OpenLOrbit3.angle := by
    funext c
    cases c <;> decide
  have he := MainTheory.FiniteOrbitPipeline.OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard002.witness_validFor
  rw [h] at he
  exact he.2.2

theorem orbit4_fibers :
    MainTheory.CubeAction.FiberEquivalent (angleFibers SixQubit.OpenLOrbit4.angle)
      (keyAt 3).fibers := by
  have h : MainTheory.FiniteOrbitPipeline.fibersOfPair input003 =
      angleFibers SixQubit.OpenLOrbit4.angle := by
    funext c
    cases c <;> decide
  have he := MainTheory.FiniteOrbitPipeline.OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard003.witness_validFor
  rw [h] at he
  exact he.2.2

def directoryImage (k : Fin 66) : Set (Fin 7 → ℝ) :=
  completionImage (keyAt k).fibers

theorem directoryImage_eq_orbitImage (k : Fin 66) :
    directoryImage k = orbitImage (keyAt k).fibers := by
  rw [orbitImage_eq_completionImage]
  rfl

theorem empty_of_noGo (k : Fin 66) (hk : k ∈ DirectoryOrbitStatus.noGoKeys) :
    directoryImage k = ∅ :=
  completionImage_eq_empty_of_noCompletion
    (DirectoryOrbitStatus.noCompletion_of_mem_noGoKeys k hk)

theorem orbit1_attainment : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆ directoryImage 0 := by
  unfold directoryImage
  rw [completionImage_eq_of_fiberEquivalent orbit1_fibers,
    ← WImage_eq_completionImage SixQubit.OpenLOrbit1.angle 0 1
      (angleFibers SixQubit.OpenLOrbit1.angle) rfl rfl]
  exact WImageOpenL.FI_subset_orbit1

theorem orbit2_attainment : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆ directoryImage 1 := by
  unfold directoryImage
  rw [completionImage_eq_of_fiberEquivalent orbit2_fibers,
    ← WImage_eq_completionImage SixQubit.OpenLOrbit2.angle 0 1
      (angleFibers SixQubit.OpenLOrbit2.angle) rfl rfl]
  exact WImageOpenL.FI_subset_orbit2

theorem orbit3_attainment : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆ directoryImage 2 := by
  unfold directoryImage
  rw [completionImage_eq_of_fiberEquivalent orbit3_fibers,
    ← WImage_eq_completionImage SixQubit.OpenLOrbit3.angle 0 1
      (angleFibers SixQubit.OpenLOrbit3.angle) rfl rfl]
  exact WImageOpenL.FI_subset_orbit3

theorem orbit4_attainment : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆ directoryImage 3 := by
  unfold directoryImage
  rw [completionImage_eq_of_fiberEquivalent orbit4_fibers,
    ← WImage_eq_completionImage SixQubit.OpenLOrbit4.angle 0 1
      (angleFibers SixQubit.OpenLOrbit4.angle) rfl rfl]
  exact WImageOpenL.FI_subset_orbit4

theorem orbit7_image : directoryImage 6 = WImages.FI '' Set.Icc 0 1 := by
  unfold directoryImage
  rw [OrderRange.keyAt06_eq]
  rw [completionImage_eq_of_fiberEquivalent OrderRange.paper7_equivalent_key06.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit7Real.av 0 1 OrderRange.paper7Fibers rfl rfl]
  exact WImages.WImage_orbit7

theorem orbit8_image : directoryImage 8 = WImages.FI '' Set.Icc (1/2) 1 := by
  unfold directoryImage
  rw [DirectoryOrbitStatus.keyAt08_eq]
  rw [completionImage_eq_of_fiberEquivalent DirectoryOrbitStatus.paper8_equivalent_key08.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit8Real.av 0 1 DirectoryOrbitStatus.paper8Fibers rfl rfl]
  exact WImages.WImage_orbit8

theorem orbit9_image : directoryImage 7 = {Levels.E2A} := by
  unfold directoryImage
  rw [DirectoryOrbitStatus.keyAt07_eq]
  rw [completionImage_eq_of_fiberEquivalent DirectoryOrbitStatus.paper9_equivalent_key07.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit9Real.av 0 1 DirectoryOrbitStatus.paper9Fibers rfl rfl]
  exact WImages.WImage_orbit9

theorem orbit10_image : directoryImage 12 = {Levels.E2A} := by
  unfold directoryImage
  rw [DirectoryOrbitStatus.keyAt12_eq]
  rw [completionImage_eq_of_fiberEquivalent DirectoryOrbitStatus.paper10_equivalent_key12.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit10Real.av 0 2 DirectoryOrbitStatus.paper10Fibers rfl rfl]
  exact WImages.WImage_orbit10

theorem orbit11_image : directoryImage 9 = {WImages.E1A} := by
  unfold directoryImage
  rw [OrderRange.keyAt09_eq]
  rw [completionImage_eq_of_fiberEquivalent OrderRange.paper11_equivalent_key09.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit11Real.av 0 2 OrderRange.paper11Fibers rfl rfl]
  exact WImages.WImage_orbit11

theorem orbit16_image : directoryImage 13 = {Levels.E2A} := by
  unfold directoryImage
  rw [DirectoryOrbitStatus.keyAt13_eq]
  rw [completionImage_eq_of_fiberEquivalent DirectoryOrbitStatus.paper16_equivalent_key13.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit16Real.av 0 2 DirectoryOrbitStatus.paper16Fibers rfl rfl]
  exact WImages.WImage_orbit16

theorem orbit21_image : directoryImage 22 = {Levels.E2A} := by
  unfold directoryImage
  rw [DirectoryOrbitStatus.keyAt22_eq]
  rw [completionImage_eq_of_fiberEquivalent DirectoryOrbitStatus.paper21_equivalent_key22.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit21Cert.av 0 2 DirectoryOrbitStatus.paper21Fibers rfl rfl]
  exact Levels.WImage_orbit21

theorem orbit22_image : directoryImage 16 = {Levels.E2A} := by
  unfold directoryImage
  rw [DirectoryOrbitStatus.keyAt16_eq]
  rw [completionImage_eq_of_fiberEquivalent DirectoryOrbitStatus.paper22_equivalent_key16.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit22Real.av 0 2 DirectoryOrbitStatus.paper22Fibers rfl rfl]
  exact WImages.WImage_orbit22

theorem orbit23_image : directoryImage 11 = {WImages.E1A} := by
  unfold directoryImage
  rw [DirectoryOrbitStatus.keyAt11_eq]
  rw [completionImage_eq_of_fiberEquivalent DirectoryOrbitStatus.paper23_equivalent_key11.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit23Real.av 0 2 DirectoryOrbitStatus.paper23Fibers rfl rfl]
  exact WImages.WImage_orbit23

theorem orbit45_image : directoryImage 45 = WImages.FII '' Set.Icc (2/3) 1 := by
  unfold directoryImage
  rw [OrderRange.keyAt45_eq]
  rw [completionImage_eq_of_fiberEquivalent OrderRange.paper45_equivalent_key45.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit45Support.av 0 3 OrderRange.paper45Fibers rfl rfl]
  exact WImages.WImage_orbit45

theorem orbit36_image : directoryImage 34 = {WImages.R5A} := by
  unfold directoryImage
  rw [completionImage_eq_of_fiberEquivalent
    OrderFivePaperIdentification.paper36_equivalent_directoryKey34.2.2,
    ← WImage_eq_completionImage SixQubit.Orbit36Transport.originalAv 0 1
      OrderFivePaperIdentification.paper36Fibers rfl rfl]
  exact WImages.WImage_orbit36

end
end MainTheory.DirectoryEnumeratorImages
