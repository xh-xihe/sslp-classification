import MainTheory.Orbit14ParityFrames
import MainTheory.Orbit15ParityFrames
import MainTheory.Orbit24ParityFrames
import MainTheory.Generated.OrbitTableNumeric
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace MainTheory.OrderTwoRecordResidues
open scoped BigOperators
def row : Fin 5 → Fin 66 := ![11,12,13,14,23]
def angle : Fin 5 → Fin 6 → ℕ :=
  ![![0,1,1,1,1,2],![0,1,1,1,2,2],![0,1,1,2,2,2],
    ![0,1,2,2,2,2],![1,2,2,2,2,3]]
theorem records_checked : ∀ i : Fin 5,
    MainTheory.Generated.OrbitTableNumericData.paperQ (row i)=4 ∧
    MainTheory.Generated.OrbitTableNumericData.paperM (row i)=2 ∧
    MainTheory.Generated.OrbitTableNumericData.paperAngle (row i)=angle i := by decide +kernel
def bit (x : SS.BitString 6) (j : Fin 6) : ZMod 4 := if x j then 1 else 0
def residue (a : Fin 6 → ℕ) (x : SS.BitString 6) : ZMod 4 := ∑ j,(a j : ZMod 4)*bit x j
theorem orbit14_residue : ∀ x : SS.BitString 6,
    residue (angle 2) x=bit x 1+bit x 2+2*(bit x 3+bit x 4+bit x 5) := by decide +kernel
theorem orbit15_residue : ∀ x : SS.BitString 6,
    residue (angle 3) x=bit x 1+2*(bit x 2+bit x 3+bit x 4+bit x 5) := by decide +kernel
theorem orbit24_residue : ∀ x : SS.BitString 6,
    residue (angle 4) x=bit x 0-bit x 5+2*(bit x 1+bit x 2+bit x 3+bit x 4) := by decide +kernel
theorem orbit14_fibers : ∀ x : SS.BitString 6,
    (x∈SixQubit.Orbit14.S0 ↔ residue (angle 2) x=0) ∧
    (x∈SixQubit.Orbit14.S1 ↔ residue (angle 2) x=2) := by decide +kernel
theorem orbit15_fibers : ∀ x : SS.BitString 6,
    (x∈SixQubit.Orbit15.S0 ↔ residue (angle 3) x=0) ∧
    (x∈SixQubit.Orbit15.S1 ↔ residue (angle 3) x=2) := by decide +kernel
theorem orbit24_fibers : ∀ x : SS.BitString 6,
    (x∈SixQubit.Orbit24.S0 ↔ residue (angle 4) x=0) ∧
    (x∈SixQubit.Orbit24.S1 ↔ residue (angle 4) x=2) := by decide +kernel
end MainTheory.OrderTwoRecordResidues
