-- Resource probe for the generic last-row certificates in sizes four/five.
import MainTheory.BinaryDetSmallCircuit

namespace MainTheory.Generated.BinaryBetaSmall.Probe

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryDetSmallCircuit

def codedPrefix4 : Matrix (Fin 4) (Fin 4) ℤ :=
  intMatrixOfRowBits ![
    BitVec.ofNat 4 14,
    BitVec.ofNat 4 13,
    BitVec.ofNat 4 11,
    BitVec.ofNat 4 0]

def prefix4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 0, 1;
     0, 0, 0, 0]

theorem codedPrefix4_eq_explicit : codedPrefix4 = prefix4 := by
  decide

/-- Prefix of the explicit determinant-three witness. -/
theorem prefix4_bound : ReducedAtRow prefix4 (3 : Fin 4) 3 := by
  apply CircuitReducedAtRow.toReducedAtRow (fuel := 2)
  decide

def codedPrefix5 : Matrix (Fin 5) (Fin 5) ℤ :=
  intMatrixOfRowBits ![
    BitVec.ofNat 5 5,
    BitVec.ofNat 5 11,
    BitVec.ofNat 5 22,
    BitVec.ofNat 5 12,
    BitVec.ofNat 5 0]

def prefix5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 0, 1, 0, 0;
     1, 1, 0, 1, 0;
     0, 1, 1, 0, 1;
     0, 0, 1, 1, 0;
     0, 0, 0, 0, 0]

theorem codedPrefix5_eq_explicit : codedPrefix5 = prefix5 := by
  decide

/-- Prefix of the explicit determinant-five witness. -/
theorem prefix5_bound : ReducedAtRow prefix5 (4 : Fin 5) 5 := by
  apply CircuitReducedAtRow.toReducedAtRow (fuel := 2)
  decide

end MainTheory.Generated.BinaryBetaSmall.Probe
