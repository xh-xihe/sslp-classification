-- Generated numerical leaf for the binary determinant bound.
-- This module is intentionally one-pattern wide so a failed or expensive
-- kernel reduction cannot fan out into concurrent Lean workers.
import MainTheory.BinaryDetCofactor

namespace MainTheory.Generated.BinaryBetaReduced.Shard000

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetCofactor

/-- Literal top block for canonical tuple `(0,0,0,1,2,4)`.  Numerical leaves
never unfold the authoritative 1716-element list; that transcription is
checked once in the separate pattern bridge. -/
def explicitTop : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- One of the 64 possible first free rows.  The eventual generator emits the
same literal form for every row, rather than trusting an external row code. -/
def firstRow000 : BinaryRow := fun _ ↦ false

def secondRow000 : BinaryRow := fun _ ↦ false

/-- Resource probe for the intended fine-grained leaf shape: one completely
closed row pair, checked by `norm_num`.  Pattern 45 has full top-row rank, but
its low authoritative index avoids traversing a thousand-element list before
the determinant calculation. -/
theorem pattern045_pair000_000 :
    (-(9 : ℤ) ≤ negativeCoefficientSum
        explicitTop
        firstRow000 secondRow000) ∧
    (positiveCoefficientSum
        explicitTop
        firstRow000 secondRow000 ≤ (9 : ℤ)) := by
  norm_num [negativeCoefficientSum, positiveCoefficientSum,
    lastRowCoefficient, firstRow000, secondRow000, basisRow, bottomOfRows,
    bitZ, explicitTop,
    MainTheory.BinaryDetCircuit.laplace33Grouped,
    MainTheory.BinaryDetCircuit.minor3Poly,
    MainTheory.BinaryDetCircuit.minor3, Matrix.det_fin_three]

/-- Table-facing form of the same arithmetic fact. -/
theorem pair000_000 :
    PairReducedBound explicitTop
      (rowOfBits (BitVec.ofNat 6 0))
      (rowOfBits (BitVec.ofNat 6 0)) 9 := by
  have hrow : rowOfBits (BitVec.ofNat 6 0) = firstRow000 := by
    funext j
    fin_cases j <;> decide
  rw [hrow]
  exact pattern045_pair000_000

end MainTheory.Generated.BinaryBetaReduced.Shard000
