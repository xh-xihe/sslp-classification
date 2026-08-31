-- Authoritative-index bridge kept separate from the arithmetic certificate.
import MainTheory.BinaryDetCofactor
import MainTheory.Generated.BinaryBetaReduced.Shard000

namespace MainTheory.Generated.BinaryBetaReduced.PatternBridge045

open MainTheory.BinaryDetCircuit

/-- The generated literal in `Shard000` is exactly pattern 45 of Lean's
authoritative enumeration.  This theorem contains no determinant arithmetic. -/
theorem explicitTop_eq_authoritative :
    MainTheory.Generated.BinaryBetaReduced.Shard000.explicitTop =
      topOfPattern (R := ℤ) (patternAt ⟨45, by decide⟩) := by
  decide

end MainTheory.Generated.BinaryBetaReduced.PatternBridge045
