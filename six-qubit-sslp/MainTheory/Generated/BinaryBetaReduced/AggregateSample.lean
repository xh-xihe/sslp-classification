-- Tiny proof-only aggregation prototype.  The full generator uses the same
-- shape recursively; this sample intentionally covers only codes (0,0),(0,1).
import MainTheory.Generated.BinaryBetaReduced.Shard001

namespace MainTheory.Generated.BinaryBetaReduced.AggregateSample

open MainTheory.BinaryDetCofactor
open MainTheory.Generated.BinaryBetaReduced.Shard000
open MainTheory.Generated.BinaryBetaReduced.Shard001

/-- The two closed arithmetic leaves can be consumed through variable BitVec
codes without re-running their determinant normalization. -/
theorem firstTwoPairs (a b : BitVec 6)
    (ha : a.toNat = 0) (hb : b.toNat ≤ 1) :
    PairReducedBound explicitTop (rowOfBits a) (rowOfBits b) 9 := by
  have ha' : a = BitVec.ofNat 6 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [ha]
  rw [ha']
  interval_cases hcode : b.toNat
  · have hb' : b = BitVec.ofNat 6 0 := by
      apply BitVec.eq_of_toNat_eq
      simp [hcode]
    simpa [hb'] using pair000_000
  · have hb' : b = BitVec.ofNat 6 1 := by
      apply BitVec.eq_of_toNat_eq
      simp [hcode]
    simpa [hb'] using pair000_001

end MainTheory.Generated.BinaryBetaReduced.AggregateSample
