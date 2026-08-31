-- Closed arithmetic leaf using kernel `decide`, for resource comparison with
-- the `norm_num` leaf in Shard001.  No function-valued quantifier remains.
import MainTheory.Generated.BinaryBetaReduced.Shard000

namespace MainTheory.Generated.BinaryBetaReduced.Shard002

open MainTheory.BinaryDetCofactor
open MainTheory.Generated.BinaryBetaReduced.Shard000

theorem pair000_002 :
    PairReducedBound explicitTop
      (rowOfBits (BitVec.ofNat 6 0))
      (rowOfBits (BitVec.ofNat 6 2)) 9 := by
  decide

end MainTheory.Generated.BinaryBetaReduced.Shard002
