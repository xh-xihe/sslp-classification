-- Batch-certificate resource probe: one kernel reduction traverses exactly
-- eight closed row-code pairs, with no function-space quantifier.
import MainTheory.Generated.BinaryBetaReduced.Shard000

namespace MainTheory.Generated.BinaryBetaReduced.BatchProbe

open MainTheory.BinaryDetCofactor
open MainTheory.Generated.BinaryBetaReduced.Shard000

abbrev PairCode := BitVec 6 × BitVec 6

def pairs : List PairCode :=
  [ (BitVec.ofNat 6 0, BitVec.ofNat 6 3),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 4),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 5),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 6),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 7),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 8),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 9),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 10) ]

def PairCode.Valid (p : PairCode) : Prop :=
  PairReducedBound explicitTop (rowOfBits p.1) (rowOfBits p.2) 9

instance (p : PairCode) : Decidable p.Valid := by
  unfold PairCode.Valid
  infer_instance

theorem pairs_valid : List.Forall PairCode.Valid pairs := by
  decide

theorem valid_of_mem {p : PairCode} (hp : p ∈ pairs) : p.Valid := by
  exact (List.forall_iff_forall_mem.mp pairs_valid) p hp

end MainTheory.Generated.BinaryBetaReduced.BatchProbe
