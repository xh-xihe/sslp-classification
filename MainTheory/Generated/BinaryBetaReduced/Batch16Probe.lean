-- Sixteen-pair midpoint resource probe.  No heartbeat override is permitted.
import MainTheory.Generated.BinaryBetaReduced.BatchProbe

namespace MainTheory.Generated.BinaryBetaReduced.Batch16Probe

open MainTheory.Generated.BinaryBetaReduced.BatchProbe

def pairs16 : List PairCode :=
  [ (BitVec.ofNat 6 0, BitVec.ofNat 6 0),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 1),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 2),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 3),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 4),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 5),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 6),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 7),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 8),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 9),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 10),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 11),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 12),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 13),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 14),
    (BitVec.ofNat 6 0, BitVec.ofNat 6 15) ]

theorem pairs16_valid : List.Forall PairCode.Valid pairs16 := by
  decide

end MainTheory.Generated.BinaryBetaReduced.Batch16Probe
