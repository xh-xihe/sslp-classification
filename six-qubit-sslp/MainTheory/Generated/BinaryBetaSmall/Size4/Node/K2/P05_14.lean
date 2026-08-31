-- Generated proof-only interval-tree node.
import MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0037

namespace MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P05_14

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic

theorem cover (x2 : BitVec 4)
    (h12 : 14 ≤ x2.toNat) :
    ReducedAtRow (prefixRowsMatrix ![BitVec.ofNat 4 5, BitVec.ofNat 4 14, x2]) (Fin.last 3) 3 := by
  have hlt : x2.toNat < 16 := x2.isLt
  interval_cases hvalue : x2.toNat
  · have hcode14 : x2 = BitVec.ofNat 4 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0037.cert_05_14_14
  · have hcode15 : x2 = BitVec.ofNat 4 15 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0037.cert_05_14_15

end MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P05_14
