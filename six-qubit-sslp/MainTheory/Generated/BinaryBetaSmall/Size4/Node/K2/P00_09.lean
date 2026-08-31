-- Generated proof-only interval-tree node.
import MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0006
import MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0007

namespace MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P00_09

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic

theorem cover (x2 : BitVec 4)
    (h12 : 9 ≤ x2.toNat) :
    ReducedAtRow (prefixRowsMatrix ![BitVec.ofNat 4 0, BitVec.ofNat 4 9, x2]) (Fin.last 3) 3 := by
  have hlt : x2.toNat < 16 := x2.isLt
  interval_cases hvalue : x2.toNat
  · have hcode09 : x2 = BitVec.ofNat 4 9 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0006.cert_00_09_09
  · have hcode10 : x2 = BitVec.ofNat 4 10 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0006.cert_00_09_10
  · have hcode11 : x2 = BitVec.ofNat 4 11 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0006.cert_00_09_11
  · have hcode12 : x2 = BitVec.ofNat 4 12 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0006.cert_00_09_12
  · have hcode13 : x2 = BitVec.ofNat 4 13 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0007.cert_00_09_13
  · have hcode14 : x2 = BitVec.ofNat 4 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0007.cert_00_09_14
  · have hcode15 : x2 = BitVec.ofNat 4 15 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x2
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Leaf.Shard0007.cert_00_09_15

end MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P00_09
