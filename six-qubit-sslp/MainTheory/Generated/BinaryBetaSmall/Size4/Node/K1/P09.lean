-- Generated proof-only interval-tree node.
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_09
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_10
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_11
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_12
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_13
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_14
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_15

namespace MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P09

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic

theorem cover (x1 : BitVec 4) (x2 : BitVec 4)
    (h01 : 9 ≤ x1.toNat)
    (h12 : x1.toNat ≤ x2.toNat) :
    ReducedAtRow (prefixRowsMatrix ![BitVec.ofNat 4 9, x1, x2]) (Fin.last 3) 3 := by
  have hlt : x1.toNat < 16 := x1.isLt
  interval_cases hvalue : x1.toNat
  · have hcode09 : x1 = BitVec.ofNat 4 9 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_09.cover x2 h12
  · have hcode10 : x1 = BitVec.ofNat 4 10 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_10.cover x2 h12
  · have hcode11 : x1 = BitVec.ofNat 4 11 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_11.cover x2 h12
  · have hcode12 : x1 = BitVec.ofNat 4 12 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_12.cover x2 h12
  · have hcode13 : x1 = BitVec.ofNat 4 13 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_13.cover x2 h12
  · have hcode14 : x1 = BitVec.ofNat 4 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_14.cover x2 h12
  · have hcode15 : x1 = BitVec.ofNat 4 15 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P09_15.cover x2 h12

end MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P09
