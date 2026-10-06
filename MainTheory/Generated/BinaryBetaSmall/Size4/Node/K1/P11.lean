-- Generated proof-only interval-tree node.
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_11
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_12
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_13
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_14
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_15

namespace MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P11

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic

theorem cover (x1 : BitVec 4) (x2 : BitVec 4)
    (h01 : 11 ≤ x1.toNat)
    (h12 : x1.toNat ≤ x2.toNat) :
    ReducedAtRow (prefixRowsMatrix ![BitVec.ofNat 4 11, x1, x2]) (Fin.last 3) 3 := by
  have hlt : x1.toNat < 16 := x1.isLt
  interval_cases hvalue : x1.toNat
  · have hcode11 : x1 = BitVec.ofNat 4 11 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_11.cover x2 h12
  · have hcode12 : x1 = BitVec.ofNat 4 12 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_12.cover x2 h12
  · have hcode13 : x1 = BitVec.ofNat 4 13 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_13.cover x2 h12
  · have hcode14 : x1 = BitVec.ofNat 4 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_14.cover x2 h12
  · have hcode15 : x1 = BitVec.ofNat 4 15 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P11_15.cover x2 h12

end MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P11
