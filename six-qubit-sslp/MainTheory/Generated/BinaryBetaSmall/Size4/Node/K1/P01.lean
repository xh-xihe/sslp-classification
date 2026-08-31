-- Generated proof-only interval-tree node.
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_01
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_02
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_03
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_04
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_05
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_06
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_07
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_08
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_09
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_10
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_11
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_12
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_13
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_14
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_15

namespace MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P01

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic

theorem cover (x1 : BitVec 4) (x2 : BitVec 4)
    (h01 : 1 ≤ x1.toNat)
    (h12 : x1.toNat ≤ x2.toNat) :
    ReducedAtRow (prefixRowsMatrix ![BitVec.ofNat 4 1, x1, x2]) (Fin.last 3) 3 := by
  have hlt : x1.toNat < 16 := x1.isLt
  interval_cases hvalue : x1.toNat
  · have hcode01 : x1 = BitVec.ofNat 4 1 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_01.cover x2 h12
  · have hcode02 : x1 = BitVec.ofNat 4 2 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_02.cover x2 h12
  · have hcode03 : x1 = BitVec.ofNat 4 3 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_03.cover x2 h12
  · have hcode04 : x1 = BitVec.ofNat 4 4 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_04.cover x2 h12
  · have hcode05 : x1 = BitVec.ofNat 4 5 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_05.cover x2 h12
  · have hcode06 : x1 = BitVec.ofNat 4 6 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_06.cover x2 h12
  · have hcode07 : x1 = BitVec.ofNat 4 7 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_07.cover x2 h12
  · have hcode08 : x1 = BitVec.ofNat 4 8 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_08.cover x2 h12
  · have hcode09 : x1 = BitVec.ofNat 4 9 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_09.cover x2 h12
  · have hcode10 : x1 = BitVec.ofNat 4 10 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_10.cover x2 h12
  · have hcode11 : x1 = BitVec.ofNat 4 11 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_11.cover x2 h12
  · have hcode12 : x1 = BitVec.ofNat 4 12 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_12.cover x2 h12
  · have hcode13 : x1 = BitVec.ofNat 4 13 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_13.cover x2 h12
  · have hcode14 : x1 = BitVec.ofNat 4 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_14.cover x2 h12
  · have hcode15 : x1 = BitVec.ofNat 4 15 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x1
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K2.P01_15.cover x2 h12

end MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P01
