-- Generated proof-only interval-tree node.
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P00
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P01
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P02
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P03
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P04
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P05
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P06
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P07
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P08
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P09
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P10
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P11
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P12
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P13
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P14
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P15

namespace MainTheory.Generated.BinaryBetaSmall.Size4.Node.K0.Root

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic

theorem cover (x0 : BitVec 4) (x1 : BitVec 4) (x2 : BitVec 4)
    (h01 : x0.toNat ≤ x1.toNat)
    (h12 : x1.toNat ≤ x2.toNat) :
    ReducedAtRow (prefixRowsMatrix ![x0, x1, x2]) (Fin.last 3) 3 := by
  have hlt : x0.toNat < 16 := x0.isLt
  interval_cases hvalue : x0.toNat
  · have hcode00 : x0 = BitVec.ofNat 4 0 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P00.cover x1 x2 h01 h12
  · have hcode01 : x0 = BitVec.ofNat 4 1 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P01.cover x1 x2 h01 h12
  · have hcode02 : x0 = BitVec.ofNat 4 2 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P02.cover x1 x2 h01 h12
  · have hcode03 : x0 = BitVec.ofNat 4 3 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P03.cover x1 x2 h01 h12
  · have hcode04 : x0 = BitVec.ofNat 4 4 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P04.cover x1 x2 h01 h12
  · have hcode05 : x0 = BitVec.ofNat 4 5 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P05.cover x1 x2 h01 h12
  · have hcode06 : x0 = BitVec.ofNat 4 6 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P06.cover x1 x2 h01 h12
  · have hcode07 : x0 = BitVec.ofNat 4 7 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P07.cover x1 x2 h01 h12
  · have hcode08 : x0 = BitVec.ofNat 4 8 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P08.cover x1 x2 h01 h12
  · have hcode09 : x0 = BitVec.ofNat 4 9 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P09.cover x1 x2 h01 h12
  · have hcode10 : x0 = BitVec.ofNat 4 10 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P10.cover x1 x2 h01 h12
  · have hcode11 : x0 = BitVec.ofNat 4 11 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P11.cover x1 x2 h01 h12
  · have hcode12 : x0 = BitVec.ofNat 4 12 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P12.cover x1 x2 h01 h12
  · have hcode13 : x0 = BitVec.ofNat 4 13 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P13.cover x1 x2 h01 h12
  · have hcode14 : x0 = BitVec.ofNat 4 14 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P14.cover x1 x2 h01 h12
  · have hcode15 : x0 = BitVec.ofNat 4 15 := by
      apply BitVec.eq_of_toNat_eq
      simp [hvalue]
    subst x0
    exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K1.P15.cover x1 x2 h01 h12

end MainTheory.Generated.BinaryBetaSmall.Size4.Node.K0.Root
