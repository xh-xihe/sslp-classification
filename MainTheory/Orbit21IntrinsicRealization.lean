import MainTheory.WImageIntrinsicBridge
import SixQubit.Orbit21Real

/-!
# A realized intrinsic element of exact order two

This leaf packages the lightweight explicit orbit-21 code and its
modulus-four finite lift in the actual intrinsic projective quotient.  Since
the physical order is four, nontriviality alone would not distinguish logical
order two from four.  The proof therefore derives that the eigenvalue ratio
squares to one and feeds that equation into the kernel-produced
`TwoFiberCertificate`; the exact order is not read from the paper label.
-/

namespace MainTheory.Orbit21IntrinsicRealization

open MainTheory
open MainTheory.GlobalClassificationBridge
open MainTheory.WImageIntrinsicBridge

noncomputable section

/-- Standard primitive fourth root for the explicit finite gate. -/
def rootFour : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (4 : ℂ))

theorem rootFour_primitive : IsPrimitiveRoot rootFour 4 := by
  exact Complex.isPrimitiveRoot_exp 4 (by norm_num)

/-- Orbit 21's explicit angle is primitive because its first coordinate is
one. -/
theorem orbit21_angle_primitive :
    Gate.Primitive 4 SixQubit.Orbit21Real.av := by
  intro divisor _ hall
  have h0 := hall 0
  have hav : (SixQubit.Orbit21Real.av 0).val = 1 := by decide
  rw [hav] at h0
  exact Nat.dvd_one.mp h0

theorem orbit21_w0_support :
    ∀ x, SS.weight SixQubit.Orbit21Real.av x ≠ 0 →
      SixQubit.Orbit21Real.w0 x = 0 := by
  intro x hweight
  apply SixQubit.Orbit21Real.w0_vanishes x
  intro hx
  exact hweight (SixQubit.Orbit21Real.L0_in_fiber x hx)

theorem orbit21_w1_support :
    ∀ x, SS.weight SixQubit.Orbit21Real.av x ≠ 2 →
      SixQubit.Orbit21Real.w1 x = 0 := by
  intro x hweight
  apply SixQubit.Orbit21Real.w1_vanishes x
  intro hx
  exact hweight (SixQubit.Orbit21Real.L1_in_fiber x hx)

/-- Residues zero and two have distinct fourth-root eigenvalues. -/
theorem rootFour_zero_two_distinct :
    rootFour ^ ((0 : ZMod 4).val) ≠
      rootFour ^ ((2 : ZMod 4).val) := by
  have h0 : ((0 : ZMod 4).val) = 0 := by decide
  have h2 : ((2 : ZMod 4).val) = 2 := by decide
  rw [h0, h2, pow_zero]
  intro hone
  have hp : rootFour ^ 2 = 1 := hone.symm
  have hdvd : 4 ∣ 2 := (rootFour_primitive.pow_eq_one_iff_dvd 2).1 hp
  norm_num at hdvd

/-- A genuine exact six-qubit code has a nontrivial intrinsic element of
group-theoretic order exactly two. -/
theorem exists_exact_six_qubit_intrinsic_order_two :
    ∃ C : CodeSpec.ExactCode 6 2 3,
      ∃ g : IntrinsicGroup C, g ≠ 1 ∧ orderOf g = 2 := by
  let C : CodeSpec.ExactCode 6 2 3 :=
    exactCodeOfPair SixQubit.Orbit21Real.w0 SixQubit.Orbit21Real.w1
      SixQubit.Orbit21Real.w0_normalized
      SixQubit.Orbit21Real.w1_normalized
      SixQubit.Orbit21Real.is_code
  let G : RankTwoGlobal.FiniteGeneratorResolution C 4 :=
    finiteGeneratorOfSupportedPair rootFour rootFour_primitive
      SixQubit.Orbit21Real.av orbit21_angle_primitive
      0 2 SixQubit.Orbit21Real.w0 SixQubit.Orbit21Real.w1
      orbit21_w0_support orbit21_w1_support
      SixQubit.Orbit21Real.w0_normalized
      SixQubit.Orbit21Real.w1_normalized
      SixQubit.Orbit21Real.is_code
      rootFour_zero_two_distinct
  let T : RankTwoGlobal.TwoFiberCertificate G :=
    Classical.choice (RankTwoGlobal.finiteGenerator_twoFiber G)
  have hratioSquare :
      (G.eigenvalue 1 / G.eigenvalue 0) ^ 2 = 1 := by
    change (rootFour ^ 2 / rootFour ^ 0) ^ 2 = 1
    simp only [pow_zero, div_one]
    calc
      (rootFour ^ 2) ^ 2 = rootFour ^ (2 * 2) :=
        (pow_mul rootFour 2 2).symm
      _ = rootFour ^ 4 := by norm_num
      _ = 1 := rootFour_primitive.pow_eq_one
  have hmdiv : T.logicalOrder ∣ 2 := by
    rw [T.logicalOrder_eq]
    exact (T.ratio_order 2).1 hratioSquare
  have hmle : T.logicalOrder ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hmdiv
  have htwo : 2 ≤ T.logicalOrder := T.two_le_logicalOrder
  have hm : T.logicalOrder = 2 := by omega
  refine ⟨C, G.intrinsicClass, T.intrinsic_class_ne_one, ?_⟩
  exact T.intrinsic_order_eq.trans hm

end

end MainTheory.Orbit21IntrinsicRealization
