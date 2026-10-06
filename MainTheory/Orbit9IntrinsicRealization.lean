import MainTheory.WImageIntrinsicBridge
import SixQubit.Orbit9Real

/-!
# A realized intrinsic element of exact order three

This leaf packages the lightweight explicit orbit-9 code as an actual
`ExactCode`, constructs its primitive finite diagonal generator, and places
that generator in the intrinsic projective quotient.  Exact order three is
derived from the kernel theorem `2 ≤ logicalOrder ∣ 3`; it is not copied from
an orbit label.
-/

namespace MainTheory.Orbit9IntrinsicRealization

open MainTheory
open MainTheory.GlobalClassificationBridge
open MainTheory.WImageIntrinsicBridge

noncomputable section

/-- Standard primitive cube root for the explicit modulus-three gate. -/
def rootThree : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (3 : ℂ))

theorem rootThree_primitive : IsPrimitiveRoot rootThree 3 := by
  exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- Orbit 9's explicit angle is primitive because its first coordinate is
one. -/
theorem orbit9_angle_primitive :
    Gate.Primitive 3 SixQubit.Orbit9Real.av := by
  intro divisor _ hall
  have h0 := hall 0
  have hav : (SixQubit.Orbit9Real.av 0).val = 1 := by decide
  rw [hav] at h0
  exact Nat.dvd_one.mp h0

theorem orbit9_w0_support :
    ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 →
      SixQubit.Orbit9Real.w0 x = 0 := by
  intro x hweight
  apply SixQubit.Orbit9Real.w0_vanishes x
  intro hx
  exact hweight (SixQubit.Orbit9Real.L0_in_fiber x hx)

theorem orbit9_w1_support :
    ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 →
      SixQubit.Orbit9Real.w1 x = 0 := by
  intro x hweight
  apply SixQubit.Orbit9Real.w1_vanishes x
  intro hx
  exact hweight (SixQubit.Orbit9Real.L1_in_fiber x hx)

/-- The two displayed residue eigenvalues are genuinely distinct. -/
theorem rootThree_zero_one_distinct :
    rootThree ^ ((0 : ZMod 3).val) ≠
      rootThree ^ ((1 : ZMod 3).val) := by
  have h0 : ((0 : ZMod 3).val) = 0 := by decide
  have h1 : ((1 : ZMod 3).val) = 1 := by decide
  rw [h0, h1, pow_zero, pow_one]
  intro hone
  have hp : rootThree ^ 1 = 1 := by simp [hone.symm]
  have hdvd : 3 ∣ 1 := (rootThree_primitive.pow_eq_one_iff_dvd 1).1 hp
  norm_num at hdvd

/-- A genuine exact six-qubit code has a nontrivial intrinsic element of
group-theoretic order exactly three. -/
theorem exists_exact_six_qubit_intrinsic_order_three :
    ∃ C : CodeSpec.ExactCode 6 2 3,
      ∃ g : IntrinsicGroup C, g ≠ 1 ∧ orderOf g = 3 := by
  let C : CodeSpec.ExactCode 6 2 3 :=
    exactCodeOfPair SixQubit.Orbit9Real.w0 SixQubit.Orbit9Real.w1
      SixQubit.Orbit9Real.w0_normalized
      SixQubit.Orbit9Real.w1_normalized
      SixQubit.Orbit9Real.is_code
  let G : RankTwoGlobal.FiniteGeneratorResolution C 3 :=
    finiteGeneratorOfSupportedPair rootThree rootThree_primitive
      SixQubit.Orbit9Real.av orbit9_angle_primitive
      0 1 SixQubit.Orbit9Real.w0 SixQubit.Orbit9Real.w1
      orbit9_w0_support orbit9_w1_support
      SixQubit.Orbit9Real.w0_normalized
      SixQubit.Orbit9Real.w1_normalized
      SixQubit.Orbit9Real.is_code
      rootThree_zero_one_distinct
  let T : RankTwoGlobal.TwoFiberCertificate G :=
    Classical.choice (RankTwoGlobal.finiteGenerator_twoFiber G)
  have hdiv : T.logicalOrder ∣ 3 := T.logicalOrder_dvd_physical
  have hle : T.logicalOrder ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have htwo : 2 ≤ T.logicalOrder := T.two_le_logicalOrder
  have hcases : T.logicalOrder = 2 ∨ T.logicalOrder = 3 := by omega
  have hm : T.logicalOrder = 3 := by
    rcases hcases with h2 | h3
    · exfalso
      rw [h2] at hdiv
      norm_num at hdiv
    · exact h3
  refine ⟨C, G.intrinsicClass, T.intrinsic_class_ne_one, ?_⟩
  exact T.intrinsic_order_eq.trans hm

end

end MainTheory.Orbit9IntrinsicRealization
