import Mathlib

import SixQubit.Orbit45Support

/-!
# Orbit 45: arbitrary-code Gram converse

This module applies the division-free algebra in `Orbit45Gram` to an
*arbitrary* normalized distance-three code on the two complete orbit-45
fibres.  No ansatz and no nonvanishing assumption is used.
-/

namespace SixQubit.Orbit45Universal

open scoped ComplexConjugate
open SixQubit.Orbit45Support

noncomputable section

private theorem normSq_star (z : ℂ) :
    Complex.normSq (star z) = Complex.normSq z := by simp

/-- The exact five-block magnitude statement.  The last two masses have
already been forced to `1/2`, so every one of their four entries has squared
modulus `1/8`. -/
structure BlockMasses (c d : SS.BitString 6 → ℂ) (g1 g2 g3 : ℝ) : Prop where
  nonneg1 : 0 ≤ g1
  nonneg2 : 0 ≤ g2
  nonneg3 : 0 ≤ g3
  moving_sum : g1 + g2 + g3 = 1
  block1 :
    Complex.normSq (c x0) = g1/4 ∧ Complex.normSq (c x1) = g1/4 ∧
    Complex.normSq (d y0) = g1/4 ∧ Complex.normSq (d y1) = g1/4
  block2 :
    Complex.normSq (c x2) = g2/4 ∧ Complex.normSq (c x3) = g2/4 ∧
    Complex.normSq (d y2) = g2/4 ∧ Complex.normSq (d y3) = g2/4
  block3 :
    Complex.normSq (c x4) = g3/4 ∧ Complex.normSq (c x5) = g3/4 ∧
    Complex.normSq (d y4) = g3/4 ∧ Complex.normSq (d y5) = g3/4
  block4 :
    Complex.normSq (c x6) = 1/8 ∧ Complex.normSq (c x7) = 1/8 ∧
    Complex.normSq (d y6) = 1/8 ∧ Complex.normSq (d y7) = 1/8
  block5 :
    Complex.normSq (c x8) = 1/8 ∧ Complex.normSq (c x9) = 1/8 ∧
    Complex.normSq (d y8) = 1/8 ∧ Complex.normSq (d y9) = 1/8

/-- The diagonal moment solution plus one exact cross-Walsh cancellation
forces the complete five-block magnitude pattern. -/
theorem block_masses (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    ∃ g1 g2 g3 : ℝ, BlockMasses c d g1 g2 g3 := by
  have hm := moments c d hc hd hnc hnd hdist
  have hs := MomentSystem.solve hm
  let g1 : ℝ := 4 * Complex.normSq (c x0)
  let g2 : ℝ := 4 * Complex.normSq (c x2)
  let g3 : ℝ := 4 * Complex.normSq (c x4)
  let g4 : ℝ := 4 * Complex.normSq (c x6)
  let g5 : ℝ := 4 * Complex.normSq (c x8)
  have hg1 : 0 ≤ g1 := by
    dsimp [g1]
    exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hg2 : 0 ≤ g2 := by
    dsimp [g2]
    exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hg3 : 0 ≤ g3 := by
    dsimp [g3]
    exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hg4 : 0 ≤ g4 := by
    dsimp [g4]
    exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hg5 : 0 ≤ g5 := by
    dsimp [g5]
    exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hgm : g1 + g2 + g3 = 1 := by
    dsimp [g1,g2,g3]
    linarith [hs.moving_sum]
  have hgf : g4 + g5 = 1 := by
    dsimp [g4,g5]
    linarith [hs.fixed_sum]
  have hb1 :
      Complex.normSq (c x0) = g1/4 ∧ Complex.normSq (c x1) = g1/4 ∧
      Complex.normSq (d y0) = g1/4 ∧ Complex.normSq (d y1) = g1/4 := by
    rcases hs.b1 with ⟨h01,h0r0,h0r1⟩
    dsimp [g1]
    constructor
    · ring
    constructor
    · rw [← h01]; ring
    constructor
    · rw [← h0r0]; ring
    · rw [← h0r1]; ring
  have hb2 :
      Complex.normSq (c x2) = g2/4 ∧ Complex.normSq (c x3) = g2/4 ∧
      Complex.normSq (d y2) = g2/4 ∧ Complex.normSq (d y3) = g2/4 := by
    rcases hs.b2 with ⟨h23,h2r2,h2r3⟩
    dsimp [g2]
    constructor
    · ring
    constructor
    · rw [← h23]; ring
    constructor
    · rw [← h2r2]; ring
    · rw [← h2r3]; ring
  have hb3 :
      Complex.normSq (c x4) = g3/4 ∧ Complex.normSq (c x5) = g3/4 ∧
      Complex.normSq (d y4) = g3/4 ∧ Complex.normSq (d y5) = g3/4 := by
    rcases hs.b3 with ⟨h45,h4r4,h4r5⟩
    dsimp [g3]
    constructor
    · ring
    constructor
    · rw [← h45]; ring
    constructor
    · rw [← h4r4]; ring
    · rw [← h4r5]; ring
  have hb4raw :
      Complex.normSq (c x6) = g4/4 ∧ Complex.normSq (c x7) = g4/4 ∧
      Complex.normSq (d y6) = g4/4 ∧ Complex.normSq (d y7) = g4/4 := by
    rcases hs.b4 with ⟨h67,h6r6,h6r7⟩
    dsimp [g4]
    constructor
    · ring
    constructor
    · rw [← h67]; ring
    constructor
    · rw [← h6r6]; ring
    · rw [← h6r7]; ring
  have hb5raw :
      Complex.normSq (c x8) = g5/4 ∧ Complex.normSq (c x9) = g5/4 ∧
      Complex.normSq (d y8) = g5/4 ∧ Complex.normSq (d y9) = g5/4 := by
    rcases hs.b5 with ⟨h89,h8r8,h8r9⟩
    dsimp [g5]
    constructor
    · ring
    constructor
    · rw [← h89]; ring
    constructor
    · rw [← h8r8]; ring
    · rw [← h8r9]; ring
  have hp4 : Complex.normSq (star (c x7) * d y7) = (g4/4)^2 := by
    rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      hb4raw.2.1, hb4raw.2.2.2]
    ring
  have hp5 : Complex.normSq (star (c x8) * d y8) = (g5/4)^2 := by
    rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      hb5raw.1, hb5raw.2.2.1]
    ring
  have h45 : g4 = g5 :=
    SixQubit.Orbit45Gram.masses_eq_of_opposite _ _ g4 g5 hg4 hg5 hp4 hp5
      (cross_fixed c d hc hd hdist)
  have hg4half : g4 = 1/2 := by linarith
  have hg5half : g5 = 1/2 := by linarith
  refine ⟨g1,g2,g3,⟨hg1,hg2,hg3,hgm,hb1,hb2,hb3,?_,?_⟩⟩
  · rw [hg4half] at hb4raw
    norm_num at hb4raw
    exact hb4raw
  · rw [hg5half] at hb5raw
    norm_num at hb5raw
    exact hb5raw

/-- The exact converse parameter carried by every code on the two fibres. -/
structure ConverseData (c d : SS.BitString 6 → ℂ)
    (g1 g2 g3 r1 r2 r3 t : ℝ) : Prop where
  blocks : BlockMasses c d g1 g2 g3
  r1_def : r1 = SixQubit.Orbit45Gram.r g1
  r2_def : r2 = SixQubit.Orbit45Gram.r g2
  r3_def : r3 = SixQubit.Orbit45Gram.r g3
  r1_nonneg : 0 ≤ r1
  r2_nonneg : 0 ≤ r2
  r3_nonneg : 0 ≤ r3
  r_sum : r1 + r2 + r3 = 1
  t_mass : t = 2 * (g1^2 + g2^2 + g3^2)
  t_simplex : t = (1 + (r1^2 + r2^2 + r3^2))/2
  lower : (2/3 : ℝ) ≤ t
  upper : t ≤ 1

/-- **Universal orbit-45 Gram converse.**  From only support,
normalization and `HasDistance`, an arbitrary code determines a simplex point
and hence a parameter in the exact interval `[2/3,1]`. -/
theorem universal_converse (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    ∃ g1 g2 g3 r1 r2 r3 t : ℝ,
      ConverseData c d g1 g2 g3 r1 r2 r3 t := by
  obtain ⟨g1,g2,g3,hb⟩ := block_masses c d hc hd hnc hnd hdist
  let p1 := conj (c x0) * d y0
  let p2 := conj (c x3) * d y3
  let p3 := conj (c x4) * d y4
  have hp1 : Complex.normSq p1 = (g1/4)^2 := by
    dsimp [p1]
    rw [Complex.normSq_mul, Complex.normSq_conj,
      hb.block1.1, hb.block1.2.2.1]
    ring
  have hp2 : Complex.normSq p2 = (g2/4)^2 := by
    dsimp [p2]
    rw [Complex.normSq_mul, Complex.normSq_conj,
      hb.block2.2.1, hb.block2.2.2.2]
    ring
  have hp3 : Complex.normSq p3 = (g3/4)^2 := by
    dsimp [p3]
    rw [Complex.normSq_mul, Complex.normSq_conj,
      hb.block3.1, hb.block3.2.2.1]
    ring
  have htri : p1 + p2 + p3 = 0 := by
    dsimp [p1,p2,p3]
    simpa only [Complex.star_def] using cross_triangle c d hc hd hdist
  obtain ⟨hg1half,hg2half,hg3half⟩ :=
    SixQubit.Orbit45Gram.triangle_half_bounds p1 p2 p3 g1 g2 g3
      hb.nonneg1 hb.nonneg2 hb.nonneg3 hp1 hp2 hp3 htri hb.moving_sum
  obtain ⟨hr1,hr2,hr3,hrsum⟩ :=
    SixQubit.Orbit45Gram.simplex_of_masses g1 g2 g3 hb.moving_sum
      hg1half hg2half hg3half
  have hinterval := SixQubit.Orbit45Gram.simplex_interval
    (SixQubit.Orbit45Gram.r g1) (SixQubit.Orbit45Gram.r g2)
    (SixQubit.Orbit45Gram.r g3) hr1 hr2 hr3 hrsum
  let t : ℝ := 2 * (g1^2 + g2^2 + g3^2)
  have htchange : t =
      (1 + (SixQubit.Orbit45Gram.r g1 ^ 2 +
        SixQubit.Orbit45Gram.r g2 ^ 2 +
        SixQubit.Orbit45Gram.r g3 ^ 2))/2 := by
    dsimp [t]
    exact SixQubit.Orbit45Gram.a2_change_of_variables g1 g2 g3 hb.moving_sum
  refine ⟨g1,g2,g3, SixQubit.Orbit45Gram.r g1,
    SixQubit.Orbit45Gram.r g2, SixQubit.Orbit45Gram.r g3, t,
    ⟨hb,rfl,rfl,rfl,hr1,hr2,hr3,hrsum,rfl,htchange,?_,?_⟩⟩
  · rw [htchange]
    exact hinterval.1
  · rw [htchange]
    exact hinterval.2

end

end SixQubit.Orbit45Universal
