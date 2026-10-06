import MainTheory.Orbit31SupportBase

/-! Phase ratios on the actual complementary orbit-31 fibres.
Ratios are asserted to be unit only on active positions. Reconstruction
also holds on the boundary because both complementary amplitudes vanish.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31SupportBase
open SixQubit.Orbit31
noncomputable section

def top (j : Fin 16) : SS.BitString 6 := fun k => !(bottom j k)
def C (c : SS.State 6 ℂ) (j : Fin 16) : ℂ := c (bottom j)
def D (d : SS.State 6 ℂ) (j : Fin 16) : ℂ := d (top j)
def sigma (c d : Fin 16 → ℂ) (j : Fin 16) : ℂ := star (d j) / c j

def nativeTop : Fin 16 → SS.BitString 6 :=
  ![z15,z14,z13,z12,z8,z9,z10,z11,z4,z5,z6,z7,z0,z1,z2,z3]
theorem top_native : top = nativeTop := by decide +kernel

theorem C_native (c : SS.State 6 ℂ) : C c =
    ![c y0,c y1,c y2,c y3,c y7,c y6,c y5,c y4,
      c y11,c y10,c y9,c y8,c y15,c y14,c y13,c y12] := by
  funext j
  fin_cases j <;> rw [C,bottom_native] <;> rfl

theorem D_native (d : SS.State 6 ℂ) : D d =
    ![d z15,d z14,d z13,d z12,d z8,d z9,d z10,d z11,
      d z4,d z5,d z6,d z7,d z0,d z1,d z2,d z3] := by
  funext j
  fin_cases j <;> rw [D,top_native] <;> rfl

def EqualProbabilities (c d : Fin 16 → ℂ) : Prop :=
  ∀ j, Complex.normSq (d j) = Complex.normSq (c j)

theorem physical_equal_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) : EqualProbabilities (C c) (D d) := by
  have hm := SixQubit.Orbit31.moments c d hc hd hnc hnd hkl
  intro j
  rw [C_native,D_native]
  fin_cases j
  · have h := eq0 hm; change Complex.normSq (d z15) = Complex.normSq (c y0); linarith
  · have h := eq1 hm; change Complex.normSq (d z14) = Complex.normSq (c y1); linarith
  · have h := eq2 hm; change Complex.normSq (d z13) = Complex.normSq (c y2); linarith
  · have h := eq3 hm; change Complex.normSq (d z12) = Complex.normSq (c y3); linarith
  · have h := eq7 hm; change Complex.normSq (d z8) = Complex.normSq (c y7); linarith
  · have h := eq6 hm; change Complex.normSq (d z9) = Complex.normSq (c y6); linarith
  · have h := eq5 hm; change Complex.normSq (d z10) = Complex.normSq (c y5); linarith
  · have h := eq4 hm; change Complex.normSq (d z11) = Complex.normSq (c y4); linarith
  · have h := eq11 hm; change Complex.normSq (d z4) = Complex.normSq (c y11); linarith
  · have h := eq10 hm; change Complex.normSq (d z5) = Complex.normSq (c y10); linarith
  · have h := eq9 hm; change Complex.normSq (d z6) = Complex.normSq (c y9); linarith
  · have h := eq8 hm; change Complex.normSq (d z7) = Complex.normSq (c y8); linarith
  · have h := eq15 hm; change Complex.normSq (d z0) = Complex.normSq (c y15); linarith
  · have h := eq14 hm; change Complex.normSq (d z1) = Complex.normSq (c y14); linarith
  · have h := eq13 hm; change Complex.normSq (d z2) = Complex.normSq (c y13); linarith
  · have h := eq12 hm; change Complex.normSq (d z3) = Complex.normSq (c y12); linarith

theorem complementary_zero_iff {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d) (j : Fin 16) :
    d j = 0 ↔ c j = 0 := by
  rw [← Complex.normSq_eq_zero,← Complex.normSq_eq_zero,hp j]

theorem reconstruct {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d) (j : Fin 16) :
    star (d j) = sigma c d j * c j := by
  by_cases hc : c j = 0
  · have hd := (complementary_zero_iff hp j).mpr hc
    simp [hc,hd,sigma]
  · exact (div_mul_cancel₀ (star (d j)) hc).symm

theorem unit_normSq {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d) {j : Fin 16}
    (hj : c j ≠ 0) : Complex.normSq (sigma c d j) = 1 := by
  rw [sigma,Complex.normSq_div]
  change Complex.normSq (starRingEnd ℂ (d j)) / Complex.normSq (c j) = 1
  rw [Complex.normSq_conj,hp j]
  exact div_self (mt Complex.normSq_eq_zero.mp hj)

theorem unit_norm {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d) {j : Fin 16}
    (hj : c j ≠ 0) : ‖sigma c d j‖ = 1 := by
  rw [Complex.norm_def,unit_normSq hp hj,Real.sqrt_one]

theorem nonzero {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d) {j : Fin 16}
    (hj : c j ≠ 0) : sigma c d j ≠ 0 := by
  intro hz
  have h := unit_normSq hp hj
  rw [hz,Complex.normSq_zero] at h
  norm_num at h

theorem equal_from_reciprocal {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    {a b : Fin 16} (ha : c a ≠ 0) (hb : c b ≠ 0)
    (h : star (c a) * d b = star (c b) * d a) : sigma c d a = sigma c d b := by
  have hs := congrArg star h
  simp only [star_mul,star_star] at hs
  rw [reconstruct hp a,reconstruct hp b] at hs
  apply mul_right_cancel₀ (mul_ne_zero ha hb)
  linear_combination -hs

end
end MainTheory.Orbit31PhaseRatios
