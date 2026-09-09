import SixQubit.K4Kernel

namespace MainTheory.Orbit36RootOfUnity

theorem rho_eq_exp : SixQubit.K4Kernel.rho =
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3) := by
  have hc : Real.cos (2 * (Real.pi / 3)) = -1/2 := by
    rw [Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  have hs : Real.sin (2 * (Real.pi / 3)) = Real.sqrt 3 / 2 := by
    rw [Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring
  rw [show 2 * (Real.pi : ℂ) * Complex.I / 3 =
    ((2 * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  unfold SixQubit.K4Kernel.rho
  push_cast
  ring

end MainTheory.Orbit36RootOfUnity
