import SixQubit.Orbit36Class
import MainTheory.Orbit36MomentCharacters
import MainTheory.Orbit36RootOfUnity

set_option autoImplicit false

namespace MainTheory.Orbit36CanonicalAmplitudes

open SixQubit.Orbit36 SixQubit.Orbit36Class
open MainTheory.Orbit36MomentCharacters

theorem anchor_exact : A36 = 1/(Real.sqrt 10 : ℂ) := by
  have hnum : SixQubit.Orbit36Code.toC (SixQubit.Orbit36Code.c0z y0) =
      2*(Real.sqrt 3 : ℂ) := by
    have he : SixQubit.Orbit36Code.c0z y0 = SixQubit.Orbit36Code.z8 0 0 2 0 0 0 0 0 := by decide
    rw [he]
    apply Complex.ext <;> simp [SixQubit.Orbit36Code.toC, SixQubit.Orbit36Code.toCre,
      SixQubit.Orbit36Code.toCim, SixQubit.Orbit36Code.rz, SixQubit.Orbit36Code.z8, SS.rp]
  have hs : (Real.sqrt 30 : ℂ) = (Real.sqrt 3 : ℂ)*(Real.sqrt 10 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<3)).ne'
  have h10 : (Real.sqrt 10 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<10)).ne'
  change ((Real.sqrt 30 : ℂ)⁻¹/2) * SixQubit.Orbit36Code.toC (SixQubit.Orbit36Code.c0z y0) = _
  rw [hnum, hs]
  field_simp

theorem edge_exact : E36 = 1/(Real.sqrt 15 : ℂ) := by
  have hnum : SixQubit.Orbit36Code.toC (SixQubit.Orbit36Code.c0z y6) =
      2*(Real.sqrt 2 : ℂ) := by
    have he : SixQubit.Orbit36Code.c0z y6 = SixQubit.Orbit36Code.z8 0 2 0 0 0 0 0 0 := by decide
    rw [he]
    apply Complex.ext <;> simp [SixQubit.Orbit36Code.toC, SixQubit.Orbit36Code.toCre,
      SixQubit.Orbit36Code.toCim, SixQubit.Orbit36Code.rz, SixQubit.Orbit36Code.z8, SS.rp]
  have hs : (Real.sqrt 30 : ℂ) = (Real.sqrt 2 : ℂ)*(Real.sqrt 15 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have h15 : (Real.sqrt 15 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<15)).ne'
  change ((Real.sqrt 30 : ℂ)⁻¹/2) * SixQubit.Orbit36Code.toC (SixQubit.Orbit36Code.c0z y6) = _
  rw [hnum, hs]
  field_simp

noncomputable def omega : ℂ := Complex.exp (2*(Real.pi : ℂ)*Complex.I/3)

theorem all_amplitudes : ∀ i : Fin 12, SixQubit.Orbit36Code.c36 (vertices i) =
    ![1/(Real.sqrt 10 : ℂ),1/(Real.sqrt 10 : ℂ),1/(Real.sqrt 10 : ℂ),
      1/(Real.sqrt 10 : ℂ),1/(Real.sqrt 10 : ℂ),1/(Real.sqrt 10 : ℂ),
      1/(Real.sqrt 15 : ℂ),omega/(Real.sqrt 15 : ℂ),omega^2/(Real.sqrt 15 : ℂ),
      omega^2/(Real.sqrt 15 : ℂ),omega/(Real.sqrt 15 : ℂ),1/(Real.sqrt 15 : ℂ)] i := by
  have hy0 : SixQubit.Orbit36Code.c36 y0 = 1/(Real.sqrt 10 : ℂ) := anchor_exact
  have hy6 : SixQubit.Orbit36Code.c36 y6 = 1/(Real.sqrt 15 : ℂ) := edge_exact
  intro i
  fin_cases i <;>
    simp [vertices, c36_y1,c36_y2,c36_y3,c36_y4,c36_y5,c36_y7,c36_y8,c36_y9,c36_y10,c36_y11,
      hy0, hy6, anchor_exact, edge_exact, MainTheory.Orbit36RootOfUnity.rho_eq_exp,
      omega, div_eq_mul_inv]

end MainTheory.Orbit36CanonicalAmplitudes
