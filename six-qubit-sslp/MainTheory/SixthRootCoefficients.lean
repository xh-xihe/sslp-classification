import SixQubit.Realize

set_option autoImplicit false

namespace MainTheory.SixthRootCoefficients

open SixQubit.Realize

noncomputable def root : ℂ := Complex.exp ((Real.pi : ℂ)*Complex.I/3)

theorem root_formula : root=(1+(Real.sqrt 3 : ℂ)*Complex.I)/2 := by
  unfold root
  rw [show (Real.pi : ℂ)*Complex.I/3=((Real.pi/3 : ℝ) : ℂ)*Complex.I by
    push_cast; ring]
  rw [Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin,
    Real.cos_pi_div_three,Real.sin_pi_div_three]
  push_cast
  ring

noncomputable def powers : Fin 6 → ℂ :=
  ![1,(1+(Real.sqrt 3 : ℂ)*Complex.I)/2,(-1+(Real.sqrt 3 : ℂ)*Complex.I)/2,
    -1,(-1-(Real.sqrt 3 : ℂ)*Complex.I)/2,(1-(Real.sqrt 3 : ℂ)*Complex.I)/2]

theorem power_formula (k : Fin 6) : root^(k : ℕ)=powers k := by
  have h2 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3)^3=3*Real.sqrt 3 := by rw [pow_succ,h2]
  have h4 : (Real.sqrt 3)^4=9 := by rw [show 4=2*2 by decide,pow_mul,h2]; norm_num
  have h5 : (Real.sqrt 3)^5=9*Real.sqrt 3 := by rw [pow_succ,h4]
  rw [root_formula]
  fin_cases k <;> apply Complex.ext <;>
    norm_num [powers,Complex.mul_re,Complex.mul_im,pow_succ] <;>
    nlinarith [h2,h3,h4,h5]

def smallData : Fin 6 → ZQ :=
  ![z8 0 0 2 0 0 0 0 0,z8 0 0 1 0 3 0 0 0,
    z8 0 0 (-1) 0 3 0 0 0,z8 0 0 (-2) 0 0 0 0 0,
    z8 0 0 (-1) 0 (-3) 0 0 0,z8 0 0 1 0 (-3) 0 0 0]

def largeData : Fin 6 → ZQ :=
  ![z8 0 0 0 2 0 0 0 0,z8 0 0 0 1 0 3 0 0,
    z8 0 0 0 (-1) 0 3 0 0,z8 0 0 0 (-2) 0 0 0 0,
    z8 0 0 0 (-1) 0 (-3) 0 0,z8 0 0 0 1 0 (-3) 0 0]

theorem smallData_formula (k : Fin 6) :
    toC (smallData k)=2*(Real.sqrt 3 : ℂ)*root^(k : ℕ) := by
  rw [power_formula]
  have h : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  fin_cases k <;> apply Complex.ext <;>
    norm_num [smallData,powers,toC,toCre,toCim,rz,SS.rp,z8] <;> nlinarith [h]

theorem largeData_formula (k : Fin 6) :
    toC (largeData k)=2*(Real.sqrt 6 : ℂ)*root^(k : ℕ) := by
  rw [power_formula]
  have h : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hmul := congrArg (fun x : ℝ => Real.sqrt 2*x) h
  have h6 : Real.sqrt 6=Real.sqrt 2*Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [h6]
  fin_cases k <;> apply Complex.ext <;>
    norm_num [largeData,powers,toC,toCre,toCim,rz,SS.rp,z8] <;> nlinarith [h,hmul]

theorem small_coefficient (k : Fin 6) :
    toC (smallData k)/12=root^(k : ℕ)/(Real.sqrt 12 : ℂ) := by
  rw [smallData_formula]
  have h12 : Real.sqrt 12=2*Real.sqrt 3 := by
    rw [show (12 : ℝ)=4*3 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  have h : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  rw [h12]
  push_cast
  have hn : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  field_simp
  linear_combination 4*root^(k : ℕ)*h

theorem large_coefficient (k : Fin 6) :
    toC (largeData k)/12=root^(k : ℕ)/(Real.sqrt 6 : ℂ) := by
  rw [largeData_formula]
  have h : (Real.sqrt 6 : ℂ)^2=6 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hn : (Real.sqrt 6 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 6)
  field_simp
  linear_combination 2*root^(k : ℕ)*h

end MainTheory.SixthRootCoefficients
