import MainTheory.Orbit7ProjectorComparison

set_option autoImplicit false

namespace MainTheory.Orbit7CircleDisplays

noncomputable def phase (c d : ℝ) (t : ℂ) : ℂ := 1+((2*c/d : ℝ) : ℂ)*t

theorem phase_norm (c d : ℝ) (t : ℂ) (hd : d ≠ 0)
    (h : c*Complex.normSq t+d*t.re=0) : Complex.normSq (phase c d t)=1 := by
  have he : Complex.normSq (phase c d t) =
      1+2*(2*c/d)*t.re+(2*c/d)^2*Complex.normSq t := by
    simp [phase,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    ring
  rw [he]
  field_simp
  linear_combination (4*c)*h

theorem phase_parametrization (c d : ℝ) (t : ℂ) (hc : c ≠ 0) (hd : d ≠ 0) :
    t=((d/(2*c) : ℝ) : ℂ)*(phase c d t-1) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [phase,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp
  ring

theorem circle_parametrization (c d : ℝ) (t : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : c*Complex.normSq t+d*t.re=0) :
    ∃ zeta : ℂ, ‖zeta‖=1 ∧ t=((d/(2*c) : ℝ) : ℂ)*(zeta-1) := by
  refine ⟨phase c d t,?_,phase_parametrization c d t hc hd⟩
  have hn := phase_norm c d t hd h
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg (phase c d t)]

theorem phase_endpoint (c d : ℝ) (t : ℂ) (hd : d ≠ 0)
    (h : (c : ℂ)*t+(d : ℂ)=0) : phase c d t = -1 := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [phase,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp
  linear_combination 2*h

theorem zeta_factor (c d : ℝ) (T N : ℂ) (hd : d ≠ 0)
    (hT : 2*(c : ℂ)*(T*star T)+(d : ℂ)*(T+star T)=0)
    (hN : 2*(c : ℂ)*(N*star N)+(d : ℂ)*(N+star N)=0)
    (hdis : (d : ℂ)*(T-N+star N-star T)+(c : ℂ)*(T*star N-N*star T)=0) :
    (phase c d T+1)*(phase c d T-phase c d N)*(phase c d N+1)=0 := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rcases SixQubit.Orbit7ProjectorAlgebra.disjoint_circle_three_cases
    (c : ℂ) (d : ℂ) T N (star T) (star N) hdC hT hN hdis with he | he | he
  · simp [he]
  · rw [phase_endpoint c d T hd he]
    ring
  · rw [phase_endpoint c d N hd he]
    ring

theorem three_cases (c d : ℝ) (T N : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hT : 2*(c : ℂ)*(T*star T)+(d : ℂ)*(T+star T)=0)
    (hN : 2*(c : ℂ)*(N*star N)+(d : ℂ)*(N+star N)=0)
    (hdis : (d : ℂ)*(T-N+star N-star T)+(c : ℂ)*(T*star N-N*star T)=0) :
    T=N ∨ T=-(d : ℂ)/(c : ℂ) ∨ N=-(d : ℂ)/(c : ℂ) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rcases SixQubit.Orbit7ProjectorAlgebra.disjoint_circle_three_cases
    (c : ℂ) (d : ℂ) T N (star T) (star N) hdC hT hN hdis with he | he | he
  · exact Or.inl he
  · right; left
    apply (eq_div_iff hcC).mpr
    linear_combination he
  · right; right
    apply (eq_div_iff hcC).mpr
    linear_combination he

end MainTheory.Orbit7CircleDisplays
