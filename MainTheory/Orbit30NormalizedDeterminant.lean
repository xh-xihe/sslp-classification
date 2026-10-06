import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit30NormalizedDeterminant
noncomputable section
def matrix (c d f g h k : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0,1,1,c,d;1,0,1,f,g;1,1,0,h,k;c,f,h,0,1;d,g,k,1,0]
theorem determinant_polynomial (c d f g h k : ℂ) :
    (matrix c d f g h k).det=-2*c^2*g*k + 2*c*d*f*k + 2*c*d*g*h - 2*c*d + 2*c*f*g*k - 2*c*f*k^2 - 2*c*g^2*h + 2*c*g*h*k + 2*c*g + 2*c*k - 2*d^2*f*h - 2*d*f^2*k + 2*d*f*g*h + 2*d*f*h*k + 2*d*f - 2*d*g*h^2 + 2*d*h - 2*f*g + 2*f*k + 2*g*h - 2*h*k - 2 := by
  simp +decide [matrix,Matrix.det_succ_row_zero,Fin.sum_univ_succ,Fin.succAbove]
  ring
theorem products (c d f g h k : ℂ)
    (h0 : 1+f*k+g*h=0) (h1 : 1+c*k+d*h=0) (h2 : 1+c*g+d*f=0)
    (h3 : k+g+d=0) (h4 : h+f+c=0) : c*d=1 ∧ f*g=1 := by
  constructor
  · linear_combination (-1/2 : ℂ)*h1+(-1/2 : ℂ)*h2+(c/2)*h3+(d/2)*h4
  · linear_combination (-1/2 : ℂ)*h0+(-1/2 : ℂ)*h2+(f/2)*h3+(g/2)*h4
theorem cube (c d f g : ℂ) (hcd : c*d=1) (hfg : f*g=1)
    (h2 : 1+c*g+d*f=0) : (c*g)^2+c*g+1=0 := by
  linear_combination (c*g)*h2-(f*g)*hcd-hfg
theorem parameter_nonzero (c d f g : ℂ) (hcd : c*d=1) (hfg : f*g=1) : c*g≠0 := by
  have hc : c≠0 := by intro h; rw [h] at hcd; norm_num at hcd
  have hg : g≠0 := by intro h; rw [h] at hfg; norm_num at hfg
  exact mul_ne_zero hc hg
theorem cleared_determinant (c d f g h k : ℂ)
    (hcd : c*d=1) (hfg : f*g=1) (h3 : k+g+d=0) (h4 : h+f+c=0) :
    (c*g)^2*(matrix c d f g h k).det=
      2*((c*g)^2-3*(c*g)+1)*(3*(c*g)^2+7*(c*g)+3) := by
  have hk : k=-g-d := by linear_combination h3
  have hh : h=-f-c := by linear_combination h4
  rw [determinant_polynomial,hk,hh]
  linear_combination (-12*c^2*f*g^3 - 8*c^2*g^2 + 6*c*d*f^2*g^2 - 4*c*f*g^2 + 6*f^2*g^2)*hcd+(-20*c^2*g^2 - 4*c*g + 6*f*g + 6)*hfg
theorem displayed_determinant (c d f g h k : ℂ)
    (hcd : c*d=1) (hfg : f*g=1) (h3 : k+g+d=0) (h4 : h+f+c=0) :
    (matrix c d f g h k).det=
      2*((c*g)^2-3*(c*g)+1)*(3*(c*g)^2+7*(c*g)+3)/(c*g)^2 := by
  apply (eq_div_iff (pow_ne_zero 2 (parameter_nonzero c d f g hcd hfg))).2
  linear_combination cleared_determinant c d f g h k hcd hfg h3 h4
theorem numerator_reduction (t : ℂ) (ht : t^2+t+1=0) :
    2*(t^2-3*t+1)*(3*t^2+7*t+3)=-32*t^2 := by
  linear_combination (6*t^2 - 10*t + 6)*ht
theorem determinant_minus32 (c d f g h k : ℂ)
    (h0 : 1+f*k+g*h=0) (h1 : 1+c*k+d*h=0) (h2 : 1+c*g+d*f=0)
    (h3 : k+g+d=0) (h4 : h+f+c=0) : (matrix c d f g h k).det=-32 := by
  have hp := products c d f g h k h0 h1 h2 h3 h4
  have ht := cube c d f g hp.1 hp.2 h2
  have hD := cleared_determinant c d f g h k hp.1 hp.2 h3 h4
  have hN := numerator_reduction (c*g) ht
  have he : (c*g)^2*((matrix c d f g h k).det+32)=0 := by
    linear_combination hD+hN
  have hf := (mul_eq_zero.mp he).resolve_left
    (pow_ne_zero 2 (parameter_nonzero c d f g hp.1 hp.2))
  linear_combination hf
end
end MainTheory.Orbit30NormalizedDeterminant
