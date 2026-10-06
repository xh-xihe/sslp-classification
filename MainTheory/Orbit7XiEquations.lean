import MainTheory.Orbit7XiMatrix

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit7XiEquations

open SixQubit.Orbit7Universal MainTheory.Orbit7XiMatrix

noncomputable def monomials (x0 x1 x2 x3 : ℂ) : Fin 6 → ℂ :=
  ![x0*x1,x0*x2,x0*x3,x1*x2,x1*x3,x2*x3]

noncomputable def chart (tau omega : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0,1,1,1,1; 0,0,tau,tau*omega,tau*omega^2;
    0,0,0,tau*omega^2,tau*omega; 0,0,0,0,tau; 0,0,0,0,0]

noncomputable def point (tau omega x0 x1 x2 x3 : ℂ) (e : Fin 5 × Fin 5) : ℂ :=
  ((![x0,x1,x2,x3,0] : Fin 5 → ℂ) e.1+(![x0,x1,x2,x3,0] : Fin 5 → ℂ) e.2)*
    chart tau omega e.1 e.2

theorem coefficient_equations (tau omega x0 x1 x2 x3 : ℂ)
    (hw : 1+omega+omega^2=0) (i : Fin 5) :
    Hafnian5 (point tau omega x0 x1 x2 x3) i =
      (if i=0 then tau^2 else tau)*
        (coefficients omega).mulVec (monomials x0 x1 x2 x3) i := by
  fin_cases i <;> simp [Hafnian5,point,chart,coefficients,monomials,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · linear_combination (omega^2*tau^2*x1*x2 + omega^2*tau^2*x1*x3 - omega*tau^2*x1*x2 - omega*tau^2*x1*x3 + tau^2*x1*x2 + tau^2*x2*x3)*hw
  · linear_combination (tau*x0*x2 + tau*x0*x3)*hw
  · linear_combination (tau*x0*x1 + tau*x1*x3)*hw
  · linear_combination (tau*x0*x1 + tau*x1*x2)*hw
  · linear_combination (tau*x0*x2 + tau*x0*x3 + tau*x1*x2 + tau*x1*x3)*hw

theorem products_equal (tau omega x0 x1 x2 x3 : ℂ)
    (ht : tau ≠ 0) (hw : 1+omega+omega^2=0)
    (hH : ∀ i,Hafnian5 (point tau omega x0 x1 x2 x3) i=0) :
    ∃ t : ℂ, monomials x0 x1 x2 x3 = fun _ => t := by
  apply (kernel_iff omega hw _).mp
  funext i
  have h := hH i
  rw [coefficient_equations tau omega x0 x1 x2 x3 hw] at h
  have hf : (if i=0 then tau^2 else tau) ≠ 0 := by
    split_ifs
    · exact pow_ne_zero _ ht
    · exact ht
  exact (mul_eq_zero.mp h).resolve_left hf

end MainTheory.Orbit7XiEquations
