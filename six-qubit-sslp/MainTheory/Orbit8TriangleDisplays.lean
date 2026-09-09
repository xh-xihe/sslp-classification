import SixQubit.Orbit8UniversalNormalizeAlgebra

set_option autoImplicit false

namespace MainTheory.Orbit8TriangleDisplays

theorem vertex_scaling (a b c d xab xac xad xbc xbd xcd : ℂ) :
    (a*b*xab)*(c*d*xcd)+(a*c*xac)*(b*d*xbd)+(a*d*xad)*(b*c*xbc)=
      (a*b*c*d)*(xab*xcd+xac*xbd+xad*xbc) := by ring

theorem scaling_zero_iff (a b c d xab xac xad xbc xbd xcd : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (a*b*xab)*(c*d*xcd)+(a*c*xac)*(b*d*xbd)+(a*d*xad)*(b*c*xbc)=0 ↔
      xab*xcd+xac*xbd+xad*xbc=0 := by
  rw [vertex_scaling,mul_eq_zero]
  simp [ha,hb,hc,hd]

theorem star_normalize (v : Fin 6 → Fin 6 → ℂ)
    (h : ∀ j : Fin 6,j ≠ 0 → v 0 j ≠ 0) :
    ∃ d : Fin 6 → ℂ,(∀ i,d i ≠ 0) ∧ ∀ j : Fin 6,j ≠ 0 → d 0*d j*v 0 j=1 := by
  classical
  refine ⟨fun i => if i=0 then 1 else (v 0 i)⁻¹,?_,?_⟩
  · intro i
    by_cases hi : i=0 <;> simp [hi,h]
  · intro j hj
    simp [hj,h j hj]

theorem normalized_triangle (xij xik xjk : ℂ) :
    1*xjk+1*xik+1*xij=xij+xik+xjk := by ring

section Seven
variable (x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 : ℂ)
variable (t134 : x13+x14+x34=0) (t135 : x13+x15+x35=0)
  (t145 : x14+x15+x45=0) (t234 : x23+x24+x34=0)
  (t235 : x23+x25+x35=0) (t245 : x24+x25+x45=0) (t345 : x34+x35+x45=0)

include t134 t135 t145 t234 t235 t245 t345

theorem seven_triangle_solution :
    x23=x13 ∧ x45=x13 ∧ x24=x14 ∧ x35=x14 ∧
      x15=-(x13+x14) ∧ x25=-(x13+x14) ∧ x34=-(x13+x14) := by
  have h34 : x34 = -x13-x14 := by linear_combination t134
  have h35 : x35 = x14 := by
    linear_combination (1/2 : ℂ)*(t345-t134+t135-t145)
  have h45 : x45 = x13 := by
    linear_combination (1/2 : ℂ)*(t345-t134-t135+t145)
  have h15 : x15 = -x13-x14 := by linear_combination t135-h35
  have h23 : x23 = x13 := by
    linear_combination (1/2 : ℂ)*(t234-t134+t235-t245-h35+h45)
  have h24 : x24 = x14 := by
    linear_combination (1/2 : ℂ)*(t234-t134-t235+t245+h35-h45)
  have h25 : x25 = -x13-x14 := by linear_combination t235-h23-h35
  exact ⟨h23,h45,h24,h35,by linear_combination h15,
    by linear_combination h25,by linear_combination h34⟩

theorem seven_hafnian_equations
    (q1345 : x13*x45+x14*x35+x15*x34=0)
    (q1235 : x12*x35+x13*x25+x15*x23=0)
    (q1245 : x12*x45+x14*x25+x15*x24=0) :
    x13^2+x13*x14+x14^2=0 ∧
      x12*x14-2*x13*(x13+x14)=0 ∧ x12*x13-2*x14*(x13+x14)=0 := by
  rcases seven_triangle_solution x13 x14 x15 x23 x24 x25 x34 x35 x45
    t134 t135 t145 t234 t235 t245 t345 with ⟨h23,h45,h24,h35,h15,h25,h34⟩
  rw [h45,h35,h15,h34] at q1345
  rw [h35,h25,h15,h23] at q1235
  rw [h45,h25,h15,h24] at q1245
  exact ⟨by linear_combination q1345/2,by linear_combination q1235,
    by linear_combination q1245⟩

theorem nine_triangle_solution (t124 : x12+x14+x24=0) (t125 : x12+x15+x25=0) :
    x13=x12 ∧ x23=x12 ∧ x45=x12 ∧ x14= -x12/2 ∧ x15= -x12/2 ∧
      x24= -x12/2 ∧ x25= -x12/2 ∧ x34= -x12/2 ∧ x35= -x12/2 := by
  rcases seven_triangle_solution x13 x14 x15 x23 x24 x25 x34 x35 x45
    t134 t135 t145 t234 t235 t245 t345 with ⟨h23,h45,h24,h35,h15,h25,h34⟩
  have ha : x13=x12 := by linear_combination -(t124+t125-h24-h15-h25)/2
  have hb : x14= -x12/2 := by linear_combination (t124-h24)/2
  exact ⟨ha,by linear_combination h23+ha,by linear_combination h45+ha,hb,
    by linear_combination h15-ha-hb,by linear_combination h24+hb,
    by linear_combination h25-ha-hb,by linear_combination h34-ha-hb,
    by linear_combination h35+hb⟩

end Seven

theorem four_support_hafnian (t : ℂ) (ht : t ≠ 0) :
    t*t+(-t/2)*(-t/2)+(-t/2)*(-t/2)=(3/2 : ℂ)*t^2 ∧ (3/2 : ℂ)*t^2 ≠ 0 := by
  constructor
  · ring
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ ht)

end MainTheory.Orbit8TriangleDisplays
