"""Connect the literal six monomials and coefficient matrix to actual hafnians."""
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
w,t=s.symbols('omega tau'); xs=s.symbols('x0:4'); r=(*xs,0)
f=1+w+w*w
M=s.Matrix([[0,0,0,-1,w+1,-w],[0,-1,-w,0,0,w+1],
 [-1,0,w+1,0,-w,0],[-w,w+1,0,-1,0,0],[w+1,-w,-1,-1,-w,w+1]])
X=s.Matrix([[0,1,1,1,1],[0,0,t,t*w,t*w*w],[0,0,0,t*w*w,t*w],
 [0,0,0,0,t],[0,0,0,0,0]])
v=s.Matrix([xs[0]*xs[1],xs[0]*xs[2],xs[0]*xs[3],xs[1]*xs[2],xs[1]*xs[3],xs[2]*xs[3]])
Y=lambda i,j:(r[i]+r[j])*X[i,j]
quot=[]
for i in range(5):
    a,b,c,d=[j for j in range(5) if j!=i]
    H=Y(a,b)*Y(c,d)+Y(a,c)*Y(b,d)+Y(a,d)*Y(b,c)
    q,rem=s.div(s.expand(H-(t*t if i==0 else t)*(M*v)[i]),f,w)
    assert s.expand(rem)==0
    quot.append(str(s.expand(q)).replace('**','^'))
out=['''import MainTheory.Orbit7XiMatrix

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
  ((! [x0,x1,x2,x3,0] : Fin 5 → ℂ) e.1+(! [x0,x1,x2,x3,0] : Fin 5 → ℂ) e.2)*
    chart tau omega e.1 e.2

theorem coefficient_equations (tau omega x0 x1 x2 x3 : ℂ)
    (hw : 1+omega+omega^2=0) (i : Fin 5) :
    Hafnian5 (point tau omega x0 x1 x2 x3) i =
      (if i=0 then tau^2 else tau)*
        (coefficients omega).mulVec (monomials x0 x1 x2 x3) i := by
  fin_cases i <;> simp [Hafnian5,point,chart,coefficients,monomials,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
'''.replace('! [','![')]
for q in quot:out.append('  · linear_combination ('+q+')*hw\n')
out.append('''
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
''')
(ROOT/'MainTheory/Orbit7XiEquations.lean').write_text(''.join(out),encoding='utf-8')
print('Wrote five actual hafnian/coefficient identities and equal-product consequence.')
