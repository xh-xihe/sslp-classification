"""Emit the literal hafnian Jacobian and a displayed five-column minor."""
from itertools import combinations
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
edges=list(combinations(range(5),2))
def e(x): return f'({x[0]},{x[1]})'
rows=[]
for i in range(5):
    a,b,c,d=[j for j in range(5) if j!=i]
    row={}
    for f,g in [((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))]:
        row[f]=g;row[g]=f
    rows.append('!['+','.join('x '+e(row[f]) if f in row else '0' for f in edges)+']')
text='''import MainTheory.Orbit7MatchingDisplays
import MainTheory.Orbit7JacobianDeterminant

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit7Jacobian

open SixQubit.Orbit7Universal MainTheory.Orbit7MatchingDisplays

'''
text+='def edges : Fin 10 → Edge := !['+','.join(map(e,edges))+']\n\n'
text+='noncomputable def jacobian (x : Edge → ℂ) : Matrix (Fin 5) (Fin 10) ℂ :=\n  !['+',\n    '.join(rows)+']\n\n'
text+='''theorem update_formula (x : Edge → ℂ) (i : Fin 5) (j : Fin 10) (t : ℂ) :
    Hafnian5 (Function.update x (edges j) (x (edges j)+t)) i =
      Hafnian5 x i + t * jacobian x i j := by
  fin_cases i <;> fin_cases j <;> simp [Hafnian5,jacobian,edges] <;> ring

theorem derivative_entry (x : Edge → ℂ) (i : Fin 5) (j : Fin 10) :
    HasDerivAt (fun t : ℂ => Hafnian5 (Function.update x (edges j) (x (edges j)+t)) i)
      (jacobian x i j) 0 := by
  have h := (hasDerivAt_const (0 : ℂ) (Hafnian5 x i)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const (jacobian x i j))
  have he : (fun t : ℂ => Hafnian5 (Function.update x (edges j) (x (edges j)+t)) i) =
      fun t => Hafnian5 x i + t * jacobian x i j := funext (update_formula x i j)
  rw [he]
  simpa only [Pi.add_apply,one_mul,zero_add] using h

noncomputable def minor (tau omega : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0,0,0,tau,tau*omega^2;
     0,tau,tau*omega,0,0;
     tau,0,tau*omega^2,0,1;
     tau*omega,tau*omega^2,0,1,1;
     tau*omega^2,tau*omega,tau,1,0]

theorem minor_determinant_raw (tau omega : ℂ) :
    (minor tau omega).det = -tau^4*omega^6+3*tau^4*omega^5-tau^4*omega^3+
      2*tau^4*omega^2+tau^4*omega-tau^4 := by
  have he : minor tau omega = MainTheory.Orbit7JacobianDeterminant.matrix19 tau omega := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [minor,MainTheory.Orbit7JacobianDeterminant.matrix19] <;> ring
  rw [he]
  linear_combination MainTheory.Orbit7JacobianDeterminant.determinant_raw tau omega

theorem minor_determinant (tau omega : ℂ) (hw : 1+omega+omega^2=0) :
    (minor tau omega).det = -4*tau^4*(omega+2) := by
  rw [minor_determinant_raw]
  linear_combination tau^4*(-omega^4+4*omega^3-3*omega^2-2*omega+7)*hw

end MainTheory.Orbit7Jacobian
'''
(ROOT/'MainTheory/Orbit7Jacobian.lean').write_text(text,encoding='utf-8')
print('Wrote Orbit7Jacobian.lean')
