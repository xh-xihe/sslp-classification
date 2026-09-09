"""Generate small ring certificates for the literal exceptional-vertex matrix."""
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
w=s.symbols('omega'); f=w*w+w+1
M=s.Matrix([[0,0,0,-1,w+1,-w],[0,-1,-w,0,0,w+1],
 [-1,0,w+1,0,-w,0],[-w,w+1,0,-1,0,0],[w+1,-w,-1,-1,-w,w+1]])
def reduce(x):
    a,b=s.fraction(s.cancel(x))
    return s.rem(a*s.invert(b,f,w),f,w)
R=M[:,:5].inv().applyfunc(reduce).col_join(s.zeros(1,5))
Q=(M*R-s.eye(5)).applyfunc(lambda x:s.div(s.expand(x),f,w)[0])
K=s.eye(6)
for i in range(6):K[i,5]-=1
QK=(R*M-K).applyfunc(lambda x:s.div(s.expand(x),f,w)[0])
assert (M*R-s.eye(5)-f*Q).applyfunc(s.expand)==s.zeros(5)
assert (R*M-K-f*QK).applyfunc(s.expand)==s.zeros(6)
def expr(x):return str(s.expand(x)).replace('**','^')
def matrix(name,A):
    param='omega' if w in A.free_symbols else '_omega'
    return f'noncomputable def {name} ({param} : ℂ) : Matrix (Fin {A.rows}) (Fin {A.cols}) ℂ :=\n  !!['+';\n    '.join(','.join(expr(A[i,j]) for j in range(A.cols)) for i in range(A.rows))+']\n'
out=['import MainTheory.Orbit7JacobianKernel','', 'set_option autoImplicit false',
 'set_option maxHeartbeats 4000000','', 'namespace MainTheory.Orbit7XiMatrix','',
 matrix('coefficients',M),matrix('rightInverse',R),matrix('rightError',Q),
 matrix('kernelProjector',K),matrix('kernelError',QK)]
for name,lhs,rhs,err in [('right_inverse','coefficients omega * rightInverse omega','1','rightError'),
 ('kernel_projector','rightInverse omega * coefficients omega','kernelProjector omega','kernelError')]:
    out.extend([f'theorem {name} (omega : ℂ) (hw : 1+omega+omega^2=0) :',
      f'    {lhs} = {rhs} := by',
      f'  have he : {lhs} - {rhs} = (1+omega+omega^2) • {err} omega := by',
      '    ext i j','    fin_cases i <;> fin_cases j <;>',
      f'      simp [coefficients,rightInverse,{"kernelProjector," if name=="kernel_projector" else ""}{err}] <;> ring',
      '  rw [hw,zero_smul] at he','  exact sub_eq_zero.mp he',''])
out.extend(['theorem rank_five (omega : ℂ) (hw : 1+omega+omega^2=0) :',
 '    (coefficients omega).rank=5 := by',
 '  have h := Matrix.rank_mul_le_left (coefficients omega) (rightInverse omega)',
 '  rw [right_inverse omega hw,Matrix.rank_one] at h',
 '  exact Nat.le_antisymm (Matrix.rank_le_card_height _) h','',
 'theorem kernel_iff (omega : ℂ) (hw : 1+omega+omega^2=0) (v : Fin 6 → ℂ) :',
 '    (coefficients omega).mulVec v=0 ↔ ∃ t : ℂ, v=fun _ => t := by',
 '  constructor',
 '  · intro h',
 '    have hh := congrArg (fun z => (rightInverse omega).mulVec z) h',
 '    change (rightInverse omega).mulVec ((coefficients omega).mulVec v) = (rightInverse omega).mulVec 0 at hh',
 '    rw [Matrix.mulVec_mulVec,kernel_projector omega hw,Matrix.mulVec_zero] at hh',
 '    refine ⟨v 5,?_⟩','    funext i','    have hi := congrFun hh i',
 '    fin_cases i <;> simp [kernelProjector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hi ⊢',
 '    all_goals linear_combination hi',
 '  · rintro ⟨t,rfl⟩','    funext i',
 '    fin_cases i <;> simp [coefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring','',
 'end MainTheory.Orbit7XiMatrix',''])
(ROOT/'MainTheory/Orbit7XiMatrix.lean').write_text('\n'.join(out),encoding='utf-8')
print('Wrote literal xi matrix, right inverse, and kernel projector certificates.')
