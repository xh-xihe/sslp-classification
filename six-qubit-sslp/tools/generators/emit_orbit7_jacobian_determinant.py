"""Small Laplace certificates avoid recursively nested finite-index normalization."""
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
t,w=s.symbols('tau omega')
matrix=s.Matrix([[0,0,0,t,t*w**2],[0,t,t*w,0,0],[t,0,t*w**2,0,1],
 [t*w,t*w**2,0,1,1],[t*w**2,t*w,t,1,0]])
def expr(x):return str(s.expand(x)).replace('**','^')
def mat(M):return '!!['+';\n    '.join(','.join(expr(M[i,j]) for j in range(M.cols)) for i in range(M.rows))+']'
out=['import Mathlib','', 'set_option autoImplicit false','set_option maxRecDepth 100000','',
 'namespace MainTheory.Orbit7JacobianDeterminant','']
cache={}; serial=0
def emit(M):
    global serial
    key=tuple(M)
    if (M.rows,key) in cache:return cache[M.rows,key]
    n=M.rows
    children={j:emit(M.minor_submatrix(0,j)) for j in range(n) if M[0,j]!=0 and n>1}
    name=f'matrix{serial}';serial+=1
    cache[M.rows,key]=name
    params=('tau' if t in M.free_symbols else '_tau')+' '+('omega' if w in M.free_symbols else '_omega')
    out.extend([f'noncomputable def {name} ({params} : ℂ) : Matrix (Fin {n}) (Fin {n}) ℂ :=',
      '  '+mat(M),'',
      f'theorem {name}_det (tau omega : ℂ) : ({name} tau omega).det = {expr(M.det())} := by'])
    if n==1:
        out.extend(['  rw [Matrix.det_fin_one]','  rfl',''])
        return name
    for j,child in children.items():
        out.extend([f'  have hs{j} : ({name} tau omega).submatrix Fin.succ ({j} : Fin {n}).succAbove = {child} tau omega := by',
          '    ext i k','    fin_cases i; fin_cases k; rfl' if n==2 else '    fin_cases i <;> fin_cases k <;> rfl'])
    terms=[f'(-1 : ℂ)^{j}*({expr(M[0,j])})*({expr(M.minor_submatrix(0,j).det())})' if M[0,j]!=0 else '0' for j in range(n)]
    out.extend([f'  have hrow : ∀ j : Fin {n}, (-1 : ℂ)^j.val*{name} tau omega 0 j*',
       f'      (({name} tau omega).submatrix Fin.succ j.succAbove).det =',
       '        (!['+','.join(terms)+f'] : Fin {n} → ℂ) j := by',
       '    intro j','    fin_cases j'])
    for j in range(n):
        if M[0,j]==0:
            out.extend([f'    · change (-1 : ℂ)^{j}*0*_ = 0','      ring'])
        else:
            out.extend([f'    · change (-1 : ℂ)^{j}*({expr(M[0,j])})*',
              f'        (({name} tau omega).submatrix Fin.succ ({j} : Fin {n}).succAbove).det = {terms[j]}',
              f'      rw [hs{j},{children[j]}_det]'])
    out.extend(['  rw [Matrix.det_succ_row_zero]','  simp_rw [hrow]',
      '  norm_num [Fin.sum_univ_succ]'])
    if name not in {'matrix1','matrix4','matrix8','matrix12'}:
        out.append('  ring')
    out.append('')
    return name
name=emit(matrix)
out.extend([f'alias determinant_raw := {name}_det','',
 'end MainTheory.Orbit7JacobianDeterminant',''])
(ROOT/'MainTheory/Orbit7JacobianDeterminant.lean').write_text('\n'.join(out),encoding='utf-8')
print('Wrote',serial,'small Laplace certificates; root',name)
