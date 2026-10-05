"""Literal complex character reflection, checked by Lean polynomial algebra."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
import sympy as s
C=s.Matrix([[1,1,1,1,1,1],[1,1,-1,-1,-1,-1],[1,-1,1,-1,-1,-1],
            [1,-1,-1,1,1,-1],[1,-1,-1,1,-1,1],[1,-1,-1,-1,1,1]])
def matrix(M):
    return '!['+','.join('!['+','.join(str(x) for x in M.row(i))+']' for i in range(M.rows))+']'
lean='''import MainTheory.Orbit33PrintedReflection

/-! Complex scalar form of the actual six-block character reflection.
Only the stated linear identities are used; no no-code conclusion is invoked.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit33ScalarReflection
open scoped BigOperators Matrix
noncomputable section

def C : Matrix (Fin 6) (Fin 6) ℂ := '''+matrix(C)+'''
def inverseC : Matrix (Fin 6) (Fin 6) ℂ := '''+matrix(C.inv())+'''
def J : Matrix (Fin 6) (Fin 6) ℂ := Matrix.diagonal ![1,-1,-1,-1,-1,-1]
def R : Fin 6 → ℂ := ![3/10,1/5,1/5,1/10,1/10,1/10]

theorem inverse_left : inverseC*C=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C,inverseC,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succ]

theorem reflection_entries : inverseC*J*C=fun i j => 2*R i-(if i=j then 1 else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C,inverseC,J,R,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succ]

theorem inverse : C⁻¹=inverseC := Matrix.inv_eq_left_inv inverse_left

theorem C_cast : C=fun i j => (MainTheory.Orbit33PrintedReflection.C i j : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C,MainTheory.Orbit33PrintedReflection.C]

theorem character_rows (f g : Fin 6 → ℂ)
    (h : ∀ i, f i+g i=2*R i*(∑ j, f j)) : C.mulVec f=J.mulVec (C.mulVec g) := by
'''
for i in range(6):
    lean+=f'  have h{i} := h ⟨{i},by decide⟩\n'
lean+='  norm_num [R,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5\n'
lean+='  funext i\n  fin_cases i\n'
for i in range(6):
    lean+='  · norm_num [C,J,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Fin.succ]\n'
    coefficients=[-1]*6 if i==0 else list(C.row(i))
    lean+='    linear_combination '+' + '.join(f'({k} : ℂ) * h{j}' for j,k in enumerate(coefficients))+'\n'
lean+='''
theorem inverse_character_rows (f g : Fin 6 → ℂ)
    (h : ∀ i, f i+g i=2*R i*(∑ j, f j)) :
    f=inverseC.mulVec (J.mulVec (C.mulVec g)) := by
  rw [← character_rows f g h,Matrix.mulVec_mulVec,inverse_left,Matrix.one_mulVec]

theorem common_sum (f g : Fin 6 → ℂ)
    (h : ∀ i, f i+g i=2*R i*(∑ j, f j)) : (∑ j, f j)=(∑ j, g j) := by
'''
for i in range(6):
    lean+=f'  have h{i} := h ⟨{i},by decide⟩\n'
lean+='  norm_num [R,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5 ⊢\n'
lean+='  linear_combination -(h0+h1+h2+h3+h4+h5)\n'
lean+='\nend\nend MainTheory.Orbit33ScalarReflection\n'
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/Orbit33ScalarReflection.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
