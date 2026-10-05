"""Emit the complete real iff between balanced moments and the full moment system."""
import argparse
import json
from pathlib import Path
import re
import sympy as s

ROOT = Path(__file__).resolve().parents[2]


def fin(i):
    return f'⟨{i},by decide⟩'


def vec(items):
    return '!['+','.join(items)+']'


def number(x):
    return str(x) if x.q==1 else f'({x.p}/{x.q})'


def multipliers(matrix,target):
    result = matrix.T.gauss_jordan_solve(target)[0]
    symbols = set().union(*(v.free_symbols for v in result))
    return result.subs({v:0 for v in symbols})


def generate():
    data=json.loads((ROOT/'results/orbit31-support-candidates-20261005.json').read_text(encoding='utf8'))
    M=s.Matrix(data['matrix']); b=s.Matrix([1]+[s.Rational(1,2)]*6)
    permutation=[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12]
    variables=s.symbols(' '.join('q'+str(j) for j in range(16))+' '+
                        ' '.join('r'+str(j) for j in range(16)))
    p=s.symbols(' '.join('p'+str(j) for j in range(16)))
    local={str(v):v for v in variables}
    substitution={variables[j]:p[permutation[j]] for j in range(16)}
    substitution.update({variables[16+j]:p[permutation[15-j]] for j in range(16)})
    source=(ROOT/'SixQubit/Orbit31.lean').read_text(encoding='utf8')
    fields=re.findall(r'^  (n[01]|m[1-6]|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
    expressions=[s.expand((s.sympify(lhs,locals=local)-s.sympify(rhs,locals=local)).subs(substitution))
                 for _,lhs,rhs in fields]
    A=s.Matrix([[e.coeff(v) for v in p] for e in expressions])
    constants=s.Matrix([-e.subs({v:0 for v in p}) for e in expressions])
    assert A.rank()==M.rank()==7
    q=[f'p {fin(j)}' for j in permutation]
    r=[f'p {fin(j)}' for j in reversed(permutation)]
    system='MomentSystem '+' '.join('('+v+')' for v in q+r)
    text=f'''import MainTheory.Orbit31SupportBase
import SixQubit.Orbit31MomentNormal

/-! The seven balanced real moments are exactly the complete diagonal
moment system after complementary probability equality. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit31BalancedMomentIff
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.Orbit31SupportBase
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

def nativeQ (p : Fin 16 → ℝ) : Fin 16 → ℝ := {vec(q)}
def nativeR (p : Fin 16 → ℝ) : Fin 16 → ℝ := {vec(r)}

theorem q_table (p : Fin 16 → ℝ) (j : Fin 16) : nativeQ p (nativeIndex j) = p j := by
  fin_cases j <;> rfl
theorem r_complement (p : Fin 16 → ℝ) : nativeR p =
    ![(nativeQ p) 15,(nativeQ p) 14,(nativeQ p) 13,(nativeQ p) 12,
      (nativeQ p) 11,(nativeQ p) 10,(nativeQ p) 9,(nativeQ p) 8,
      (nativeQ p) 7,(nativeQ p) 6,(nativeQ p) 5,(nativeQ p) 4,
      (nativeQ p) 3,(nativeQ p) 2,(nativeQ p) 1,(nativeQ p) 0] := by
  funext j
  fin_cases j <;> rfl

theorem full_moments_of_feasible (p : Fin 16 → ℝ) (hp : Feasible M b p) :
    VectorMomentSystem (nativeQ p) (nativeR p) := by
'''
    for i in range(7):
        text+=f'  have h{i} := congrFun hp.equations {fin(i)}\n'
    text+='  norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at '+' '.join('h'+str(i) for i in range(7))+'\n'
    text+=f'  change {system}\n  constructor\n'
    for e,constant in zip(expressions,constants):
        coefficients=multipliers(M,s.Matrix([e.coeff(v) for v in p]))
        assert (coefficients.T*b)[0]==constant
        if all(v==0 for v in coefficients):
            text+='  · ring\n'
        else:
            proof=' + '.join(number(v)+' * h'+str(i) for i,v in enumerate(coefficients) if v)
            text+='  · norm_num\n    linear_combination '+proof+'\n'
    for j in permutation+list(reversed(permutation)):
        text+=f'  · exact hp.nonneg {fin(j)}\n'
    text+=f'''
theorem feasible_of_full_moments (p : Fin 16 → ℝ)
    (hm : VectorMomentSystem (nativeQ p) (nativeR p)) : Feasible M b p := by
  change {system} at hm
  constructor
  · intro j
    fin_cases j
'''
    for j in range(16):
        text+=f'    · exact hm.nq{permutation[j]}\n'
    coefs=[multipliers(A,M.row(i).T) for i in range(7)]
    for i,coefficients in enumerate(coefs):
        assert (coefficients.T*constants)[0]==b[i]
    needed=sorted({i for row in coefs for i,v in enumerate(row) if v})
    text+='  ·\n'
    # Separate hypotheses avoid unfolding a structure into a conjunction.
    text+='\n'.join(f'    have g{i} := hm.{fields[i][0]}' for i in needed)+'\n'
    text+='    norm_num at '+' '.join('g'+str(i) for i in needed)+'\n'
    text+='    ext i\n    fin_cases i\n'
    for coefficients in coefs:
        proof=' + '.join(number(v)+' * g'+str(i) for i,v in enumerate(coefficients) if v)
        text+='    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]\n'
        text+='      linear_combination '+proof+'\n'
    text+='''
theorem feasible_iff_full_moments (p : Fin 16 → ℝ) :
    Feasible M b p ↔ VectorMomentSystem (nativeQ p) (nativeR p) :=
  ⟨full_moments_of_feasible p,feasible_of_full_moments p⟩

end
end MainTheory.Orbit31BalancedMomentIff
'''
    return text


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    content=generate()
    path=ROOT/'MainTheory/Orbit31BalancedMomentIff.lean'
    if args.check:
        if path.read_text(encoding='utf8')!=content:
            raise SystemExit('Generated balanced moment iff differs')
    else:
        path.write_text(content,encoding='utf8',newline='\n')
    print('Prepared full real moment iff; Lean acceptance remains required.')
