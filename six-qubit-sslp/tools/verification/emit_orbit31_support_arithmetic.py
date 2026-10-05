"""Emit checked actual moment data and untrusted primal/dual arithmetic inputs.

The emitted Lean propositions, including the physical KL bridge, must compile.
This stage does not prove completeness of the 65536-mask classification.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import re
import sympy as s

ROOT=Path(__file__).resolve().parents[2]


def vec(values):
    return '!['+','.join(str(v) for v in values)+']'


def num(v):
    return str(v) if v.q==1 else f'({v.p}/{v.q})'


def generate(data):
    words=[int(''.join(map(str,w)),2) for w in data['words']]
    permutation=[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12]
    matrix=data['matrix']
    base=f'''import MainTheory.MatrixPositiveSupportCertificates
import MainTheory.OrderEightSupportDisplays
import SixQubit.CodeOrbit31

/-! Actual bottom-fibre coordinates and balanced real moments for orbit 31.
No final impossibility result is used, and no real probability is rationalized.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace MainTheory.Orbit31SupportBase
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

def words : Fin 16 → ℕ := {vec(words)}
def bottom (j : Fin 16) : SS.BitString 6 := bits (words j)
def native : Fin 16 → SS.BitString 6 := {vec(['y'+str(j) for j in range(16)])}
def nativeIndex : Fin 16 → Fin 16 := {vec(permutation)}

theorem bottom_native : ∀ j, bottom j = native (nativeIndex j) := by decide +kernel
theorem bottom_fiber : Finset.univ.image bottom = S0 := by decide +kernel
theorem top_fiber : Finset.univ.image (fun j => fun k => !(bottom j k)) = S1 := by decide +kernel
theorem bottom_injective : Function.Injective bottom := by decide +kernel

def integerRows : Matrix (Fin 7) (Fin 16) ℤ := {vec([vec(row) for row in matrix])}
def actualRows : Matrix (Fin 7) (Fin 16) ℤ := fun i j =>
  if h : i.val=0 then 1 else if bottom j ⟨i.val-1,by omega⟩ then 1 else 0
theorem actual_rows : actualRows = integerRows := by decide +kernel

def rhsTwice : Fin 7 → ℤ := ![2,1,1,1,1,1,1]
def M : Matrix (Fin 7) (Fin 16) ℝ := fun i j => integerRows i j
def b : Fin 7 → ℝ := ![1,1/2,1/2,1/2,1/2,1/2,1/2]
def probabilities (c : SS.State 6 ℂ) (j : Fin 16) : ℝ := Complex.normSq (c (bottom j))

theorem probabilities_native (c : SS.State 6 ℂ) : probabilities c =
    {vec([f'Complex.normSq (c y{j})' for j in permutation])} := by
  funext j
  fin_cases j <;> rw [probabilities,bottom_native] <;> rfl

theorem physical_balanced (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Feasible M b (probabilities c) := by
  have hm := SixQubit.Orbit31.moments c d hc hd hnc hnd hkl
'''
    variables=s.symbols(' '.join('q'+str(j) for j in range(16))+' '+
                        ' '.join('r'+str(j) for j in range(16)))
    local={str(v):v for v in variables}
    source=(ROOT/'SixQubit/Orbit31.lean').read_text(encoding='utf8')
    fields=re.findall(r'^  (n[01]|m[1-6]|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
    assert len(fields)==23
    expressions=[s.expand(s.sympify(lhs,locals=local)-s.sympify(rhs,locals=local))
                 for _,lhs,rhs in fields]
    A=s.Matrix([[e.coeff(v) for v in variables] for e in expressions])
    rhs=s.Matrix([-e.subs({v:0 for v in variables}) for e in expressions])
    assert A.rank()==23
    for i,row in enumerate(matrix):
        target=s.zeros(32,1)
        for j,value in enumerate(row):
            target[permutation[j]]=value
        coefs=A.T.gauss_jordan_solve(target)[0]
        constant=1 if i==0 else s.Rational(1,2)
        assert (coefs.T*rhs)[0]==constant
        lhs=' + '.join(f'Complex.normSq (c y{j})' for j in range(16) if target[j])
        proof=' + '.join(f'{num(v)} * hm.{fields[k][0]}' for k,v in enumerate(coefs) if v)
        base+=f'  have h{i} : {lhs} = {num(s.Rational(constant))} := by\n    linear_combination {proof}\n'
    base+='''  constructor
  · intro j
    exact Complex.normSq_nonneg _
  · ext i
    fin_cases i <;> norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,
      probabilities_native,native,nativeIndex,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [h0,h1,h2,h3,h4,h5,h6]

end
end MainTheory.Orbit31SupportBase
'''
    numerators=[]
    masks=[]
    for point in data['primals']:
        values=[Fraction(*v) for v in point['point']]
        assert all((8*v).denominator==1 for v in values)
        numerators.append([int(8*v) for v in values])
        masks.append(point['mask'])
    assert len(numerators)==204 and len(data['duals'])==68
    duals=data['duals']
    arithmetic=f'''import MainTheory.Orbit31SupportBase

/-! Integer primal and dual arithmetic candidates for support certification.
This module proves each arithmetic record; the all-mask coverage is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000

namespace MainTheory.Generated.Orbit31SupportArithmetic
open MainTheory.Orbit31SupportBase
open scoped BigOperators

def primalNumerators : Fin 204 → Fin 16 → ℤ := {vec([vec(row) for row in numerators])}
def primalMasks : Fin 204 → ℕ := {vec(masks)}
def dualMultipliers : Fin 68 → Fin 7 → ℤ := {vec([vec(d['multipliers']) for d in duals])}
def dualCoefficients : Fin 68 → Fin 16 → ℤ := {vec([vec(d['coefficients']) for d in duals])}
def dualRhsTwice : Fin 68 → ℤ := {vec([d['rhs_twice'] for d in duals])}
def dualNegativeMasks : Fin 68 → ℕ := {vec([d['negative_mask'] for d in duals])}
def dualPositiveMasks : Fin 68 → ℕ := {vec([d['positive_mask'] for d in duals])}

theorem primal_valid : ∀ v : Fin 204,
    (∀ j, 0 ≤ primalNumerators v j) ∧
    (∀ i, 2 * (∑ j, integerRows i j * primalNumerators v j) = 8 * rhsTwice i) ∧
    (∀ j, (primalMasks v).testBit j.val = true ↔ 0 < primalNumerators v j) := by
  decide +kernel

theorem dual_valid : ∀ v : Fin 68,
    (∀ j, dualCoefficients v j = ∑ i, dualMultipliers v i * integerRows i j) ∧
    dualRhsTwice v = (∑ i, dualMultipliers v i * rhsTwice i) ∧
    (∀ j, (dualNegativeMasks v).testBit j.val = true ↔ dualCoefficients v j < 0) ∧
    (∀ j, (dualPositiveMasks v).testBit j.val = true ↔ 0 < dualCoefficients v j) := by
  decide +kernel

end MainTheory.Generated.Orbit31SupportArithmetic
'''
    return base,arithmetic


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidates',type=Path,default=ROOT/'results/orbit31-support-candidates-20261005.json')
    parser.add_argument('--output-dir',type=Path,default=ROOT)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    data=json.loads(args.candidates.read_text(encoding='utf8'))
    output=generate(data)
    for relative,text in zip(['MainTheory/Orbit31SupportBase.lean',
                              'MainTheory/Generated/Orbit31SupportArithmetic.lean'],output):
        path=args.output_dir/relative
        if args.check:
            if path.read_text(encoding='utf8')!=text:
                raise SystemExit('Generated source differs: '+relative)
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(text,encoding='utf8',newline='\n')
    print('Prepared actual orbit-31 moment bridge and 204/68 integer arithmetic records; all-mask proof pending')
