"""Generate a kernel-checkable rank and full positive moment-polytope witness."""
from pathlib import Path
import re
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def vec(xs):return '!['+','.join(map(str,xs))+']'
def matrix(m):return vec(vec('('+str(x)+')' for x in row) for row in m.tolist())
source=(ROOT/'SixQubit/Orbit30.lean').read_text(encoding='utf8')
names=re.search(r'structure MomentSystem \((.+?) : Real\)',source).group(1)
v=s.symbols(names)
fields=re.findall(r'^  (n[01]|m[1-6](?:[1-6])?|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
loc={str(x):x for x in v}
A=s.Matrix([[s.expand(s.sympify(a,locals=loc)-s.sympify(b,locals=loc)).coeff(x) for x in v] for _,a,b in fields])
columns=list(A.rref()[1]);rows=list(A[:,columns].T.rref()[1]);r=len(columns)
assert r==23
minor=A.extract(rows,columns);desired=minor.det()
L,U,sw=minor.LUdecomposition();P=s.eye(r)
for i,j in sw:P.row_swap(i,j)
perm=[next(j for j in range(r) if P[i,j]) for i in range(r)]
inv=[perm.index(j) for j in range(r)]
sign=(-1)**len(sw);ud=desired*sign
B=A[:,columns];T=minor.inv()*A[rows,:]
assert B*T==A and P*minor==L*U
orbit=30;n=16;m=16
template=(ROOT/'tools/verification/generate_order_three_printed_ranks.py').read_text(encoding='utf8')
template=template.split("parts.append(f'''\n",1)[1].split("\n''')",1)[0]
template=template.replace('MainTheory.OrderThreePrintedMoments.Orbit{orbit}.','MainTheory.Orbit30MomentRank.Orbit{orbit}.')
template=template.replace('namespace Orbit{orbit}', '''namespace Orbit{orbit}
def bottom : Fin 16 → SS.BitString 6 := {vec('SixQubit.Orbit30.y'+str(i) for i in range(16))}
def top : Fin 16 → SS.BitString 6 := {vec('SixQubit.Orbit30.z'+str(i) for i in range(16))}
''',1)
body=eval('f'+repr(template))
prob=[s.Rational(3,40) if i in (0,1,2,4,8) else s.Rational(1,8) if i==15 else s.Rational(1,20) for i in range(16)]
center=prob+prob[::-1];rhs=[1,1]+[0]*21
assert A*s.Matrix(center)==s.Matrix(rhs) and min(center)>0
extra=f'''
namespace Orbit30
def centerQ : Fin 32 → ℚ := {vec('('+str(x)+')' for x in center)}
def rhsQ : Fin 23 → ℚ := {vec(rhs)}
theorem positive_witness : matrixQ.mulVec centerQ=rhsQ ∧ (∀ i, 0 < centerQ i) := by decide +kernel
def centerR : Fin 32 → ℝ := fun i => (centerQ i : ℝ)
def rhsR : Fin 23 → ℝ := fun i => (rhsQ i : ℝ)
theorem real_matrix_cast : matrixR=matrixQ.map (Rat.castHom ℝ) := by
  ext i j
  simp [matrixR,matrixQ,Matrix.map_apply]
theorem real_witness : matrixR.mulVec centerR=rhsR ∧ (∀ i, 0 < centerR i) := by
  constructor
  · rw [real_matrix_cast]
    funext i
    have he := RingHom.map_mulVec (Rat.castHom ℝ) matrixQ centerQ i
    rw [positive_witness.1] at he
    exact he.symm
  · intro i
    change (0 : ℝ) < (centerQ i : ℝ)
    exact_mod_cast positive_witness.2 i
theorem full_diagonal_polytope_dimension :
    Module.finrank ℝ (affineSpan ℝ (LPDimension.feasibleSet matrixR rhsR)).direction=9 := by
  have h := LPDimension.finrank_eq_card_sub_rank_of_positive matrixR rhsR centerR
    real_witness.1 real_witness.2
  rw [rank_exact] at h
  simpa using h
end Orbit30
'''
header='''import SixQubit.Orbit30
import MainTheory.LPDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit30MomentRank
open scoped BigOperators Matrix
noncomputable section
def coordinatePairs : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
'''
lean=header+body+extra+'\nend\nend MainTheory.Orbit30MomentRank\n'
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
target=ROOT/'MainTheory/Orbit30MomentRank.lean'
if args.check:
    if target.read_text(encoding='utf8')!=lean:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(lean,encoding='utf8',newline='\n')
print('Actual rank',r,'signed minor',desired,'kernel and full affine dimension',32-r)
