"""Generate the actual active orbit-29 moment rank and positive witness."""
from pathlib import Path
import re
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def vec(xs):return '!['+','.join(map(str,xs))+']'
def matrix(m):return vec(vec('('+str(x)+')' for x in row) for row in m.tolist())
source=(ROOT/'SixQubit/Orbit29.lean').read_text(encoding='utf8')
names=re.search(r'structure MomentSystem \((.+?) : Real\)',source).group(1)
v=s.symbols(names)
fields=re.findall(r'^  (n[01]|m[1-6](?:[1-6])?|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
loc={str(x):x for x in v}
full=s.Matrix([[s.expand(s.sympify(a,locals=loc)-s.sympify(b,locals=loc)).coeff(x) for x in v] for _,a,b in fields])
A=full[:,2:]
columns=list(A.rref()[1]);rows=list(A[:,columns].T.rref()[1]);r=len(columns)
assert r==22
minor=A.extract(rows,columns);desired=minor.det()
L,U,sw=minor.LUdecomposition();P=s.eye(r)
for i,j in sw:P.row_swap(i,j)
perm=[next(j for j in range(r) if P[i,j]) for i in range(r)]
inv=[perm.index(j) for j in range(r)]
sign=(-1)**len(sw);ud=desired*sign
B=A[:,columns];T=minor.inv()*A[rows,:]
assert B*T==A and P*minor==L*U
orbit=29;n=14;m=16
template=(ROOT/'tools/verification/generate_order_three_printed_ranks.py').read_text(encoding='utf8')
template=template.split("parts.append(f'''\n",1)[1].split("\n''')",1)[0]
template=template.replace('MainTheory.OrderThreePrintedMoments.Orbit{orbit}.','MainTheory.Orbit29MomentRank.Orbit{orbit}.')
template=template.replace('namespace Orbit{orbit}', '''namespace Orbit{orbit}
def bottom : Fin 14 → SS.BitString 6 := {vec('SixQubit.Orbit29.y'+str(i) for i in range(2,16))}
def top : Fin 16 → SS.BitString 6 := {vec('SixQubit.Orbit29.z'+str(i) for i in range(16))}
def fullMatrixZ : Matrix (Fin 23) (Fin 32) ℤ := {matrix(full)}
def activeColumns : Fin 30 → Fin 32 := fun i => ⟨i.val+2,by omega⟩
''',1)
body=eval('f'+repr(template))
center=[s.Rational(1,16)]*12+[s.Rational(1,8)]*2+[s.Rational(1,32)]*6+[s.Rational(3,32)]*2+[s.Rational(1,32)]*2+[s.Rational(3,32)]*6
rhs=[1,1]+[0]*21
assert len(center)==30 and A*s.Matrix(center)==s.Matrix(rhs) and min(center)>0
extra=f'''
namespace Orbit29
def fullMatrixQ : Matrix (Fin 23) (Fin 32) ℚ := fullMatrixZ.map (Int.castRingHom ℚ)
def fullMatrixR : Matrix (Fin 23) (Fin 32) ℝ := fullMatrixZ.map (Int.castRingHom ℝ)
theorem active_matrix : matrixQ=fullMatrixQ.submatrix id activeColumns := by decide +kernel
def centerQ : Fin 30 → ℚ := {vec('('+str(x)+')' for x in center)}
def rhsQ : Fin 23 → ℚ := {vec(rhs)}
theorem positive_witness : matrixQ.mulVec centerQ=rhsQ ∧ (∀ i, 0 < centerQ i) := by decide +kernel
def centerR : Fin 30 → ℝ := fun i => (centerQ i : ℝ)
def rhsR : Fin 23 → ℝ := fun i => (rhsQ i : ℝ)
theorem full_real_cast : fullMatrixR=fullMatrixQ.map (Rat.castHom ℝ) := by
  ext i j
  simp [fullMatrixR,fullMatrixQ,Matrix.map_apply]
theorem real_matrix_cast : matrixR=matrixQ.map (Rat.castHom ℝ) := by
  ext i j
  simp [matrixR,matrixQ,Matrix.map_apply]
theorem real_active_matrix : matrixR=fullMatrixR.submatrix id activeColumns := by
  rw [real_matrix_cast,full_real_cast]
  have h := congrArg (fun M : Matrix (Fin 23) (Fin 30) ℚ => M.map (Rat.castHom ℝ)) active_matrix
  exact h
theorem real_witness : matrixR.mulVec centerR=rhsR ∧ (∀ i, 0 < centerR i) := by
  constructor
  · rw [real_matrix_cast]
    funext i
    have he := RingHom.map_mulVec (Rat.castHom ℝ) matrixQ centerQ i
    rw [positive_witness.1] at he
    change (rhsQ i : ℝ)=(matrixQ.map (Rat.castHom ℝ)).mulVec centerR i at he
    exact he.symm
  · intro i
    change (0 : ℝ) < (centerQ i : ℝ)
    exact_mod_cast positive_witness.2 i
theorem active_polytope_dimension :
    Module.finrank ℝ (affineSpan ℝ (LPDimension.feasibleSet matrixR rhsR)).direction=8 := by
  have h := LPDimension.finrank_eq_card_sub_rank_of_positive matrixR rhsR centerR
    real_witness.1 real_witness.2
  rw [rank_exact] at h
  simpa using h
end Orbit29
'''
header='''import SixQubit.Orbit29
import MainTheory.LPDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit29MomentRank
open scoped BigOperators Matrix
noncomputable section
def coordinatePairs : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
'''
lean=header+body+extra+'\nend\nend MainTheory.Orbit29MomentRank\n'
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/Orbit29MomentRank.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Active rank',r,'signed minor',desired,'kernel and active affine dimension',30-r)
