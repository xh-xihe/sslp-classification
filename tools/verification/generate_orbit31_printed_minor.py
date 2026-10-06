"""Discover LU data; the generated Lean certificate checks every identity."""
import ast
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
source = (ROOT/'SixQubit/Orbit31MomentRank.lean').read_text(encoding='utf8')
rows = ast.literal_eval(source.split('def momentMatrixZ')[1].split(':=',1)[1]
                        .split('private def')[0].strip().replace('![','['))
columns = list(range(16))+[31,30,29,28,24,20,16]
minor = sp.Matrix(rows)[:,columns]
lower,upper,swaps = minor.LUdecomposition()
perm = sp.eye(23)
for i,j in swaps:
    perm.row_swap(i,j)
assert perm*minor == lower*upper

def vec(xs):
    return '!['+','.join(map(str,xs))+']'

def matrix(m):
    return vec(vec('('+str(x)+')' for x in row) for row in m.tolist())

lean = '''import SixQubit.Orbit31MomentRank
import Mathlib.LinearAlgebra.Matrix.Block

/-! The literal 23-column minor printed in the SI. LU entries are untrusted
inputs until the finite identities below are checked by the Lean kernel. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
namespace MainTheory.Orbit31PrintedMinor
open scoped Matrix BigOperators
noncomputable section
'''
lean += 'def printedColumns : Fin 23 → Fin 32 := '+vec(f'⟨{j},by decide⟩' for j in columns)+'\n'
lean += '''def minorQ : Matrix (Fin 23) (Fin 23) ℚ :=
  (SixQubit.Orbit31.momentMatrixZ.submatrix id printedColumns).map (Int.castRingHom ℚ)
'''
lean += 'def P : Matrix (Fin 23) (Fin 23) ℚ := '+matrix(perm)+'\n'
lean += 'def L : Matrix (Fin 23) (Fin 23) ℚ := '+matrix(lower)+'\n'
lean += 'def U : Matrix (Fin 23) (Fin 23) ℚ := '+matrix(upper)+'\n'
lean += '''
theorem factorization : P*minorQ=L*U := by
  have he : ∀ i j : Fin 23, (P*minorQ) i j=(L*U) i j := by decide +kernel
  exact Matrix.ext he

theorem permutation_orthogonal : P*P.transpose=1 := by
  have he : ∀ i j : Fin 23, (P*P.transpose) i j=(1 : Matrix (Fin 23) (Fin 23) ℚ) i j := by decide +kernel
  exact Matrix.ext he

theorem lower_triangular : L.BlockTriangular OrderDual.toDual := by
  change ∀ i j : Fin 23, i < j → L i j=0
  decide +kernel
theorem upper_triangular : U.BlockTriangular id := by
  change ∀ i j : Fin 23, j < i → U i j=0
  decide +kernel
theorem lower_diagonal : (∏ i : Fin 23, L i i)=1 := by decide +kernel
theorem upper_diagonal : (∏ i : Fin 23, U i i)= -128 := by decide +kernel
theorem lower_det : L.det=1 := by
  rw [Matrix.det_of_lowerTriangular L lower_triangular,lower_diagonal]
theorem upper_det : U.det= -128 := by
  rw [Matrix.det_of_upperTriangular upper_triangular,upper_diagonal]

theorem determinant_abs : |minorQ.det|=128 := by
  have hp : P.det*P.det=1 := by
    have he := congrArg Matrix.det permutation_orthogonal
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using he
  have hf : P.det*minorQ.det= -128 := by
    have he := congrArg Matrix.det factorization
    simpa only [Matrix.det_mul,lower_det,upper_det,one_mul] using he
  have hm : minorQ.det*minorQ.det=16384 := by
    nlinarith [sq_nonneg (P.det*minorQ.det+128)]
  by_cases h : 0 ≤ minorQ.det
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith

def minorR : Matrix (Fin 23) (Fin 23) ℝ :=
  SixQubit.Orbit31.momentMatrix.submatrix id printedColumns
theorem real_cast : minorR=minorQ.map (Rat.castHom ℝ) := by
  ext i j
  simp [minorR,minorQ,SixQubit.Orbit31.momentMatrix,Matrix.map_apply,Matrix.submatrix_apply]
theorem real_determinant_abs : |minorR.det|=128 := by
  rw [real_cast]
  change |((Rat.castHom ℝ).mapMatrix minorQ).det|=128
  rw [← RingHom.map_det]
  change |(minorQ.det : ℝ)|=128
  exact_mod_cast determinant_abs
end
end MainTheory.Orbit31PrintedMinor
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/Orbit31PrintedMinor.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated literal minor certificate; discovery determinant:',minor.det())
