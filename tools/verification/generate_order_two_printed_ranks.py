"""Untrusted LU and rectangular factors for the six actual moment matrices."""
from pathlib import Path
import re
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def vec(xs):return '!['+','.join(map(str,xs))+']'
def matrix(m):return vec(vec('('+str(x)+')' for x in row) for row in m.tolist())
parts=['''import SixQubit.CodeOrbit18
import SixQubit.CodeOrbit41
import SixQubit.CodeOrbit42
import SixQubit.CodeOrbit43
import SixQubit.CodeOrbit44
import SixQubit.CodeOrbit46
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block

/-! The actual 23-row occupation-moment matrices, their literal maximal
minors, and exact ranks. Candidate LU and column factors are verified in the
kernel; they are independent of phase constraints and no-code conclusions.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.OrderTwoPrintedRanks
open scoped BigOperators Matrix
noncomputable section
def coordinatePairs : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
''']
for orbit,desired in [(18,-1024),(41,108),(42,108),(43,-108),(44,-108),(46,-108)]:
    source=(ROOT/f'SixQubit/Orbit{orbit}.lean').read_text(encoding='utf8')
    names=re.search(r'structure MomentSystem \((.+?) : Real\)',source).group(1)
    v=s.symbols(names)
    n=sum(str(x).startswith('q') for x in v)
    m=len(v)-n
    fields=re.findall(r'^  (n[01]|m[1-6](?:[1-6])?|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
    loc={str(x):x for x in v}
    A=s.Matrix([[s.expand(s.sympify(a,locals=loc)-s.sympify(b,locals=loc)).coeff(x) for x in v] for _,a,b in fields])
    columns=list(A.rref()[1])
    rows=list(A[:,columns].T.rref()[1])
    r=len(columns)
    minor=A.extract(rows,columns)
    if minor.det()!=desired:
        rows[0],rows[1]=rows[1],rows[0]
        minor=A.extract(rows,columns)
    assert minor.det()==desired
    L,U,sw=minor.LUdecomposition()
    P=s.eye(r)
    for i,j in sw:P.row_swap(i,j)
    perm=[next(j for j in range(r) if P[i,j]) for i in range(r)]
    inv=[perm.index(j) for j in range(r)]
    sign=(-1)**len(sw)
    ud=desired*sign
    B=A[:,columns]
    T=minor.inv()*A[rows,:]
    assert B*T==A and P*minor==L*U
    parts.append(f'''
namespace Orbit{orbit}
open SixQubit.Orbit{orbit}
def bottom : Fin {n} → SS.BitString 6 := {vec("y"+str(i) for i in range(n))}
def top : Fin {m} → SS.BitString 6 := {vec("z"+str(i) for i in range(m))}
def matrixZ : Matrix (Fin 23) (Fin {n+m}) ℤ := {matrix(A)}
def actualMatrix : Matrix (Fin 23) (Fin {n+m}) ℤ := fun i j =>
  if i.val=0 then (if j.val<{n} then 1 else 0) else
  if i.val=1 then (if j.val<{n} then 0 else 1) else
  let x := if h : j.val<{n} then bottom ⟨j.val,h⟩
    else top ⟨j.val-{n},by omega⟩
  let sign : ℤ := if j.val<{n} then 1 else -1
  if h : i.val<8 then sign*(if x ⟨i.val-2,by omega⟩ then 1 else 0) else
    let pair := coordinatePairs ⟨i.val-8,by omega⟩
    sign*(if x pair.1 then 1 else 0)*(if x pair.2 then 1 else 0)
theorem actual_matrix : matrixZ=actualMatrix := by decide +kernel
def rows : Fin {r} → Fin 23 := {vec(f'⟨{j},by decide⟩' for j in rows)}
def columns : Fin {r} → Fin {n+m} := {vec(f'⟨{j},by decide⟩' for j in columns)}
def matrixQ : Matrix (Fin 23) (Fin {n+m}) ℚ := matrixZ.map (Int.castRingHom ℚ)
def minorQ : Matrix (Fin {r}) (Fin {r}) ℚ := matrixQ.submatrix rows columns
def P : Matrix (Fin {r}) (Fin {r}) ℚ := {matrix(P)}
def L : Matrix (Fin {r}) (Fin {r}) ℚ := {matrix(L)}
def U : Matrix (Fin {r}) (Fin {r}) ℚ := {matrix(U)}
theorem factorization : P*minorQ=L*U := by
  have he : ∀ i j : Fin {r}, (P*minorQ) i j=(L*U) i j := by decide +kernel
  exact Matrix.ext he
theorem lower_triangular : L.BlockTriangular OrderDual.toDual := by
  change ∀ i j : Fin {r}, i < j → L i j=0
  decide +kernel
theorem upper_triangular : U.BlockTriangular id := by
  change ∀ i j : Fin {r}, j < i → U i j=0
  decide +kernel
theorem lower_diagonal : (∏ i : Fin {r}, L i i)=1 := by decide +kernel
theorem upper_diagonal : (∏ i : Fin {r}, U i i)={ud} := by decide +kernel
theorem lower_det : L.det=1 := by
  rw [Matrix.det_of_lowerTriangular L lower_triangular,lower_diagonal]
theorem upper_det : U.det={ud} := by
  rw [Matrix.det_of_upperTriangular upper_triangular,upper_diagonal]
def permFunction : Fin {r} → Fin {r} := {vec(f'⟨{j},by decide⟩' for j in perm)}
def inverseFunction : Fin {r} → Fin {r} := {vec(f'⟨{j},by decide⟩' for j in inv)}
def permutation : Equiv.Perm (Fin {r}) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_matrix : P=(1 : Matrix (Fin {r}) (Fin {r}) ℚ).submatrix permutation id := by decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation={sign} := by decide +kernel
theorem permutation_det : P.det={sign} := by
  rw [permutation_matrix,Matrix.det_permute,Matrix.det_one,permutation_sign]
  norm_num
theorem determinant : minorQ.det={desired} := by
  have he := congrArg Matrix.det factorization
  norm_num only [Matrix.det_mul,permutation_det,lower_det,upper_det,one_mul] at he
  linear_combination {sign}*he
def basisColumns : Matrix (Fin 23) (Fin {r}) ℚ := {matrix(B)}
def coefficients : Matrix (Fin {r}) (Fin {n+m}) ℚ := {matrix(T)}
theorem rank_factorization : matrixQ=basisColumns*coefficients := by
  have he : ∀ i j, matrixQ i j=(basisColumns*coefficients) i j := by decide +kernel
  exact Matrix.ext he
def matrixR : Matrix (Fin 23) (Fin {n+m}) ℝ := matrixZ.map (Int.castRingHom ℝ)
def selectedRows : Matrix (Fin {r}) (Fin {n+m}) ℝ := matrixR.submatrix rows id
def minorR : Matrix (Fin {r}) (Fin {r}) ℝ := selectedRows.submatrix id columns
theorem real_cast : minorR=minorQ.map (Rat.castHom ℝ) := by
  ext i j
  simp [minorR,selectedRows,minorQ,matrixR,matrixQ,Matrix.map_apply,Matrix.submatrix_apply]
theorem real_determinant : minorR.det={desired} := by
  rw [real_cast]
  change ((Rat.castHom ℝ).mapMatrix minorQ).det={desired}
  rw [← RingHom.map_det]
  change (minorQ.det : ℝ)={desired}
  exact_mod_cast determinant
theorem real_rank_factorization : matrixR=
    (basisColumns.map (Rat.castHom ℝ))*(coefficients.map (Rat.castHom ℝ)) := by
  rw [← Matrix.map_mul,← rank_factorization]
  ext i j
  simp [matrixR,matrixQ,Matrix.map_apply]
theorem rank_exact : matrixR.rank={r} := by
  have hminor : minorR.rank={r} := by
    have hu : IsUnit minorR.det := by rw [real_determinant]; norm_num
    simpa using Matrix.rank_of_isUnit minorR ((Matrix.isUnit_iff_isUnit_det minorR).mpr hu)
  have hr : selectedRows.rank ≤ matrixR.rank := Matrix.rank_submatrix_le rows (Equiv.refl _) matrixR
  have hc : minorR.rank ≤ selectedRows.rank := by
    rw [← Matrix.rank_transpose minorR,← Matrix.rank_transpose selectedRows]
    exact Matrix.rank_submatrix_le columns (Equiv.refl _) selectedRows.transpose
  apply le_antisymm
  · rw [real_rank_factorization]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width _)
  · rw [hminor] at hc
    exact le_trans hc hr
theorem kernel_dimension : Module.finrank ℝ (LinearMap.ker matrixR.mulVecLin)={n+m-r} := by
  have he := LinearMap.finrank_range_add_finrank_ker matrixR.mulVecLin
  change matrixR.rank+Module.finrank ℝ (LinearMap.ker matrixR.mulVecLin)=Module.finrank ℝ (Fin {n+m} → ℝ) at he
  rw [rank_exact] at he
  norm_num at he
  omega
end Orbit{orbit}
''')
parts.append('\nend\nend MainTheory.OrderTwoPrintedRanks\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/OrderTwoPrintedRanks.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated six actual matrix, signed minor, rank and kernel-dimension certificates')
