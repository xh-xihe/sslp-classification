"""Candidate LU certificate for the signed minor printed for SI orbit 32."""
from pathlib import Path
import re
import sympy as sp

WORK=Path(__file__).resolve().parent
ROOT=Path(__file__).resolve().parents[2]
native=(ROOT/'SixQubit/Orbit32.lean').read_text(encoding='utf8')
v=sp.symbols(' '.join('q'+str(j) for j in range(16))+' '+' '.join('r'+str(j) for j in range(16)))
loc={str(x):x for x in v}
fields=re.findall(r'^  (n[01]|m[1-6]|c[1-6][1-6]) : (.+) = (.+)$',native,re.M)
expressions=[sp.sympify(a,locals=loc)-sp.sympify(b,locals=loc) for _,a,b in fields]
rows=[[x.coeff(y) for y in v] for x in expressions]
columns=list(range(16))+[16+j for j in [0,1,2,3,4,8,12]]
minor=sp.Matrix(rows)[:,columns]
l,u,sw=minor.LUdecomposition()
p=sp.eye(23)
for i,j in sw:
    p.row_swap(i,j)
permutation=[next(j for j in range(23) if p[i,j]==1) for i in range(23)]
inverse=[permutation.index(j) for j in range(23)]
assert p*minor==l*u and len(sw)%2==0 and u.det()==3456

def vec(xs): return '!['+','.join(map(str,xs))+']'
def matrix(m): return vec(vec('('+str(x)+')' for x in row) for row in m.tolist())
base=(ROOT/'MainTheory/Orbit31PrintedMinor.lean').read_text(encoding='utf8')
base=base.replace('import SixQubit.Orbit31MomentRank','import SixQubit.CodeOrbit32\nimport Mathlib.LinearAlgebra.Matrix.Rank')
base=base.replace('MainTheory.Orbit31PrintedMinor','MainTheory.Orbit32PrintedMinor')
base=re.sub(r'def printedColumns :.*?\ndef minorQ',
    'def printedColumns : Fin 23 → Fin 32 := '+vec(f'⟨{j},by decide⟩' for j in columns)+'\ndef minorQ',base,flags=re.S)
base=base.replace('SixQubit.Orbit31.momentMatrixZ','matrixZ')
base=base.replace('SixQubit.Orbit31.momentMatrix','matrixR')
for name,m in [('P',p),('L',l),('U',u)]:
    base=re.sub(r'def '+name+r' : Matrix .*?\n',
                'def '+name+' : Matrix (Fin 23) (Fin 23) ℚ := '+matrix(m)+'\n',base,count=1)
start=base.index('theorem determinant_abs')
end=base.index('def minorR',start)
base=base[:start]+'''def permFunction : Fin 23 → Fin 23 := '''+vec(f'⟨{j},by decide⟩' for j in permutation)+'''
def inverseFunction : Fin 23 → Fin 23 := '''+vec(f'⟨{j},by decide⟩' for j in inverse)+'''
def permutation : Equiv.Perm (Fin 23) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_matrix : P=(1 : Matrix (Fin 23) (Fin 23) ℚ).submatrix permutation id := by
  decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation=1 := by decide +kernel
theorem permutation_det : P.det=1 := by
  rw [permutation_matrix,Matrix.det_permute,Matrix.det_one,permutation_sign]
  norm_num
theorem determinant : minorQ.det=3456 := by
  have he := congrArg Matrix.det factorization
  simpa only [Matrix.det_mul,permutation_det,lower_det,upper_det,one_mul] using he
theorem determinant_abs : |minorQ.det|=3456 := by rw [determinant]; norm_num

'''+base[end:]
base=base.replace(' -128','3456').replace('=128','=3456')
base=base.replace('SixQubit.Orbit31.momentMatrix','matrixR')
base=base.replace('def minorR :','def matrixR : Matrix (Fin 23) (Fin 32) ℝ := matrixZ.map (Int.castRingHom ℝ)\n\ndef minorR :')
prefix='def matrixZ : Matrix (Fin 23) (Fin 32) ℤ := '+matrix(sp.Matrix(rows))+'\n'
prefix+='''def bottom : Fin 16 → SS.BitString 6 :=
  ![SixQubit.Orbit32.y0,SixQubit.Orbit32.y1,SixQubit.Orbit32.y2,SixQubit.Orbit32.y3,
    SixQubit.Orbit32.y4,SixQubit.Orbit32.y5,SixQubit.Orbit32.y6,SixQubit.Orbit32.y7,
    SixQubit.Orbit32.y8,SixQubit.Orbit32.y9,SixQubit.Orbit32.y10,SixQubit.Orbit32.y11,
    SixQubit.Orbit32.y12,SixQubit.Orbit32.y13,SixQubit.Orbit32.y14,SixQubit.Orbit32.y15]
def top : Fin 16 → SS.BitString 6 :=
  ![SixQubit.Orbit32.z0,SixQubit.Orbit32.z1,SixQubit.Orbit32.z2,SixQubit.Orbit32.z3,
    SixQubit.Orbit32.z4,SixQubit.Orbit32.z5,SixQubit.Orbit32.z6,SixQubit.Orbit32.z7,
    SixQubit.Orbit32.z8,SixQubit.Orbit32.z9,SixQubit.Orbit32.z10,SixQubit.Orbit32.z11,
    SixQubit.Orbit32.z12,SixQubit.Orbit32.z13,SixQubit.Orbit32.z14,SixQubit.Orbit32.z15]
def coordinatePairs : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
def actualMatrix : Matrix (Fin 23) (Fin 32) ℤ := fun i j =>
  if i.val=0 then (if j.val<16 then 1 else 0) else
  if i.val=1 then (if j.val<16 then 0 else 1) else
  let x := if h : j.val<16 then bottom ⟨j.val,h⟩ else top ⟨j.val-16,by omega⟩
  let sign : ℤ := if j.val<16 then 1 else -1
  if h : i.val<8 then sign*(if x ⟨i.val-2,by omega⟩ then 1 else 0) else
    let pair := coordinatePairs ⟨i.val-8,by omega⟩
    sign*(if x pair.1 then 1 else 0)*(if x pair.2 then 1 else 0)
theorem actual_matrix : matrixZ=actualMatrix := by decide +kernel

'''
base=base.replace('def printedColumns',prefix+'def printedColumns',1)
base=base.replace('theorem real_determinant_abs', '''theorem real_determinant : minorR.det=3456 := by
  rw [real_cast]
  change ((Rat.castHom ℝ).mapMatrix minorQ).det=3456
  rw [← RingHom.map_det]
  change (minorQ.det : ℝ)=3456
  exact_mod_cast determinant

theorem real_determinant_abs''')
base=base.replace('end\nend MainTheory.Orbit32PrintedMinor', '''theorem full_rank : matrixR.rank=23 := by
  have hu : IsUnit minorR.det := by
    rw [real_determinant]
    norm_num
  have hm : minorR.rank=23 := by
    simpa using Matrix.rank_of_isUnit minorR ((Matrix.isUnit_iff_isUnit_det minorR).mpr hu)
  have hle : minorR.rank ≤ matrixR.rank := by
    rw [← Matrix.rank_transpose minorR,← Matrix.rank_transpose matrixR]
    exact Matrix.rank_submatrix_le printedColumns (Equiv.refl (Fin 23)) matrixR.transpose
  apply le_antisymm
  · simpa using Matrix.rank_le_card_height matrixR
  · simpa only [hm] using hle
theorem kernel_dimension : Module.finrank ℝ (LinearMap.ker matrixR.mulVecLin)=9 := by
  have he := LinearMap.finrank_range_add_finrank_ker matrixR.mulVecLin
  change matrixR.rank+Module.finrank ℝ (LinearMap.ker matrixR.mulVecLin)=Module.finrank ℝ (Fin 32 → ℝ) at he
  rw [full_rank] at he
  norm_num at he
  omega
end
end MainTheory.Orbit32PrintedMinor''')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=base
target=ROOT/'MainTheory/Orbit32PrintedMinor.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated actual matrix and signed determinant 3456 certificate')
