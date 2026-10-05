"""Generate the actual seven affine phase rows and exact inverse certificate."""
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
words=[0,9,10,23,28,39,44,49,50,59]
anchors=[0,1,2,3,4,5,7]
A=s.Matrix([[1]+[(words[r]>>(5-j))&1 for j in range(6)] for r in anchors])
assert A.det()==6
L,U,swaps=A.LUdecomposition()
perm=list(range(7))
for i,j in swaps:perm[i],perm[j]=perm[j],perm[i]
inverse=[perm.index(j) for j in range(7)]
sign=(-1)**len(swaps)
def num(v):return str(v) if v.q==1 else f'({v.p}/{v.q})'
def mat(M):return '!!['+';\n    '.join(','.join(num(v) for v in M.row(i)) for i in range(M.rows))+']'
lean=f'''import MainTheory.Orbit45PrintedFibers
import MainTheory.BoundedRepresentation
import MainTheory.Orbit9DiagonalGauge

/-! The actual seven affine rows of the positive-stratum phase gauge have
signed determinant six. Their exact inverse supplies all seven real angles. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.Orbit45AffineGauge
open MainTheory.Orbit45PrintedFibers MainTheory.ClassificationLevels
open scoped BigOperators Matrix
noncomputable section
def anchors : Fin 7 → Fin 10 := ![0,1,2,3,4,5,7]
def A : Matrix (Fin 7) (Fin 7) ℚ := {mat(A)}
def B : Matrix (Fin 7) (Fin 7) ℚ := {mat(A.inv())}
def lower : Matrix (Fin 7) (Fin 7) ℚ := {mat(L)}
def upper : Matrix (Fin 7) (Fin 7) ℚ := {mat(U)}
def permFunction : Fin 7 → Fin 7 := ![{','.join(map(str,perm))}]
def inverseFunction : Fin 7 → Fin 7 := ![{','.join(map(str,inverse))}]
def permutation : Equiv.Perm (Fin 7) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation={sign} := by decide +kernel
theorem actual_rows : ∀ i j,
    A i j=(if j.val=0 then 1 else if bottom (anchors i) ⟨j.val-1,by omega⟩ then 1 else 0) := by
  decide +kernel
theorem inverse_checked : A*B=1 := by decide +kernel
theorem factorization : A.submatrix permutation id=lower*upper := by decide +kernel
theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel
theorem determinant : A.det=6 := by
  have he := congrArg Matrix.det factorization
  rw [Matrix.det_permute,permutation_sign,Matrix.det_mul,
    Matrix.det_of_lowerTriangular lower lower_triangular,
    Matrix.det_of_upperTriangular upper_triangular] at he
  norm_num [lower,upper,Fin.prod_univ_succ] at he
  linarith
def AR : Matrix (Fin 7) (Fin 7) ℝ := A.map (Rat.castHom ℝ)
def BR : Matrix (Fin 7) (Fin 7) ℝ := B.map (Rat.castHom ℝ)
theorem real_inverse : AR*BR=1 := by
  rw [AR,BR,← Matrix.map_mul,inverse_checked]
  ext i j
  simp only [Matrix.map_apply,Matrix.one_apply]
  split_ifs <;> norm_num
theorem real_determinant : AR.det=6 := by
  change ((Rat.castHom ℝ).mapMatrix A).det=6
  rw [← RingHom.map_det,determinant]
  norm_num
theorem solve_angles (t : Fin 7 → ℝ) : AR *ᵥ (BR *ᵥ t)=t := by
  rw [Matrix.mulVec_mulVec,real_inverse,Matrix.one_mulVec]
def localPhases (theta : Fin 7 → ℝ) : LocalPhase 6 :=
  fun j => MainTheory.BoundedRepresentation.circlePhase (theta j.succ)
def globalPhase (theta : Fin 7 → ℝ) : ℂ :=
  Complex.exp ((theta 0 : ℂ)*Complex.I)
def phaseAction (theta : Fin 7 → ℝ) (c : SS.State 6 ℂ) : SS.State 6 ℂ :=
  fun x => globalPhase theta*diagonalAction (localPhases theta) c x
theorem value_exponential (theta : Fin 7 → ℝ) (x : SS.BitString 6) :
    globalPhase theta*diagonalValue (localPhases theta) x=
      Complex.exp (((theta 0+(∑ j : Fin 6, if x j then theta j.succ else 0) : ℝ) : ℂ)*Complex.I) := by
  rw [globalPhase,diagonalValue]
  have he : (∏ j : Fin 6, if x j then ((localPhases theta j : unitary ℂ) : ℂ) else 1)=
      Complex.exp (((∑ j : Fin 6, if x j then theta j.succ else 0 : ℝ) : ℂ)*Complex.I) := by
    rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    cases x j <;> simp [localPhases,MainTheory.BoundedRepresentation.circlePhase]
  rw [he,← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem affine_angle (theta : Fin 7 → ℝ) (i : Fin 7) :
    (AR *ᵥ theta) i=theta 0+∑ j : Fin 6,
      if bottom (anchors i) j then theta j.succ else 0 := by
  change (∑ j, (A i j : ℝ)*theta j)=_
  simp_rw [actual_rows]
  rw [Fin.sum_univ_succ]
  norm_num only [Fin.val_zero,ite_true,Rat.cast_one,one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.succ.val ≠ 0 := by simp
  rw [if_neg hj]
  have hi : (⟨j.succ.val-1,by omega⟩ : Fin 6)=j := by ext; simp
  rw [hi]
  cases bottom (anchors i) j <;> simp
theorem normalize_arg (z : ℂ) :
    Complex.exp (((-Complex.arg z : ℝ) : ℂ)*Complex.I)*z=(‖z‖ : ℂ) := by
  conv_lhs => rhs; rw [← Complex.norm_mul_exp_arg_mul_I z]
  calc
    _ = (‖z‖ : ℂ)*(Complex.exp (((-Complex.arg z : ℝ) : ℂ)*Complex.I)*
        Complex.exp ((Complex.arg z : ℂ)*Complex.I)) := by ring
    _ = _ := by rw [← Complex.exp_add]; simp
theorem anchors_positive (c : SS.State 6 ℂ) :
    ∃ theta : Fin 7 → ℝ, ∀ i : Fin 7,
      phaseAction theta c (bottom (anchors i))=(‖c (bottom (anchors i))‖ : ℂ) := by
  let t : Fin 7 → ℝ := fun i => -Complex.arg (c (bottom (anchors i)))
  refine ⟨BR *ᵥ t,?_⟩
  intro i
  have he := congrFun (solve_angles t) i
  rw [affine_angle] at he
  rw [phaseAction,diagonalAction,← mul_assoc,value_exponential,he]
  exact normalize_arg _
end
end MainTheory.Orbit45AffineGauge
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/Orbit45AffineGauge.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
