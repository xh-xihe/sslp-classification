"""Generate the four literal ten-character half-angle matrices."""
from pathlib import Path
import re
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def vec(xs):return '!['+','.join(map(str,xs))+']'
def matrix(m):return vec(vec('('+str(x)+')' for x in row) for row in m.tolist())
def idx(i):return f'⟨{i},by decide⟩'
parts=['''import MainTheory.OrderTwoPrintedMoments
import MainTheory.FlipCharacterObstruction
import Mathlib.LinearAlgebra.Matrix.Block

/-! The SI's actual ten-incidence, ten-character half-angle systems.
Literal signed determinants use kernel-checked LU factors. The final
physical exclusions follow the printed full-rank matched-flip argument. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.OrderTwoPrintedWalsh
open scoped BigOperators Matrix
noncomputable section
theorem norm_sq_matched_product (c d : ℂ) (hm : Complex.normSq d=Complex.normSq c) :
    Complex.normSq (star c*d)=(Complex.normSq c)^2 := by
  rw [Complex.normSq_mul]
  change Complex.normSq ((starRingEnd ℂ) c)*Complex.normSq d=(Complex.normSq c)^2
  rw [Complex.normSq_conj,hm,pow_two]
''']
for orbit,desired in [(42,73728),(43,73728),(44,-32768),(46,-73728)]:
    text=(ROOT/f'SixQubit/Orbit{orbit}.lean').read_text(encoding='utf8')
    wordrows=re.findall(r'^def z(\d+) : SS.BitString 6 := bs (.+?)\s*--\s*([01]{6})',text,re.M)
    words=[list(map(int,w)) for _,_,w in sorted(wordrows,key=lambda row:int(row[0]))]
    f=4 if orbit==44 else 5
    indices=[[],[f]]+[row for j in range(4) for row in ([j],[f,j])]
    W=s.Matrix([[(-1)**sum(word[j] for j in row) for word in words] for row in indices])
    assert W.det()==desired,(orbit,W.det(),desired)
    L,U,sw=W.LUdecomposition();P=s.eye(10)
    for a,b in sw:P.row_swap(a,b)
    perm=[next(j for j in range(10) if P[i,j]) for i in range(10)]
    inv=[perm.index(j) for j in range(10)];sign=(-1)**len(sw)
    def bits(row):
        if not row:return '(fun _ => false)'
        if len(row)==1:return 'SS.stdBasis '+idx(row[0])
        return f'SS.bxor (SS.stdBasis {idx(row[0])}) (SS.stdBasis {idx(row[1])})'
    parts.append(f'''
namespace Orbit{orbit}
open MainTheory.OrderTwoPrintedMoments.Orbit{orbit}
def flip : SS.BitString 6 := SS.stdBasis {idx(f)}
def characters : Fin 10 → SS.BitString 6 := {vec(bits(row) for row in indices)}
def W : Matrix (Fin 10) (Fin 10) ℚ := {matrix(W)}
def WC : Matrix (Fin 10) (Fin 10) ℂ := W.map (Rat.castHom ℂ)
def products (c d : SS.State 6 ℂ) : Fin 10 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem actual_incidence : Finset.univ.image top=
    SixQubit.Orbit{orbit}.S1.filter (fun y => SS.bxor y flip ∈ SixQubit.Orbit{orbit}.S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (top j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
def P : Matrix (Fin 10) (Fin 10) ℚ := {matrix(P)}
def L : Matrix (Fin 10) (Fin 10) ℚ := {matrix(L)}
def U : Matrix (Fin 10) (Fin 10) ℚ := {matrix(U)}
theorem factorization : P*W=L*U := by
  have he : ∀ i j : Fin 10, (P*W) i j=(L*U) i j := by decide +kernel
  exact Matrix.ext he
theorem lower_triangular : L.BlockTriangular OrderDual.toDual := by
  change ∀ i j : Fin 10, i < j → L i j=0
  decide +kernel
theorem upper_triangular : U.BlockTriangular id := by
  change ∀ i j : Fin 10, j < i → U i j=0
  decide +kernel
theorem lower_diagonal : (∏ i : Fin 10, L i i)=1 := by decide +kernel
theorem upper_diagonal : (∏ i : Fin 10, U i i)={desired*sign} := by decide +kernel
theorem lower_det : L.det=1 := by
  rw [Matrix.det_of_lowerTriangular L lower_triangular,lower_diagonal]
theorem upper_det : U.det={desired*sign} := by
  rw [Matrix.det_of_upperTriangular upper_triangular,upper_diagonal]
def permFunction : Fin 10 → Fin 10 := {vec(idx(j) for j in perm)}
def inverseFunction : Fin 10 → Fin 10 := {vec(idx(j) for j in inv)}
def permutation : Equiv.Perm (Fin 10) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_matrix : P=(1 : Matrix (Fin 10) (Fin 10) ℚ).submatrix permutation id := by decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation={sign} := by decide +kernel
theorem permutation_det : P.det={sign} := by
  rw [permutation_matrix,Matrix.det_permute,Matrix.det_one,permutation_sign]
  norm_num
theorem determinant : W.det={desired} := by
  have he := congrArg Matrix.det factorization
  norm_num only [Matrix.det_mul,permutation_det,lower_det,upper_det,one_mul] at he
  linear_combination {sign}*he
theorem complex_determinant : WC.det={desired} := by
  change ((Rat.castHom ℂ).mapMatrix W).det={desired}
  rw [← RingHom.map_det]
  change (W.det : ℂ)={desired}
  exact_mod_cast determinant
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 10) :
    products c d j=star (c (bottom j))*d (top j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit{orbit}.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit{orbit}.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit{orbit}.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit{orbit}.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  have hdW : WC.det≠0 := by rw [complex_determinant]; norm_num
  have hu : IsUnit WC := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdW)
  have hz : products c d=0 := Matrix.mulVec_injective_of_isUnit hu (by simpa using physical_rows c d hc hd hkl)
  exact fun j => congrFun hz j
theorem physical_product_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit{orbit}.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit{orbit}.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 10) :
    Complex.normSq (products c d j)=(Complex.normSq (c (bottom j)))^2 := by
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit{orbit}.moments c d hc hd hnc hnd hkl
  have he : Complex.normSq (d (top j))=Complex.normSq (c (bottom j)) :=
    (congrFun (matched_probabilities _ _ hm) j).symm
  rw [product_expansion,Complex.normSq_mul]
  change Complex.normSq ((starRingEnd ℂ) (c (bottom j)))*Complex.normSq (d (top j))=
    (Complex.normSq (c (bottom j)))^2
  rw [Complex.normSq_conj,he,pow_two]
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit{orbit}.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit{orbit}.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hp : ∀ j, Complex.normSq (c (bottom j))=0 := by
    intro j
    have he := physical_product_norm c d hc hd hnc hnd hkl j
    rw [physical_products_zero c d hc hd hkl j,Complex.normSq_zero] at he
    exact (sq_eq_zero_iff).1 he.symm
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit{orbit}.moments c d hc hd hnc hnd hkl
  have hn := hm.n0
  simp only [hp] at hn
  norm_num at hn
end Orbit{orbit}
''')
parts.append('\nend\nend MainTheory.OrderTwoPrintedWalsh\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/OrderTwoPrintedWalsh.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated four literal signed determinants and physical matched-flip exclusions')
