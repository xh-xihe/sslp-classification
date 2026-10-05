"""Emit the manuscript's actual X5, X4 and X2 cross systems."""
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
parts=['''import MainTheory.OrderThreePrintedMoments
import MainTheory.FlipCharacterObstruction

/-! Literal physical cross-incidence systems of SI orbits 47, 48 and 52.
Every displayed intermediate row and probability product is exposed without
calling any final no-code theorem. The orbit-52 proof includes zero amplitudes.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderThreePrintedCrossRows
open scoped Matrix BigOperators
noncomputable section
''']
DATA=[(47,4,[0,7],[1,8],[None,0],[[1,1],[1,-1]]),
      (48,3,[0,2,5,8],[2,4,6,8],[None,0,1,2],[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]),
      (52,1,[0,1,6,7],[2,3,8,9],[None,0,2,3],[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])]
for o,flip,dest,src,chars,W in DATA:
    n=len(src)
    det=s.Matrix(W).det()
    rows=';'.join(','.join(map(str,row)) for row in W)
    characters=','.join('(fun _ => false)' if j is None else f'SS.stdBasis ⟨{j},by decide⟩' for j in chars)
    parts.append(f'''
namespace Orbit{o}
open SixQubit.Orbit{o}
def flip : SS.BitString 6 := SS.stdBasis ⟨{flip},by decide⟩
def sources : Fin {n} → SS.BitString 6 := ![{','.join('z'+str(i) for i in src)}]
def destinations : Fin {n} → SS.BitString 6 := ![{','.join('y'+str(i) for i in dest)}]
def characters : Fin {n} → SS.BitString 6 := ![{characters}]
def W : Matrix (Fin {n}) (Fin {n}) ℚ := !![{rows}]
def WC : Matrix (Fin {n}) (Fin {n}) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin {n} → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=
    S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j,
    W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem determinant : W.det={det} := by decide +kernel
theorem determinant_complex : WC.det={det} := by
  have he : WC.det=(W.det : ℂ) := ((algebraMap ℚ ℂ).map_det W).symm
  rw [he,determinant]
  norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin {n}) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem product_norm (c d : SS.State 6 ℂ) (j : Fin {n}) :
    Complex.normSq (products c d j)=
    Complex.normSq (c (destinations j))*Complex.normSq (d (sources j)) := by
  rw [products,MainTheory.FlipCharacter.normSq_incidenceMonomial,actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  apply MainTheory.FlipCharacter.monomials_zero_of_det_ne_zero S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  rw [matrix_checked,determinant_complex]
  norm_num
''')
    if o in (47,48):
        nbot=9 if o==47 else 11
        idx=nbot+src[0]
        parts.append(f'''theorem physical_first_product_positive (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (products c d 0)=1/18 ∧ 0<Complex.normSq (products c d 0) := by
  have hm := moments c d hc hd hnc hnd hkl
  have h0 := MainTheory.OrderThreePrintedMoments.Orbit{o}.consequence0 hm
  have h1 := MainTheory.OrderThreePrintedMoments.Orbit{o}.consequence{idx} hm
  have he : Complex.normSq (products c d 0)=1/18 := by
    rw [product_norm]
    norm_num [destinations,sources,h0,h1]
  exact ⟨he,by rw [he]; norm_num⟩
''')
    else:
        parts.append('''theorem physical_half_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (c y0)=Complex.normSq (d z2)/2 ∧
    Complex.normSq (c y1)=Complex.normSq (d z3)/2 ∧
    Complex.normSq (d z2)+Complex.normSq (d z3)=1/3 := by
  have hm := moments c d hc hd hnc hnd hkl
  have h0 := MainTheory.OrderThreePrintedMoments.Orbit52.consequence0 hm
  have h1 := MainTheory.OrderThreePrintedMoments.Orbit52.consequence1 hm
  have h2 := MainTheory.OrderThreePrintedMoments.Orbit52.consequence12 hm
  refine ⟨?_,?_,?_⟩ <;> linarith only [h0,h1,h2]
theorem physical_squared_products (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (products c d 0)=1/2*(Complex.normSq (d z2))^2 ∧
    Complex.normSq (products c d 1)=1/2*(Complex.normSq (d z3))^2 := by
  have he := physical_half_relations c d hc hd hnc hnd hkl
  constructor
  · rw [product_norm]
    norm_num [destinations,sources]
    rw [he.1]
    ring
  · rw [product_norm]
    norm_num [destinations,sources]
    rw [he.2.1]
    ring
''')
    if o in (47,48):
        parts.append('''theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hz := physical_products_zero c d hc hd hkl 0
  have hp := (physical_first_product_positive c d hc hd hnc hnd hkl).2
  rw [hz,Complex.normSq_zero] at hp
  exact (lt_irrefl 0) hp
''')
    else:
        parts.append('''theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hz0 := physical_products_zero c d hc hd hkl 0
  have hz1 := physical_products_zero c d hc hd hkl 1
  have hp := physical_squared_products c d hc hd hnc hnd hkl
  have hs := (physical_half_relations c d hc hd hnc hnd hkl).2.2
  rw [hz0,Complex.normSq_zero] at hp
  rw [hz1,Complex.normSq_zero] at hp
  have h0 : Complex.normSq (d z2)=0 := by nlinarith only [hp.1]
  have h1 : Complex.normSq (d z3)=0 := by nlinarith only [hp.2]
  linarith only [h0,h1,hs]
''')
    parts.append(f'\nend Orbit{o}\n')
parts.append('\nend\nend MainTheory.OrderThreePrintedCrossRows\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/OrderThreePrintedCrossRows.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated the three literal cross systems and probability products')
