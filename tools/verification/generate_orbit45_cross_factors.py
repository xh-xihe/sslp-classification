"""Generate every actual orbit-45 remaining cross row and its printed factors."""
from pathlib import Path
import sympy as s
import re
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
words=[0,9,10,23,28,39,44,49,50,59]
tops=[x^4 for x in words]
pairs=[(1,5),(1,4),(1,2),(0,5),(0,4),(0,2)]
def idx(i):return f'⟨{i},by decide⟩'
def vec(items):return '!['+','.join(map(str,items))+']'
def mat(A):return '!!['+';'.join(','.join(map(str,row)) for row in A)+']'
parts=['''import MainTheory.RectangularFlipCharacters
import MainTheory.Orbit45PrintedFibers

/-! The complete six remaining physical cross incidences and all four
Pauli dressings. Literal substitution proves the printed factor table with
the nonzero common amplitude and unit-phase denominators retained. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit45CrossFactors
open MainTheory.Orbit45PrintedFibers SixQubit.Orbit45Support
open scoped BigOperators Matrix
noncomputable section
def C (B G S H : ℝ) (U V W : ℂ) : Fin 10 → ℂ :=
  ![G,B,S,H,H,H,(H : ℂ)*U,S,(B : ℂ)*V,(G : ℂ)*W]
def D (B G S H : ℝ) (U V W xi eta zeta : ℂ) : Fin 10 → ℂ :=
  ![(G : ℂ)*eta,(B : ℂ)*xi,(S : ℂ)*zeta,H,-H,-H,(H : ℂ)*U,
    (S : ℂ)*zeta,(B : ℂ)*V*xi,(G : ℂ)*W*eta]
def pairs : Fin 6 → Fin 6 × Fin 6 := ![(1,5),(1,4),(1,2),(0,5),(0,4),(0,2)]
def flip (r : Fin 6) := SS.bxor (SS.stdBasis (pairs r).1) (SS.stdBasis (pairs r).2)
theorem all_cross_masks : ∀ e : SS.BitString 6, SS.hammingWt e ≤ 2 →
    ((∃ y ∈ S1, SS.bxor y e ∈ S0) ↔ e=SS.stdBasis 3 ∨ ∃ r, e=flip r) := by decide +kernel
theorem unit_nonzero (u : ℂ) (hu : Complex.normSq u=1) : u ≠ 0 := by
  intro h
  simp [h] at hu
theorem star_unit (u : ℂ) (hu : Complex.normSq u=1) : star u=u⁻¹ := by
  rw [← one_div]
  apply (eq_div_iff (unit_nonzero u hu)).2
  rw [SixQubit.star_mul_self,hu]
  norm_num
''']
factor0=['(V+1)*(V*xi-1)','zeta-1','(W+1)*(W*eta-1)',
         '(U+V*xi)*(U*V+1)','(U+1)*(U+zeta)','(U+W*eta)*(U*W+1)']
factor1=['(V-1)*(V*xi-1)','0','(W-1)*(W*eta-1)',
         '(U+V*xi)*(U*V-1)','(U-1)*(U+zeta)','(U+W*eta)*(U*W-1)']
denoms=['V','1','W','U*V','U','U*W']
commons=['(B : ℂ)*(H : ℂ)','2*(S : ℂ)*(H : ℂ)','(G : ℂ)*(H : ℂ)',
         '(B : ℂ)*(H : ℂ)','(S : ℂ)*(H : ℂ)','(G : ℂ)*(H : ℂ)']
used=[['V'],[],['W'],['U','V'],['U'],['U','W']]
for r,(u,v) in enumerate(pairs):
    m=(1<<(5-u))+(1<<(5-v))
    src=[j for j,y in enumerate(tops) if y^m in words]
    dst=[words.index(tops[j]^m) for j in src]
    n=len(src)
    W=[[(-1)**((k&tops[j]).bit_count()) for j in src] for k in [0,1<<(5-u),1<<(5-v),m]]
    factors=[factor0[r],'-('+factor1[r]+')',factor1[r],'-('+factor0[r]+')']
    if r in (2,5):factors=[factor0[r],'-('+factor1[r]+')','-('+factor1[r]+')',factor0[r]]
    if r==1:factors=[factor0[r],'0','0','-('+factor0[r]+')']
    factor_arguments=' '.join(v if any(re.search(r'\b'+v+r'\b',expr) for expr in factors) else '_'+v
      for v in ['U','V','W','xi','eta','zeta'])
    parts.append(f'''
namespace Row{r}
def sourceIndices : Fin {n} → Fin 10 := {vec(idx(j) for j in src)}
def destinationIndices : Fin {n} → Fin 10 := {vec(idx(j) for j in dst)}
def sources : Fin {n} → SS.BitString 6 := fun j => top (sourceIndices j)
def destinations : Fin {n} → SS.BitString 6 := fun j => bottom (destinationIndices j)
def characters : Fin 4 → SS.BitString 6 :=
  ![(fun _ => false),SS.stdBasis ⟨{u},by decide⟩,SS.stdBasis ⟨{v},by decide⟩,flip ⟨{r},by decide⟩]
def walsh : Matrix (Fin 4) (Fin {n}) ℚ := {mat(W)}
def WC : Matrix (Fin 4) (Fin {n}) ℂ := fun i j => walsh i j
def products (c d : SS.State 6 ℂ) : Fin {n} → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d (flip ⟨{r},by decide⟩) (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y (flip ⟨{r},by decide⟩) ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) (flip ⟨{r},by decide⟩)=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, walsh i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip ⟨{r},by decide⟩,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : RectangularFlipCharacters.matrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(walsh i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin {n}) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    (flip ⟨{r},by decide⟩) characters sources sources_injective actual_incidence weights
def gaugeProducts (B G S H : ℝ) (U V W xi eta zeta : ℂ) : Fin {n} → ℂ :=
  fun j => star (C B G S H U V W (destinationIndices j))*D B G S H U V W xi eta zeta (sourceIndices j)
def factors ({factor_arguments} : ℂ) : Fin 4 → ℂ := {vec(factors)}
theorem substitution (B G S H : ℝ) (U V W xi eta zeta : ℂ)
    (_hU : Complex.normSq U=1) (_hV : Complex.normSq V=1) (_hW : Complex.normSq W=1)
    (a : Fin 4) :
    ({denoms[r]})*(WC *ᵥ gaugeProducts B G S H U V W xi eta zeta) a=
      ({commons[r]})*factors U V W xi eta zeta a := by
  fin_cases a <;>
    norm_num [WC,walsh,gaugeProducts,C,D,sourceIndices,destinationIndices,factors,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
''')
    if used[r]:
        parts.append('  all_goals simp only [starRingEnd_apply]\n')
        parts.append('  all_goals simp only ['+', '.join('star_unit '+v+' _h'+v for v in used[r])+']\n')
        parts.append('  all_goals field_simp ['+', '.join('unit_nonzero '+v+' _h'+v for v in used[r])+']\n')
    parts.append('  all_goals ring\n')
    parts.append(f'''theorem physical_factors (B G S H : ℝ) (U V W xi eta zeta : ℂ)
    (hU : Complex.normSq U=1) (hV : Complex.normSq V=1) (hW : Complex.normSq W=1)
    (hcommon : ({commons[r]}) ≠ 0)
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3)
    (hC : (fun j => c (bottom j))=C B G S H U V W)
    (hD : (fun j => d (top j))=D B G S H U V W xi eta zeta) :
    factors U V W xi eta zeta=0 := by
  have he := physical_rows c d hc hd hkl
  have hp : products c d=gaugeProducts B G S H U V W xi eta zeta := by
    funext j
    rw [product_expansion]
    change star (c (bottom (destinationIndices j)))*d (top (sourceIndices j))=_
    rw [show c (bottom (destinationIndices j))=C B G S H U V W (destinationIndices j) from congrFun hC _,
      show d (top (sourceIndices j))=D B G S H U V W xi eta zeta (sourceIndices j) from congrFun hD _]
    rfl
  rw [hp] at he
  funext a
  have hf := substitution B G S H U V W xi eta zeta hU hV hW a
  rw [he] at hf
  simp only [Pi.zero_apply,mul_zero] at hf
  exact (mul_eq_zero.mp hf.symm).resolve_left hcommon
end Row{r}
''')
parts.append('''
theorem forced_phases (U V W xi eta zeta : ℂ)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (h0 : Row0.factors U V W xi eta zeta=0)
    (h1 : Row1.factors U V W xi eta zeta=0)
    (h2 : Row2.factors U V W xi eta zeta=0)
    (h3 : Row3.factors U V W xi eta zeta=0) :
    U=-1 ∧ V=star xi ∧ W=star eta ∧ zeta=1 := by
  have h00 := congrFun h0 0
  have h01 := congrFun h0 1
  have h10 := congrFun h1 0
  have h20 := congrFun h2 0
  have h21 := congrFun h2 1
  have h30 := congrFun h3 0
  have h31 := congrFun h3 1
  change (V+1)*(V*xi-1)=0 at h00
  change -((V-1)*(V*xi-1))=0 at h01
  change zeta-1=0 at h10
  change (W+1)*(W*eta-1)=0 at h20
  change -((W-1)*(W*eta-1))=0 at h21
  change (U+V*xi)*(U*V+1)=0 at h30
  change -((U+V*xi)*(U*V-1))=0 at h31
  have hv : V*xi=1 := by linear_combination (h00+h01)/2
  have hw : W*eta=1 := by linear_combination (h20+h21)/2
  have hu : U+V*xi=0 := by linear_combination (h30+h31)/2
  refine ⟨?_,?_,?_,?_⟩
  · rw [hv] at hu
    linear_combination hu
  · apply mul_right_cancel₀ (unit_nonzero xi hxi)
    rw [hv,SixQubit.star_mul_self,hxi]
    norm_num
  · apply mul_right_cancel₀ (unit_nonzero eta heta)
    rw [hw,SixQubit.star_mul_self,heta]
    norm_num
  · linear_combination h10
theorem triangle_after_gauge (b g s : ℝ) (xi eta zeta : ℂ)
    (ht : (b : ℂ)*xi+(g : ℂ)*eta+(s : ℂ)*zeta=0) (hz : zeta=1) :
    (b : ℂ)*xi+(g : ℂ)*eta+(s : ℂ)=0 := by simpa only [hz,mul_one] using ht
theorem remaining_factors_zero (xi eta : ℂ)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1) :
    Row0.factors (-1) (star xi) (star eta) xi eta 1=0 ∧
    Row1.factors (-1) (star xi) (star eta) xi eta 1=0 ∧
    Row2.factors (-1) (star xi) (star eta) xi eta 1=0 ∧
    Row3.factors (-1) (star xi) (star eta) xi eta 1=0 ∧
    Row4.factors (-1) (star xi) (star eta) xi eta 1=0 ∧
    Row5.factors (-1) (star xi) (star eta) xi eta 1=0 := by
  have hx : star xi*xi=1 := by rw [SixQubit.star_mul_self,hxi]; norm_num
  have he : star eta*eta=1 := by rw [SixQubit.star_mul_self,heta]; norm_num
  change (starRingEnd ℂ) xi*xi=1 at hx
  change (starRingEnd ℂ) eta*eta=1 at he
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> funext a <;> fin_cases a <;>
    simp [Row0.factors,Row1.factors,Row2.factors,Row3.factors,Row4.factors,Row5.factors,hx,he]
end
end MainTheory.Orbit45CrossFactors
''')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/Orbit45CrossFactors.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
