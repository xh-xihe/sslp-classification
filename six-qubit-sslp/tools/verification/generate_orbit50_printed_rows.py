"""Generate the literal two- and six-incidence orbit-50 cross tables."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
text=(ROOT/'SixQubit/Orbit50.lean').read_text(encoding='utf8')
words={name:[x=='true' for x in values.split()] for name,values in
       re.findall(r'def ([yz]\d+) : SS.BitString 6 := bs ((?:(?:true|false)\s+){5}(?:true|false))',text)}
parts=['''import MainTheory.OrderThreePrintedMoments
import MainTheory.RectangularFlipCharacters

/-! Literal orbit-50 tables in complementary top indexing. The native top
order is reversed; the Z4 row has an explicit harmless global sign change
to match the SI row-reduced convention. Every physical incidence is retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit50PrintedRows
open scoped BigOperators Matrix
open SixQubit.Orbit50
noncomputable section
''']
DATA=[(4,5,[10,0],[0,10]),(0,1,[1,0],[0,1]),(0,2,[2,0],[0,2]),(1,2,[5,0],[0,5]),
      (2,3,[10,7,6,4,3,1],[1,3,4,6,7,10]),
      (1,3,[10,9,8,4,3,2],[2,3,4,8,9,10]),
      (0,3,[10,9,8,7,6,5],[5,6,7,8,9,10])]
def index(i):return f'⟨{i},by decide⟩'
for r,(u,v,matched,dst) in enumerate(DATA):
    src=[10-i for i in matched]
    flip=[i in [u,v] for i in range(6)]
    for a,b in zip(src,dst):
        assert [x!=y for x,y in zip(words['z'+str(a)],flip)]==words['y'+str(b)]
    n=len(src);m=1 if n==2 else 2
    W=[[1]*n] if m==1 else [[1]*6,[-1,1,1,1,1,-1]]
    signs=[1] if m==1 else [1,-1]
    if m==2:
        assert [(-1)**words['z'+str(a)][3]*(-1) for a in src]==W[1]
    chars='(fun _ => false)' if m==1 else '(fun _ => false),SS.stdBasis ⟨3,by decide⟩'
    rows=';'.join(','.join(map(str,row)) for row in W)
    parts.append(f'''
namespace Row{r:02d}
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨{u},by decide⟩) (SS.stdBasis ⟨{v},by decide⟩)
def printedSources : Fin {n} → Fin 11 := ![{','.join(index(i) for i in matched)}]
def printedDestinations : Fin {n} → Fin 11 := ![{','.join(index(i) for i in dst)}]
def sources : Fin {n} → SS.BitString 6 := ![{','.join('z'+str(i) for i in src)}]
def destinations : Fin {n} → SS.BitString 6 := ![{','.join('y'+str(i) for i in dst)}]
def characters : Fin {m} → SS.BitString 6 := ![{chars}]
def rowSign : Fin {m} → ℚ := ![{','.join(map(str,signs))}]
def W : Matrix (Fin {m}) (Fin {n}) ℚ := !![{rows}]
def WC : Matrix (Fin {m}) (Fin {n}) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin {n} → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin {m}) (j : Fin {n}) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin {n}) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
''')
    eq='v 0+v 1=0' if n==2 else 'v 0+v ⟨5,by decide⟩=0 ∧ v 1+v ⟨2,by decide⟩+v ⟨3,by decide⟩+v ⟨4,by decide⟩=0'
    parts.append(f'''theorem row_reduction (v : Fin {n} → ℂ) : WC *ᵥ v=0 ↔ {eq} := by
  constructor
  · intro h
    have h0 := congrFun h 0
''')
    if m==2:parts.append('    have h1 := congrFun h 1\n')
    parts.append('    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n')
    if m==1:parts.append('    exact h0\n')
    else:parts.append('    constructor\n    · linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1\n    · linear_combination (1/2 : ℂ)*h0+(1/2 : ℂ)*h1\n')
    if m==1:parts.append('  · intro h0\n    ext i\n    fin_cases i\n    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n    exact h0\n')
    else:parts.append('  · rintro ⟨h0,h1⟩\n    ext i\n    fin_cases i\n    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n      linear_combination h0+h1\n    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n      linear_combination -h0+h1\n')
    parts.append(f'''theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y{dst[0]})*d z{src[0]}+star (c y{dst[-1]})*d z{src[-1]}=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using {'he' if n==2 else 'he.1'}
end Row{r:02d}
''')
parts.append('\nend\nend MainTheory.Orbit50PrintedRows\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/Orbit50PrintedRows.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated seven literal tables, complementary indexing and signed physical row reductions')
