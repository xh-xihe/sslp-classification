"""Generate the twelve literal orbit-49 SI cross tables and row reductions."""
from pathlib import Path
import re
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
text=(ROOT/'SixQubit/Orbit49.lean').read_text(encoding='utf8')
words={name:[x=='true' for x in values.split()] for name,values in
       re.findall(r'def ([yz]\d+) : SS.BitString 6 := bs ((?:(?:true|false)\s+){5}(?:true|false))',text)}
parts=['''import MainTheory.OrderThreePrintedMoments
import MainTheory.FlipCharacterObstruction

/-! The exact twelve orbit-49 masks printed in the SI. All four physical
Pauli dressings, every endpoint, and both directions of each literal row
reduction are checked. No impossibility result proves an intermediate row. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit49PrintedRows
open scoped BigOperators Matrix
open SixQubit.Orbit49
noncomputable section
''']
DATA=[(3,5,[0,1,8,9],[8,9,0,1]),(4,5,[0,1,8,9],[9,8,1,0]),
      (2,3,[2,3,8,9],[8,9,2,3]),(2,4,[2,3,8,9],[9,8,3,2]),
      (1,3,[4,5,8,9],[8,9,4,5]),(1,4,[4,5,8,9],[9,8,5,4]),
      (0,3,[6,7,8,9],[8,9,6,7]),(0,4,[6,7,8,9],[9,8,7,6]),
      (0,1,[3,2,1,0],[0,1,2,3]),(0,2,[5,4,1,0],[0,1,4,5]),
      (0,5,[5,4,3,2],[2,3,4,5]),(1,2,[7,6,1,0],[0,1,6,7])]
for r,(u,v,src,dst) in enumerate(DATA):
    flip=[i in [u,v] for i in range(6)]
    for a,b in zip(src,dst):
        assert [x!=y for x,y in zip(words['z'+str(a)],flip)]==words['y'+str(b)]
    W=s.Matrix([[(-1)**sum(words['z'+str(a)][i] for i in indices) for a in src]
                for indices in [[],[u],[v],[u,v]]])
    if r<8:
        i0,i1=(2,3) if r%2==0 else (3,2)
        target=s.Matrix([[int(i in [0,i0]) for i in range(4)],
                         [int(i in [1,i1]) for i in range(4)]])
    else:target=s.ones(1,4)
    K=[]
    for row in target.tolist():
        sol=list(s.linsolve((W.T,s.Matrix(row))))[0]
        free=set().union(*(x.free_symbols for x in sol))
        K.append([x.subs(dict.fromkeys(free,0)) for x in sol])
    assert s.Matrix(K)*W==target
    T=[]
    for row in W.tolist():
        T.append([row[0],row[1]] if r<8 else [row[0]])
    assert s.Matrix(T)*target==W
    rows=';'.join(','.join(map(str,row)) for row in W.tolist())
    parts.append(f'''
namespace Row{r:02d}
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨{u},by decide⟩) (SS.stdBasis ⟨{v},by decide⟩)
def sources : Fin 4 → SS.BitString 6 := ![{','.join('z'+str(i) for i in src)}]
def destinations : Fin 4 → SS.BitString 6 := ![{','.join('y'+str(i) for i in dst)}]
def characters : Fin 4 → SS.BitString 6 :=
  ![(fun _ => false),SS.stdBasis ⟨{u},by decide⟩,SS.stdBasis ⟨{v},by decide⟩,flip]
def W : Matrix (Fin 4) (Fin 4) ℚ := !![{rows}]
def WC : Matrix (Fin 4) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
''')
    equation=f'v 0+v ⟨{i0},by decide⟩=0 ∧ v 1+v ⟨{i1},by decide⟩=0' if r<8 else 'v 0+v 1+v ⟨2,by decide⟩+v ⟨3,by decide⟩=0'
    parts.append(f'''theorem row_reduction (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ {equation} := by
  constructor
  · intro h
''')
    for i in range(4):
        parts.append(f'    have h{i} := congrFun h ⟨{i},by decide⟩\n')
    parts.append('    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n')
    if r<8:parts.append('    constructor\n')
    for row in K:
        expr=' + '.join(f'({x} : ℂ)*h{i}' for i,x in enumerate(row) if x)
        parts.append(('    ·' if r<8 else '   ')+' linear_combination '+expr+'\n')
    parts.append('  · '+('rintro ⟨h0,h1⟩\n' if r<8 else 'intro h0\n')+'    ext i\n    fin_cases i\n')
    for row in T:
        expr=' + '.join(f'({x} : ℂ)*h{i}' for i,x in enumerate(row) if x)
        parts.append('    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n      linear_combination '+expr+'\n')
    polys=[f'star (c y{dst[0]})*d z{src[0]}+star (c y{dst[i0]})*d z{src[i0]}=0',
           f'star (c y{dst[1]})*d z{src[1]}+star (c y{dst[i1]})*d z{src[i1]}=0'] if r<8 else [
           '+'.join(f'star (c y{b})*d z{a}' for a,b in zip(src,dst))+'=0']
    parts.append(f'''theorem physical_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : {' ∧ '.join(polys)} := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row{r:02d}
''')
parts.append('\nend\nend MainTheory.Orbit49PrintedRows\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/Orbit49PrintedRows.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated all twelve literal four-Pauli cross tables and bidirectional row reductions')
