"""Generate the five literal orbit-51 rectangular cross systems."""
from pathlib import Path
import re
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
text=(ROOT/'SixQubit/Orbit51.lean').read_text(encoding='utf8')
words={name:[x=='true' for x in values.split()] for name,values in
       re.findall(r'def ([yz]\d+) : SS.BitString 6 := bs ((?:(?:true|false)\s+){5}(?:true|false))',text)}
parts=['''import MainTheory.OrderThreePrintedMoments
import MainTheory.RectangularFlipCharacters

/-! Every orbit-51 flip and incidence printed in the SI. Rectangular
character systems retain all incidences and all zero-amplitude boundaries.
Both directions of the printed kernels and row reductions are checked. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit51PrintedRows
open scoped BigOperators Matrix
open SixQubit.Orbit51
noncomputable section
''']
DATA=[([2],[9,8,1,0],[0,1,8,9],[[],[0],[3]]),
      ([5],[9,8,3,2],[2,3,8,9],[[],[0],[3]]),
      ([0,3],[6,7,8,9],[8,9,6,7],[[],[0],[3],[0,3]]),
      ([0,4],[6,7,8,9],[9,8,7,6],[[],[0],[4],[0,4]]),
      ([0,1],[3,2,1,0],[0,1,2,3],[[],[0],[1],[0,1]])]
def idx(i):return f'⟨{i},by decide⟩'
def bits(indices):
    return '(fun _ => false)' if not indices else ('SS.stdBasis '+idx(indices[0]) if len(indices)==1 else
        f'SS.bxor (SS.stdBasis {idx(indices[0])}) (SS.stdBasis {idx(indices[1])})')
for r,(flip,src,dst,chars) in enumerate(DATA):
    for a,b in zip(src,dst):
        assert [x!=(i in flip) for i,x in enumerate(words['z'+str(a)])]==words['y'+str(b)]
    W=s.Matrix([[(-1)**sum(words['z'+str(a)][i] for i in indices) for a in src] for indices in chars])
    if r<2:
        assert W==s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1]])
        target=s.Matrix([[1,0,0,-1],[0,1,-1,0],[1,1,0,0]])
    elif r<4:
        p,q=(2,3) if r==2 else (3,2)
        target=s.Matrix([[int(i in [0,p]) for i in range(4)],
                         [int(i in [1,q]) for i in range(4)]])
    else:target=s.ones(1,4)
    def coefficients(A,B):
        out=[]
        for row in B.tolist():
            solution=list(s.linsolve((A.T,s.Matrix(row))))[0]
            free=set().union(*(x.free_symbols for x in solution))
            out.append([x.subs(dict.fromkeys(free,0)) for x in solution])
        assert s.Matrix(out)*A==B
        return out
    K=coefficients(W,target);T=coefficients(target,W);m=W.rows
    parts.append(f'''
namespace Row{r:02d}
def flip : SS.BitString 6 := {bits(flip)}
def sources : Fin 4 → SS.BitString 6 := ![{','.join('z'+str(i) for i in src)}]
def destinations : Fin 4 → SS.BitString 6 := ![{','.join('y'+str(i) for i in dst)}]
def characters : Fin {m} → SS.BitString 6 := ![{','.join(bits(x) for x in chars)}]
def W : Matrix (Fin {m}) (Fin 4) ℚ := !![{';'.join(','.join(map(str,row)) for row in W.tolist())}]
def WC : Matrix (Fin {m}) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters sources=WC := by
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
  exact MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
''')
    if r<2:
        eq='v 0=v ⟨3,by decide⟩ ∧ v 1=v ⟨2,by decide⟩ ∧ v 0+v 1=0'
        literals=[f'star (c y{dst[0]})*d z{src[0]}=star (c y{dst[3]})*d z{src[3]}',
                  f'star (c y{dst[1]})*d z{src[1]}=star (c y{dst[2]})*d z{src[2]}',
                  f'star (c y{dst[0]})*d z{src[0]}+star (c y{dst[1]})*d z{src[1]}=0']
    elif r<4:
        eq=f'v 0+v {idx(p)}=0 ∧ v 1+v {idx(q)}=0'
        literals=[f'star (c y{dst[0]})*d z{src[0]}+star (c y{dst[p]})*d z{src[p]}=0',
                  f'star (c y{dst[1]})*d z{src[1]}+star (c y{dst[q]})*d z{src[q]}=0']
    else:
        eq='v 0+v 1+v ⟨2,by decide⟩+v ⟨3,by decide⟩=0'
        literals=['+'.join(f'star (c y{b})*d z{a}' for a,b in zip(src,dst))+'=0']
    parts.append(f'theorem row_reduction (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ {eq} := by\n  constructor\n  · intro h\n')
    for i in range(m):parts.append(f'    have h{i} := congrFun h {idx(i)}\n')
    parts.append('    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n')
    if len(K)>1:parts.append('    refine ⟨?_,?_'+(',?_' if len(K)==3 else '')+'⟩\n')
    for row in K:
        expr=' + '.join(f'({x} : ℂ)*h{i}' for i,x in enumerate(row) if x)
        parts.append(('    ·' if len(K)>1 else '   ')+' linear_combination '+expr+'\n')
    parts.append('  · '+('rintro ⟨'+','.join('h'+str(i) for i in range(len(K)))+'⟩\n' if len(K)>1 else 'intro h0\n')+'    ext i\n    fin_cases i\n')
    for row in T:
        expr=' + '.join(f'({x} : ℂ)*h{i}' for i,x in enumerate(row) if x)
        parts.append('    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *\n      linear_combination '+expr+'\n')
    if r<2:
        parts.append('''theorem kernel_span (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ ∃ a : ℂ, v=![a,-a,-a,a] := by
  constructor
  · intro h
    obtain ⟨h0,h1,h2⟩ := (row_reduction v).1 h
    refine ⟨v 0,?_⟩
    ext i
    fin_cases i
    · rfl
    · change v 1= -v 0
      linear_combination h2
    · change v ⟨2,by decide⟩= -v 0
      linear_combination h2-h1
    · change v ⟨3,by decide⟩=v 0
      exact h0.symm
  · rintro ⟨a,rfl⟩
    apply (row_reduction _).2
    norm_num [Fin.succ]
''')
    parts.append(f'''theorem physical_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : {' ∧ '.join(literals)} := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row{r:02d}
''')
parts.append('\nend\nend MainTheory.Orbit51PrintedRows\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/Orbit51PrintedRows.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated five literal cross systems and both directions of the two one-dimensional kernels')
