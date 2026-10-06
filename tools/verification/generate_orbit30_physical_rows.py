"""Expose the literal K5 reciprocal, star and matching physical Walsh rows."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def vec(xs):return '!['+','.join(xs)+']'
def expr(xs):return ' + '.join(xs) or '0'
vertices=[0,1,2,4,8]
edges=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
idx=dict(zip(edges,[14,13,11,7,12,10,6,9,5,3]))
def edge(i,j):return idx[tuple(sorted((i,j)))] if i!=j else 0
source=(ROOT/'SixQubit/Orbit30.lean').read_text(encoding='utf8')
header=source.split('theorem rows (c d',1)[1].split(' := by',1)[0]
native=header.split(' :\n    ',1)[1]
flips=re.findall(r'offSum c d (ef\d+) (w\d+) = 0',header)
assert len(flips)==35
names=[f'D{i}_{j}' for i in range(5) for j in range(5) if i!=j]+[f'M{i}' for i in range(5)]+[f'R{i}' for i in range(5)]+[f'T{i}' for i in range(5)]
T=[expr(f'pointU c {fin(j)}*edgeV d {fin(i)} {fin(j)}' for j in range(5) if i!=j) for i in range(5)]
M=[]
for i in range(5):
    a,b,c,d=[j for j in range(5) if j!=i]
    pairs=[((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))]
    M.append(expr(term for (j,k),(l,m) in pairs for term in
      [f'edgeU c {fin(j)} {fin(k)}*edgeV d {fin(l)} {fin(m)}',
       f'edgeU c {fin(l)} {fin(m)}*edgeV d {fin(j)} {fin(k)}']))
lean=f'''import MainTheory.Orbit30ProbabilityLabels
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit30PhysicalRows
open SixQubit.Orbit30
open MainTheory.Orbit30PrintedMoments MainTheory.Orbit30ProbabilityLabels
noncomputable section
def pointC (c : SS.State 6 ℂ) (i : Fin 5) : ℂ := c (bottom (vertexIndex i))
def pointV (d : SS.State 6 ℂ) (i : Fin 5) : ℂ := d (top (complementIndex (vertexIndex i)))
def edgeIndexMatrix : Fin 5 → Fin 5 → Fin 16 := {vec(vec(fin(edge(i,j)) for j in range(5)) for i in range(5))}
def edgeC (c : SS.State 6 ℂ) (i j : Fin 5) : ℂ :=
  if i=j then 0 else c (bottom (edgeIndexMatrix i j))
def edgeV (d : SS.State 6 ℂ) (i j : Fin 5) : ℂ :=
  if i=j then 0 else d (top (complementIndex (edgeIndexMatrix i j)))
def pointU (c : SS.State 6 ℂ) (i : Fin 5) : ℂ := star (pointC c i)
def edgeU (c : SS.State 6 ℂ) (i j : Fin 5) : ℂ := star (edgeC c i j)
def anchorU (c : SS.State 6 ℂ) : ℂ := star (c y15)
def anchorV (d : SS.State 6 ℂ) : ℂ := d z0
def starSum (c d : SS.State 6 ℂ) : Fin 5 → ℂ := {vec(T)}
def matchingSum (c d : SS.State 6 ℂ) : Fin 5 → ℂ := {vec(M)}
def NativeRows (c d : SS.State 6 ℂ) : Prop :=
    {native}
theorem physical_native_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : NativeRows c d := by
  exact SixQubit.Orbit30.rows c d
'''
lean+=''.join(f'    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl {e} {w} (by decide))\n' for e,w in flips)
lean+='''theorem canonical_rows (c d : SS.State 6 ℂ) (h : NativeRows c d) :
    (∀ i j,i≠j → pointU c j*edgeV d i j-edgeU c i j*pointV d j=0) ∧
    (∀ i,anchorU c*pointV d i+pointU c i*anchorV d=0) ∧
    (∀ i,starSum c d i=0) ∧ (∀ i,matchingSum c d i=0) := by
'''
lean+='  rcases h with ⟨'+','.join(names)+'⟩\n  refine ⟨?_,?_,?_,?_⟩\n  · intro i j hi\n    fin_cases i <;> fin_cases j\n'
for i in range(5):
    for j in range(5):
        if i==j:lean+='    · exact False.elim (hi rfl)\n'
        else:
            vi=vertices[j];ei=edge(i,j)
            lean+=f'    · change star (c y{vi})*d z{15-ei}-star (c y{ei})*d z{15-vi}=0\n      exact D{i}_{j}\n'
lean+='  · intro i\n    fin_cases i\n'
for i in range(5):
    vi=vertices[i]
    lean+=f'    · change star (c y15)*d z{15-vi}+star (c y{vi})*d z0=0\n      exact R{i}\n'
lean+='  · intro i\n    fin_cases i\n'
for i in range(5):
    terms=expr(f'star (c y{vertices[j]})*d z{15-edge(i,j)}' for j in range(5) if i!=j)
    lean+=f'    · change {terms}=0\n      exact T{i}\n'
lean+='  · intro i\n    fin_cases i\n'
for i in range(5):
    a,b,c,d=[j for j in range(5) if j!=i]
    terms=[]
    for (j,k),(l,m) in [((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))]:
        x,y=edge(j,k),edge(l,m)
        terms.extend([f'star (c y{x})*d z{15-y}',f'star (c y{y})*d z{15-x}'])
    lean+=f'    · change {expr(terms)}=0\n      exact M{i}\n'
lean+='''theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ i j,i≠j → pointU c j*edgeV d i j-edgeU c i j*pointV d j=0) ∧
    (∀ i,anchorU c*pointV d i+pointU c i*anchorV d=0) ∧
    (∀ i,starSum c d i=0) ∧ (∀ i,matchingSum c d i=0) :=
  canonical_rows c d (physical_native_rows c d hc hd hkl)
end
end MainTheory.Orbit30PhysicalRows
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
target=ROOT/'MainTheory/Orbit30PhysicalRows.lean'
if args.check:
    if target.read_text(encoding='utf8')!=lean:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(lean,encoding='utf8',newline='\n')
