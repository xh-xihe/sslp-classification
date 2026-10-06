"""Supply relabeling witnesses; the kernel checks every five-vertex mask."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
import itertools
WORK=Path(__file__).resolve().parent
edges=list(itertools.combinations(range(5),2))
edge_index={e:i for i,e in enumerate(edges)}
reps=[512,192,768,896,200,704,184,424,480,220]
def adj(m,i,j):return False if i==j else bool(m&(1<<edge_index[tuple(sorted((i,j)))]))
def valid(m):return m!=0 and all(sum(adj(m,i,j) for j in range(5))<=2 for i in range(5))
perms=list(itertools.permutations(range(5)))
witness=[];typ=[]
for m in range(1024):
    if not valid(m):witness.append(tuple(range(5)));typ.append(0);continue
    found=next((r,p) for r,rm in enumerate(reps) for p in perms
      if all(adj(m,i,j)==adj(rm,p[i],p[j]) for i,j in edges))
    typ.append(found[0]);witness.append(found[1])
def vec(xs):return '!['+','.join(xs)+']'
def fin(i):return f'⟨{i},by decide⟩'
index=[[0 if i==j else edge_index[tuple(sorted((i,j)))] for j in range(5)] for i in range(5)]
blocks=''
for b in range(16):
    blocks+=f'def typeBlock{b} : Fin 64 → Fin 10 := '+vec(fin(i) for i in typ[b*64:(b+1)*64])+'\n'
    blocks+=f'def relabelBlock{b} : Fin 64 → Fin 5 → Fin 5 := '+vec(vec(fin(i) for i in p) for p in witness[b*64:(b+1)*64])+'\n'
lean=f'''import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit30GraphClassification
open scoped BigOperators
def endpoints : Fin 10 → Fin 5 × Fin 5 := {vec('('+fin(i)+','+fin(j)+')' for i,j in edges)}
def edgeIndex : Fin 5 → Fin 5 → Fin 10 := {vec(vec(fin(i) for i in row) for row in index)}
def missing (m : Fin 1024) (i j : Fin 5) : Bool :=
  if i=j then false else Nat.testBit m.val (edgeIndex i j).val
def degree (m : Fin 1024) (i : Fin 5) : ℕ := ∑ j : Fin 5,if missing m i j then 1 else 0
def Admissible (m : Fin 1024) : Prop := m.val≠0 ∧ ∀ i,degree m i≤2
instance (m : Fin 1024) : Decidable (Admissible m) := by unfold Admissible; infer_instance
def representative : Fin 10 → Fin 1024 := {vec(fin(i) for i in reps)}
{blocks}
def typeBlocks : Fin 16 → Fin 64 → Fin 10 := {vec('typeBlock'+str(i) for i in range(16))}
def relabelBlocks : Fin 16 → Fin 64 → Fin 5 → Fin 5 := {vec('relabelBlock'+str(i) for i in range(16))}
def typeWitness (m : Fin 1024) : Fin 10 :=
  typeBlocks ⟨m.val/64,by omega⟩ ⟨m.val%64,by omega⟩
def relabelWitness (m : Fin 1024) : Fin 5 → Fin 5 :=
  relabelBlocks ⟨m.val/64,by omega⟩ ⟨m.val%64,by omega⟩
theorem literal_representatives : Function.Injective representative ∧
    (∀ r,Admissible (representative r)) := by decide +kernel
theorem exhaustive_relabeling : ∀ m,Admissible m →
    Function.Bijective (relabelWitness m) ∧
    (∀ i j,missing m i j=missing (representative (typeWitness m)) (relabelWitness m i) (relabelWitness m j)) :=
  by decide +kernel
def pattern (m : Fin 1024) : Fin 10 → Bool := fun e => Nat.testBit m.val e.val
end MainTheory.Orbit30GraphClassification
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
target=ROOT/'MainTheory/Orbit30GraphClassification.lean'
if args.check:
    if target.read_text(encoding='utf8')!=lean:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(lean,encoding='utf8',newline='\n')
print('All masks',1024,'admissible masks',sum(map(valid,range(1024))),'literal types',len(reps))
