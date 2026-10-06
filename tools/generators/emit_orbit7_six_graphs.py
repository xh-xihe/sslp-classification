"""Propose exact six-template graph witnesses, checked by kernel reduction."""
from itertools import combinations,permutations
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
edges=list(combinations(range(5),2))
templates=[
 {e for e in edges if 0 in e},
 {e for e in edges if (e[0]<2) != (e[1]<2)},
 {e for e in edges if not (e[0]<3 and e[1]<3)},
 set(edges)-{(0,1),(2,3)},set(edges)-{(0,1)},set(edges)]
def admissible(g):
    for v in range(5):
        a,b,c,d=[j for j in range(5) if j!=v]
        if sum(e in g and f in g for e,f in [((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))])==1:
            return False
    return all(any(v in e for e in g) for v in range(5))
def mask(es):
    return '⟨'+','.join('true' if e in es else 'false' for e in edges)+'⟩'
ks=[]; ps=[]; active=0
for idx in range(1024):
    g={e for j,e in enumerate(edges) if idx&(1<<j)}
    witness=(0,tuple(range(5)))
    if admissible(g):
        active+=1
        found=False
        for k,t in enumerate(templates):
            if len(g)!=len(t): continue
            for p in permutations(range(5)):
                if all((e in g)==(tuple(sorted((p[e[0]],p[e[1]]))) in t) for e in edges):
                    witness=(k,p);found=True;break
            if found:break
        if not found:raise RuntimeError(('unclassified',idx,g))
    ks.append(str(witness[0])); ps.append('!['+','.join(map(str,witness[1]))+']')
fields=['e'+''.join(map(str,e)) for e in edges]
out=['import SixQubit.Orbit7Mask','',
 'set_option autoImplicit false','set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
 'namespace MainTheory.Orbit7SixGraphs','',
 'open SixQubit.Orbit7Mask','',
 'def templates : Fin 6 → Mask := !['+','.join(map(mask,templates))+']','',
 'def index (g : Mask) : Fin 1024 :=',
 '  '+' + '.join(f'(if g.{f} then {1<<i} else 0)' for i,f in enumerate(fields)),'',
 *sum(([f'def templateBlock{k} : Fin 32 → Fin 6 := !['+','.join(ks[k*32:(k+1)*32])+']',
        f'def permutationBlock{k} : Fin 32 → Fin 5 → Fin 5 := !['+','.join(ps[k*32:(k+1)*32])+']',''] for k in range(32)),[]),
 'def templateIndex (i : Fin 1024) : Fin 6 :=',
 '  (!['+','.join(f'templateBlock{k}' for k in range(32))+'] (⟨i.val/32,by omega⟩ : Fin 32)) ⟨i.val%32,by omega⟩','',
 'def permutation (i : Fin 1024) : Fin 5 → Fin 5 :=',
 '  (!['+','.join(f'permutationBlock{k}' for k in range(32))+'] (⟨i.val/32,by omega⟩ : Fin 32)) ⟨i.val%32,by omega⟩','',
 'theorem permutation_bijective : ∀ k : Fin 1024, Function.Bijective (permutation k) := by decide +kernel','',
 'theorem certificate : ∀ '+' '.join(fields)+' : Bool,',
 '    let g : Mask := ⟨'+','.join(fields)+'⟩',
 '    AdmissibleB g = true → isolatedB g = false →',
 '      ∀ i j : Fin 5, edge g i j =',
 '        edge (templates (templateIndex (index g))) (permutation (index g) i) (permutation (index g) j) := by',
 '  decide +kernel','',
 'noncomputable def relabel (k : Fin 1024) : Equiv.Perm (Fin 5) := Equiv.ofBijective (permutation k) (permutation_bijective k)','',
 'theorem classification (g : Mask) (hg : AdmissibleB g = true) (hi : ¬ Isolated g) :',
 '    ∃ k : Fin 6, ∃ p : Equiv.Perm (Fin 5), ∀ i j, edge g i j = edge (templates k) (p i) (p j) := by',
 '  have hiB : isolatedB g = false := by',
 '    cases hb : isolatedB g',
 '    · rfl',
 '    · exact (hi ((isolatedB_eq_true g).mp hb)).elim',
 '  refine ⟨templateIndex (index g),relabel (index g),?_⟩',
 '  rcases g with ⟨'+','.join(fields)+'⟩',
 '  exact certificate '+' '.join(fields)+' hg hiB','',
 'end MainTheory.Orbit7SixGraphs','']
(ROOT/'MainTheory/Orbit7SixGraphs.lean').write_text('\n'.join(out),encoding='utf-8')
print('Wrote six-template kernel witnesses for',active,'admissible graphs with no isolated vertex.')
