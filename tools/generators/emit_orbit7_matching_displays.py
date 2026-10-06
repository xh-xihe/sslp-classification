"""Emit finite matching expansions; every equality is checked by Lean."""
from itertools import combinations
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
def edge(e):
    return f'({e[0]},{e[1]})'
rows=[]
for v in range(5):
    a,b,c,d=[j for j in range(5) if j!=v]
    rows.append([((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))])
out=['import SixQubit.Orbit7FullTangent','',
 'set_option autoImplicit false','set_option maxRecDepth 100000','',
 'namespace MainTheory.Orbit7MatchingDisplays','',
 'open SixQubit.Orbit7Universal','',
 'abbrev Edge := Fin 5 × Fin 5','',
 'def matchings : Fin 5 → Fin 3 → Edge × Edge :=',
 '  !['+',\n    '.join('!['+','.join(f'({edge(e)},{edge(f)})' for e,f in row)+']' for row in rows)+']','',
 'def nonincidentExplicit : Fin 5 → Finset Edge :=',
 '  !['+',\n    '.join('{'+','.join(edge(e) for e in combinations([j for j in range(5) if j!=v],2))+'}' for v in range(5))+']','',
 'theorem nonincidentPairs_explicit : ∀ v, nonincidentPairs v = nonincidentExplicit v := by decide +kernel','',
 'theorem hafnian_sum (x : Edge → ℂ) (i : Fin 5) :',
 '    Hafnian5 x i = ∑ k : Fin 3, x (matchings i k).1 * x (matchings i k).2 := by',
 '  fin_cases i <;> simp [Hafnian5,matchings,Fin.sum_univ_succ] <;> ring','',
 'theorem polar_sum (x y : Edge → ℂ) (i : Fin 5) :',
 '    PolarHafnian5 x y i = ∑ k : Fin 3,',
 '      (x (matchings i k).1 * y (matchings i k).2 +',
 '        x (matchings i k).2 * y (matchings i k).1) := by',
 '  fin_cases i <;> simp [PolarHafnian5,matchings,Fin.sum_univ_succ] <;> ring','',
 'noncomputable def matchingMatrix (A B : Edge → Spinor) (i : Fin 5) : Mat2 := fun p q =>',
 '  ∑ k : Fin 3, (B (matchings i k).2 p * star (A (matchings i k).1 q) +',
 '    B (matchings i k).1 p * star (A (matchings i k).2 q))','',
 'theorem oneflip_expansion (c d : SS.State 6 ℂ) (i : Fin 5) :',
 '    oneFlipMat c d i = matchingMatrix (fun e => spinor c (aBase e.1 e.2))',
 '      (fun e => spinor d (bBase e.1 e.2)) i := by',
 '  funext p q','  simp only [oneFlipMat,nonincidentPairs_explicit]','  fin_cases i']
for v in range(5):
    edges=list(combinations([j for j in range(5) if j!=v],2))
    out += ['  · simp [nonincidentExplicit]',
      '    rw [']
    eqs=[]
    for a,b in edges:
        c,d=[j for j in range(5) if j not in [v,a,b]]
        eqs.append(f'      show SS.bxor (bBase {a} {b}) (vmask {v}) = aBase {c} {d} by decide')
    out += [',\n'.join(eqs)+']',
      '    simp [matchingMatrix,matchings,Fin.sum_univ_succ]',
      '    ring']
out += ['', 'end MainTheory.Orbit7MatchingDisplays','']
(ROOT/'MainTheory/Orbit7MatchingDisplays.lean').write_text('\n'.join(out),encoding='utf-8')
print('Wrote Orbit7MatchingDisplays.lean')
