"""Generate the literal six monomial and four odd binomial support exclusions."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def term(p):return '*'.join('z '+fin(i) for i in p)
def vec(xs):return '!['+','.join(xs)+']'
H=[[(4,9),(5,8),(6,7)],[(1,9),(2,8),(3,7)],[(0,9),(2,6),(3,5)],[(0,8),(1,6),(3,4)],[(0,7),(1,5),(2,4)]]
monos=[(220,0,(5,8)),(480,0,(4,9)),(424,0,(4,9)),(704,0,(5,8)),(200,2,(0,9)),(768,0,(6,7))]
bins=[(184,[1,2,3],[(1,9),(2,6),(0,8)],[(2,8),(0,9),(1,6)]),
      (896,[2,3,4],[(2,6),(3,4),(1,5)],[(3,5),(1,6),(2,4)]),
      (192,[0,1,4],[(4,9),(2,8),(1,5)],[(5,8),(1,9),(2,4)]),
      (512,[0,1,2],[(5,8),(3,7),(2,6)],[(6,7),(2,8),(3,5)])]
def hypotheses(mask):
    out=''
    for e in range(10):
        if mask&(1<<e):out+=f'  have hz{e} : z {fin(e)}=0 := (hm {fin(e)}).2 (by decide +kernel)\n'
        else:out+=f'  have hn{e} : z {fin(e)}≠0 := by\n    intro h\n    have hf := (hm {fin(e)}).1 h\n    contradiction\n'
    return out
lean=f'''import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30ProperGraphTables
noncomputable section
def Missing (z : Fin 10 → ℂ) (m : Fin 1024) : Prop :=
  ∀ e,z e=0 ↔ Nat.testBit m.val e.val=true
def hafnian (z : Fin 10 → ℂ) : Fin 5 → ℂ :=
  {vec(' + '.join(term(p) for p in row) for row in H)}
theorem odd_product_contradiction (a b c d e f : ℂ)
    (h1 : a+d=0) (h2 : b+e=0) (h3 : c+f=0)
    (he : a*b*c=d*e*f) (hn : d*e*f≠0) : False := by
  have ha : a=-d := by linear_combination h1
  have hb : b=-e := by linear_combination h2
  have hc : c=-f := by linear_combination h3
  rw [ha,hb,hc] at he
  have hz : d*e*f=0 := by linear_combination (-1/2 : ℂ)*he
  exact hn hz
'''
for n,(mask,row,pair) in enumerate(monos):
    lean+=f'''theorem monomial{n} (z : Fin 10 → ℂ) (hm : Missing z {fin(mask)})
    (hh : hafnian z {fin(row)}=0) : False := by
'''+hypotheses(mask)
    lean+=f'  change '+ ' + '.join(term(p) for p in H[row])+'=0 at hh\n'
    zs=[f'hz{e}' for e in range(10) if mask&(1<<e)]
    lean+='  rw ['+','.join(zs)+'] at hh\n'
    lean+=f'  have he : {term(pair)}=0 := by linear_combination hh\n'
    lean+=f'  exact (mul_ne_zero hn{pair[0]} hn{pair[1]}) he\n'
for n,(mask,rows,aa,bb) in enumerate(bins):
    lean+=f'''theorem binomial{n} (z : Fin 10 → ℂ) (hm : Missing z {fin(mask)})
    (hh : ∀ i,hafnian z i=0) : False := by
'''+hypotheses(mask)
    zeros=[f'hz{e}' for e in range(10) if mask&(1<<e)]
    for j,row in enumerate(rows):
        lean+=f'  have he{j} := hh {fin(row)}\n  change '+' + '.join(term(p) for p in H[row])+'=0 at he'+str(j)+'\n'
        # Rewrite only zero factors actually present in this hafnian.
        used={e for pair in H[row] for e in pair}
        zr=[f'hz{e}' for e in range(10) if mask&(1<<e) and e in used]
        lean+='  rw ['+','.join(zr)+'] at he'+str(j)+'\n'
        lean+=f'  have hs{j} : {term(aa[j])}+{term(bb[j])}=0 := by linear_combination he{j}\n'
    args=' '.join('('+term(p)+')' for p in aa+bb)
    lean+=f'  apply odd_product_contradiction {args} hs0 hs1 hs2\n  · ring\n'
    ns=[f'(mul_ne_zero hn{p[0]} hn{p[1]})' for p in bb]
    lean+=f'  · exact mul_ne_zero (mul_ne_zero {ns[0]} {ns[1]}) {ns[2]}\n'
lean+='''end
end MainTheory.Orbit30ProperGraphTables
'''
# Delete unused witnesses and avoid rewriting absent zero factors.
for n,(mask,row,pair) in enumerate(monos):
    begin=lean.index(f'theorem monomial{n} ')
    end=lean.find('\ntheorem ',begin+1)
    if end<0:end=len(lean)
    block=lean[begin:end]
    used={e for p in H[row] for e in p}
    block=block.replace('rw ['+','.join(f'hz{e}' for e in range(10) if mask&(1<<e))+']',
        'rw ['+','.join(f'hz{e}' for e in range(10) if mask&(1<<e) and e in used)+']')
    lean=lean[:begin]+block+lean[end:]
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
target=ROOT/'MainTheory/Orbit30ProperGraphTables.lean'
if args.check:
    if target.read_text(encoding='utf8')!=lean:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(lean,encoding='utf8',newline='\n')
