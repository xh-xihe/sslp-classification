"""Generate complete real complement-normal form identities for actual orbit 30."""
import re
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def vec(xs):return '!['+','.join(xs)+']'
def expr(xs):return ' + '.join(xs) or '0'
source=(ROOT/'SixQubit/Orbit30.lean').read_text(encoding='utf8')
fields=re.findall(r'^  (n[01]|m[1-6](?:[1-6])?|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
v=s.symbols('q0:16 r0:16');q=v[:16];r=v[16:];loc={str(x):x for x in v}
eq=[s.expand(s.sympify(a,locals=loc)-s.sympify(b,locals=loc)) for _,a,b in fields]
def row(e):return [e.coeff(x) for x in v]+[e.subs(dict.fromkeys(v,0))]
A=s.Matrix([row(e) for e in eq]).T
def proof(e):
    co,free=A.gauss_jordan_solve(s.Matrix(row(s.expand(e))))
    co=co.subs(dict.fromkeys(free,0))
    return 'linear_combination '+expr([f'({c} : ℝ)*hm.{fields[j][0]}' for j,c in enumerate(co) if c])
words=[x for _,x in sorted([(int(i),x) for i,x in re.findall(r'^def y(\d+) : SS.BitString 6 := bs .+?--\s*([01]{6})',source,re.M)])]
assert len(words)==16 and len(fields)==23
balance=[sum(q[i] for i,w in enumerate(words) if w[j]=='1')-s.Rational(1,2) for j in range(6)]
refs={x:'p '+fin(i) for i,x in enumerate(q)}|{x:'t '+fin(15-i) for i,x in enumerate(r)}
def translate(e):
    text=str(s.expand(e))
    return re.sub(r'\b(?:q|r)\d+\b',lambda m:'('+refs[loc[m.group()]]+')',text)
coordinate_expr=[expr('p '+fin(i) for i,w in enumerate(words) if w[j]=='1') for j in range(6)]
word_defs=','.join('y'+str(i) for i in range(16))
native='MomentSystem '+' '.join('(p '+fin(i)+')' for i in range(16))+' '+' '.join('(t '+fin(15-i)+')' for i in range(16))
parts=[f'''import SixQubit.CodeOrbit30
set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace MainTheory.Orbit30PrintedMoments
open SixQubit.Orbit30
open scoped BigOperators
noncomputable section
def bottom : Fin 16 → SS.BitString 6 := {vec('y'+str(i) for i in range(16))}
def top : Fin 16 → SS.BitString 6 := {vec('z'+str(i) for i in range(16))}
def complementIndex : Fin 16 → Fin 16 := fun i => ⟨15-i.val,by omega⟩
theorem actual_fibers : S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top ∧
    (∀ i,top (complementIndex i)=SS.complement (bottom i)) := by decide +kernel
def Moment (p t : Fin 16 → ℝ) : Prop := {native}
def coordinateSum (p : Fin 16 → ℝ) : Fin 6 → ℝ :=
  {vec(coordinate_expr)}
theorem literal_coordinate_sum (p : Fin 16 → ℝ) (j : Fin 6) :
    coordinateSum p j=∑ i,p i*(if bottom i j then (1 : ℝ) else 0) := by
  fin_cases j <;> norm_num [coordinateSum,bottom,{word_defs},bs,Fin.sum_univ_succ,Fin.succ] <;> ring
def totalSum (p : Fin 16 → ℝ) : ℝ := {expr('p '+fin(i) for i in range(16))}
theorem literal_total_sum (p : Fin 16 → ℝ) : totalSum p=∑ i,p i := by
  simp [totalSum,Fin.sum_univ_succ,Fin.succ]
  ring
def Normal (p t : Fin 16 → ℝ) : Prop :=
  t=p ∧ (∀ i,0 ≤ p i) ∧ totalSum p=1 ∧ (∀ j,coordinateSum p j=1/2)
''']
for i in range(16):
    parts.append(f'''theorem complement{i} (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t {fin(i)}=p {fin(i)} := by
  {proof(r[15-i]-q[i])}
''')
for j in range(6):
    parts.append(f'''theorem balance{j} (p t : Fin 16 → ℝ) (hm : Moment p t) :
    coordinateSum p {fin(j)}=1/2 := by
  change {coordinate_expr[j]}=1/2
  {proof(balance[j])}
''')
parts.append('''theorem normal_of_moment (p t : Fin 16 → ℝ) (hm : Moment p t) : Normal p t := by
  refine ⟨?_,?_,?_,?_⟩
  · funext i
    fin_cases i
''')
parts.extend(f'    · exact complement{i} p t hm\n' for i in range(16))
parts.append('''  · intro i
    fin_cases i
''')
parts.extend(f'    · exact hm.nq{i}\n' for i in range(16))
parts.append('''  · exact hm.n0
  · intro j
    fin_cases j
''')
parts.extend(f'    · exact balance{j} p t hm\n' for j in range(6))
parts.append('''theorem moment_of_normal (p t : Fin 16 → ℝ) (h : Normal p t) : Moment p t := by
  rcases h with ⟨ht,hn,hs,hb⟩
  rw [ht]
''')
parts.extend(f'  have hb{j} := hb {fin(j)}\n  change {coordinate_expr[j]}=1/2 at hb{j}\n' for j in range(6))
parts.append('  change '+expr('p '+fin(i) for i in range(16))+'=1 at hs\n  unfold Moment\n  constructor\n')
for name,lhs,rhs in fields:
    if name.startswith('n'):
        parts.append('  · linarith only [hs]\n')
    else:
        parts.append('  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]\n')
parts.extend(f'  · exact hn {fin(i)}\n' for i in range(16))
parts.extend(f'  · exact hn {fin(15-i)}\n' for i in range(16))
parts.append('''theorem complete_normal (p t : Fin 16 → ℝ) : Moment p t ↔ Normal p t :=
  ⟨normal_of_moment p t,moment_of_normal p t⟩
def bottomProbability (c : SS.State 6 ℂ) : Fin 16 → ℝ := fun i => Complex.normSq (c (bottom i))
def topProbability (d : SS.State 6 ℂ) : Fin 16 → ℝ :=
  fun i => Complex.normSq (d (top (complementIndex i)))
theorem physical_moments (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3) :
    Moment (bottomProbability c) (topProbability d) := by
  exact SixQubit.Orbit30.moments c d hc hd hnc hnd hkl
theorem physical_normal (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3) :
    Normal (bottomProbability c) (topProbability d) :=
  normal_of_moment _ _ (physical_moments c d hc hd hnc hnd hkl)
end
end MainTheory.Orbit30PrintedMoments
''')
lean=''.join(parts)
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
target=ROOT/'MainTheory/Orbit30PrintedMoments.lean'
if args.check:
    if target.read_text(encoding='utf8')!=lean:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(lean,encoding='utf8',newline='\n')
