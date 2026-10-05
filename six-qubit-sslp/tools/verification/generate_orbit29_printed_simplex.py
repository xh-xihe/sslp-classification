"""Emit rational elimination identities for the literal reduced orbit-29 simplex."""
import re
from pathlib import Path
import sympy as sp
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def vec(xs):return '!['+','.join(xs)+']'
variables=sp.symbols('q0:16 r0:16')
q=variables[:16];r=variables[16:]
context={str(x):x for x in variables}
block=(ROOT/'SixQubit/Orbit29.lean').read_text(encoding='utf8').split('structure MomentSystem ',1)[1].split('/-- The four top pairs',1)[0]
fields=re.findall(r'^  (\w+) : (.+) = (.+)$',block,re.M)
assert len(fields)==23
equations=[sp.expand(sp.sympify(lhs,locals=context)-sp.sympify(rhs,locals=context)) for _,lhs,rhs in fields]
names=['h.'+name for name,_,_ in fields]
def row(expression):
    return [expression.coeff(x) for x in variables]+[expression.subs(dict.fromkeys(variables,0))]
def combination(target,exprs,refs):
    if sp.expand(target)==0:return 'rfl'
    matrix=sp.Matrix([row(sp.expand(e)) for e in exprs]).T
    result,free=matrix.gauss_jordan_solve(sp.Matrix(row(sp.expand(target))))
    result=result.subs(dict.fromkeys(free,0))
    terms=[f'({str(c)} : ℝ)*{name}' for c,name in zip(result,refs) if c]
    assert terms
    return 'linear_combination '+' + '.join(terms)
zero_proof=combination(q[0]+q[1],equations,names)
balanced=[q[2+2*i]-q[3+2*i] for i in range(6)]+[r[i]-r[i+1] for i in [6,10,12,14]]
eqs=equations+balanced+[q[0],q[1]]
refs=names+[f'hb{i}' for i in range(6)]+[f'ht{i}' for i in range(4)]+['hz.1','hz.2']
a,b,c=r[4],r[2],r[0]
normalq=[0,0,b+c,b+c,a+c,a+c,a+b,a+b,sp.Rational(1,8)-a-b,sp.Rational(1,8)-a-b,
         sp.Rational(1,8)-a-c,sp.Rational(1,8)-a-c,sp.Rational(1,8)-b-c,sp.Rational(1,8)-b-c,sp.Rational(1,8),sp.Rational(1,8)]
normalr=[c,c,b,b,a,a,a+b+c,a+b+c,sp.Rational(1,8)-a-b-c,sp.Rational(1,8)-a-b-c,
         sp.Rational(1,8)-a,sp.Rational(1,8)-a,sp.Rational(1,8)-b,sp.Rational(1,8)-b,sp.Rational(1,8)-c,sp.Rational(1,8)-c]
qp=[combination(q[i]-normalq[i],eqs,refs) for i in range(16)]
rp=[combination(r[i]-normalr[i],eqs,refs) for i in range(16)]
balancedbind='\n'.join(f'  have hb{i} := hb {fin(i)}\n  change q {fin(2+2*i)}=q {fin(3+2*i)} at hb{i}' for i in range(6))+'\n'+'\n'.join(f'  have ht{i} := ht {fin(i)}\n  change r {fin(k)}=r {fin(k+1)} at ht{i}' for i,k in enumerate([6,10,12,14]))
mom='MomentSystem '+' '.join('q '+fin(i) for i in range(16))+'\n    '+' '.join('r '+fin(i) for i in range(16))
# Parenthesize function applications in the native 32-argument structure.
mom='MomentSystem '+' '.join('(q '+fin(i)+')' for i in range(16))+'\n    '+' '.join('(r '+fin(i)+')' for i in range(16))
qlean=['0','0','b+c','b+c','a+c','a+c','a+b','a+b','1/8-a-b','1/8-a-b','1/8-a-c','1/8-a-c','1/8-b-c','1/8-b-c','1/8','1/8']
rlean=['c','c','b','b','a','a','a+b+c','a+b+c','1/8-a-b-c','1/8-a-b-c','1/8-a','1/8-a','1/8-b','1/8-b','1/8-c','1/8-c']
def substitute(text):
    for v,k in [('a',4),('b',2),('c',0)]:
        text=re.sub(r'\b'+v+r'\b','(r '+fin(k)+')',text)
    return text
qcases='\n'.join(f'    · change q {fin(i)}={substitute(qlean[i])}\n      {proof}' for i,proof in enumerate(qp))
rcases='\n'.join(f'    · change r {fin(i)}={substitute(rlean[i])}\n      {proof}' for i,proof in enumerate(rp))
bottomidx=[[14,15],[13,12],[11,10],[7,6],[9,8],[5,4],[3,2]]
topidx=[[8,9],[4,5],[2,3],[0,1],[15,14],[13,12],[11,10],[7,6]]
source=f'''import MainTheory.Orbit29PhysicalPairReduction
import MainTheory.Orbit29PrintedFaceAudit

/-! Literal per-string probabilities and the exact reduced three-simplex.
Elimination identities are rational linear combinations checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace MainTheory.Orbit29PrintedSimplex
open SixQubit.Orbit29
open scoped BigOperators
noncomputable section

def Moment (q r : Fin 16 → ℝ) : Prop :=
  {mom}
def bottomIndex : Fin 6 → Fin 2 → Fin 16 :=
  {vec([vec([fin(2+2*i),fin(3+2*i)]) for i in range(6)])}
def highIndex : Fin 4 → Fin 2 → Fin 16 :=
  {vec([vec([fin(i),fin(i+1)]) for i in [6,10,12,14]])}
def normalQ (a b c : ℝ) : Fin 16 → ℝ := {vec(qlean)}
def normalR (a b c : ℝ) : Fin 16 → ℝ := {vec(rlean)}

theorem omitted_zero (q r : Fin 16 → ℝ) (h : Moment q r) :
    q ⟨0,by decide⟩=0 ∧ q ⟨1,by decide⟩=0 := by
  have hs : q ⟨0,by decide⟩+q ⟨1,by decide⟩=0 := by
    {zero_proof}
  constructor <;> linarith [h.nq0,h.nq1]

theorem reduced_normal (q r : Fin 16 → ℝ) (h : Moment q r)
    (hb : ∀ i, q (bottomIndex i 0)=q (bottomIndex i 1))
    (ht : ∀ i, r (highIndex i 0)=r (highIndex i 1)) :
    q=normalQ (r ⟨4,by decide⟩) (r ⟨2,by decide⟩) (r ⟨0,by decide⟩) ∧
    r=normalR (r ⟨4,by decide⟩) (r ⟨2,by decide⟩) (r ⟨0,by decide⟩) := by
  have hz := omitted_zero q r h
{balancedbind}
  constructor
  · funext i
    fin_cases i
{qcases}
  · funext i
    fin_cases i
{rcases}

def xs : Fin 16 → SS.BitString 6 := {vec(['y'+str(i) for i in range(16)])}
def ys : Fin 16 → SS.BitString 6 := {vec(['z'+str(i) for i in range(16)])}
def probabilities (c : SS.State 6 ℂ) (xs : Fin 16 → SS.BitString 6) : Fin 16 → ℝ :=
  fun i => Complex.normSq (c (xs i))
def printedBottomIndex : Fin 7 → Fin 2 → Fin 16 := {vec([vec([fin(i) for i in row]) for row in bottomidx])}
def printedTopIndex : Fin 8 → Fin 2 → Fin 16 := {vec([vec([fin(i) for i in row]) for row in topidx])}
theorem literal_native_pairs :
    (∀ i j, Orbit29PrintedFaceAudit.bottomPairs i j=xs (printedBottomIndex i j)) ∧
    (∀ i j, Orbit29PrintedFaceAudit.topPairs i j=ys (printedTopIndex i j)) := by decide +kernel
theorem native_bottom_index : ∀ i j, xs (bottomIndex i j)=
    (![{','.join(vec(['y'+str(2+2*i),'y'+str(3+2*i)]) for i in range(6))}] : Fin 6 → Fin 2 → SS.BitString 6) i j := by decide +kernel
theorem native_high_index : ∀ i j, ys (highIndex i j)=
    (![{','.join(vec(['z'+str(i),'z'+str(i+1)]) for i in [6,10,12,14])}] : Fin 4 → Fin 2 → SS.BitString 6) i j := by decide +kernel

theorem physical_normal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) :
    probabilities c xs=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ∧
    probabilities d ys=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) := by
  have hm := Orbit29PhysicalPairReduction.physical_moments c d hc hd hnc hnd hdist
  apply reduced_normal (probabilities c xs) (probabilities d ys) hm
  · intro i
    change Complex.normSq (c (xs (bottomIndex i 0)))=Complex.normSq (c (xs (bottomIndex i 1)))
    rw [native_bottom_index,native_bottom_index]
    have hb := Orbit29PhysicalPairReduction.bottom_balanced c d hm hc hd hdist i
    fin_cases i <;> simpa [Orbit29PhysicalPairReduction.bottom] using hb
  · intro i
    change Complex.normSq (d (ys (highIndex i 0)))=Complex.normSq (d (ys (highIndex i 1)))
    rw [native_high_index,native_high_index]
    have ht := Orbit29PhysicalPairReduction.high_balanced c d hm hc hd hdist i
    fin_cases i <;> simpa [Orbit29PhysicalPairReduction.highPairs] using ht

def bottomProbability (a b c : ℝ) : Fin 7 → ℝ :=
  ![1/8,1/8-b-c,1/8-a-c,a+b,1/8-a-b,a+c,b+c]
def topProbability (a b c : ℝ) : Fin 8 → ℝ :=
  ![1/8-a-b-c,a,b,c,1/8-c,1/8-b,1/8-a,a+b+c]

theorem printed_probability_indices (a b c : ℝ) :
    (∀ i j, normalQ a b c (printedBottomIndex i j)=bottomProbability a b c i) ∧
    (∀ i j, normalR a b c (printedTopIndex i j)=topProbability a b c i) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl

theorem physical_printed_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) :
    (∀ i j, Complex.normSq (c (Orbit29PrintedFaceAudit.bottomPairs i j))=
      bottomProbability (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) i) ∧
    (∀ i j, Complex.normSq (d (Orbit29PrintedFaceAudit.topPairs i j))=
      topProbability (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) i) := by
  have hp := physical_normal c d hc hd hnc hnd hdist
  constructor
  · intro i j
    rw [literal_native_pairs.1]
    change probabilities c xs (printedBottomIndex i j)=_
    rw [hp.1]
    exact (printed_probability_indices _ _ _).1 i j
  · intro i j
    rw [literal_native_pairs.2]
    change probabilities d ys (printedTopIndex i j)=_
    rw [hp.2]
    exact (printed_probability_indices _ _ _).2 i j

theorem physical_domain (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) :
    0 ≤ Complex.normSq (d z4) ∧ 0 ≤ Complex.normSq (d z2) ∧
    0 ≤ Complex.normSq (d z0) ∧
      Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)≤1/8 := by
  have hp := physical_normal c d hc hd hnc hnd hdist
  have hr := congrFun hp.2 ⟨8,by decide⟩
  change Complex.normSq (d z8)=1/8-Complex.normSq (d z4)-Complex.normSq (d z2)-Complex.normSq (d z0) at hr
  exact ⟨Complex.normSq_nonneg _,Complex.normSq_nonneg _,Complex.normSq_nonneg _,
    by linarith [Complex.normSq_nonneg (d z8)]⟩

theorem physical_omitted_amplitudes (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) : c y0=0 ∧ c y1=0 := by
  have hm := Orbit29PhysicalPairReduction.physical_moments c d hc hd hnc hnd hdist
  have hz := omitted_zero (probabilities c xs) (probabilities d ys) hm
  exact ⟨Complex.normSq_eq_zero.mp hz.1,Complex.normSq_eq_zero.mp hz.2⟩

end
end MainTheory.Orbit29PrintedSimplex
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=source
target=ROOT/'MainTheory/Orbit29PrintedSimplex.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
