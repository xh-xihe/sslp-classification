"""Connect the native orbit-29 moments and physical Walsh rows to pair balance."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i): return f'⟨{i},by decide⟩'
def vec(xs): return '!['+','.join(xs)+']'
edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
high=[6,10,12,14]
native=[3,5,6,7]
orbit=(ROOT/'SixQubit/Orbit29.lean').read_text(encoding='utf8')
orth=[]
for e,(i,j) in enumerate(edges):
    for k in (i,j):
        name=f'orth{e+1}_{native[k]}'
        block=orbit.split('theorem '+name+' ',1)[1].split('\ntheorem ',1)[0]
        args=re.findall(r'offSum c d (ef\d+) (w\d+) = 0',block)
        assert len(args)==4
        rows='\n'.join('      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist '+a+' '+b+' (by decide))' for a,b in args)
        orth.append(f'''  · simpa [bottom,highPairs,node] using {name} c d
{rows}''')
weights=[]
for e in range(6):
    weights.append(f'''  · have he := mc{e+1} h
    norm_num [bottom,Q,highPairs,node]
    linarith''')
weighted=[]
for i in range(4):
    for j in range(4):
        if i==j:weighted.append('  · ring');continue
        e=edges.index(tuple(sorted((i,j))))
        weighted.append(f'''  · have he := SixQubit.Pair29.perp_det
      (bottom c {fin(e)} 0) (bottom c {fin(e)} 1)
      (highPairs d (node {fin(e)} 0) 0) (highPairs d (node {fin(e)} 0) 1)
      (highPairs d (node {fin(e)} 1) 0) (highPairs d (node {fin(e)} 1) 1)
      (native_orth c d hc hd hdist {fin(e)} 0) (native_orth c d hc hd hdist {fin(e)} 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h {fin(e)}] at he
    change ((Q d {fin(min(i,j))}+Q d {fin(max(i,j))}-1/4 : ℝ) : ℂ)*
      (highPairs d {fin(min(i,j))} 0*highPairs d {fin(max(i,j))} 1-
        highPairs d {fin(max(i,j))} 0*highPairs d {fin(min(i,j))} 1)=0 at he
    push_cast at he ⊢
    linear_combination {'' if i<j else '-'}he''')
mom='MomentSystem '+ ' '.join('(Complex.normSq (c y'+str(i)+'))' for i in range(16))+'\n  '+ ' '.join('(Complex.normSq (d z'+str(i)+'))' for i in range(16))
source=f'''import SixQubit.CodeOrbit29
import MainTheory.Orbit29PairBalance

/-! The pair-balance reduction follows from actual supported physical code
amplitudes, their degree-two moments, and the twelve physical Walsh relations.
No final no-code result is used to prove an intermediate manuscript formula. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.Orbit29PhysicalPairReduction
open SixQubit.Orbit29
open scoped BigOperators
noncomputable section

def Moment (c d : SS.State 6 ℂ) : Prop :=
  {mom}
def bottom (c : SS.State 6 ℂ) : Fin 6 → Fin 2 → ℂ :=
  {vec([vec(['c y'+str(2+2*i),'c y'+str(3+2*i)]) for i in range(6)])}
def highPairs (d : SS.State 6 ℂ) : Fin 4 → Fin 2 → ℂ :=
  {vec([vec(['d z'+str(i),'d z'+str(i+1)]) for i in high])}
def node : Fin 6 → Fin 2 → Fin 4 :=
  {vec([vec([fin(i),fin(j)]) for i,j in edges])}
def Q (d : SS.State 6 ℂ) (i : Fin 4) : ℝ :=
  Complex.normSq (highPairs d i 0)+Complex.normSq (highPairs d i 1)

theorem physical_moments (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) : Moment c d :=
  moments c d hc hd hnc hnd hdist

theorem native_orth (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ e j,
    star (bottom c e 0)*highPairs d (node e j) 0+
      star (bottom c e 1)*highPairs d (node e j) 1=0 := by
  intro e j
  fin_cases e <;> fin_cases j
{chr(10).join(orth)}

theorem bottom_mass (c d : SS.State 6 ℂ) (h : Moment c d) : ∀ e,
    Complex.normSq (bottom c e 0)+Complex.normSq (bottom c e 1)=
      Q d (node e 0)+Q d (node e 1)-1/4 := by
  intro e
  fin_cases e
{chr(10).join(weights)}

theorem total_high_mass (c d : SS.State 6 ℂ) (h : Moment c d) :
    (∑ i, Q d i)=3/4 := by
  have he := mq h
  norm_num [Q,highPairs,Fin.sum_univ_succ,Fin.succ]
  linarith

theorem high_mass_bound (c d : SS.State 6 ℂ) (h : Moment c d) : ∀ i, Q d i≤1/4 := by
  intro i
  fin_cases i
  · have he := mp3 h
    norm_num [Q,highPairs]
    linarith [h.nr8,h.nr9]
  · have he := mp5 h
    norm_num [Q,highPairs]
    linarith [h.nr4,h.nr5]
  · have he := mp6 h
    norm_num [Q,highPairs]
    linarith [h.nr2,h.nr3]
  · have he := mp7 h
    norm_num [Q,highPairs]
    linarith [h.nr0,h.nr1]

theorem weighted_determinants (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ i j,
    ((Q d i+Q d j-1/4 : ℝ) : ℂ)*
      (highPairs d i 0*highPairs d j 1-highPairs d j 0*highPairs d i 1)=0 := by
  intro i j
  fin_cases i <;> fin_cases j
{chr(10).join(weighted)}

theorem high_parallel (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ i j,
    highPairs d i 0*highPairs d j 1-highPairs d j 0*highPairs d i 1=0 := by
  apply Orbit29PairBalance.parallel_all (fun i => highPairs d i 0) (fun i => highPairs d i 1) (Q d)
    (total_high_mass c d h) (high_mass_bound c d h)
  · intro i
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  · intro i
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add]
    rfl
  · exact weighted_determinants c d h hc hd hdist

theorem high_balanced (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ i,
    Complex.normSq (highPairs d i 0)=Complex.normSq (highPairs d i 1) := by
  apply Orbit29PairBalance.balanced_high (fun i => highPairs d i 0) (fun i => highPairs d i 1)
  · have he := total_high_mass c d h
    simpa only [Q,Finset.sum_add_distrib] using he
  · have he := me h
    norm_num [highPairs,Fin.sum_univ_succ,Fin.succ]
    linarith
  · exact high_parallel c d h hc hd hdist

theorem bottom_balanced (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ e,
    Complex.normSq (bottom c e 0)=Complex.normSq (bottom c e 1) := by
  intro e
  have hw := bottom_mass c d h e
  have hnn0 := Complex.normSq_nonneg (bottom c e 0)
  have hnn1 := Complex.normSq_nonneg (bottom c e 1)
  have hqa : 0 ≤ Q d (node e 0) := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hqb : 0 ≤ Q d (node e 1) := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  by_cases ha : Q d (node e 0)=0
  · have hp : 0 < Q d (node e 1) := by linarith
    exact Orbit29PairBalance.perpendicular_balance _ _ _ _
      (native_orth c d hc hd hdist e 1) (high_balanced c d h hc hd hdist _ ) hp
  · have hp : 0 < Q d (node e 0) := lt_of_le_of_ne hqa (Ne.symm ha)
    exact Orbit29PairBalance.perpendicular_balance _ _ _ _
      (native_orth c d hc hd hdist e 0) (high_balanced c d h hc hd hdist _ ) hp

end
end MainTheory.Orbit29PhysicalPairReduction
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=source
target=ROOT/'MainTheory/Orbit29PhysicalPairReduction.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
