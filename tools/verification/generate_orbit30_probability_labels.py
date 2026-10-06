"""Generate exact pointwise K5-label identities and their physical probabilities."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def vec(xs):return '!['+','.join(xs)+']'
vertices=[0,1,2,4,8]
edges=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
edgeidx=[14,13,11,7,12,10,6,9,5,3]
stars=[[j for j,e in enumerate(edges) if i in e] for i in range(5)]
degree_expr=[' + '.join('p '+fin(edgeidx[j]) for j in star) for star in stars]
lean=f'''import MainTheory.Orbit30PrintedMoments
set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace MainTheory.Orbit30ProbabilityLabels
open SixQubit.Orbit30
open MainTheory.Orbit30PrintedMoments
open scoped BigOperators
noncomputable section
def vertexIndex : Fin 5 → Fin 16 := {vec(fin(i) for i in vertices)}
def edgeIndex : Fin 10 → Fin 16 := {vec(fin(i) for i in edgeidx)}
def endpoints : Fin 10 → Fin 5 × Fin 5 := {vec('('+fin(i)+','+fin(j)+')' for i,j in edges)}
def coordQ (i : Fin 16) (j : Fin 6) : ℚ := if bottom i j then 1 else 0
def firstFourQ (i : Fin 16) : ℚ := coordQ i 0+coordQ i 1+coordQ i 2+coordQ i 3
def starIndicatorQ (i : Fin 16) : ℚ := if i.val=15 then 1 else 0
def vertexIndicatorQ (v : Fin 5) (i : Fin 16) : ℚ := if vertexIndex v=i then 1 else 0
def degreeIndicatorQ (v : Fin 5) (i : Fin 16) : ℚ :=
  ∑ e : Fin 10,if (endpoints e).1=v ∨ (endpoints e).2=v then
    (if edgeIndex e=i then 1 else 0) else 0
theorem literal_pointwise_identities :
    (∀ i,starIndicatorQ i=firstFourQ i/4-coordQ i 4/2-coordQ i 5/4) ∧
    (∀ i,degreeIndicatorQ 0 i-vertexIndicatorQ 0 i=
      -1+firstFourQ i/4+coordQ i 4/2+3*coordQ i 5/4) ∧
    (∀ v : Fin 4,∀ i,degreeIndicatorQ ⟨v.val+1,by omega⟩ i-
      vertexIndicatorQ ⟨v.val+1,by omega⟩ i=
      firstFourQ i/4-coordQ i ⟨3-v.val,by omega⟩+coordQ i 4/2-coordQ i 5/4) := by decide +kernel
def pointMass (p : Fin 16 → ℝ) : Fin 5 → ℝ := fun i => p (vertexIndex i)
def edgeMass (p : Fin 16 → ℝ) : Fin 10 → ℝ := fun i => p (edgeIndex i)
def degreeMass (p : Fin 16 → ℝ) : Fin 5 → ℝ := {vec(degree_expr)}
theorem literal_degree_sum (p : Fin 16 → ℝ) (v : Fin 5) :
    degreeMass p v=∑ e : Fin 10,if (endpoints e).1=v ∨ (endpoints e).2=v then edgeMass p e else 0 := by
  fin_cases v <;> norm_num [degreeMass,edgeMass,edgeIndex,endpoints,Fin.sum_univ_succ,Fin.succ] <;> ring
theorem actual_probabilities (p t : Fin 16 → ℝ) (hm : Moment p t) :
    p ⟨15,by decide⟩=1/8 ∧
    (∀ v,degreeMass p v=pointMass p v+1/8) ∧
    (∑ v,pointMass p v)=3/8 ∧ (∑ e,edgeMass p e)=1/2 := by
  have he := hm.endpoints
  refine ⟨he.1,?_,?_,?_⟩
  · intro v
    fin_cases v
'''
lean+=''.join(f'    · exact he'+'.2'*(i+2)+'.1\n' for i in range(5))
lean+='''  · have h := he.2.2.2.2.2.2.2.1
    change p (0 : Fin 16)+p (1 : Fin 16)+p ⟨2,by decide⟩+p ⟨4,by decide⟩+p ⟨8,by decide⟩=3/8 at h
    norm_num [pointMass,vertexIndex,Fin.sum_univ_succ,Fin.succ]
    convert h using 1
    ring
  · have h := he.2.2.2.2.2.2.2.2
    norm_num [edgeMass,edgeIndex,Fin.sum_univ_succ,Fin.succ]
    convert h using 1
    ring
theorem physical_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3) :
    bottomProbability c ⟨15,by decide⟩=1/8 ∧
    (∀ v,degreeMass (bottomProbability c) v=pointMass (bottomProbability c) v+1/8) ∧
    (∑ v,pointMass (bottomProbability c) v)=3/8 ∧
    (∑ e,edgeMass (bottomProbability c) e)=1/2 :=
  actual_probabilities _ _ (physical_moments c d hc hd hnc hnd hkl)
end
end MainTheory.Orbit30ProbabilityLabels
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
target=ROOT/'MainTheory/Orbit30ProbabilityLabels.lean'
if args.check:
    if target.read_text(encoding='utf8')!=lean:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(lean,encoding='utf8',newline='\n')
