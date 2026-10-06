"""Generate the actual four target Walsh systems and printed eta equations."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def vec(xs):return '!['+','.join(xs)+']'
targets=[3,5,6,7]
neighbors=[[3,4,5],[1,2,5],[0,2,4],[0,1,3]]
lows=[[0,2,4],[0,2,8],[0,4,8],[2,4,8]]
orbit=(ROOT/'SixQubit/Orbit29.lean').read_text(encoding='utf8')
rows=[]
for i,target in enumerate(targets):
    for letter in 'ABCD':
        name=f'wc{target}{letter}'
        block=orbit.split('theorem '+name+' ',1)[1].split('\ntheorem ',1)[0]
        args=re.findall(r'offSum c d (ef\d+) (w\d+) = 0',block)
        assert len(args)==2
        arguments='\n'.join('      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d H.support0 H.support1 H.distance '+a+' '+b+' (by decide))' for a,b in args)
        rows.append(f'''  · simpa [rowExpressions,neighbor,lowWords,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Fin.sum_univ_succ,Fin.succ,add_assoc] using {name} c d
{arguments}''')
bottomproof='\n'.join(f'''  · have he := hg {fin(v)}
    simpa [amplitudes,colors,sign,Orbit29PhysicalPairReduction.bottom] using he''' for v in [5,4,2,3,1,0])
highproof='\n'.join(f'''  · have he := hg {fin(v)}
    norm_num [amplitudes,colors,sign] at he
    change d z{k+1}= -d z{k}
    linear_combination he''' for v,k in zip([9,8,7,6],[6,10,12,14]))
source=f'''import MainTheory.Orbit29PhysicalPairGauge

/-! The displayed four Walsh equations in eta follow from the actual
target errors after the physical pair gauge, uniformly over all fifteen faces. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.Orbit29PrintedEta
open SixQubit.Orbit29 Orbit29PrintedSimplex Orbit29PhysicalRatios SignedPhaseSupport
open Orbit29PhysicalPairReduction Orbit29PhysicalPairGauge
open Orbit29PrintedFaceAudit
open ClassificationLevels
open scoped BigOperators
noncomputable section

def neighbor : Fin 4 → Fin 3 → Fin 6 := {vec([vec([fin(j) for j in row]) for row in neighbors])}
def lowWords : Fin 4 → Fin 3 → Fin 2 → SS.BitString 6 :=
  {vec([vec([vec(['z'+str(k),'z'+str(k+1)]) for k in row]) for row in lows])}
def rowExpressions (c d : SS.State 6 ℂ) (i : Fin 4) : Fin 4 → ℂ :=
  ![(∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 0))+star (c y15)*highPairs d i 1,
    (∑ j, star (bottom c (neighbor i j) 1)*d (lowWords i j 1))+star (c y14)*highPairs d i 0,
    (∑ j, star (bottom c (neighbor i j) 1)*d (lowWords i j 0))+star (c y15)*highPairs d i 0,
    (∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 1))+star (c y14)*highPairs d i 1]

theorem actual_rows (c d : SS.State 6 ℂ) (H : FullKL c d) : ∀ i j,
    rowExpressions c d i j=0 := by
  intro i j
  fin_cases i <;> fin_cases j
{chr(10).join(rows)}

def PairGauge (c d : SS.State 6 ℂ) : Prop :=
  ∀ v, amplitudes c d v 1=sign (Orbit29PrintedFaceAudit.colors v) (amplitudes c d v 0)

theorem aligned_bottom (c d : SS.State 6 ℂ) (hg : PairGauge c d) :
    ∀ i, bottom c i 0=bottom c i 1 := by
  intro i
  fin_cases i
{bottomproof}

theorem opposite_high (c d : SS.State 6 ℂ) (hg : PairGauge c d) :
    ∀ i, highPairs d i 1= -highPairs d i 0 := by
  intro i
  fin_cases i
{highproof}

def eta (c : SS.State 6 ℂ) : ℂ := star (c y15)/star (c y14)
def A (c d : SS.State 6 ℂ) (i : Fin 4) : ℂ := star (c y14)*highPairs d i 0
def R (c d : SS.State 6 ℂ) (i : Fin 4) : ℂ :=
  (∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 0))+
    (∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 1))
def S (c d : SS.State 6 ℂ) (i : Fin 4) : ℂ :=
  (∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 1))-
    (∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 0))

theorem pinned_probability (c d : SS.State 6 ℂ) (H : FullKL c d) :
    Complex.normSq (c y14)=1/8 ∧ Complex.normSq (c y15)=1/8 := by
  have hp := physical_normal c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  have h14 := congrFun hp.1 (⟨14,by decide⟩ : Fin 16)
  have h15 := congrFun hp.1 (⟨15,by decide⟩ : Fin 16)
  norm_num [probabilities,xs,normalQ] at h14 h15
  exact ⟨h14,h15⟩

theorem pinned_nonzero (c d : SS.State 6 ℂ) (H : FullKL c d) : c y14≠0 := by
  intro hz
  have hp := (pinned_probability c d H).1
  rw [hz,Complex.normSq_zero] at hp
  norm_num at hp

theorem eta_unit (c d : SS.State 6 ℂ) (H : FullKL c d) : Complex.normSq (eta c)=1 := by
  have hm := pinned_probability c d H
  simp only [eta,Complex.normSq_div,Complex.star_def,Complex.normSq_conj,hm.1,hm.2]
  norm_num

def targetPair : Fin 4 → Fin 8 := ![⟨7,by decide⟩,⟨6,by decide⟩,⟨5,by decide⟩,⟨4,by decide⟩]
def flipQubit : Fin 4 → Fin 6 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩]
def maskFive : Fin 4 → SS.BitString 6 := ![ef11,ef8,ef5,ef2]
def maskSix : Fin 4 → SS.BitString 6 := ![ef10,ef7,ef4,ef1]
theorem literal_target_errors : (∀ i, (targetPair i).val=7-i.val ∧ (flipQubit i).val=i.val) ∧
    (∀ i, maskFive i=SS.bxor (SS.stdBasis (flipQubit i)) (SS.stdBasis 4) ∧
      maskSix i=SS.bxor (SS.stdBasis (flipQubit i)) (SS.stdBasis 5)) ∧
    (∀ i j, topPairs (targetPair i) j=ys (highIndex i (1-j))) := by decide +kernel

theorem eta_mul (c : SS.State 6 ℂ) (hc : c y14≠0) : eta c*star (c y14)=star (c y15) :=
  div_mul_cancel₀ _ (star_ne_zero.mpr hc)

theorem printed_eta_equations (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hg : PairGauge c d) (i : Fin 4) :
    (1-eta c)*A c d i+R c d i=0 ∧ -(1-eta c)*A c d i+R c d i=0 ∧
    (1+eta c)*A c d i+S c d i=0 ∧ -(1+eta c)*A c d i+S c d i=0 := by
  have e0 := actual_rows c d H i ⟨0,by decide⟩
  have e1 := actual_rows c d H i ⟨1,by decide⟩
  have e2 := actual_rows c d H i ⟨2,by decide⟩
  have e3 := actual_rows c d H i ⟨3,by decide⟩
  change (∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 0))+star (c y15)*highPairs d i 1=0 at e0
  change (∑ j, star (bottom c (neighbor i j) 1)*d (lowWords i j 1))+star (c y14)*highPairs d i 0=0 at e1
  change (∑ j, star (bottom c (neighbor i j) 1)*d (lowWords i j 0))+star (c y15)*highPairs d i 0=0 at e2
  change (∑ j, star (bottom c (neighbor i j) 0)*d (lowWords i j 1))+star (c y14)*highPairs d i 1=0 at e3
  simp_rw [← aligned_bottom c d hg] at e1 e2
  rw [opposite_high c d hg] at e0 e3
  have he := eta_mul c (pinned_nonzero c d H)
  unfold A R S
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination e0+e1-highPairs d i 0*he
  · linear_combination e2+e3+highPairs d i 0*he
  · linear_combination e1-e0+highPairs d i 0*he
  · linear_combination e3-e2-highPairs d i 0*he

theorem active_product_nonzero (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hg : PairGauge c d) (i : Fin 4) (hp : 0 < Q d i) : A c d i≠0 := by
  apply mul_ne_zero (star_ne_zero.mpr (pinned_nonzero c d H))
  intro hz
  have ht := opposite_high c d hg i
  have hm : Q d i=0 := by simp [Q,hz,ht]
  rw [hm] at hp
  exact (lt_irrefl 0) hp

theorem eta_contradiction (e A R S : ℂ) (ha : A≠0)
    (h1 : (1-e)*A+R=0) (h2 : -(1-e)*A+R=0)
    (h3 : (1+e)*A+S=0) (h4 : -(1+e)*A+S=0) : False := by
  have hm : (1-e)*A=0 := by linear_combination (1/2 : ℂ)*h1-(1/2 : ℂ)*h2
  have hp : (1+e)*A=0 := by linear_combination (1/2 : ℂ)*h3-(1/2 : ℂ)*h4
  have he1 : e=1 := by
    have he := (mul_eq_zero.mp hm).resolve_right ha
    linear_combination -he
  rw [he1] at hp
  norm_num at hp
  exact ha hp

theorem physical_no_go (c d : SS.State 6 ℂ) (H : FullKL c d) : False := by
  obtain ⟨u,Hu,_,_,hg⟩ := physical_pair_gauge c d H
  let C := diagonalAction (singlePhase u) c
  let D := diagonalAction (singlePhase u) d
  have hm := physical_moments C D Hu.support0 Hu.support1 Hu.norm0 Hu.norm1 Hu.distance
  have hs := total_high_mass C D hm
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ Q D i := by
    intro i _
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hp : 0 < ∑ i, Q D i := by rw [hs]; norm_num
  obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp hp
  obtain ⟨e1,e2,e3,e4⟩ := printed_eta_equations C D Hu hg i
  exact eta_contradiction _ _ _ _ (active_product_nonzero C D Hu hg i hi) e1 e2 e3 e4

end
end MainTheory.Orbit29PrintedEta
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=source
target=ROOT/'MainTheory/Orbit29PrintedEta.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
