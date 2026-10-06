"""Emit all literal orbit-28 probabilities directly from the real moment inequalities."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[2]
TARGET=ROOT/'MainTheory/Orbit28PrintedProbabilities.lean'
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
options=parser.parse_args()

def emit(path,text):
    if options.check:
        if not path.is_file() or path.read_text(encoding='utf8')!=text:
            raise SystemExit('Generated source differs: '+str(path))
    else:path.write_text(text,encoding='utf8',newline='\n')

source=(ROOT/'SixQubit/Orbit28.lean').read_text(encoding='utf8')
fields=re.findall(r'^  ([a-z]+[0-9]+) : ',source,re.M)
assert len(fields)==55,fields
args=' '.join(f'(q ⟨{i},by decide⟩)' for i in range(16))+' '+ ' '.join(f'(r ⟨{i},by decide⟩)' for i in range(16))
bottom=['3/8' if i==0 else '1/8' if i in [7,11,13,14,15] else '0' for i in range(16)]
top=['3/8' if i==15 else '1/8' if i in [0,1,2,4,8] else '0' for i in range(16)]
bottom_steps='\n'.join(f'    · change q ⟨{i},by decide⟩={v}\n      linarith' for i,v in enumerate(bottom))
top_steps='\n'.join(f'    · change r ⟨{i},by decide⟩={v}\n      linarith' for i,v in enumerate(top))
text=f'''import SixQubit.CodeOrbit28
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit28PrintedProbabilities
open SixQubit.Orbit28
open scoped BigOperators
noncomputable section
def bottom : Fin 16 → SS.BitString 6 := ![{','.join(f'y{i}' for i in range(16))}]
def top : Fin 16 → SS.BitString 6 := ![{','.join(f'z{i}' for i in range(16))}]
def bottomProbability : Fin 16 → ℝ := ![{','.join(bottom)}]
def topProbability : Fin 16 → ℝ := ![{','.join(top)}]
def VectorMoments (q r : Fin 16 → ℝ) : Prop := MomentSystem {args}

theorem complete_normal (q r : Fin 16 → ℝ) (hm : VectorMoments q r) :
    q=bottomProbability ∧ r=topProbability := by
  change MomentSystem {args} at hm
  obtain ⟨{','.join(fields)}⟩ := hm
  constructor
  · ext i
    fin_cases i
{bottom_steps}
  · ext i
    fin_cases i
{top_steps}

theorem physical_normal (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (fun i => Complex.normSq (c (bottom i)))=bottomProbability ∧
    (fun i => Complex.normSq (d (top i)))=topProbability := by
  apply complete_normal
  exact SixQubit.Orbit28.moments c d hc hd hnc hnd hkl

def bottomActive : Finset (SS.BitString 6) := {{y0,y7,y11,y13,y14,y15}}
def topActive : Finset (SS.BitString 6) := {{z0,z1,z2,z4,z8,z15}}

theorem literal_supports : bottomActive.card=6 ∧ topActive.card=6 ∧
    (∀ i : Fin 16,bottomProbability i≠0 ↔ bottom i∈bottomActive) ∧
    (∀ i : Fin 16,topProbability i≠0 ↔ top i∈topActive) := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [bottomProbability,bottom,bottomActive] <;> decide +kernel
  · intro i
    fin_cases i <;> norm_num [topProbability,top,topActive] <;> decide +kernel
theorem bottom_full : ∀ x : SS.BitString 6,x∈S0 ↔ ∃ i,bottom i=x := by decide +kernel
theorem top_full : ∀ x : SS.BitString 6,x∈S1 ↔ ∃ i,top i=x := by decide +kernel

theorem physical_supports (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ x,c x≠0 ↔ x∈bottomActive) ∧ (∀ x,d x≠0 ↔ x∈topActive) := by
  obtain ⟨hq,hr⟩ := physical_normal c d hc hd hnc hnd hkl
  constructor
  · intro x
    by_cases hs : x∈S0
    · obtain ⟨i,rfl⟩ := (bottom_full x).mp hs
      have he := congrFun hq i
      simp only [ne_eq,← Complex.normSq_eq_zero,he]
      exact literal_supports.2.2.1 i
    · have hz := hc x hs
      have ha : bottomActive⊆S0 := by decide +kernel
      simp only [hz,ne_eq,not_true_eq_false,false_iff]
      exact fun h => hs (ha h)
  · intro x
    by_cases hs : x∈S1
    · obtain ⟨i,rfl⟩ := (top_full x).mp hs
      have he := congrFun hr i
      simp only [ne_eq,← Complex.normSq_eq_zero,he]
      exact literal_supports.2.2.2 i
    · have hz := hd x hs
      have ha : topActive⊆S1 := by decide +kernel
      simp only [hz,ne_eq,not_true_eq_false,false_iff]
      exact fun h => hs (ha h)
end
end MainTheory.Orbit28PrintedProbabilities
'''
emit(TARGET,text)
print('Generated complete orbit-28 probabilities and actual support bridge')
