"""Emit the literal sixteen-row SI support table and its complete orbit checks."""
import argparse
from itertools import permutations
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
PRINTED=[
    ('0011|1100|0011|0011',18,8),('1111|1111|1100|0011',18,12),
    ('0011|1111|1111|0011',18,12),('0110|1111|0111|0111',36,12),
    ('0111|1111|0111|0111',12,13),('1011|1111|1111|0011',36,13),
    ('1110|1111|0111|0111',36,13),('0110|1111|1111|0111',36,13),
    ('1100|1111|1111|1111',6,14),('1111|1111|0111|0111',12,14),
    ('0111|1111|1111|0111',12,14),('1111|1111|1111|0011',18,14),
    ('1110|1111|1111|0111',36,14),('1110|1111|1111|1111',4,15),
    ('1111|1111|1111|0111',12,15),('1111|1111|1111|1111',1,16),
]


def fin(i):
    return f'⟨{i},by decide⟩'


def vec(items):
    return '!['+','.join(map(str,items))+']'


def mask_from_words(words):
    return sum((1<<j) for j,c in enumerate(words.replace('|','')) if c=='1')


def transform(mask,row,col):
    return sum((1<<(col[j] if j<4 else 4+4*row[(j-4)//4]+col[(j-4)%4]))
               for j in range(16) if mask&(1<<j))


def generate():
    data=json.loads((ROOT/'results/orbit31-support-candidates-20261005.json').read_text(encoding='utf8'))
    reps=[mask_from_words(words) for words,_,_ in PRINTED]
    orbits=[]
    for rep,(_,size,weight) in zip(reps,PRINTED):
        orbit=sorted({transform(rep,row,col) for row in permutations(range(3)) for col in permutations(range(4))})
        assert len(orbit)==size and rep.bit_count()==weight
        assert not any(set(orbit)&set(old) for old in orbits)
        orbits.append(orbit)
    assert sorted({m for orbit in orbits for m in orbit})==data['phase_consistent_masks']
    words=vec(vec(vec('true' if c=='1' else 'false' for c in word)
                  for word in text.split('|')) for text,_,_ in PRINTED)
    expected=vec('({'+','.join(fin(m) for m in orbit)+'} : Finset (Fin 65536))' for orbit in orbits)
    text=f'''import MainTheory.Orbit31TableSymmetry
import MainTheory.Orbit31PhaseClassification

/-! The literal SI representatives, physical group orbits, and all 311 masks.
No orbit number, printed size or enumeration input is accepted without a proof.
-/
set_option autoImplicit false
set_option maxHeartbeats 256000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31PrintedSupportOrbits
open MainTheory.Orbit31TableSymmetry
open MainTheory.Orbit31SupportSemantics (maskSet)

def representatives : Fin 16 → Fin 65536 := {vec(fin(m) for m in reps)}
def printedWords : Fin 16 → Fin 4 → Fin 4 → Bool := {words}
def printedOrbitSizes : Fin 16 → ℕ := {vec(size for _,size,_ in PRINTED)}
def printedSupportSizes : Fin 16 → ℕ := {vec(weight for _,_,weight in PRINTED)}
def expectedOrbits : Fin 16 → Finset (Fin 65536) := {expected}

def orbit (t : Fin 16) : Finset (Fin 65536) :=
  Finset.univ.image fun g : Fin 144 => action g (representatives t)

theorem literal_words : ∀ t r e,
    (representatives t).val.testBit (4*r.val+e.val) = printedWords t r e := by decide +kernel
theorem support_sizes : ∀ t, (maskSet (representatives t).val).card = printedSupportSizes t := by decide +kernel
theorem actual_orbits : ∀ t, orbit t = expectedOrbits t := by decide +kernel
theorem expected_sizes : ∀ t, (expectedOrbits t).card = printedOrbitSizes t := by decide +kernel
theorem expected_disjoint : ∀ i j, i ≠ j → Disjoint (expectedOrbits i) (expectedOrbits j) := by decide +kernel
theorem complete_survivor_set : MainTheory.Orbit31PhaseClassification.survivorMasks =
    Finset.univ.biUnion expectedOrbits := by decide +kernel
theorem size_sum : (∑ t, printedOrbitSizes t) = 311 := by decide +kernel

theorem orbit_sizes (t : Fin 16) : (orbit t).card = printedOrbitSizes t := by
  rw [actual_orbits]
  exact expected_sizes t
theorem orbits_disjoint (i j : Fin 16) (h : i ≠ j) : Disjoint (orbit i) (orbit j) := by
  rw [actual_orbits,actual_orbits]
  exact expected_disjoint i j h

theorem classified (mask : Fin 65536)
    (hm : mask ∈ MainTheory.Orbit31PhaseClassification.survivorMasks) :
    ∃ t : Fin 16, ∃ g : Fin 144, action g (representatives t) = mask := by
  rw [complete_survivor_set] at hm
  obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hm
  rw [← actual_orbits t] at ht
  obtain ⟨g,_,hg⟩ := Finset.mem_image.mp ht
  exact ⟨t,g,hg⟩

theorem unique_type (mask : Fin 65536)
    (hm : mask ∈ MainTheory.Orbit31PhaseClassification.survivorMasks) :
    ∃! t : Fin 16, mask ∈ orbit t := by
  obtain ⟨t,g,hg⟩ := classified mask hm
  have ht : mask ∈ orbit t := Finset.mem_image.mpr ⟨g,Finset.mem_univ _,hg⟩
  refine ⟨t,ht,?_⟩
  intro i hi
  by_contra hne
  exact Finset.disjoint_left.mp (orbits_disjoint i t hne) hi ht

end MainTheory.Generated.Orbit31PrintedSupportOrbits
'''
    return text


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    content=generate()
    path=ROOT/'MainTheory/Generated/Orbit31PrintedSupportOrbits.lean'
    if args.check:
        if path.read_text(encoding='utf8')!=content:
            raise SystemExit('Generated printed support orbits differ')
    else:
        path.write_text(content,encoding='utf8',newline='\n')
    print('Prepared the literal 16-row SI support table and exact orbit coverage; Lean acceptance remains required.')
