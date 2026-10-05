"""Literal physical phase and grid-support displays for SI orbits 37 and 38."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]

def bridge(ef,w='0'):
    return f'(SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef{ef} w{w} (by decide))'
lean='''import MainTheory.ComplementaryPhasePair
import MainTheory.GridSupportAlgebra
import MainTheory.OrderFivePrintedMoments

/-! Actual physical grid labels, hub phases and full support in the printed SI.
Every intermediate step retains zero amplitudes until positivity is proved.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderFiveGridRemainingDisplays
open scoped BigOperators
noncomputable section
open MainTheory.ComplementaryPhasePair

namespace Orbit38
open SixQubit.Orbit38
def A := MainTheory.OrderFivePrintedMoments.Orbit38.A
def B := MainTheory.OrderFivePrintedMoments.Orbit38.B
def topGrid : Fin 2 → Fin 4 → SS.BitString 6 := ![![z8,z7,z6,z5],![z4,z3,z2,z1]]
def b (c : SS.State 6 ℂ) : Fin 2 → Fin 4 → ℂ := fun i j => c (B i j)
def db (d : SS.State 6 ℂ) : Fin 2 → Fin 4 → ℂ := fun i j => d (topGrid i j)
def phaseS (c d : SS.State 6 ℂ) : ℂ := sigma (c y12) (d z0)
def rowSupport (c : SS.State 6 ℂ) := MainTheory.GridSupportAlgebra.rowSupport (b c)

theorem literal_labels :
    S0=(Finset.univ.image A ∪ Finset.univ.image (fun p : Fin 2 × Fin 4 => B p.1 p.2)) ∪ {y12} ∧
    (∀ i j, SS.complement (B i j)=topGrid i j) ∧ SS.complement y12=z0 := by decide +kernel

theorem physical_hub (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i j,
    star (b c i j)*d z0+star (c y12)*db d i j=0 := by
  intro i j
  fin_cases i <;> fin_cases j
'''
for i in range(2):
    for j in range(4):
        ef=9-j+4*i
        lean+=f'  · have he := rec{i+1}{j+1} c d '+bridge(ef)+'\n'
        lean+='    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he\n'
lean+='''
theorem physical_star_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : c y12≠0 ∧ d z0≠0 := by
  have hn := (moments c d hc hd hnc hnd hkl).facts
  constructor
  · intro he
    have hs := hn.1
    rw [he,Complex.normSq_zero] at hs
    norm_num at hs
  · intro he
    have hs := hn.2.1
    rw [he,Complex.normSq_zero] at hs
    norm_num at hs

theorem physical_weighted_phases (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i j,
    star (db d i j)= -phaseS c d*b c i j := by
  intro i j
  exact weighted_opposition _ _ _ _ (physical_star_nonzero c d hc hd hnc hnd hkl).1
    (physical_hub c d hc hd hkl i j)

theorem physical_common_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 2) (j : Fin 4) (hj : b c i j≠0) :
    sigma (b c i j) (db d i j)= -phaseS c d :=
  active_opposition _ _ _ _ hj (physical_star_nonzero c d hc hd hnc hnd hkl).1
    (physical_hub c d hc hd hkl i j)

theorem physical_rectangle (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (j k : Fin 4) (hne : j≠k) :
    star (b c 0 j)*db d 1 k+star (b c 0 k)*db d 1 j+
      star (b c 1 j)*db d 0 k+star (b c 1 k)*db d 0 j=0 := by
  fin_cases j <;> fin_cases k
'''
pairs={(0,1):0,(0,2):1,(0,3):2,(1,2):3,(1,3):4,(2,3):5}
for j in range(4):
    for k in range(4):
        if j==k:
            lean+='  · exact False.elim (hne rfl)\n'
        else:
            ef=pairs[tuple(sorted((j,k)))]
            lean+=f'  · have he : offSum c d ef{ef} w0=0 := '+bridge(ef)+'\n'
            lean+=f'    rw [ex{ef}] at he\n'
            lean+='    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢\n'
            lean+='    linear_combination he\n'
lean+='''
theorem physical_permanents (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j k, j≠k →
    b c 0 j*b c 1 k+b c 0 k*b c 1 j=0 := by
  intro j k hne
  have hn := physical_star_nonzero c d hc hd hnc hnd hkl
  have hk : -phaseS c d≠0 := neg_ne_zero.2 (div_ne_zero (star_ne_zero.2 hn.2) hn.1)
  have hw := physical_weighted_phases c d hc hd hnc hnd hkl
  exact MainTheory.GridSupportAlgebra.permanent_from_weighted_phase _ _ _ _ _ _ _ _ _ hk
    (hw 0 j) (hw 0 k) (hw 1 j) (hw 1 k) (physical_rectangle c d hc hd hkl j k hne)

theorem physical_supports_full (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : rowSupport c 0=Finset.univ ∧ rowSupport c 1=Finset.univ := by
  apply MainTheory.GridSupportAlgebra.supports_univ
  · intro i
    apply MainTheory.GridSupportAlgebra.nonempty_of_mass
    have he := (MainTheory.OrderFivePrintedMoments.Orbit38.physical_display c d hc hd hnc hnd hkl).2.1 i
    change (∑ j, Complex.normSq (c (MainTheory.OrderFivePrintedMoments.Orbit38.B i j)))>0
    rw [he]
    norm_num
  · intro j
    by_contra hh
    push_neg at hh
    have hp := (MainTheory.OrderFivePrintedMoments.Orbit38.physical_column_positive c d hc hd hnc hnd hkl j).2
    change 0<Complex.normSq (b c 0 j)+Complex.normSq (b c 1 j) at hp
    rw [hh.1,hh.2] at hp
    norm_num at hp
  · exact physical_permanents c d hc hd hnc hnd hkl
end Orbit38

namespace Orbit37
open SixQubit.Orbit37
def A := MainTheory.OrderFivePrintedMoments.Orbit37.A
def B := MainTheory.OrderFivePrintedMoments.Orbit37.B
def topA : Fin 3 → SS.BitString 6 := ![z10,z11,z12]
def topB : Fin 3 → Fin 3 → SS.BitString 6 := ![![z9,z8,z7],![z6,z5,z4],![z3,z2,z1]]
def activeColumns (c : SS.State 6 ℂ) : Finset (Fin 3) := Finset.univ.filter (fun j => c (A j)≠0)
def rowSupport (c : SS.State 6 ℂ) (i : Fin 3) := (activeColumns c).filter (fun j => c (B i j)≠0)
theorem actual_complements : (∀ j, SS.complement (A j)=topA j) ∧
    (∀ i j, SS.complement (B i j)=topB i j) ∧ SS.complement y12=z0 := by decide +kernel

theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 3) :
    star (c (A j))*d z0+star (c y12)*d (topA j)=0 := by
  fin_cases j
'''
for j,(rec,ef) in enumerate(((3,1),(2,2),(1,0))):
    lean+=f'  · have he := rec{rec} c d '+bridge(ef)+'\n'
    lean+='    simpa [A,topA,MainTheory.OrderFivePrintedMoments.Orbit37.A] using he\n'
lean+='''
theorem physical_sync (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin 3) :
    star (c (A j))*d (topB i j)=star (c (B i j))*d (topA j) := by
  fin_cases i <;> fin_cases j
'''
for i,(ef,wfirst) in enumerate(((11,11),(7,15),(3,15))):
    for j in range(3):
        native_j=3-j
        dress={3:(wfirst,2),2:(4,2),1:(wfirst,4)}[native_j]
        lean+=f'  · have he := sync{i+1}_{native_j} c d '+bridge(ef,str(dress[0]))+'\n      '+bridge(ef,str(dress[1]))+'\n'
        lean+='    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he\n'
lean+='''
theorem physical_active_column_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin 3)
    (ha : c (A j)≠0) (hb : c (B i j)≠0) :
    sigma (c (B i j)) (d (topB i j))=sigma (c (A j)) (d (topA j)) ∧
      sigma (c (A j)) (d (topA j))= -sigma (c y12) (d z0) := by
  have hm := moments c d hc hd hnc hnd hkl
  have hs : c y12≠0 := by
    intro he
    have hx := MainTheory.OrderFivePrintedMoments.Orbit37.consequence0 hm
    rw [he,Complex.normSq_zero] at hx
    norm_num at hx
  exact active_column_opposition _ _ _ _ _ _ ha hb hs
    (physical_reciprocal c d hc hd hkl j) (physical_sync c d hc hd hkl i j)
end Orbit37

end
end MainTheory.OrderFiveGridRemainingDisplays
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/OrderFiveGridRemainingDisplays.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
