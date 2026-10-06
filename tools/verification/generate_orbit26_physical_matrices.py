"""Connect all twelve native orbit-26 outer rows to the literal physical block matrices."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
native=(ROOT/'SixQubit/Orbit26.lean').read_text(encoding='utf8')
parts=['''import MainTheory.Orbit26PrintedProbabilities
import MainTheory.Orbit26AnchorMatrix
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26PhysicalMatrices
open scoped BigOperators Matrix
open SixQubit.Orbit26 MainTheory.OrderFour26Support
open MainTheory.Orbit26PrintedProbabilities (bottom_native top_native)
open MainTheory.Orbit26 (cj Jmat)
noncomputable section
def groupIndex (g : Fin 4) (j : Fin 2) : Fin 8 := ⟨2*g.val+j.val,by omega⟩
def C (c : SS.State 6 ℂ) (g : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a j => c (bottomAt (a=1) (groupIndex g j))
def D (d : SS.State 6 ℂ) (g : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a j => d (topAt (a=1) (groupIndex g j))
''']
for g,h,ng,nh in [(0,1,0,2),(0,2,0,1),(1,2,1,2)]:
    name=f'outer_{g}{h}'
    parts.append(f'''
theorem {name} (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    cj (C c {g})*Jmat*(D d {h}).transpose+
    cj (C c {h})*Jmat*(D d {g}).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b
''')
    for a,b in [(0,0),(0,1),(1,0),(1,1)]:
        theorem=f'outer_g{ng}h{nh}_a{a}b{b}'
        match=re.search(r'theorem '+theorem+r'.*?\n    \(h0 : offSum c d (ef\d+) (w\d+) = 0\) \(h1 : offSum c d (ef\d+) (w\d+) = 0\)',native,re.S)
        assert match,theorem
        e,z,e1,z1=match.groups();assert e==e1
        parts.append(f'''  · have hn := SixQubit.Orbit26.{theorem} c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl {e} {z} (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl {e} {z1} (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
''')
parts.append('''
theorem physical_outer (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (g h : Fin 3) (hgh : g<h) :
    cj (C c g.castSucc)*Jmat*(D d h.castSucc).transpose+
    cj (C c h.castSucc)*Jmat*(D d g.castSucc).transpose=0 := by
  fin_cases g <;> fin_cases h
  all_goals simp only [Fin.lt_def] at hgh
  all_goals norm_num at hgh
  all_goals first | exact outer_01 c d hc hd hkl | exact outer_02 c d hc hd hkl | exact outer_12 c d hc hd hkl
end
end MainTheory.Orbit26PhysicalMatrices
''')
source='\n'.join(parts)
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
options=parser.parse_args()

def emit(path,text):
    if options.check:
        if not path.is_file() or path.read_text(encoding='utf8')!=text:
            raise SystemExit('Generated source differs: '+str(path))
    else:path.write_text(text,encoding='utf8',newline='\n')
imports=''.join(f'import MainTheory.OrderFour26DiagonalRows{g}\n' for g in range(4))
source=source.replace('set_option autoImplicit false',imports+'set_option autoImplicit false')
parts=[]
for name,values in [('bottom',[0,6,17,23,9,15,26,28,32,38,49,55,41,47,58,60]),
                    ('top',[31,25,14,8,22,16,5,3,63,57,46,40,54,48,37,35])]:
    expr=''.join(f'if i.val={i} then MainTheory.OrderEightSupportDisplays.bits {v} else ' for i,v in enumerate(values[:-1]))+f'MainTheory.OrderEightSupportDisplays.bits {values[-1]}'
    parts.append(f'theorem {name}_eval : ∀ i : Fin 16,{name} i=({expr}) := by decide +kernel\n')
for g,ng in [(0,0),(1,2),(2,1)]:
    parts.append(f'''
theorem anchor_{g} (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (C c 3)ᴴ*D d {g}+((C c {g})ᴴ*D d 3).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b
''')
    for a,b in [(0,0),(0,1),(1,0),(1,1)]:
        theorem=f'anch_i{2*ng+b}_j{6+a}'
        match=re.search(r'theorem '+theorem+r'.*?\n    \(h0 : offSum c d (ef\d+) (w\d+) = 0\) \(h1 : offSum c d (ef\d+) (w\d+) = 0\)',native,re.S)
        assert match,theorem
        e,z,e1,z1=match.groups();assert e==e1
        parts.append(f'''  · have hn := SixQubit.Orbit26.{theorem} c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl {e} {z} (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl {e} {z1} (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
''')
for g in range(4):
    parts.append(f'''
theorem moment_{g} (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    C c {g}*(C c {g})ᴴ+D d {g}*(D d {g})ᴴ=
      (1/2 : ℂ) • (∑ k : Fin 4,C c k*(C c k)ᴴ) := by
  ext a b
  fin_cases a <;> fin_cases b
''')
    for a,b in [(0,0),(0,1),(1,0),(1,1)]:
        parts.append(f'''  · have hn := MainTheory.OrderFour26DiagonalRows{g}.Entry{a}{b}.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
''')
parts.append('''
theorem physical_anchor (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (g : Fin 3) :
    (C c 3)ᴴ*D d g.castSucc+((C c g.castSucc)ᴴ*D d 3).transpose=0 := by
  fin_cases g
  · exact anchor_0 c d hc hd hkl
  · exact anchor_1 c d hc hd hkl
  · exact anchor_2 c d hc hd hkl

theorem physical_moment (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (g : Fin 4) :
    C c g*(C c g)ᴴ+D d g*(D d g)ᴴ=
      (1/2 : ℂ) • (∑ k : Fin 4,C c k*(C c k)ᴴ) := by
  fin_cases g
  · exact moment_0 c d hc hd hkl
  · exact moment_1 c d hc hd hkl
  · exact moment_2 c d hc hd hkl
  · exact moment_3 c d hc hd hkl

theorem physical_rho (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∑ k : Fin 4,C c k*(C c k)ᴴ)=(∑ k : Fin 4,D d k*(D d k)ᴴ) := by
  ext a b
  have h0 := congrArg (fun X => X a b) (moment_0 c d hc hd hkl)
  have h1 := congrArg (fun X => X a b) (moment_1 c d hc hd hkl)
  have h2 := congrArg (fun X => X a b) (moment_2 c d hc hd hkl)
  have h3 := congrArg (fun X => X a b) (moment_3 c d hc hd hkl)
  norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
    bottomAt,topAt,tailWords] at h0 h1 h2 h3 ⊢
  linear_combination -h0-h1-h2-h3

''')
source=source.replace('theorem physical_outer',''.join(parts)+'theorem physical_outer')
emit(ROOT/'MainTheory/Orbit26PhysicalMatrices.lean',source)
print('Checked orbit-26 physical block generation')
