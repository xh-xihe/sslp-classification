"""Expose actual parity fiber coordinates and pre-contradiction KL rows."""
from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
options=parser.parse_args()

def emit(path,text):
    if options.check:
        if not path.is_file() or path.read_text(encoding='utf8')!=text:
            raise SystemExit('Generated source differs: '+str(path))
    else:path.write_text(text,encoding='utf8',newline='\n')

generated={}

for orbit in (14,15,24):
    native=(R/f'SixQubit/Orbit{orbit}.lean').read_text(encoding='utf8')
    wrapper=(R/f'SixQubit/CodeOrbit{orbit}.lean').read_text(encoding='utf8')
    header,body=native[native.index('theorem no_go_of_moments'):].split('    : False := by\n',1)
    if orbit in (14,15):
        prefix=body[:body.index('  have s1z :')]
        lo=prefix.index('  have s0z :');hi=prefix.index('  have s1o12 :',lo)
        prefix=prefix[:lo]+prefix[hi:]
        diagonal=[('sd0',range(4),range(4)),('sd1',range(8,12),range(8,12)),
                  ('sd6',range(4,8),range(4,8)),('sd7',range(12,16),range(12,16))]
        pattern=r'^  have (s[01]o\d\d|s[01]fB) : (.*?) := by'
    else:
        prefix=body[:body.index('  have tot :=')]
        diagonal=[('cd0',range(8),range(8)),('cd1',range(8,16),range(8,16))]
        pattern=r'^  have (g\d_\d|fB) : (.*?) := by'
    rows=[(m.group(1),m.group(2)) for m in re.finditer(pattern,prefix,re.M|re.S)]
    assert len(rows)==(26 if orbit in (14,15) else 33),(orbit,len(rows))
    assert 'slice_zero' not in prefix and 'False' not in prefix
    for name,ys,zs in diagonal:
        left=' + '.join(f'Complex.normSq (c y{i})' for i in ys)
        right=' + '.join(f'Complex.normSq (d z{i})' for i in reversed(list(zs))) if orbit!=24 else ' + '.join(f'Complex.normSq (d z{i})' for i in zs)
        rows.append((name,f'{left} = {right}'))
    data='def FrameData (c d : SS.State 6 ℂ) : Prop :=\n  '+' ∧\n  '.join('('+p+')' for _,p in rows)+'\n'
    proof=header.replace('theorem no_go_of_moments','theorem frame_data_of_rows')+'    : FrameData c d := by\n'+prefix+'  exact ⟨'+','.join(n for n,_ in rows)+'⟩\n'
    physical=wrapper[wrapper.index('theorem no_code'):]
    physical=physical[:physical.index('\nend')]
    physical=physical.replace('theorem no_code','theorem physical_frame_data').replace(' : False :=',' : FrameData c d :=')
    physical=physical.replace('no_go_of_moments c d','frame_data_of_rows c d').replace('(by decide)','(by decide +kernel)')
    effective={14:'![x 1,x 3,x 4,x 5]',15:'![x 2,x 3,x 4,x 5]',24:'![x 1,x 2,x 3,x 4]'}[orbit]
    constraint={14:'x 1=x 2',15:'x 1=false',24:'x 0=x 5'}[orbit]
    pack={14:'![a,z 0,z 0,z 1,z 2,z 3]',15:'![a,false,z 0,z 1,z 2,z 3]',24:'![a,z 0,z 1,z 2,z 3,a]'}[orbit]
    pair={14:'x 0',15:'x 0',24:'x 0'}[orbit]
    intro=f'''import SixQubit.CodeOrbit{orbit}
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit{orbit}ParityFrames
open scoped BigOperators Matrix
open SixQubit SixQubit.Orbit{orbit}
noncomputable section
def effective (x : SS.BitString 6) : SS.BitString 4 := {effective}
def parity (z : SS.BitString 4) : Bool := (List.ofFn z).count true % 2 = 1
def pack (a : Bool) (z : SS.BitString 4) : SS.BitString 6 := {pack}
def spinor (c : SS.State 6 ℂ) (z : SS.BitString 4) : Fin 2 → ℂ :=
  fun a => c (pack (a=1) z)
theorem literal_fibers : ∀ x : SS.BitString 6,
    (x∈S0 ↔ {constraint} ∧ parity (effective x)=false) ∧
    (x∈S1 ↔ {constraint} ∧ parity (effective x)=true) := by decide +kernel
theorem pack_reconstruction : ∀ x : SS.BitString 6,x∈S0 ∪ S1 →
    pack ({pair}) (effective x)=x := by decide +kernel
theorem pack_injective : Function.Injective (fun p : Bool × SS.BitString 4 => pack p.1 p.2) := by decide +kernel
theorem bottom_coordinates : (Finset.univ.filter fun p : Bool × SS.BitString 4 => parity p.2=false).image
    (fun p => pack p.1 p.2)=S0 := by decide +kernel
theorem top_coordinates : (Finset.univ.filter fun p : Bool × SS.BitString 4 => parity p.2=true).image
    (fun p => pack p.1 p.2)=S1 := by decide +kernel
'''
    generated[orbit]=intro+'\n'+data+'\n'+proof+'\n'+physical+f'\nend\nend MainTheory.Orbit{orbit}ParityFrames\n'
    print('Generated literal physical parity data:',orbit,len(rows))

for orbit in (14,15,24):
    s=generated[orbit];marker=f'\nend\nend MainTheory.Orbit{orbit}ParityFrames\n'
    assert 'def bottomSpinor' not in s
    words=lambda letter,start:'!['+','.join(f'{letter}{i}' for i in range(start,start+8))+']'
    ns=[f'h{i}' for i in range(30 if orbit!=24 else 35)]
    off=(12,25) if orbit!=24 else (32,)
    diag=(26,27,28,29) if orbit!=24 else (33,34)
    extra=f'''
def bottomWords : Fin 8 → SS.BitString 6 := {words('y',0)}
def bottomWordsOne : Fin 8 → SS.BitString 6 := {words('y',8)}
def topWords : Fin 8 → SS.BitString 6 := {words('z',0)}
def topWordsOne : Fin 8 → SS.BitString 6 := {words('z',8)}
def bottomLabels (i : Fin 8) := effective (bottomWords i)
def topLabels (i : Fin 8) := effective (topWords i)
def bottomSpinor (c : SS.State 6 ℂ) (i : Fin 8) : Fin 2 → ℂ :=
  ![c (bottomWords i),c (bottomWordsOne i)]
def topSpinor (d : SS.State 6 ℂ) (i : Fin 8) : Fin 2 → ℂ :=
  ![d (topWords i),d (topWordsOne i)]
theorem bottom_spinor_words : ∀ (i : Fin 8) (a : Fin 2),pack (a=1) (bottomLabels i)=
    (if a=0 then bottomWords i else bottomWordsOne i) := by decide +kernel
theorem top_spinor_words : ∀ (i : Fin 8) (a : Fin 2),pack (a=1) (topLabels i)=
    (if a=0 then topWords i else topWordsOne i) := by decide +kernel
theorem bottom_labels_exact : Function.Injective bottomLabels ∧
    Finset.univ.image bottomLabels=Finset.univ.filter (fun z => parity z=false) := by decide +kernel
theorem top_labels_exact : Function.Injective topLabels ∧
    Finset.univ.image topLabels=Finset.univ.filter (fun z => parity z=true) := by decide +kernel
theorem actual_bottom_spinor (c : SS.State 6 ℂ) (i : Fin 8) :
    bottomSpinor c i=spinor c (bottomLabels i) := by
  funext a
  rw [spinor,bottom_spinor_words]
  fin_cases a <;> simp [bottomSpinor]
theorem actual_top_spinor (d : SS.State 6 ℂ) (i : Fin 8) :
    topSpinor d i=spinor d (topLabels i) := by
  funext a
  rw [spinor,top_spinor_words]
  fin_cases a <;> simp [topSpinor]
def bottomFrame (c : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i,Matrix.vecMulVec (bottomSpinor c i) (star (bottomSpinor c i))
def topFrame (d : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i,Matrix.vecMulVec (topSpinor d i) (star (topSpinor d i))
theorem frame_of_data (c d : SS.State 6 ℂ) (h : FrameData c d) :
    bottomFrame c=topFrame d := by
  obtain ⟨{','.join(ns)}⟩ := h
'''
    for i in diag:
        extra+=f'  have c{i} := congrArg (fun x : ℝ => (x : ℂ)) h{i}\n  push_cast at c{i}\n  simp only [Complex.normSq_eq_conj_mul_self] at c{i}\n'
    for i in off:extra+=f'  have s{i} := congrArg star h{i}\n'
    used=[*(f'c{i}' for i in diag),*(f'h{i}' for i in off),*(f's{i}' for i in off)]
    extra+='  ext a b\n  fin_cases a <;> fin_cases b\n'
    extra+='  all_goals norm_num [bottomFrame,topFrame,bottomSpinor,topSpinor,bottomWords,bottomWordsOne,topWords,topWordsOne,Matrix.sum_apply,Matrix.vecMulVec_apply,Pi.star_apply,Fin.sum_univ_succ,Fin.succ] at '+' '.join(used)+' ⊢\n'
    extra+='  all_goals simp only [starRingEnd_apply] at '+' '.join(used)+' ⊢\n'
    sums=lambda prefix,indices:'+'.join(f'{prefix}{i}' for i in indices)
    for expr in [sums('c',diag[::2]),sums('h',off),sums('s',off),sums('c',diag[1::2])]:
        extra+=f'  · linear_combination {expr}\n'
    extra+='''theorem physical_frame_equality (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : bottomFrame c=topFrame d := by
  exact frame_of_data c d (physical_frame_data c d hc hd hnc hnd hkl)
'''
    generated[orbit]=s.replace(marker,'\n'+extra+marker)
    print('Extended actual frame equality:',orbit)

for orbit,source in generated.items():emit(R/f'MainTheory/Orbit{orbit}ParityFrames.lean',source)
