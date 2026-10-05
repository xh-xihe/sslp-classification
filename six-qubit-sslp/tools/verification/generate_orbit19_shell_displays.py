"""Expose actual orbit-19 shell projectors and pre-contradiction physical rows."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[2]
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
options=parser.parse_args()

def emit(path,text):
    if options.check:
        if not path.is_file() or path.read_text(encoding='utf8')!=text:
            raise SystemExit('Generated source differs: '+str(path))
    else:path.write_text(text,encoding='utf8',newline='\n')

native=(ROOT/'SixQubit/Orbit19.lean').read_text(encoding='utf8')
wrapper=(ROOT/'SixQubit/CodeOrbit19.lean').read_text(encoding='utf8')
header,body=native[native.index('theorem no_go_of_moments'):].split('    : False := by\n',1)
prefix=body[:body.index('  have sq0 :')]
propositions=[]
for name in [*(f'p{i}' for i in range(8)),'z0m','z4m']:
    match=re.search(r'^  have '+name+r' : (.*?) := (?:by|nsqZero)',prefix,re.M|re.S)
    assert match,name
    propositions.append((name,match.group(1)))
anchor=[('a0','Complex.normSq (c y0)+Complex.normSq (c y1)=Complex.normSq (d z0)+Complex.normSq (d z1)'),
 ('a4','Complex.normSq (c y14)+Complex.normSq (c y15)=Complex.normSq (d z14)+Complex.normSq (d z15)'),
 ('ah','Complex.normSq (c y0)+Complex.normSq (c y1)+Complex.normSq (c y14)+Complex.normSq (c y15)=1/2')]
props=propositions[:8]+anchor+propositions[8:]
typedef='def AnchorData (c d : SS.State 6 ℂ) : Prop :=\n  '+' ∧\n  '.join('('+p+')' for _,p in props)+'\n'
proof=header.replace('theorem no_go_of_moments','theorem anchor_data_of_rows')+'    : AnchorData c d := by\n'+prefix
proof+='  exact ⟨'+','.join(n for n,_ in props)+'⟩\n'
physical=wrapper[wrapper.index('theorem no_code'):]
physical=physical[:physical.index('\nend')]
physical=physical.replace('theorem no_code','theorem physical_anchor_data').replace(' : False :=',' : AnchorData c d :=')
physical=physical.replace('no_go_of_moments c d','anchor_data_of_rows c d').replace('(by decide)','(by decide +kernel)')
intro='''import SixQubit.CodeOrbit19
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit19ShellDisplays
open scoped BigOperators
open SixQubit SixQubit.Orbit19
noncomputable section
def bit (x : SS.BitString 6) (j : Fin 6) : ℤ := if x j then 1 else 0
def w (x : SS.BitString 6) : ℤ := ∑ j : Fin 4,bit x (Fin.castAdd 2 j)
def g0 (x : SS.BitString 6) : ℚ := ((w x : ℚ)-2)*((w x : ℚ)-4)/8
def g4 (x : SS.BitString 6) : ℚ := (w x : ℚ)*((w x : ℚ)-2)/8
def h (x : SS.BitString 6) : ℚ := g0 x+g4 x
def u (x : SS.BitString 6) : ℚ := (bit x 4 : ℚ)+(bit x 5 : ℚ)-2*(bit x 4 : ℚ)*(bit x 5 : ℚ)
def chi (j : Fin 6) (x : SS.BitString 6) : ℚ := if x j then -1 else 1
def sign (a : Bool) : ℚ := if a then -1 else 1
def sigma (x : SS.BitString 6) : ℚ := ∑ j : Fin 4,chi (Fin.castAdd 2 j) x
def phi5 (a b : Bool) (x : SS.BitString 6) : ℚ :=
  (1+sign b*chi 4 x)/16*(2+sign a*sigma x-2*sign b*chi 5 x)
def phi6 (a b : Bool) (x : SS.BitString 6) : ℚ :=
  (1+sign b*chi 5 x)/16*(2+sign a*sigma x-2*sign b*chi 4 x)

theorem literal_fibers : ∀ x : SS.BitString 6,
    (x∈S0 ↔ ((w x=0 ∨ w x=4) ∧ x 4=x 5) ∨ (w x=2 ∧ x 4≠x 5)) ∧
    (x∈S1 ↔ ((w x=0 ∨ w x=4) ∧ x 4≠x 5) ∨ (w x=2 ∧ x 4=x 5)) := by decide +kernel
theorem square_weight : ∀ x : SS.BitString 6,
    w x^2=w x+2*(∑ i : Fin 4,∑ j : Fin 4,
      if i<j then bit x (Fin.castAdd 2 i)*bit x (Fin.castAdd 2 j) else 0) := by decide +kernel
theorem shell_projectors : ∀ x : SS.BitString 6,x∈S0 ∪ S1 →
    g0 x=(if w x=0 then 1 else 0) ∧ g4 x=(if w x=4 then 1 else 0) := by decide +kernel
theorem u_restriction : (∀ x : SS.BitString 6,x∈S0 → u x=1-h x) ∧
    (∀ x : SS.BitString 6,x∈S1 → u x=h x) := by decide +kernel
theorem phi5_anchor : ∀ a b x,x∈S1 →
    phi5 a b x=(if x=![a,a,a,a,b,!b] then 1 else 0) := by decide +kernel
theorem phi6_anchor : ∀ a b x,x∈S1 →
    phi6 a b x=(if x=![a,a,a,a,!b,b] then 1 else 0) := by decide +kernel
theorem phi5_expansion : ∀ a b x,
    16*phi5 a b x=2+sign a*sigma x-2*sign b*chi 5 x+2*sign b*chi 4 x+
      sign a*sign b*chi 4 x*sigma x-2*chi 4 x*chi 5 x := by decide +kernel
theorem phi6_expansion : ∀ a b x,
    16*phi6 a b x=2+sign a*sigma x-2*sign b*chi 4 x+2*sign b*chi 5 x+
      sign a*sign b*chi 5 x*sigma x-2*chi 5 x*chi 4 x := by decide +kernel
'''
target=ROOT/'MainTheory/Orbit19ShellDisplays.lean'
emit(target,intro+'\n'+typedef+'\n'+proof+'\n'+physical+'\nend\nend MainTheory.Orbit19ShellDisplays\n')
print('Generated shell projectors and physical pre-contradiction anchor rows')
