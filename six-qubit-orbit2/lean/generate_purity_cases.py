#!/usr/bin/env python3
"""Generate disjoint finite purity coefficient checks; Lean proves each batch.
The mathematical definitions are maintained in PurityDefinitions.lean.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parent/'Orbit2'
def main():
    out=ROOT/'PurityCases';out.mkdir(exist_ok=True)
    imports=[];proof=[]
    for r in range(4):
        for b in range(4):
            for c in range(4):
                name=f'Case{r*16+b*4+c:03d}'
                imports.append(f'import Orbit2.PurityCases.{name}')
                (out/(name+'.lean')).write_text(f'''import Orbit2.PurityDefinitions
namespace Orbit2.PurityReduction.{name}
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked : ∀ a : Orbit2.TensorPauli.Label 4,
    let p := packed {r} {b} {c} a
    ¬ (forbidden p ∨ forbidden (partner p)) →
    purityCoefficient p + purityCoefficient (partner p) =
      -4 * (targetCoefficient p + targetCoefficient (partner p)) := by
  decide +kernel
end Orbit2.PurityReduction.{name}
''')
                proof.append(f'  · exact {name}.checked a')
    (ROOT/'PurityCases.lean').write_text('\n'.join(imports)+'''
namespace Orbit2.PurityReduction
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packed_identity (r b c : Fin 4) (a : Label 4) :
    let p := packed r b c a
    ¬ (forbidden p ∨ forbidden (partner p)) →
    purityCoefficient p + purityCoefficient (partner p) =
      -4 * (targetCoefficient p + targetCoefficient (partner p)) := by
  fin_cases r <;> fin_cases b <;> fin_cases c
'''+ '\n'.join(proof)+'\nend Orbit2.PurityReduction\n')
    print('Generated 64 batches covering all 16384 purity labels.')
if __name__=='__main__':main()
