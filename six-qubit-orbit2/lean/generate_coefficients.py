#!/usr/bin/env python3
"""Untrusted producer for Lean checks of the direct quartic coefficient formula.
Includes all same-character coordinates, including all 36 zero coordinates.
"""
from pathlib import Path
from collections import defaultdict
import importlib.util
import json
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('exact', ROOT.parent/'orbit2_exact_certificate.py')
v=importlib.util.module_from_spec(spec); spec.loader.exec_module(v)

def vec(xs):
    return '!['+', '.join(xs)+']'

def matrix(A):
    return vec([vec([str(x) if x>=0 else f'({x})' for x in row]) for row in A])

def main():
    M=v.build_integer_certificate()
    blocks=json.loads((ROOT.parent/'orbit2_certificate_blocks.json').read_text())['blocks']
    groups=defaultdict(list)
    for r,(a,b) in enumerate(v.MONOMIALS):
        groups[v.MUL[v.T_IDS[a]][v.T_IDS[b]]].append(r)
    out=ROOT/'Orbit2/Coefficients';out.mkdir(exist_ok=True)
    imports=[]
    entries=[]
    owner=[None]*528
    slots=[None]*528
    characters=[]
    for b,(character,indices) in enumerate(sorted(groups.items())):
        name=f'Coefficient{b:03d}'
        imports.append(f'import Orbit2.Coefficients.{name}')
        n=len(indices)
        ns=f'Coefficient{b:03d}'
        entries.append('{ n := '+str(n)+', indices := '+ns+'.indices, expected := '+ns+
            '.expected, coefficients := '+ns+'.coefficient_identity, block := '+str(b)+
            ', energy := '+ns+'.energy_identity }')
        characters.append(vec([str(k) for k in v.LABELS[character]]))
        for i,r in enumerate(indices):
            assert owner[r] is None
            owner[r]=b;slots[r]=i
        A=[[2*M.get((r,c),0) for c in indices] for r in indices]
        block=blocks[b]
        assert block['character']==v.label_string(v.LABELS[character])
        positive=block['monomial_indices']
        d=len(positive)
        embedding=[indices.index(r) for r in positive]
        active=[r in positive for r in indices]
        positions=[positive.index(r) if r in positive else 0 for r in indices]
        source=f'''import Orbit2.QuarticCoefficients
import Orbit2.ZeroExtension

/-! Exact coefficient check for character {v.label_string(v.LABELS[character])}.
Coordinates include the weight-one/weight-one zero monomials. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Orbit2.Quartic.{name}

def indices : Fin {n} → Fin 528 := {vec([str(i) for i in indices])}
def expected : Matrix (Fin {n}) (Fin {n}) ℤ := {matrix(A)}
def active : Fin {n} → Bool := {vec(['true' if a else 'false' for a in active])}
def position : Fin {n} → Fin {d} := {vec([str(k) for k in positions])}
def positivePosition : Fin {d} → Fin {n} := {vec([str(k) for k in embedding])}

/-- Reconstructing 24Q gives exactly twice the integer Gram matrix. -/
theorem coefficient_identity : ∀ i j,
    twiceCoefficient (indices i) (indices j) = expected i j := by
  decide +kernel

/-- The reconstructed coefficients are the very matrices whose LDL factors
were checked, with zero coordinates retained explicitly. -/
theorem certified_matrix : ∀ i j, (expected i j : ℚ) =
    if active i ∧ active j then 2 * Orbit2.Block{b:03d}.M (position i) (position j) else 0 := by
  decide +kernel

theorem certified_indices : ∀ k,
    indices (positivePosition k) = (checkedBlocks {b}).indices k := by
  decide +kernel

theorem positive_retraction : ∀ k, position (positivePosition k) = k := by
  decide +kernel

theorem active_embedding : ∀ i, active i → positivePosition (position i) = i := by
  decide +kernel

theorem positive_active : ∀ k, active (positivePosition k) := by
  decide +kernel

theorem energy_identity (z : Fin 528 → ℂ) :
    complexEnergy (fun i j => (expected i j : ℚ)) (fun i => z (indices i)) =
      2 * blockEnergy (checkedBlocks {b}) z := by
  have h := complexEnergy_zero_extension (fun i j => (expected i j : ℚ))
    Orbit2.Block{b:03d}.M active position positivePosition positive_retraction
    positive_active active_embedding certified_matrix (fun i => z (indices i))
  change _ = 2 * complexEnergy Orbit2.Block{b:03d}.M
    (fun k => z ((checkedBlocks {b}).indices k))
  simpa only [certified_indices] using h

end Orbit2.Quartic.{name}
'''
        (out/f'{name}.lean').write_text(source)
    (ROOT/'Orbit2/Coefficients.lean').write_text('\n'.join(imports)+'\n')
    assert all(b is not None for b in owner)
    reconstruction=f'''import Orbit2.Coefficients
import Orbit2.ReconstructionBase
import Orbit2.CharacterBlocks

namespace Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def reconstructedBlocks : Fin 111 → ReconstructedBlock := {vec(entries)}
def coordinateOwner : Fin 528 → Fin 111 := {vec([str(b) for b in owner])}
def coordinateSlot : Fin 528 → Fin 32 := {vec([str(k) for k in slots])}
def characters : Fin 111 → Orbit2.TensorPauli.Label 4 := {vec(characters)}

theorem block_order : ∀ b, (reconstructedBlocks b).block = b := by decide +kernel
theorem coordinate_bound : ∀ r, (coordinateSlot r).val <
    (reconstructedBlocks (coordinateOwner r)).n := by decide +kernel
def coordinateIndex (r : Fin 528) : Fin (reconstructedBlocks (coordinateOwner r)).n :=
  ⟨(coordinateSlot r).val, coordinate_bound r⟩
theorem coordinate_covered : ∀ r,
    (reconstructedBlocks (coordinateOwner r)).indices (coordinateIndex r) = r := by
  decide +kernel
theorem coordinate_unique : ∀ b (i : Fin (reconstructedBlocks b).n),
    coordinateOwner ((reconstructedBlocks b).indices i) = b ∧
      (coordinateSlot ((reconstructedBlocks b).indices i)).val = i.val := by
  decide +kernel
theorem coordinate_character : ∀ b (i : Fin (reconstructedBlocks b).n),
    monomialCharacter ((reconstructedBlocks b).indices i) = characters b := by
  decide +kernel
theorem characters_injective : Function.Injective characters := by decide +kernel

theorem cross_block_zero (b c : Fin 111) (h : b ≠ c)
    (i : Fin (reconstructedBlocks b).n) (j : Fin (reconstructedBlocks c).n) :
    twiceCoefficient ((reconstructedBlocks b).indices i) ((reconstructedBlocks c).indices j) = 0 := by
  apply twiceCoefficient_offblock
  rw [coordinate_character,coordinate_character]
  exact fun he => h (characters_injective he)

/-- The coefficient polynomial, including its zero coordinates, has exactly
the certified Gram energy and normalization. The operator expansion is a
separate obligation, not a field of this theorem. -/
theorem reconstructed_polynomial_eq_certificate (z : Fin 528 → ℂ) :
    reconstructedEnergy reconstructedBlocks z = familyEnergy checkedBlocks z :=
  reconstructedEnergy_eq_family reconstructedBlocks block_order z

end Orbit2.Quartic
'''
    (ROOT/'Orbit2/Reconstruction.lean').write_text(reconstruction)
    print(f'Generated {len(imports)} coefficient modules; 3584 entries including zeros.')

if __name__=='__main__':main()
