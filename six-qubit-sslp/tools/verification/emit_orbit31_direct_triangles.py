"""Emit checked signed paths and exact direct permanent substitutions."""
import argparse
from collections import deque
from pathlib import Path
from emit_orbit31_printed_orbits import PRINTED, mask_from_words
from generate_orbit31_support_candidates import graph

ROOT = Path(__file__).resolve().parents[2]
DIRECT = {3: (2, 3), 6: (2, 3), 12: (2, 3),
          **{k: (1, 2) for k in (4, 5, 7, 8, 10, 11, 13, 15)}}
ROW_PAIRS = [(0, 1), (0, 2), (1, 2)]
COL_PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def fin(j):
    return f'⟨{j},by decide⟩'


def vec(items):
    return '![' + ','.join(map(str, items)) + ']'


def generate():
    outputs = {}
    for number in sorted({1, 2} | DIRECT.keys()):
        mask = mask_from_words(PRINTED[number-1][0])
        active = [j for j in range(16) if mask >> j & 1]
        anchor = min(active)
        adjacent = [[] for _ in range(16)]
        for u, v, sign in graph(mask):
            adjacent[u].append((v, sign))
            adjacent[v].append((u, sign))
        colors, parent = {anchor: 0}, {}
        queue = deque([anchor])
        while queue:
            u = queue.popleft()
            for v, sign in adjacent[u]:
                if v not in colors:
                    colors[v] = colors[u] ^ sign
                    parent[v] = (u, sign)
                    queue.append(v)
                else:
                    assert colors[v] == colors[u] ^ sign
        assert set(colors) <= set(active)
        paths = []
        for v in range(16):
            path, here = [], v
            while here in parent:
                nxt, sign = parent[here]
                path.append(f'({"true" if sign else "false"},{fin(nxt)})')
                here = nxt
            paths.append('[' + ','.join(path) + ']')
        name = f'Type{number:02d}'
        text = f'''import MainTheory.Generated.Orbit31PrintedSupportOrbits
import MainTheory.Orbit31PhysicalSupportFilters
import MainTheory.Orbit31PermanentAlgebra

/-! Actual signed-phase propagation for the literal SI support type {number}.
Every path is checked in the actual support graph; no final no-go is used. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31DirectTriangles.{name}
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31PermanentAlgebra
open MainTheory.SignedPhaseSupport
open scoped BigOperators
noncomputable section
def mask : ℕ := {mask}
def anchor : Fin 16 := {fin(anchor)}
def colors : Fin 16 → Bool := {vec('true' if colors.get(j,0) else 'false' for j in range(16))}
def reached : Fin 16 → Bool := {vec('true' if j in colors else 'false' for j in range(16))}
def paths : Fin 16 → List (Bool × Fin 16) := {vec(paths)}
theorem printed_binding : mask =
    (MainTheory.Generated.Orbit31PrintedSupportOrbits.representatives {fin(number-1)}).val := by decide +kernel
theorem checked : ∀ v, reached v=true →
    ValidWalk (edges mask) v (paths v) ∧
    finish v (paths v)=anchor ∧ parity (paths v)=colors v := by decide +kernel

theorem phase_pattern {{c d : Fin 16 → ℂ}} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) (v : Fin 16)
    (hv : reached v=true) : sigma c d v = sign (colors v) (sigma c d anchor) := by
  have hw := checked v hv
  have he := walk_equation (graph_assignment hp hs hm) hw.1
  rw [hw.2.1,hw.2.2] at he
  exact he

theorem anchor_nonzero {{c d : Fin 16 → ℂ}} (hp : EqualProbabilities c d)
    (hm : AmplitudeSupport mask c) : sigma c d anchor ≠ 0 :=
  nonzero hp ((hm anchor).mp (by decide +kernel))
'''
        if number in DIRECT:
            e, f = DIRECT[number]
            slot = COL_PAIRS.index((e, f))
            for r, (i, j) in enumerate(ROW_PAIRS):
                signs = [1 if colors[4+4*k+h] == 0 else -1 for k,h in ((i,e),(j,f),(i,f),(j,e))]
                assert signs[0]+signs[1] == signs[2]+signs[3] and abs(signs[0]+signs[1]) == 2
                factor = (signs[0]+signs[1]) // 2
                text += f'''
theorem permanent_{r} {{c d : Fin 16 → ℂ}} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) :
    permanent c {fin(i)} {fin(j)} {fin(e)} {fin(f)}=0 := by
  have he := rectangle_phase hp hs {fin(r)} {fin(slot)}
  dsimp only at he
  norm_num [rowPairs,colPairs,B,Fin.succ] at he
  have hp0 := phase_pattern hp hs hm {fin(4+4*i+e)} (by decide +kernel)
  have hp1 := phase_pattern hp hs hm {fin(4+4*j+f)} (by decide +kernel)
  have hp2 := phase_pattern hp hs hm {fin(4+4*i+f)} (by decide +kernel)
  have hp3 := phase_pattern hp hs hm {fin(4+4*j+e)} (by decide +kernel)
  simp only [hp0,hp1,hp2,hp3] at he
  norm_num [colors,sign,Fin.succ] at he
  have hf : (2 : ℂ)*sigma c d anchor*permanent c {fin(i)} {fin(j)} {fin(e)} {fin(f)}=0 := by
    unfold permanent
    conv_lhs => norm_num [B,Fin.succ]
    linear_combination ({factor} : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (mul_ne_zero (by norm_num) (anchor_nonzero hp hm))
'''
            text += f'''
theorem no_go {{c d : Fin 16 → ℂ}} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : False := by
  apply odd_permanent_triangle (fun i => c (B i {fin(e)})) (fun i => c (B i {fin(f)}))
  · intro i
    fin_cases i <;> exact (hm _).mp (by decide +kernel)
  · intro i
    fin_cases i <;> exact (hm _).mp (by decide +kernel)
  · exact permanent_0 hp hs hm
  · exact permanent_1 hp hs hm
  · exact permanent_2 hp hs hm

theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit31.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit31.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (hm : AmplitudeSupport mask (C c)) : False :=
  no_go (physical_equal_probabilities c d hc hd hnc hnd hkl)
    (MainTheory.Orbit31PhysicalSupportFilters.physical_cross_system c d hc hd hkl) hm
'''
        text += f'\nend\nend MainTheory.Generated.Orbit31DirectTriangles.{name}\n'
        outputs[f'MainTheory/Generated/Orbit31DirectTriangles/{name}.lean'] = text
    outputs['MainTheory/Generated/Orbit31DirectTriangles/Aggregate.lean'] = '\n'.join(
        f'import MainTheory.Generated.Orbit31DirectTriangles.Type{k:02d}'
        for k in sorted({1, 2} | DIRECT.keys())) + '\n'
    return outputs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generate()
    for relative, text in outputs.items():
        path = ROOT / relative
        if args.check:
            if path.read_text(encoding='utf8') != text:
                raise SystemExit(f'stale source: {relative}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf8', newline='\n')
    print(f'{len(outputs)} direct-triangle modules ' + ('checked' if args.check else 'emitted'))


if __name__ == '__main__':
    main()
