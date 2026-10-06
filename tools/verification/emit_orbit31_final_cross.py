"""Emit literal cross-equation substitutions for SI types one and two."""
import argparse
from pathlib import Path
from emit_orbit31_printed_orbits import PRINTED, mask_from_words

ROOT = Path(__file__).resolve().parents[2]


def fin(j):
    return f'⟨{j},by decide⟩'


def c(j):
    return '(c ' + fin(j) + ')'


def generate():
    text = '''import MainTheory.Generated.Orbit31DirectTriangles.Type01
import MainTheory.Generated.Orbit31DirectTriangles.Type02

/-! Literal SI equations for the mixed triangle and final twelve-string class.
Each equation follows from actual signed paths and canonical physical rows. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace MainTheory.Orbit31FinalCross
noncomputable section
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31PermanentAlgebra
open MainTheory.SignedPhaseSupport
open scoped BigOperators

theorem inactive_zero {mask : ℕ} {c : Fin 16 → ℂ} (hm : AmplitudeSupport mask c)
    (j : Fin 16) (hj : active mask j=false) : c j=0 := by
  by_contra hn
  have ha := (hm j).mpr hn
  rw [hj] at ha
  contradiction
'''
    for number in (1, 2):
        text += f'\nnamespace Type{number:02d}\nopen MainTheory.Generated.Orbit31DirectTriangles.Type{number:02d}\n'
        mask = mask_from_words(PRINTED[number-1][0])
        if number == 1:
            specs = [('equation1', 'weight', 1, 1, c(2)+'*'+c(10)+'+'+c(3)+'*'+c(11)),
                     ('equation2', 'weight', 2, 1, c(2)+'*'+c(14)+'+'+c(3)+'*'+c(15)),
                     ('equation3', 'rectangle', (2, 5), 1, c(10)+'*'+c(15)+'+'+c(11)+'*'+c(14))]
        else:
            specs = [('equation1', 'weight', 1, 1, c(0)+'*'+c(8)+'+'+c(1)+'*'+c(9)),
                     ('equation2', 'rectangle', (0, 0), 1, c(4)+'*'+c(9)+'+'+c(5)+'*'+c(8)),
                     ('equation3', 'weight', 2, -1, c(2)+'*'+c(14)+'+'+c(3)+'*'+c(15)),
                     ('equation4', 'rectangle', (1, 5), -1, c(6)+'*'+c(15)+'+'+c(7)+'*'+c(14)),
                     ('equation5', 'weight', 0, 1, c(0)+'*'+c(4)+'+'+c(1)+'*'+c(5)+'-'+c(2)+'*'+c(6)+'-'+c(3)+'*'+c(7))]
        for name, kind, parameter, factor, expression in specs:
            text += f'''
theorem {name} {{c d : Fin 16 → ℂ}} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : {expression}=0 := by
'''
            if kind == 'weight':
                text += f'  have he := weight_one_phase_sum hp hs {fin(parameter)}\n'
                indices = [4+4*parameter+e for e in range(4)]
                zeros = [(e if not mask >> e & 1 else 4+4*parameter+e)
                         for e in range(4) if not (mask >> e & 1 and mask >> (4+4*parameter+e) & 1)]
                indices = [4+4*parameter+e for e in range(4)
                           if mask >> e & 1 and mask >> (4+4*parameter+e) & 1]
                factor_scale = factor
            else:
                r, k = parameter
                i, j = [(0, 1), (0, 2), (1, 2)][r]
                e, f = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)][k]
                indices = [4+4*i+e, 4+4*j+f, 4+4*i+f, 4+4*j+e]
                zeros = []
                text += f'  have he := rectangle_phase hp hs {fin(r)} {fin(k)}\n  dsimp only at he\n'
                factor_scale = factor/2
            text += '  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he\n'
            inactive = sorted(set(zeros))
            for j in inactive:
                text += f'  have hz{j} := inactive_zero hm {fin(j)} (by decide +kernel)\n'
            if inactive:
                text += '  simp at ' + ' '.join('hz'+str(j) for j in inactive) + '\n'
                text += '  simp [' + ','.join('hz'+str(j) for j in inactive) + '] at he\n'
            else:
                text += '  simp at he\n'
            for j in sorted(set(indices)):
                if mask >> j & 1:
                    text += f'  have hs{j} := phase_pattern hp hs hm {fin(j)} (by decide +kernel)\n'
            text += '  simp [colors,sign] at ' + ' '.join('hs'+str(j) for j in sorted(set(indices)) if mask >> j & 1) + '\n'
            text += '  simp only [' + ','.join('hs'+str(j) for j in sorted(set(indices)) if mask >> j & 1) + '] at he\n'
            text += f'''  have hf : sigma c d anchor*({expression})=0 := by
    conv_lhs => simp
    linear_combination ({factor_scale if kind == 'weight' else str(factor)+'/2'} : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)
'''
        if number == 1:
            text += f'''
theorem no_go {{c d : Fin 16 → ℂ}} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : False :=
  mixed_triangle {c(2)} {c(3)} {c(10)} {c(11)} {c(14)} {c(15)}
    ((hm _).mp (by decide +kernel)) ((hm _).mp (by decide +kernel))
    ((hm _).mp (by decide +kernel)) (equation1 hp hs hm) (equation2 hp hs hm) (equation3 hp hs hm)
'''
        else:
            text += f'''
theorem commonK {{c d : Fin 16 → ℂ}} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ e : Fin 4, c (A e)*c (B {fin(0)} e)=K := by
  have hl := product_equality {c(0)} {c(1)} {c(4)} {c(5)} {c(8)} {c(9)}
    ((hm _).mp (by decide +kernel)) (equation1 hp hs hm) (equation2 hp hs hm)
  have hr := product_equality {c(2)} {c(3)} {c(6)} {c(7)} {c(14)} {c(15)}
    ((hm _).mp (by decide +kernel)) (equation3 hp hs hm) (equation4 hp hs hm)
  have hall := common_product ![{c(0)},{c(1)},{c(2)},{c(3)}] ![{c(4)},{c(5)},{c(6)},{c(7)}]
    hl hr (equation5 hp hs hm)
  refine ⟨{c(0)}*{c(4)},mul_ne_zero ((hm _).mp (by decide +kernel))
    ((hm _).mp (by decide +kernel)),?_⟩
  intro e
  fin_cases e
  · rfl
  · exact hl.symm
  · exact hall.1.symm
  · exact hall.2.symm
'''
        text += f'\nend Type{number:02d}\n'
    text += '\nend\nend MainTheory.Orbit31FinalCross\n'
    return text


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT/'MainTheory/Orbit31FinalCross.lean'
    text = generate()
    if args.check:
        if path.read_text(encoding='utf8') != text:
            raise SystemExit('stale final cross source')
    else:
        path.write_text(text, encoding='utf8', newline='\n')
    print('final cross source ' + ('checked' if args.check else 'emitted'))


if __name__ == '__main__':
    main()
