#!/usr/bin/env python3
"""Untrusted certificate producer. Lean checks every emitted equality/pivot.
Does not run a search: deterministic rational LDL of the 111 supplied blocks.
"""
from fractions import Fraction
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent

def q(x):
    x = Fraction(x)
    if x.denominator == 1:
        return str(x.numerator) if x >= 0 else f'({x.numerator})'
    return f'({x.numerator} / {x.denominator})'

def vec(xs):
    return '![' + ', '.join(xs) + ']'

def matrix(xs):
    return vec([vec([q(x) for x in row]) for row in xs])

def main():
    data = json.loads((ROOT.parent / 'orbit2_certificate_blocks.json').read_text())
    out = ROOT / 'Orbit2' / 'Blocks'
    out.mkdir(exist_ok=True)
    imports = []
    for b, block in enumerate(data['blocks']):
        M = block['matrix']
        n = len(M)
        A = [[Fraction(M[i][j] - 4*(i == j)) for j in range(n)] for i in range(n)]
        L = [[Fraction(i == j) for j in range(n)] for i in range(n)]
        d = []
        for k in range(n):
            d.append(A[k][k])
            assert d[-1] > 0
            for i in range(k+1, n):
                L[i][k] = A[i][k] / d[k]
            for i in range(k+1, n):
                for j in range(k+1, n):
                    A[i][j] -= L[i][k] * d[k] * L[j][k]
        assert d == [Fraction(x) for x in block['ldlt_pivots_of_matrix_minus_4I']]
        name = f'Block{b:03d}'
        imports.append(f'import Orbit2.Blocks.{name}')
        source = f'''import Orbit2.Certificate

/-! Generated, untrusted data for character {block['character']}.
Global monomial indices: {block['monomial_indices']}.
All assertions below are checked by Lean's kernel using `decide +kernel`.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2.{name}

def M : Matrix (Fin {n}) (Fin {n}) ℚ := {matrix(M)}
def L : Matrix (Fin {n}) (Fin {n}) ℚ := {matrix(L)}
def d : Fin {n} → ℚ := {vec([q(x) for x in d])}

def certificate : LDLCertificate {n} {n} where
  A := fun i j => M i j - if i = j then 4 else 0
  L := L
  d := d
  positive := by decide +kernel
  factorization := by decide +kernel

theorem coercivity (z : Fin {n} → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z :=
  shifted_coercivity M certificate (fun _ _ => rfl) z

end Orbit2.{name}
'''
        (out / f'{name}.lean').write_text(source)
    (ROOT / 'Orbit2' / 'Blocks.lean').write_text('\n'.join(imports) + '\n')
    print(f'Generated {len(imports)} kernel-checkable block certificates.')

# The family is a concrete polynomial in the original 32 complex coordinates.
def generate_global():
    data = json.loads((ROOT.parent / 'orbit2_certificate_blocks.json').read_text())
    entries = []
    where_diagonal = {}
    for b, block in enumerate(data['blocks']):
        ns = f'Block{b:03d}'
        entries.append('{ n := ' + str(len(block['matrix'])) + ', M := ' + ns + '.M, '
            'certificate := ' + ns + '.certificate, shifted := fun _ _ => rfl, '
            'indices := ' + vec([str(i) for i in block['monomial_indices']]) + ' }')
        for k, idx in enumerate(block['monomial_indices']):
            a, c = data['monomials'][idx]
            if a == c:
                where_diagonal[a] = (b, k)
    three = [i for i,p in enumerate(data['pauli_order']) if sum(x != 'I' for x in p) == 3]
    assert len(three) == 24 and all(i in where_diagonal for i in three)
    proof = '\n'.join(f'  · exact ⟨{where_diagonal[i][0]}, ⟨{where_diagonal[i][1]}, by decide +kernel⟩, by decide +kernel⟩' for i in three)
    basis = vec([vec([str('IXYZ'.index(x)) for x in p]) for p in data['pauli_order']])
    source = f'''import Orbit2.Blocks
import Orbit2.BlockFamily

/-! Concrete checked block polynomial. The equality between this polynomial
and the trace contractions in the manuscript remains a formalization obligation. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2

def checkedBlocks : Fin 111 → CheckedBlock := {vec(entries)}

def monomials : Fin 528 → Fin 32 × Fin 32 :=
  {vec([f'({a}, {b})' for a,b in data['monomials']])}

def weightThreeLabels : Fin 24 → Fin 32 := {vec([str(i) for i in three])}

/-- I=0, X=1, Y=2, Z=3, in the supplied lexicographic coordinate order. -/
def pauliBasis : Fin 32 → Fin 4 → Fin 4 := {basis}

def pauliWeight (p : Fin 4 → Fin 4) : ℕ := ∑ i, if p i = 0 then 0 else 1

def transverseCount (p : Fin 4 → Fin 4) : ℕ :=
  ∑ i, if p i = 1 ∨ p i = 2 then 1 else 0

theorem pauliBasis_support : ∀ j, transverseCount (pauliBasis j) = 1 ∧
    (pauliWeight (pauliBasis j) = 1 ∨ pauliWeight (pauliBasis j) = 3) := by
  decide +kernel

theorem weightThreeLabels_correct : ∀ i,
    pauliWeight (pauliBasis (weightThreeLabels i)) = 3 := by decide +kernel

theorem weightThreeLabels_complete : ∀ j, pauliWeight (pauliBasis j) = 3 →
    ∃ i, weightThreeLabels i = j := by decide +kernel

def quadraticMonomials (t : Fin 32 → ℂ) : Fin 528 → ℂ :=
  fun j => t (monomials j).1 * t (monomials j).2

/-- Each weight-three square actually occurs in one of the checked blocks. -/
theorem weightThree_diagonal_covered (i : Fin 24) :
    ∃ b, ∃ k : Fin (checkedBlocks b).n,
      monomials ((checkedBlocks b).indices k) = (weightThreeLabels i, weightThreeLabels i) := by
  fin_cases i
{proof}

/-- The finite certificate's rigidity implication with a single, explicit
remaining hypothesis: the constrained trace-to-polynomial equality.
This is NOT the full encoder theorem. -/
theorem checked_polynomial_rigidity (t : Fin 32 → ℂ) (c : Fin 48 → ℝ)
    (hidentity : familyEnergy checkedBlocks (quadraticMonomials t) = -(∑ e, c e^2)) :
    (∀ e, c e = 0) ∧ (∀ i, t (weightThreeLabels i) = 0) := by
  obtain ⟨hc, hz⟩ := family_rigidity checkedBlocks (quadraticMonomials t) c hidentity
  refine ⟨hc, ?_⟩
  intro i
  obtain ⟨b, k, hdiag⟩ := weightThree_diagonal_covered i
  have hi := hz b k
  simp only [quadraticMonomials, hdiag] at hi
  exact mul_self_eq_zero.mp hi

end Orbit2
'''
    (ROOT / 'Orbit2' / 'Global.lean').write_text(source)

if __name__ == '__main__':
    main()
    generate_global()
