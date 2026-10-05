"""Independently check every Orbit-2 block against the manuscript's table.

Requires SymPy. Run after generating orbit2-blocks.json with the packaged
standard-library verifier; this additional check is not a Lean certificate.
"""
from pathlib import Path
import json
import sympy as sp

ROOT = Path(__file__).resolve().parent
x = sp.Symbol('x')
EXPECTED = {
    (0, 0, 24): (x-424)*(x-192)**4*(x-24)**11*(x-16)**2*(x*x-48*x+192)**3,
    (1, 0, 3): (x-384)*(x-48)**2,
    (2, 2, 3): (x-52)*(x*x-460*x+47872),
    (3, 2, 4): (x-50)*(x-46)*(x*x-248*x+10716),
    (2, 0, 8): (x-32)*(x-24)*(x*x-408*x+9856)*(x*x-352*x+9216)**2,
    (3, 0, 12): (x-136)*(x-48)*(x*x-352*x+9216)**3*(x*x-64*x+720)**2,
    (4, 2, 4): (x-56)*(x-44)*(x*x-380*x+23936),
}


def main():
    data = json.loads((ROOT/'orbit2-blocks.json').read_text(encoding='utf-8'))
    checks = []
    for block in data['blocks']:
        character = block['character']
        signature = (4-character.count('I'),
                     character.count('X')+character.count('Y'),
                     len(block['matrix']))
        actual = sp.Poly(sp.Matrix(block['matrix']).charpoly(x).as_expr(), x)
        expected = sp.Poly(EXPECTED[signature], x)
        checks.append(dict(character=character, signature=signature,
                           passed=actual == expected))
    (ROOT/'orbit2-charpolys.json').write_text(
        json.dumps(checks, indent=2)+'\n', encoding='utf-8')
    if len(checks) != 111 or not all(row['passed'] for row in checks):
        raise ArithmeticError('Orbit-2 characteristic-polynomial table mismatch')
    print('Independent exact characteristic-polynomial checks: 111 / 111')


if __name__ == '__main__':
    main()
