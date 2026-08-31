import MainTheory.PhysicalProjectorBridge

/-!
# The one-qubit matrices underlying `CodeEquiv.LocalMonomial`

For one physical site, `CodeEquiv.monAct` uses either a diagonal matrix or an
antidiagonal matrix.  This leaf records that exact `2 × 2` matrix and proves
from the existing `normSq = 1` hypotheses that it is an admissible
`ClassificationLevels.IsOneQubitUnitary` generator.
-/

namespace MainTheory.LocalMonomialElementary

open scoped ComplexConjugate

noncomputable section

/-- The one-site factor with output coefficients matching
`CodeEquiv.monAct`: rows are output bits and columns are input bits. -/
def monomialMatrix (flip : Bool) (al be : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if flip then
    !![0, al;
       be, 0]
  else
    !![al, 0;
       0, be]

/-- Unit-modulus nonzero entries make either the diagonal or antidiagonal
factor a genuine one-qubit unitary. -/
theorem monomialMatrix_unitary (flip : Bool) (al be : ℂ)
    (hal : Complex.normSq al = 1) (hbe : Complex.normSq be = 1) :
    MainTheory.ClassificationLevels.IsOneQubitUnitary
      (monomialMatrix flip al be) := by
  have halL : star al * al = 1 :=
    SixQubit.CodeEquiv.unit_of_normSq hal
  have halR : al * star al = 1 := by
    simpa [mul_comm] using halL
  have hbeL : star be * be = 1 :=
    SixQubit.CodeEquiv.unit_of_normSq hbe
  have hbeR : be * star be = 1 := by
    simpa [mul_comm] using hbeL
  cases flip <;>
    constructor <;>
    ext i j <;>
    fin_cases i <;>
    fin_cases j <;>
    simp [monomialMatrix, Matrix.mul_apply]
  all_goals
    first
    | change star al * al = 1
      exact halL
    | change al * star al = 1
      exact halR
    | change star be * be = 1
      exact hbeL
    | change be * star be = 1
      exact hbeR

end

end MainTheory.LocalMonomialElementary
