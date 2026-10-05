import SixQubit.Generated.SpectatorCubicTwirl.Data

/-! Literal complex Cliffords and their Gaussian three-copy factors. -/

namespace MainTheory.SpectatorCubicTwirlFactorization
noncomputable section
open MainTheory.ThreeCopyPermutationCommutant
open SixQubit.Generated.SpectatorCubicTwirl
open SixQubit.Generated.SpectatorClifford
open Orbit2.TensorPauli
open scoped BigOperators
set_option maxHeartbeats 4000000

def scalar (g : Fin 24) : ℂ := (denominator g : ℂ)⁻¹

theorem clifford_factorization (g : Fin 24) :
    clifford g=scalar g • (SixQubit.Generated.SpectatorCubicTwirl.localG g).map
      GaussianInt.toComplex := by
  fin_cases g <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [clifford, scalar, denominator,
      SixQubit.Generated.SpectatorCubicTwirl.localG,
      C00,C01,C02,C03,C04,C05,C06,C07,C08,C09,C10,C11,
      C12,C13,C14,C15,C16,C17,C18,C19,C20,C21,C22,C23,
      Matrix.smul_apply, Matrix.map_apply, GaussianInt.toComplex_def] <;> ring

theorem scalar_weight (g : Fin 24) :
    scalar g^3*star (scalar g^3)=(weight g : ℂ)/64 := by
  fin_cases g <;> norm_num [scalar, denominator, weight]

theorem gaussian_copies (g : Fin 24) (x y : Triple) :
    copies ((SixQubit.Generated.SpectatorCubicTwirl.localG g).map
      GaussianInt.toComplex) x y=GaussianInt.toComplex (gaussianCopies g x y) := by
  simp only [copies, tensor, Matrix.map_apply, gaussianCopies, map_prod]

theorem copies_factorization (g : Fin 24) (x y : Triple) :
    copies (clifford g) x y=scalar g^3*GaussianInt.toComplex (gaussianCopies g x y) := by
  rw [clifford_factorization]
  unfold copies
  rw [tensor_smul]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Matrix.smul_apply, smul_eq_mul]
  rw [← gaussian_copies]
  rfl

theorem balanced_factorization (g : Fin 24) (x z a b : Triple) :
    copies (clifford g) x a*star (copies (clifford g) z b)=
      (1/64 : ℂ)*GaussianInt.toComplex
        ((weight g : GaussianInt)*gaussianCopies g x a*star (gaussianCopies g z b)) := by
  rw [copies_factorization, copies_factorization, star_mul]
  rw [show scalar g^3*GaussianInt.toComplex (gaussianCopies g x a)*
      (star (GaussianInt.toComplex (gaussianCopies g z b))*star (scalar g^3))=
      (scalar g^3*star (scalar g^3))*
        (GaussianInt.toComplex (gaussianCopies g x a)*
          star (GaussianInt.toComplex (gaussianCopies g z b))) by ring]
  rw [scalar_weight]
  simp only [map_mul, map_intCast, GaussianInt.toComplex_star, Complex.star_def]
  ring

end
end MainTheory.SpectatorCubicTwirlFactorization
