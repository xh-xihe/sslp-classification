import SixQubit.Generated.Orbit2Spectra.All

/-! The counts and dimensions of the seven SI spectral patterns. -/
namespace MainTheory.Orbit2SpectralTable

open SixQubit.Generated.Orbit2Spectra
open scoped BigOperators

def sizes : Fin 7 → ℕ := ![24, 3, 3, 4, 8, 12, 4]
def counts : Fin 7 → ℕ := ![1, 4, 24, 48, 6, 4, 24]

theorem counts_correct : ∀ p : Fin 7,
    (Finset.univ.filter fun i : Fin 111 => pattern i = p).card = counts p := by decide +kernel

theorem number_of_blocks : (∑ p : Fin 7, counts p) = 111 := by decide +kernel

theorem number_of_coordinates : (∑ p : Fin 7, counts p * sizes p) = 492 := by decide +kernel

theorem all_polynomials (i : Fin 111) : characteristicPolynomials i = tablePolynomials (pattern i) :=
  all_characteristic_polynomials i

end MainTheory.Orbit2SpectralTable
