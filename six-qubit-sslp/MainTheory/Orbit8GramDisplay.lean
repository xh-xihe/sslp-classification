import SixQubit.Orbit8RaisingGram

set_option autoImplicit false

namespace MainTheory.Orbit8GramDisplay

open SixQubit.Orbit8Universal SixQubit.Orbit8RaisingGram

theorem normal_matrix (ud : Fin 6 → ℂ) :
    normalMatrix ud=(1/2 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)-
      (6 : ℂ) • Matrix.diagonal (fun i => (Complex.normSq (ud i) : ℂ))+
      (3 : ℂ) • (show Matrix (Fin 6) (Fin 6) ℂ from fun i j => ud i*star (ud j)) := by
  ext i j
  by_cases hij : i=j <;> simp [normalMatrix,hij] <;> ring

theorem raising_gram (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    raisingGram c=(1/2 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)-
      (6 : ℂ) • Matrix.diagonal (fun i => (p d i : ℂ))+
      (3 : ℂ) • (show Matrix (Fin 6) (Fin 6) ℂ from fun i j => u d i*star (u d j)) := by
  rw [raisingGram_eq_normalMatrix c d hc hd hnc hnd hcode]
  exact normal_matrix (u d)

end MainTheory.Orbit8GramDisplay
