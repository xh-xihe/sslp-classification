import SixQubit.ParityPauliScalars

/-! # Actual logical superpositions used by the cubic moment certificate

All statements concern arbitrary complex amplitudes. KL and a physical parity
involution produce the zero expectation rows of the logical superposition;
no moment feasibility is assumed.
-/

namespace SixQubit.ParityLogicalState

open SS.MacWilliams SixQubit.ParityPauliScalars

noncomputable section

variable {n : ℕ}

def superposition (psi : Fin 2 → SS.State n ℂ) : SS.State n ℂ :=
  fun s => psi 0 s + psi 1 s

theorem mel_add (u v a b : SS.State n ℂ) (P : SS.PauliString n) :
    mel (u + v) (a + b) P =
      mel u a P + mel u b P + mel v a P + mel v b P := by
  classical
  unfold mel
  simp only [Pi.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem superposition_expansion (psi : Fin 2 → SS.State n ℂ) (P : SS.PauliString n) :
    mel (superposition psi) (superposition psi) P =
      mel (psi 0) (psi 0) P + mel (psi 0) (psi 1) P +
      mel (psi 1) (psi 0) P + mel (psi 1) (psi 1) P := mel_add _ _ _ _ _

theorem kl_mel (psi : Fin 2 → SS.State n ℂ) (P : SS.PauliString n)
    (h : SS.KLCondition psi P) :
    mel (psi 0) (psi 1) P = 0 ∧ mel (psi 1) (psi 0) P = 0 ∧
      mel (psi 0) (psi 0) P = mel (psi 1) (psi 1) P := by
  obtain ⟨c, hc⟩ := h
  have h01 := hc 0 1
  have h10 := hc 1 0
  have h00 := hc 0 0
  have h11 := hc 1 1
  simp only [innerC_eq_mel] at h01 h10 h00 h11
  norm_num at h01 h10 h00 h11
  refine ⟨?_, ?_, ?_⟩
  · exact h01
  · exact h10
  · exact mul_left_cancel₀ (SS.pauliPrefactor_ne_zero P) (h00.trans h11.symm)

theorem superposition_commuting (psi : Fin 2 → SS.State n ℂ)
    {mask : SS.BitString n} (hp : ParityPair mask psi) (P : SS.PauliString n)
    (hc : chi mask P.x = 1) :
    mel (superposition psi) (superposition psi) P = melTr psi P := by
  obtain ⟨h01, h10⟩ := offdiag_zero hp P hc
  rw [superposition_expansion, h01, h10]
  simp [melTr, Fin.sum_univ_two]

theorem superposition_twisted_kl_zero (psi : Fin 2 → SS.State n ℂ)
    {mask : SS.BitString n} (hp : ParityPair mask psi) (P : SS.PauliString n)
    (hkl : SS.KLCondition psi P) :
    mel (superposition psi) (superposition psi) ⟨P.x, SS.bxor P.z mask⟩ = 0 := by
  obtain ⟨h01, h10, hdiag⟩ := kl_mel psi P hkl
  rw [superposition_expansion]
  rw [mel_zshift (hp 0), mel_zshift (hp 1),
    mel_zshift (hp 0), mel_zshift (hp 1)]
  norm_num [logicalSign, h01, h10, hdiag]

theorem superposition_anticommuting_kl_zero (psi : Fin 2 → SS.State n ℂ)
    {mask : SS.BitString n} (hp : ParityPair mask psi) (P : SS.PauliString n)
    (hc : chi mask P.x = -1) (hkl : SS.KLCondition psi P) :
    mel (superposition psi) (superposition psi) P = 0 := by
  obtain ⟨h01, h10, _⟩ := kl_mel psi P hkl
  rw [superposition_expansion, diagonal_zero hp P hc 0,
    diagonal_zero hp P hc 1, h01, h10]
  simp

theorem superposition_trace_zero (psi : Fin 2 → SS.State n ℂ)
    {mask : SS.BitString n} (hp : ParityPair mask psi) (P : SS.PauliString n)
    (hc : chi mask P.x = 1) (hz : trProj psi P = 0) :
    mel (superposition psi) (superposition psi) P = 0 := by
  rw [superposition_commuting psi hp P hc]
  rw [trProj_eq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (SS.pauliPrefactor_ne_zero P)

end
end SixQubit.ParityLogicalState
