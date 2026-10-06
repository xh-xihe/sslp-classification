import Mathlib

import SixQubit.BEnumerator
import SixQubit.Orbit45A2
import SixQubit.Pin

/-!
# Orbit 45: exact shadow saturation and the complete enumerator family

This module closes the arbitrary-code converse.  Its spin-flip calculation is
performed on the complete ten-point fibres; no phase ansatz is assumed.
-/

namespace SixQubit.Orbit45Family

open scoped BigOperators ComplexConjugate
open SixQubit.Realize
open SixQubit.Orbit45Support
open SixQubit.Orbit45Phase
open SixQubit.Orbit45Universal
open SS.MacWilliams

noncomputable section

set_option maxRecDepth 20000

structure BlockDeterminants (c d : SS.BitString 6 → ℂ) : Prop where
  block1 : c x0 * d y1 - c x1 * d y0 = 0
  block2 : c x2 * d y3 - c x3 * d y2 = 0
  block3 : c x4 * d y5 - c x5 * d y4 = 0
  block4 : c x6 * d y7 - c x7 * d y6 = 0
  block5 : c x8 * d y9 - c x9 * d y8 = 0

/-- The five complementary two-by-two determinants vanish, with zero entries
handled by the division-free Gram lemma. -/
theorem block_determinants (c d : SS.BitString 6 → ℂ)
    (g1 g2 g3 : ℝ) (hb : BlockMasses c d g1 g2 g3)
    (hp : PhaseRelations c d) : BlockDeterminants c d := by
  refine ⟨
    SixQubit.Orbit45Gram.det_zero_of_balanced _ _ _ _
      (hb.block1.1.trans hb.block1.2.1.symm) hp.block1,
    SixQubit.Orbit45Gram.det_zero_of_balanced _ _ _ _
      (hb.block2.1.trans hb.block2.2.1.symm) hp.block2.symm,
    SixQubit.Orbit45Gram.det_zero_of_balanced _ _ _ _
      (hb.block3.1.trans hb.block3.2.1.symm) hp.block3,
    SixQubit.Orbit45Gram.det_zero_of_balanced _ _ _ _
      (hb.block4.1.trans hb.block4.2.1.symm) hp.block4.symm,
    SixQubit.Orbit45Gram.det_zero_of_balanced _ _ _ _
      (hb.block5.1.trans hb.block5.2.1.symm) hp.block5⟩

private def flip55 : SS.BitString 6 := nbit 55

private theorem psign_flip55 : SS.Shadow.psign flip55 = -1 := by
  simp [SS.Shadow.psign, SS.MacWilliams.chi, SS.ones, flip55, nbit,
    Fin.prod_univ_succ,
    show Nat.testBit 55 0 = true from by decide,
    show Nat.testBit 55 1 = true from by decide,
    show Nat.testBit 55 2 = true from by decide,
    show Nat.testBit 55 3 = false from by decide,
    show Nat.testBit 55 4 = true from by decide,
    show Nat.testBit 55 5 = true from by decide]

private theorem psign_x1 : SS.Shadow.psign x1 = -SS.Shadow.psign x0 := by
  rw [show x1 = SS.bxor x0 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_x3 : SS.Shadow.psign x3 = -SS.Shadow.psign x2 := by
  rw [show x3 = SS.bxor x2 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_x5 : SS.Shadow.psign x5 = -SS.Shadow.psign x4 := by
  rw [show x5 = SS.bxor x4 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_x7 : SS.Shadow.psign x7 = -SS.Shadow.psign x6 := by
  rw [show x7 = SS.bxor x6 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_x9 : SS.Shadow.psign x9 = -SS.Shadow.psign x8 := by
  rw [show x9 = SS.bxor x8 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_y1 : SS.Shadow.psign y1 = -SS.Shadow.psign y0 := by
  rw [show y1 = SS.bxor y0 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_y3 : SS.Shadow.psign y3 = -SS.Shadow.psign y2 := by
  rw [show y3 = SS.bxor y2 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_y5 : SS.Shadow.psign y5 = -SS.Shadow.psign y4 := by
  rw [show y5 = SS.bxor y4 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_y7 : SS.Shadow.psign y7 = -SS.Shadow.psign y6 := by
  rw [show y7 = SS.bxor y6 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem psign_y9 : SS.Shadow.psign y9 = -SS.Shadow.psign y8 := by
  rw [show y9 = SS.bxor y8 flip55 from by decide,
    SS.Shadow.psign_bxor, psign_flip55]
  ring

private theorem Tf_zero_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) :
    SS.Shadow.Tf ![c,d] 0 0 = 0 := by
  have hsum :
      (∑ u ∈ S0, ((SS.Shadow.psign u : ℝ) : ℂ) * c u *
        c (SS.complement u)) =
      ∑ u, ((SS.Shadow.psign u : ℝ) : ℂ) * c u *
        c (SS.complement u) := by
    apply Finset.sum_subset (Finset.subset_univ S0)
    intro u _ hu
    rw [hc u hu]
    ring
  rw [SS.Shadow.Tf]
  simp only [SixQubit.pair_zero]
  rw [← hsum]
  unfold S0
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show SS.complement x0 = y1 from by decide,
    show SS.complement x1 = y0 from by decide,
    show SS.complement x2 = y3 from by decide,
    show SS.complement x3 = y2 from by decide,
    show SS.complement x4 = y5 from by decide,
    show SS.complement x5 = y4 from by decide,
    show SS.complement x6 = y7 from by decide,
    show SS.complement x7 = y6 from by decide,
    show SS.complement x8 = y9 from by decide,
    show SS.complement x9 = y8 from by decide]
  simp [hc y0 (by decide), hc y1 (by decide), hc y2 (by decide),
    hc y3 (by decide), hc y4 (by decide), hc y5 (by decide),
    hc y6 (by decide), hc y7 (by decide), hc y8 (by decide),
    hc y9 (by decide)]

private theorem Tf_one_one (c d : SS.BitString 6 → ℂ)
    (hd : ∀ y, y ∉ S1 → d y = 0) :
    SS.Shadow.Tf ![c,d] 1 1 = 0 := by
  have hsum :
      (∑ u ∈ S1, ((SS.Shadow.psign u : ℝ) : ℂ) * d u *
        d (SS.complement u)) =
      ∑ u, ((SS.Shadow.psign u : ℝ) : ℂ) * d u *
        d (SS.complement u) := by
    apply Finset.sum_subset (Finset.subset_univ S1)
    intro u _ hu
    rw [hd u hu]
    ring
  rw [SS.Shadow.Tf]
  simp only [SixQubit.pair_one]
  rw [← hsum]
  unfold S1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show SS.complement y0 = x1 from by decide,
    show SS.complement y1 = x0 from by decide,
    show SS.complement y2 = x3 from by decide,
    show SS.complement y3 = x2 from by decide,
    show SS.complement y4 = x5 from by decide,
    show SS.complement y5 = x4 from by decide,
    show SS.complement y6 = x7 from by decide,
    show SS.complement y7 = x6 from by decide,
    show SS.complement y8 = x9 from by decide,
    show SS.complement y9 = x8 from by decide]
  simp [hd x0 (by decide), hd x1 (by decide), hd x2 (by decide),
    hd x3 (by decide), hd x4 (by decide), hd x5 (by decide),
    hd x6 (by decide), hd x7 (by decide), hd x8 (by decide),
    hd x9 (by decide)]

private theorem Tf_zero_one_expansion (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) :
    SS.Shadow.Tf ![c,d] 0 1 =
      ((SS.Shadow.psign x0 : ℝ) : ℂ) * (c x0 * d y1 - c x1 * d y0) +
      ((SS.Shadow.psign x2 : ℝ) : ℂ) * (c x2 * d y3 - c x3 * d y2) +
      ((SS.Shadow.psign x4 : ℝ) : ℂ) * (c x4 * d y5 - c x5 * d y4) +
      ((SS.Shadow.psign x6 : ℝ) : ℂ) * (c x6 * d y7 - c x7 * d y6) +
      ((SS.Shadow.psign x8 : ℝ) : ℂ) * (c x8 * d y9 - c x9 * d y8) := by
  have hsum :
      (∑ u ∈ S0, ((SS.Shadow.psign u : ℝ) : ℂ) * c u *
        d (SS.complement u)) =
      ∑ u, ((SS.Shadow.psign u : ℝ) : ℂ) * c u *
        d (SS.complement u) := by
    apply Finset.sum_subset (Finset.subset_univ S0)
    intro u _ hu
    rw [hc u hu]
    ring
  rw [SS.Shadow.Tf]
  simp only [SixQubit.pair_zero, SixQubit.pair_one]
  rw [← hsum]
  unfold S0
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show SS.complement x0 = y1 from by decide,
    show SS.complement x1 = y0 from by decide,
    show SS.complement x2 = y3 from by decide,
    show SS.complement x3 = y2 from by decide,
    show SS.complement x4 = y5 from by decide,
    show SS.complement x5 = y4 from by decide,
    show SS.complement x6 = y7 from by decide,
    show SS.complement x7 = y6 from by decide,
    show SS.complement x8 = y9 from by decide,
    show SS.complement x9 = y8 from by decide,
    psign_x1, psign_x3, psign_x5, psign_x7, psign_x9]
  push_cast
  ring

private theorem Tf_one_zero_expansion (c d : SS.BitString 6 → ℂ)
    (hd : ∀ y, y ∉ S1 → d y = 0) :
    SS.Shadow.Tf ![c,d] 1 0 =
      ((SS.Shadow.psign y1 : ℝ) : ℂ) * (c x0 * d y1 - c x1 * d y0) +
      ((SS.Shadow.psign y3 : ℝ) : ℂ) * (c x2 * d y3 - c x3 * d y2) +
      ((SS.Shadow.psign y5 : ℝ) : ℂ) * (c x4 * d y5 - c x5 * d y4) +
      ((SS.Shadow.psign y7 : ℝ) : ℂ) * (c x6 * d y7 - c x7 * d y6) +
      ((SS.Shadow.psign y9 : ℝ) : ℂ) * (c x8 * d y9 - c x9 * d y8) := by
  have hsum :
      (∑ u ∈ S1, ((SS.Shadow.psign u : ℝ) : ℂ) * d u *
        c (SS.complement u)) =
      ∑ u, ((SS.Shadow.psign u : ℝ) : ℂ) * d u *
        c (SS.complement u) := by
    apply Finset.sum_subset (Finset.subset_univ S1)
    intro u _ hu
    rw [hd u hu]
    ring
  rw [SS.Shadow.Tf]
  simp only [SixQubit.pair_zero, SixQubit.pair_one]
  rw [← hsum]
  unfold S1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show SS.complement y0 = x1 from by decide,
    show SS.complement y1 = x0 from by decide,
    show SS.complement y2 = x3 from by decide,
    show SS.complement y3 = x2 from by decide,
    show SS.complement y4 = x5 from by decide,
    show SS.complement y5 = x4 from by decide,
    show SS.complement y6 = x7 from by decide,
    show SS.complement y7 = x6 from by decide,
    show SS.complement y8 = x9 from by decide,
    show SS.complement y9 = x8 from by decide,
    psign_y1, psign_y3, psign_y5, psign_y7, psign_y9]
  push_cast
  ring

/-- Every entry of the exact spin-flip matrix vanishes. -/
theorem Tf_all_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdet : BlockDeterminants c d) :
    ∀ a b, SS.Shadow.Tf ![c,d] a b = 0 := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact Tf_zero_zero c d hc
  · change SS.Shadow.Tf ![c,d] 0 1 = 0
    rw [Tf_zero_one_expansion c d hc, hdet.block1, hdet.block2,
      hdet.block3, hdet.block4, hdet.block5]
    ring
  · change SS.Shadow.Tf ![c,d] 1 0 = 0
    rw [Tf_one_zero_expansion c d hd, hdet.block1, hdet.block2,
      hdet.block3, hdet.block4, hdet.block5]
    ring
  · exact Tf_one_one c d hd

/-- Equality case of the six-qubit shadow inequality, derived directly from
the kernel identity `core = sum |Tf|^2`. -/
theorem shadow_saturated (psi : Fin 2 → SS.State 6 ℂ)
    (hdist : SS.HasDistance psi 3) (hA0 : Aco psi 0 = 4)
    (hTf : ∀ a b, SS.Shadow.Tf psi a b = 0) :
    Aco psi 1 + Aco psi 2 + Aco psi 3 = 4 := by
  have hcore : SS.Shadow.core psi = 0 := by
    rw [SS.Shadow.core_eq_sum_normSq]
    simp_rw [hTf]
    simp
  have haltC := SS.Shadow.alt_sum_eq_core psi
  rw [hcore, mul_zero] at haltC
  have halt :
      ∑ P : SS.PauliString 6,
        ((-1 : ℝ)) ^ P.wt * Complex.normSq (trProj psi P) = 0 := by
    have hcast :
        ((↑(∑ P : SS.PauliString 6,
          ((-1 : ℝ)) ^ P.wt * Complex.normSq (trProj psi P)) : ℂ) = 0) := by
      push_cast
      push_cast at haltC
      exact haltC
    exact Complex.ofReal_inj.mp hcast
  rw [SS.Shadow.alt_sum_as_Aco] at halt
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, one_mul] at halt
  norm_num at halt
  obtain ⟨h4,h5,h6⟩ := macwilliams_six psi hdist hA0
  rw [h4,h5,h6,hA0] at halt
  linarith

/-! ## The weight-one coefficient -/

private theorem bottom_mass_one (c d : SS.BitString 6 → ℂ)
    (g1 g2 g3 : ℝ) (hb : BlockMasses c d g1 g2 g3) :
    SixQubit.massOn S0 c = 1 := by
  rw [mass_bottom, hb.block1.1, hb.block1.2.1,
    hb.block2.1, hb.block2.2.1, hb.block3.1, hb.block3.2.1,
    hb.block4.1, hb.block4.2.1, hb.block5.1, hb.block5.2.1]
  linarith [hb.moving_sum]

private theorem bottom_occ_half (c d : SS.BitString 6 → ℂ)
    (g1 g2 g3 : ℝ) (hb : BlockMasses c d g1 g2 g3) :
    ∀ i : Fin 6, SixQubit.occOn S0 c i = 1/2 := by
  intro i
  fin_cases i
  · change SixQubit.occOn S0 c (0 : Fin 6) = 1/2
    rw [occ_bottom0, hb.block1.2.1, hb.block2.2.1,
      hb.block3.2.1, hb.block4.2.1, hb.block5.2.1]
    linarith [hb.moving_sum]
  · change SixQubit.occOn S0 c (1 : Fin 6) = 1/2
    rw [occ_bottom1, hb.block1.2.1, hb.block2.2.1,
      hb.block3.2.1, hb.block4.1, hb.block5.1]
    linarith [hb.moving_sum]
  · change SixQubit.occOn S0 c (2 : Fin 6) = 1/2
    rw [occ_bottom2, hb.block1.2.1, hb.block2.1,
      hb.block3.1, hb.block4.2.1, hb.block5.1]
    linarith [hb.moving_sum]
  · change SixQubit.occOn S0 c (3 : Fin 6) = 1/2
    rw [occ_bottom3, hb.block4.1, hb.block4.2.1,
      hb.block5.1, hb.block5.2.1]
    norm_num
  · change SixQubit.occOn S0 c (4 : Fin 6) = 1/2
    rw [occ_bottom4, hb.block1.2.1, hb.block2.2.1,
      hb.block3.1, hb.block4.1, hb.block5.2.1]
    linarith [hb.moving_sum]
  · change SixQubit.occOn S0 c (5 : Fin 6) = 1/2
    rw [occ_bottom5, hb.block1.2.1, hb.block2.1,
      hb.block3.2.1, hb.block4.1, hb.block5.2.1]
    linarith [hb.moving_sum]

private theorem diagOn_zero_eq_charOn (c : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (z : SS.BitString 6) :
    SixQubit.diagOn S0 c (fun _ => false) z =
      ((SixQubit.charOn S0 c z : ℝ) : ℂ) := by
  have h := SixQubit.innerC_pureZ_eq_charOn S0 c hc z
  rw [SixQubit.innerC_eq_diagOn S0 c hc,
    SixQubit.numY_of_x_zero, pow_zero, one_mul] at h
  exact h

private theorem diagOn_stdBasis_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (g1 g2 g3 : ℝ) (hb : BlockMasses c d g1 g2 g3)
    (i : Fin 6) :
    SixQubit.diagOn S0 c Orbit45A2.e00 (SS.stdBasis i) = 0 := by
  rw [show Orbit45A2.e00 = (fun _ => false) from by decide,
    diagOn_zero_eq_charOn c hc,
    SixQubit.charOn_stdBasis,
    bottom_mass_one c d g1 g2 g3 hb,
    bottom_occ_half c d g1 g2 g3 hb]
  norm_num

private def zOne : Finset (SS.BitString 6) :=
  {nbit 1,nbit 2,nbit 4,nbit 8,nbit 16,nbit 32}

private theorem pure_weight_one_mem :
    ∀ z : SS.BitString 6,
      (⟨Orbit45A2.e00,z⟩ : SS.PauliString 6).wt = 1 → z ∈ zOne := by decide

private theorem diagOn_pure_weight_one_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (g1 g2 g3 : ℝ) (hb : BlockMasses c d g1 g2 g3)
    (z : SS.BitString 6) (hz : z ∈ zOne) :
    SixQubit.diagOn S0 c Orbit45A2.e00 z = 0 := by
  simp only [zOne, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [show nbit 1 = SS.stdBasis (0 : Fin 6) from by decide] using
      diagOn_stdBasis_zero c d hc g1 g2 g3 hb 0
  · simpa [show nbit 2 = SS.stdBasis (1 : Fin 6) from by decide] using
      diagOn_stdBasis_zero c d hc g1 g2 g3 hb 1
  · simpa [show nbit 4 = SS.stdBasis (2 : Fin 6) from by decide] using
      diagOn_stdBasis_zero c d hc g1 g2 g3 hb 2
  · simpa [show nbit 8 = SS.stdBasis (3 : Fin 6) from by decide] using
      diagOn_stdBasis_zero c d hc g1 g2 g3 hb 3
  · simpa [show nbit 16 = SS.stdBasis (4 : Fin 6) from by decide] using
      diagOn_stdBasis_zero c d hc g1 g2 g3 hb 4
  · simpa [show nbit 32 = SS.stdBasis (5 : Fin 6) from by decide] using
      diagOn_stdBasis_zero c d hc g1 g2 g3 hb 5

private theorem weight_one_nonzero_x_not_live :
    ∀ P : SS.PauliString 6, P.wt = 1 → P.x ≠ Orbit45A2.e00 →
      P.x ∉ Orbit45A2.liveX := by
  intro P hw hx hmem
  have hxw := Orbit45A2.hammingWt_x_le_wt P
  simp only [Orbit45A2.liveX, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h0 | h03 | h20 | h36 | h48
  · exact hx h0
  · rw [h03] at hxw
    have : SS.hammingWt Orbit45A2.e03 = 2 := by decide
    omega
  · rw [h20] at hxw
    have : SS.hammingWt Orbit45A2.e20 = 2 := by decide
    omega
  · rw [h36] at hxw
    have : SS.hammingWt Orbit45A2.e36 = 2 := by decide
    omega
  · rw [h48] at hxw
    have : SS.hammingWt Orbit45A2.e48 = 2 := by decide
    omega

/-- Every weight-one projector trace vanishes.  Nonzero flips have no edge in
the full fibre; pure-Z rows vanish because every one-coordinate occupation is
exactly one half. -/
theorem trProj_weight_one_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3)
    (g1 g2 g3 : ℝ) (hb : BlockMasses c d g1 g2 g3)
    (P : SS.PauliString 6) (hw : P.wt = 1) :
    trProj ![c,d] P = 0 := by
  rw [Orbit45A2.trProj_eq_two_diagOn c d hc hd hdist P (by omega)]
  by_cases he : P.x = Orbit45A2.e00
  · have hpure : (⟨Orbit45A2.e00,P.z⟩ : SS.PauliString 6).wt = 1 := by
      rw [← he]
      exact hw
    rw [he, diagOn_pure_weight_one_zero c d hc g1 g2 g3 hb P.z
      (pure_weight_one_mem P.z hpure)]
    ring
  · rw [Orbit45A2.diagOn_eq_zero_of_not_live c P.x P.z
      (le_trans (Orbit45A2.hammingWt_x_le_wt P) (by omega))
      (weight_one_nonzero_x_not_live P hw he)]
    ring

theorem Aco_one_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3)
    (g1 g2 g3 : ℝ) (hb : BlockMasses c d g1 g2 g3) :
    Aco ![c,d] 1 = 0 := by
  rw [Aco]
  apply Finset.sum_eq_zero
  intro P hP
  rw [trProj_weight_one_zero c d hc hd hdist g1 g2 g3 hb P
      (Finset.mem_filter.mp hP).2,
    Complex.normSq_zero]

/-! ## Complete A/B enumerator image -/

def IsFamilyA (psi : Fin 2 → SS.State 6 ℂ) (t : ℝ) : Prop :=
  Aco psi 0 = 4 ∧ Aco psi 1 = 0 ∧ Aco psi 2 = 4*t ∧
    Aco psi 3 = 4*(1-t) ∧ Aco psi 4 = 4*(12-t) ∧
    Aco psi 5 = 4*(15+t) ∧ Aco psi 6 = 12

def IsFamilyB (psi : Fin 2 → SS.State 6 ℂ) (t : ℝ) : Prop :=
  Bco psi 0 = 4 ∧ Bco psi 1 = 0 ∧ Bco psi 2 = 4*t ∧
    Bco psi 3 = 4*(22+2*t) ∧ Bco psi 4 = 4*(39-4*t) ∧
    Bco psi 5 = 4*(42-2*t) ∧ Bco psi 6 = 4*(24+3*t)

/-- **Arbitrary-code orbit-45 converse.**  Any normalized distance-three code
on the complete two fibres has exactly the manuscript's A and B enumerators,
with the genuine code parameter in `[2/3,1]`. -/
theorem universal_family (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    ∃ t : ℝ, (2/3 : ℝ) ≤ t ∧ t ≤ 1 ∧
      IsFamilyA ![c,d] t ∧ IsFamilyB ![c,d] t := by
  obtain ⟨g1,g2,g3,r1,r2,r3,t,hcv⟩ :=
    SixQubit.Orbit45Universal.universal_converse c d hc hd hnc hnd hdist
  have hp := phase_relations c d hc hd hdist
  have hA2raw := Orbit45A2.Aco_two_value c d g1 g2 g3 hc hd hdist hcv.blocks hp
  have hA2 : Aco ![c,d] 2 = 4*t := by
    rw [hA2raw, hcv.t_mass]
    ring
  have hA1 := Aco_one_zero c d hc hd hdist g1 g2 g3 hcv.blocks
  have hdet := block_determinants c d g1 g2 g3 hcv.blocks hp
  have hTf := Tf_all_zero c d hc hd hdet
  have hnorm : ∀ k, SS.innerC (![c,d] k) (![c,d] k) = 1 := by
    intro k
    fin_cases k
    · exact hnc
    · exact hnd
  have hA0 := SixQubit.Pin.Aco_zero ![c,d] hnorm
  have hsat := shadow_saturated ![c,d] hdist hA0 hTf
  have hA3 : Aco ![c,d] 3 = 4*(1-t) := by
    linarith
  obtain ⟨hA4,hA5,hA6⟩ := macwilliams_six ![c,d] hdist hA0
  have hfA : IsFamilyA ![c,d] t := by
    dsimp only [IsFamilyA]
    refine ⟨hA0,hA1,hA2,hA3,?_,?_,?_⟩ <;> linarith
  rcases SS.MacWilliams.bco_transform_six ![c,d] with
    ⟨hB0,hB1,hB2,hB3,hB4,hB5,hB6⟩
  have hfB : IsFamilyB ![c,d] t := by
    dsimp only [IsFamilyB]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
  exact ⟨t,hcv.lower,hcv.upper,hfA,hfB⟩

end

end SixQubit.Orbit45Family
