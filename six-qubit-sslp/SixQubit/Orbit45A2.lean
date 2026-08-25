import Mathlib

import SixQubit.MacWilliams
import SixQubit.Orbit45Phase
import SixQubit.Orbit45Universal

/-!
# Orbit 45: identifying the Gram parameter with `A_2`

The preceding module obtains a parameter in `[2/3,1]`.  Here the finite
same-fibre calculation identifies it with the normalized Shor--Laflamme
coefficient `Aco 2 / 4`.
-/

namespace SixQubit.Orbit45A2

open scoped BigOperators ComplexConjugate
open SixQubit.Realize
open SixQubit.Orbit45Support
open SixQubit.Orbit45Phase
open SS.MacWilliams

noncomputable section

private theorem nonzero_of_normSq_eq_eighth {z : ℂ}
    (h : Complex.normSq z = 1/8) : z ≠ 0 := by
  intro hz
  rw [hz, Complex.normSq_zero] at h
  norm_num at h

/-- The connector rows force the two bilinear frame sums to vanish.  This is
the only phase input needed by the weight-two frame-potential calculation. -/
theorem bilinear_sums_zero (c d : SS.BitString 6 → ℂ)
    (g1 g2 g3 : ℝ)
    (hb : SixQubit.Orbit45Universal.BlockMasses c d g1 g2 g3)
    (hp : PhaseRelations c d) :
    c x0 * c x1 + c x2 * c x3 + c x4 * c x5 = 0 ∧
      c x6 * c x7 + c x8 * c x9 = 0 := by
  have hprod : d y6 *
      (star (c x0) * star (c x1) + star (c x2) * star (c x3) +
        star (c x4) * star (c x5)) = 0 := by
    linear_combination
      star (c x0) * hp.e41 + star (c x2) * hp.e42 +
      star (c x4) * hp.e43 - star (c x7) * hp.triangle
  have hy6 : d y6 ≠ 0 := nonzero_of_normSq_eq_eighth hb.block4.2.2.1
  have hstar123 :
      star (c x0) * star (c x1) + star (c x2) * star (c x3) +
        star (c x4) * star (c x5) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hy6
  have ht123 : c x0 * c x1 + c x2 * c x3 + c x4 * c x5 = 0 := by
    have h := congrArg star hstar123
    simp only [star_add, star_mul', star_star, star_zero] at h
    linear_combination h
  have he41 := hp.e41
  have he42 := hp.e42
  have he43 := hp.e43
  have he51 := hp.e51
  have he52 := hp.e52
  have he53 := hp.e53
  simp only [Complex.star_def] at he41 he42 he43 he51 he52 he53
  let Q : ℂ := conj (c x8) * d y6 - conj (c x7) * d y9
  have hQprod :
      (conj (c x1) * c x1 + conj (c x3) * c x3 + conj (c x5) * c x5) * Q = 0 := by
    dsimp [Q]
    linear_combination
      c x1 * (conj (c x8) * he41 - conj (c x7) * he51) +
      c x3 * (conj (c x8) * he42 - conj (c x7) * he52) +
      c x5 * (conj (c x8) * he43 - conj (c x7) * he53)
  have hcoef :
      conj (c x1) * c x1 + conj (c x3) * c x3 + conj (c x5) * c x5 =
        (1/4 : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self,
      ← Complex.normSq_eq_conj_mul_self,
      ← Complex.normSq_eq_conj_mul_self]
    rw [hb.block1.2.1, hb.block2.2.1, hb.block3.2.1]
    have hr : g1/4 + g2/4 + g3/4 = (1/4 : ℝ) := by
      linarith [hb.moving_sum]
    calc
      ((g1/4 : ℝ) : ℂ) + ((g2/4 : ℝ) : ℂ) + ((g3/4 : ℝ) : ℂ) =
          ((g1/4 + g2/4 + g3/4 : ℝ) : ℂ) := by push_cast; ring
      _ = (((1/4 : ℝ) : ℂ)) := by rw [hr]
      _ = (1/4 : ℂ) := by norm_num
  have hQ : Q = 0 := by
    rw [hcoef] at hQprod
    exact (mul_eq_zero.mp hQprod).resolve_left (by norm_num)
  have hR : conj (c x6) * d y6 + conj (c x9) * d y9 = 0 := by
    have h := hp.fixed
    rw [hp.block4, hp.block5] at h
    simp only [Complex.star_def] at h
    exact h
  have hprod45 : d y6 *
      (conj (c x6) * conj (c x7) + conj (c x8) * conj (c x9)) = 0 := by
    dsimp [Q] at hQ
    linear_combination conj (c x7) * hR + conj (c x9) * hQ
  have hstar45 :
      conj (c x6) * conj (c x7) + conj (c x8) * conj (c x9) = 0 :=
    (mul_eq_zero.mp hprod45).resolve_left hy6
  have ht45 : c x6 * c x7 + c x8 * c x9 = 0 := by
    have h := congrArg conj hstar45
    simp only [map_add, map_mul, map_zero, Complex.conj_conj] at h
    linear_combination h
  exact ⟨ht123,ht45⟩

def e00 : SS.BitString 6 := nbit 0
def e03 : SS.BitString 6 := nbit 3
def e20 : SS.BitString 6 := nbit 20
def e36 : SS.BitString 6 := nbit 36
def e48 : SS.BitString 6 := nbit 48

def liveX : Finset (SS.BitString 6) := {e00,e03,e20,e36,e48}

/-- Kernel-checked classification of all same-fibre flip masks. -/
theorem incidence_empty_of_not_live :
    ∀ e : SS.BitString 6, SS.hammingWt e ≤ 2 → e ∉ liveX →
      S0.filter (fun s => SS.bxor s e ∈ S0) = ∅ := by decide

theorem hammingWt_x_le_wt (P : SS.PauliString 6) :
    SS.hammingWt P.x ≤ P.wt := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [hi]
  rfl

theorem diagOn_eq_zero_of_not_live (c : SS.BitString 6 → ℂ)
    (e z : SS.BitString 6) (hwt : SS.hammingWt e ≤ 2) (he : e ∉ liveX) :
    SixQubit.diagOn S0 c e z = 0 := by
  unfold SixQubit.diagOn
  rw [incidence_empty_of_not_live e hwt he]
  simp

/-- For a low-weight Pauli, the KL equality makes the projector trace twice
the bottom diagonal matrix element. -/
theorem trProj_eq_two_diagOn (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3) (P : SS.PauliString 6)
    (hw : P.wt ≤ 2) :
    trProj ![c,d] P =
      2 * (Complex.I ^ P.numY * SixQubit.diagOn S0 c P.x P.z) := by
  have heq := SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
    P.x P.z hw
  rw [trProj, Fin.sum_univ_two, SixQubit.pair_zero, SixQubit.pair_one,
    SixQubit.innerC_eq_diagOn S0 c hc,
    SixQubit.innerC_eq_diagOn S1 d hd, heq]
  ring

private theorem normSq_two_prefactor (k : ℕ) (z : ℂ) :
    Complex.normSq (2 * (Complex.I ^ k * z)) = 4 * Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_mul, map_pow, Complex.normSq_I]
  norm_num [Complex.normSq_apply]

theorem normSq_trProj_eq_four_diagOn (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3) (P : SS.PauliString 6)
    (hw : P.wt ≤ 2) :
    Complex.normSq (trProj ![c,d] P) =
      4 * Complex.normSq (SixQubit.diagOn S0 c P.x P.z) := by
  rw [trProj_eq_two_diagOn c d hc hd hdist P hw,
    normSq_two_prefactor]

/-- The weight-two coefficient as an exact double bitstring sum. -/
theorem Aco_two_double_sum (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    Aco ![c,d] 2 =
      ∑ e : SS.BitString 6, ∑ z : SS.BitString 6,
        if (⟨e,z⟩ : SS.PauliString 6).wt = 2 then
          4 * Complex.normSq (SixQubit.diagOn S0 c e z) else 0 := by
  rw [Aco, Finset.sum_filter, sum_pauli]
  refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun z _ => ?_))
  by_cases hw : (⟨e,z⟩ : SS.PauliString 6).wt = 2
  · simpa [hw] using
      normSq_trProj_eq_four_diagOn c d hc hd hdist ⟨e,z⟩ (by omega)
  · simp [hw]

def zPure : Finset (SS.BitString 6) :=
  {nbit 3,nbit 5,nbit 6,nbit 9,nbit 10,nbit 12,nbit 17,nbit 18,
    nbit 20,nbit 24,nbit 33,nbit 34,nbit 36,nbit 40,nbit 48}

def z03 : Finset (SS.BitString 6) := {nbit 0,nbit 1,nbit 2,nbit 3}
def z20 : Finset (SS.BitString 6) := {nbit 0,nbit 4,nbit 16,nbit 20}
def z36 : Finset (SS.BitString 6) := {nbit 0,nbit 4,nbit 32,nbit 36}
def z48 : Finset (SS.BitString 6) := {nbit 0,nbit 16,nbit 32,nbit 48}

def dressingSum (c : SS.BitString 6 → ℂ)
    (e : SS.BitString 6) (Z : Finset (SS.BitString 6)) : ℝ :=
  ∑ z ∈ Z, Complex.normSq (SixQubit.diagOn S0 c e z)

private theorem inner_sum_eq (c : SS.BitString 6 → ℂ)
    (e : SS.BitString 6) (Z : Finset (SS.BitString 6))
    (hZ : (Finset.univ : Finset (SS.BitString 6)).filter
      (fun z => (⟨e,z⟩ : SS.PauliString 6).wt = 2) = Z) :
    (∑ z : SS.BitString 6,
      if (⟨e,z⟩ : SS.PauliString 6).wt = 2 then
        4 * Complex.normSq (SixQubit.diagOn S0 c e z) else 0) =
      4 * dressingSum c e Z := by
  rw [← Finset.sum_filter, hZ, dressingSum, Finset.mul_sum]

theorem inner00 (c : SS.BitString 6 → ℂ) :
    (∑ z : SS.BitString 6,
      if (⟨e00,z⟩ : SS.PauliString 6).wt = 2 then
        4 * Complex.normSq (SixQubit.diagOn S0 c e00 z) else 0) =
      4 * dressingSum c e00 zPure :=
  inner_sum_eq c e00 zPure (by decide)

theorem inner03 (c : SS.BitString 6 → ℂ) :
    (∑ z : SS.BitString 6,
      if (⟨e03,z⟩ : SS.PauliString 6).wt = 2 then
        4 * Complex.normSq (SixQubit.diagOn S0 c e03 z) else 0) =
      4 * dressingSum c e03 z03 :=
  inner_sum_eq c e03 z03 (by decide)

theorem inner20 (c : SS.BitString 6 → ℂ) :
    (∑ z : SS.BitString 6,
      if (⟨e20,z⟩ : SS.PauliString 6).wt = 2 then
        4 * Complex.normSq (SixQubit.diagOn S0 c e20 z) else 0) =
      4 * dressingSum c e20 z20 :=
  inner_sum_eq c e20 z20 (by decide)

theorem inner36 (c : SS.BitString 6 → ℂ) :
    (∑ z : SS.BitString 6,
      if (⟨e36,z⟩ : SS.PauliString 6).wt = 2 then
        4 * Complex.normSq (SixQubit.diagOn S0 c e36 z) else 0) =
      4 * dressingSum c e36 z36 :=
  inner_sum_eq c e36 z36 (by decide)

theorem inner48 (c : SS.BitString 6 → ℂ) :
    (∑ z : SS.BitString 6,
      if (⟨e48,z⟩ : SS.PauliString 6).wt = 2 then
        4 * Complex.normSq (SixQubit.diagOn S0 c e48 z) else 0) =
      4 * dressingSum c e48 z48 :=
  inner_sum_eq c e48 z48 (by decide)

/-- Only five flip masks can contribute at weight two. -/
theorem Aco_two_live_sum (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    Aco ![c,d] 2 = 4 *
      (dressingSum c e00 zPure + dressingSum c e03 z03 +
        dressingSum c e20 z20 + dressingSum c e36 z36 +
        dressingSum c e48 z48) := by
  rw [Aco_two_double_sum c d hc hd hdist]
  have hrestrict :
      (∑ e : SS.BitString 6, ∑ z : SS.BitString 6,
        if (⟨e,z⟩ : SS.PauliString 6).wt = 2 then
          4 * Complex.normSq (SixQubit.diagOn S0 c e z) else 0) =
      ∑ e ∈ liveX, ∑ z : SS.BitString 6,
        if (⟨e,z⟩ : SS.PauliString 6).wt = 2 then
          4 * Complex.normSq (SixQubit.diagOn S0 c e z) else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ liveX)
    intro e _ he
    apply Finset.sum_eq_zero
    intro z _
    by_cases hw : (⟨e,z⟩ : SS.PauliString 6).wt = 2
    · rw [if_pos hw, diagOn_eq_zero_of_not_live c e z
          (le_trans (hammingWt_x_le_wt ⟨e,z⟩) (by omega)) he,
        Complex.normSq_zero, mul_zero]
    · rw [if_neg hw]
  rw [hrestrict]
  unfold liveX
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, inner00, inner03, inner20, inner36, inner48]
  ring

/-! ## Exact dressing expansions and Parseval blocks -/

theorem diag_pure_03 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 3) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + ((Complex.normSq (c x2) : ℝ) : ℂ) + ((Complex.normSq (c x3) : ℝ) : ℂ) + ((Complex.normSq (c x4) : ℝ) : ℂ) + ((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 3) x0 = false from by decide,
    show SS.bdot (nbit 3) x1 = false from by decide,
    show SS.bdot (nbit 3) x2 = false from by decide,
    show SS.bdot (nbit 3) x3 = false from by decide,
    show SS.bdot (nbit 3) x4 = false from by decide,
    show SS.bdot (nbit 3) x5 = false from by decide,
    show SS.bdot (nbit 3) x6 = true from by decide,
    show SS.bdot (nbit 3) x7 = true from by decide,
    show SS.bdot (nbit 3) x8 = true from by decide,
    show SS.bdot (nbit 3) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_05 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 5) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + ((Complex.normSq (c x6) : ℝ) : ℂ) + ((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 5) x0 = false from by decide,
    show SS.bdot (nbit 5) x1 = false from by decide,
    show SS.bdot (nbit 5) x2 = true from by decide,
    show SS.bdot (nbit 5) x3 = true from by decide,
    show SS.bdot (nbit 5) x4 = true from by decide,
    show SS.bdot (nbit 5) x5 = true from by decide,
    show SS.bdot (nbit 5) x6 = false from by decide,
    show SS.bdot (nbit 5) x7 = false from by decide,
    show SS.bdot (nbit 5) x8 = true from by decide,
    show SS.bdot (nbit 5) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_06 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 6) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + ((Complex.normSq (c x8) : ℝ) : ℂ) + ((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 6) x0 = false from by decide,
    show SS.bdot (nbit 6) x1 = false from by decide,
    show SS.bdot (nbit 6) x2 = true from by decide,
    show SS.bdot (nbit 6) x3 = true from by decide,
    show SS.bdot (nbit 6) x4 = true from by decide,
    show SS.bdot (nbit 6) x5 = true from by decide,
    show SS.bdot (nbit 6) x6 = true from by decide,
    show SS.bdot (nbit 6) x7 = true from by decide,
    show SS.bdot (nbit 6) x8 = false from by decide,
    show SS.bdot (nbit 6) x9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_09 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 9) = ((Complex.normSq (c x0) : ℝ) : ℂ) + -((Complex.normSq (c x1) : ℝ) : ℂ) + ((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + ((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + ((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + ((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 9) x0 = false from by decide,
    show SS.bdot (nbit 9) x1 = true from by decide,
    show SS.bdot (nbit 9) x2 = false from by decide,
    show SS.bdot (nbit 9) x3 = true from by decide,
    show SS.bdot (nbit 9) x4 = false from by decide,
    show SS.bdot (nbit 9) x5 = true from by decide,
    show SS.bdot (nbit 9) x6 = true from by decide,
    show SS.bdot (nbit 9) x7 = false from by decide,
    show SS.bdot (nbit 9) x8 = true from by decide,
    show SS.bdot (nbit 9) x9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_10 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 10) = ((Complex.normSq (c x0) : ℝ) : ℂ) + -((Complex.normSq (c x1) : ℝ) : ℂ) + ((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + ((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + ((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + ((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 10) x0 = false from by decide,
    show SS.bdot (nbit 10) x1 = true from by decide,
    show SS.bdot (nbit 10) x2 = false from by decide,
    show SS.bdot (nbit 10) x3 = true from by decide,
    show SS.bdot (nbit 10) x4 = false from by decide,
    show SS.bdot (nbit 10) x5 = true from by decide,
    show SS.bdot (nbit 10) x6 = false from by decide,
    show SS.bdot (nbit 10) x7 = true from by decide,
    show SS.bdot (nbit 10) x8 = false from by decide,
    show SS.bdot (nbit 10) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_12 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 12) = ((Complex.normSq (c x0) : ℝ) : ℂ) + -((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + ((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + ((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + ((Complex.normSq (c x7) : ℝ) : ℂ) + ((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 12) x0 = false from by decide,
    show SS.bdot (nbit 12) x1 = true from by decide,
    show SS.bdot (nbit 12) x2 = true from by decide,
    show SS.bdot (nbit 12) x3 = false from by decide,
    show SS.bdot (nbit 12) x4 = true from by decide,
    show SS.bdot (nbit 12) x5 = false from by decide,
    show SS.bdot (nbit 12) x6 = true from by decide,
    show SS.bdot (nbit 12) x7 = false from by decide,
    show SS.bdot (nbit 12) x8 = false from by decide,
    show SS.bdot (nbit 12) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_17 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 17) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + ((Complex.normSq (c x2) : ℝ) : ℂ) + ((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + ((Complex.normSq (c x8) : ℝ) : ℂ) + ((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 17) x0 = false from by decide,
    show SS.bdot (nbit 17) x1 = false from by decide,
    show SS.bdot (nbit 17) x2 = false from by decide,
    show SS.bdot (nbit 17) x3 = false from by decide,
    show SS.bdot (nbit 17) x4 = true from by decide,
    show SS.bdot (nbit 17) x5 = true from by decide,
    show SS.bdot (nbit 17) x6 = true from by decide,
    show SS.bdot (nbit 17) x7 = true from by decide,
    show SS.bdot (nbit 17) x8 = false from by decide,
    show SS.bdot (nbit 17) x9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_18 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 18) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + ((Complex.normSq (c x2) : ℝ) : ℂ) + ((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + ((Complex.normSq (c x6) : ℝ) : ℂ) + ((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 18) x0 = false from by decide,
    show SS.bdot (nbit 18) x1 = false from by decide,
    show SS.bdot (nbit 18) x2 = false from by decide,
    show SS.bdot (nbit 18) x3 = false from by decide,
    show SS.bdot (nbit 18) x4 = true from by decide,
    show SS.bdot (nbit 18) x5 = true from by decide,
    show SS.bdot (nbit 18) x6 = false from by decide,
    show SS.bdot (nbit 18) x7 = false from by decide,
    show SS.bdot (nbit 18) x8 = true from by decide,
    show SS.bdot (nbit 18) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_20 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 20) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + ((Complex.normSq (c x4) : ℝ) : ℂ) + ((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 20) x0 = false from by decide,
    show SS.bdot (nbit 20) x1 = false from by decide,
    show SS.bdot (nbit 20) x2 = true from by decide,
    show SS.bdot (nbit 20) x3 = true from by decide,
    show SS.bdot (nbit 20) x4 = false from by decide,
    show SS.bdot (nbit 20) x5 = false from by decide,
    show SS.bdot (nbit 20) x6 = true from by decide,
    show SS.bdot (nbit 20) x7 = true from by decide,
    show SS.bdot (nbit 20) x8 = true from by decide,
    show SS.bdot (nbit 20) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_24 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 24) = ((Complex.normSq (c x0) : ℝ) : ℂ) + -((Complex.normSq (c x1) : ℝ) : ℂ) + ((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + ((Complex.normSq (c x5) : ℝ) : ℂ) + ((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + ((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 24) x0 = false from by decide,
    show SS.bdot (nbit 24) x1 = true from by decide,
    show SS.bdot (nbit 24) x2 = false from by decide,
    show SS.bdot (nbit 24) x3 = true from by decide,
    show SS.bdot (nbit 24) x4 = true from by decide,
    show SS.bdot (nbit 24) x5 = false from by decide,
    show SS.bdot (nbit 24) x6 = false from by decide,
    show SS.bdot (nbit 24) x7 = true from by decide,
    show SS.bdot (nbit 24) x8 = true from by decide,
    show SS.bdot (nbit 24) x9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_33 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 33) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + ((Complex.normSq (c x4) : ℝ) : ℂ) + ((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + ((Complex.normSq (c x8) : ℝ) : ℂ) + ((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 33) x0 = false from by decide,
    show SS.bdot (nbit 33) x1 = false from by decide,
    show SS.bdot (nbit 33) x2 = true from by decide,
    show SS.bdot (nbit 33) x3 = true from by decide,
    show SS.bdot (nbit 33) x4 = false from by decide,
    show SS.bdot (nbit 33) x5 = false from by decide,
    show SS.bdot (nbit 33) x6 = true from by decide,
    show SS.bdot (nbit 33) x7 = true from by decide,
    show SS.bdot (nbit 33) x8 = false from by decide,
    show SS.bdot (nbit 33) x9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_34 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 34) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + ((Complex.normSq (c x4) : ℝ) : ℂ) + ((Complex.normSq (c x5) : ℝ) : ℂ) + ((Complex.normSq (c x6) : ℝ) : ℂ) + ((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 34) x0 = false from by decide,
    show SS.bdot (nbit 34) x1 = false from by decide,
    show SS.bdot (nbit 34) x2 = true from by decide,
    show SS.bdot (nbit 34) x3 = true from by decide,
    show SS.bdot (nbit 34) x4 = false from by decide,
    show SS.bdot (nbit 34) x5 = false from by decide,
    show SS.bdot (nbit 34) x6 = false from by decide,
    show SS.bdot (nbit 34) x7 = false from by decide,
    show SS.bdot (nbit 34) x8 = true from by decide,
    show SS.bdot (nbit 34) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_36 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 36) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + ((Complex.normSq (c x2) : ℝ) : ℂ) + ((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + -((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + -((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 36) x0 = false from by decide,
    show SS.bdot (nbit 36) x1 = false from by decide,
    show SS.bdot (nbit 36) x2 = false from by decide,
    show SS.bdot (nbit 36) x3 = false from by decide,
    show SS.bdot (nbit 36) x4 = true from by decide,
    show SS.bdot (nbit 36) x5 = true from by decide,
    show SS.bdot (nbit 36) x6 = true from by decide,
    show SS.bdot (nbit 36) x7 = true from by decide,
    show SS.bdot (nbit 36) x8 = true from by decide,
    show SS.bdot (nbit 36) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_40 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 40) = ((Complex.normSq (c x0) : ℝ) : ℂ) + -((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + ((Complex.normSq (c x3) : ℝ) : ℂ) + ((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + ((Complex.normSq (c x6) : ℝ) : ℂ) + -((Complex.normSq (c x7) : ℝ) : ℂ) + -((Complex.normSq (c x8) : ℝ) : ℂ) + ((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 40) x0 = false from by decide,
    show SS.bdot (nbit 40) x1 = true from by decide,
    show SS.bdot (nbit 40) x2 = true from by decide,
    show SS.bdot (nbit 40) x3 = false from by decide,
    show SS.bdot (nbit 40) x4 = false from by decide,
    show SS.bdot (nbit 40) x5 = true from by decide,
    show SS.bdot (nbit 40) x6 = false from by decide,
    show SS.bdot (nbit 40) x7 = true from by decide,
    show SS.bdot (nbit 40) x8 = true from by decide,
    show SS.bdot (nbit 40) x9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_pure_48 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e00 (nbit 48) = ((Complex.normSq (c x0) : ℝ) : ℂ) + ((Complex.normSq (c x1) : ℝ) : ℂ) + -((Complex.normSq (c x2) : ℝ) : ℂ) + -((Complex.normSq (c x3) : ℝ) : ℂ) + -((Complex.normSq (c x4) : ℝ) : ℂ) + -((Complex.normSq (c x5) : ℝ) : ℂ) + ((Complex.normSq (c x6) : ℝ) : ℂ) + ((Complex.normSq (c x7) : ℝ) : ℂ) + ((Complex.normSq (c x8) : ℝ) : ℂ) + ((Complex.normSq (c x9) : ℝ) : ℂ) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e00 = x0 from by decide,
    show SS.bxor x1 e00 = x1 from by decide,
    show SS.bxor x2 e00 = x2 from by decide,
    show SS.bxor x3 e00 = x3 from by decide,
    show SS.bxor x4 e00 = x4 from by decide,
    show SS.bxor x5 e00 = x5 from by decide,
    show SS.bxor x6 e00 = x6 from by decide,
    show SS.bxor x7 e00 = x7 from by decide,
    show SS.bxor x8 e00 = x8 from by decide,
    show SS.bxor x9 e00 = x9 from by decide]
  simp only [show SS.bdot (nbit 48) x0 = false from by decide,
    show SS.bdot (nbit 48) x1 = false from by decide,
    show SS.bdot (nbit 48) x2 = true from by decide,
    show SS.bdot (nbit 48) x3 = true from by decide,
    show SS.bdot (nbit 48) x4 = true from by decide,
    show SS.bdot (nbit 48) x5 = true from by decide,
    show SS.bdot (nbit 48) x6 = false from by decide,
    show SS.bdot (nbit 48) x7 = false from by decide,
    show SS.bdot (nbit 48) x8 = false from by decide,
    show SS.bdot (nbit 48) x9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true, SixQubit.star_mul_self]
  ring

theorem diag_03_00 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e03 (nbit 0) = star (c x9) * c x6 + star (c x8) * c x7 + star (c x7) * c x8 + star (c x6) * c x9 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e03 ∈ S0) =
      ({x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x6 e03 = x9 from by decide,
    show SS.bxor x7 e03 = x8 from by decide,
    show SS.bxor x8 e03 = x7 from by decide,
    show SS.bxor x9 e03 = x6 from by decide]
  simp only [show SS.bdot (nbit 0) x6 = false from by decide,
    show SS.bdot (nbit 0) x7 = false from by decide,
    show SS.bdot (nbit 0) x8 = false from by decide,
    show SS.bdot (nbit 0) x9 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem diag_03_01 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e03 (nbit 1) = star (c x9) * c x6 + -star (c x8) * c x7 + star (c x7) * c x8 + -star (c x6) * c x9 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e03 ∈ S0) =
      ({x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x6 e03 = x9 from by decide,
    show SS.bxor x7 e03 = x8 from by decide,
    show SS.bxor x8 e03 = x7 from by decide,
    show SS.bxor x9 e03 = x6 from by decide]
  simp only [show SS.bdot (nbit 1) x6 = false from by decide,
    show SS.bdot (nbit 1) x7 = true from by decide,
    show SS.bdot (nbit 1) x8 = false from by decide,
    show SS.bdot (nbit 1) x9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem diag_03_02 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e03 (nbit 2) = -star (c x9) * c x6 + star (c x8) * c x7 + -star (c x7) * c x8 + star (c x6) * c x9 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e03 ∈ S0) =
      ({x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x6 e03 = x9 from by decide,
    show SS.bxor x7 e03 = x8 from by decide,
    show SS.bxor x8 e03 = x7 from by decide,
    show SS.bxor x9 e03 = x6 from by decide]
  simp only [show SS.bdot (nbit 2) x6 = true from by decide,
    show SS.bdot (nbit 2) x7 = false from by decide,
    show SS.bdot (nbit 2) x8 = true from by decide,
    show SS.bdot (nbit 2) x9 = false from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

theorem diag_03_03 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e03 (nbit 3) = -star (c x9) * c x6 + -star (c x8) * c x7 + -star (c x7) * c x8 + -star (c x6) * c x9 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e03 ∈ S0) =
      ({x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x6 e03 = x9 from by decide,
    show SS.bxor x7 e03 = x8 from by decide,
    show SS.bxor x8 e03 = x7 from by decide,
    show SS.bxor x9 e03 = x6 from by decide]
  simp only [show SS.bdot (nbit 3) x6 = true from by decide,
    show SS.bdot (nbit 3) x7 = true from by decide,
    show SS.bdot (nbit 3) x8 = true from by decide,
    show SS.bdot (nbit 3) x9 = true from by decide,
    SixQubit.signMul_true]
  ring

theorem diag_20_00 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e20 (nbit 0) = star (c x4) * c x0 + star (c x5) * c x1 + star (c x0) * c x4 + star (c x1) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e20 ∈ S0) =
      ({x0,x1,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e20 = x4 from by decide,
    show SS.bxor x1 e20 = x5 from by decide,
    show SS.bxor x4 e20 = x0 from by decide,
    show SS.bxor x5 e20 = x1 from by decide]
  simp only [show SS.bdot (nbit 0) x0 = false from by decide,
    show SS.bdot (nbit 0) x1 = false from by decide,
    show SS.bdot (nbit 0) x4 = false from by decide,
    show SS.bdot (nbit 0) x5 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem diag_20_04 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e20 (nbit 4) = star (c x4) * c x0 + -star (c x5) * c x1 + -star (c x0) * c x4 + star (c x1) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e20 ∈ S0) =
      ({x0,x1,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e20 = x4 from by decide,
    show SS.bxor x1 e20 = x5 from by decide,
    show SS.bxor x4 e20 = x0 from by decide,
    show SS.bxor x5 e20 = x1 from by decide]
  simp only [show SS.bdot (nbit 4) x0 = false from by decide,
    show SS.bdot (nbit 4) x1 = true from by decide,
    show SS.bdot (nbit 4) x4 = true from by decide,
    show SS.bdot (nbit 4) x5 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem diag_20_16 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e20 (nbit 16) = star (c x4) * c x0 + -star (c x5) * c x1 + -star (c x0) * c x4 + star (c x1) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e20 ∈ S0) =
      ({x0,x1,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e20 = x4 from by decide,
    show SS.bxor x1 e20 = x5 from by decide,
    show SS.bxor x4 e20 = x0 from by decide,
    show SS.bxor x5 e20 = x1 from by decide]
  simp only [show SS.bdot (nbit 16) x0 = false from by decide,
    show SS.bdot (nbit 16) x1 = true from by decide,
    show SS.bdot (nbit 16) x4 = true from by decide,
    show SS.bdot (nbit 16) x5 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem diag_20_20 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e20 (nbit 20) = star (c x4) * c x0 + star (c x5) * c x1 + star (c x0) * c x4 + star (c x1) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e20 ∈ S0) =
      ({x0,x1,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e20 = x4 from by decide,
    show SS.bxor x1 e20 = x5 from by decide,
    show SS.bxor x4 e20 = x0 from by decide,
    show SS.bxor x5 e20 = x1 from by decide]
  simp only [show SS.bdot (nbit 20) x0 = false from by decide,
    show SS.bdot (nbit 20) x1 = false from by decide,
    show SS.bdot (nbit 20) x4 = false from by decide,
    show SS.bdot (nbit 20) x5 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem diag_36_00 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e36 (nbit 0) = star (c x2) * c x0 + star (c x3) * c x1 + star (c x0) * c x2 + star (c x1) * c x3 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e36 ∈ S0) =
      ({x0,x1,x2,x3} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e36 = x2 from by decide,
    show SS.bxor x1 e36 = x3 from by decide,
    show SS.bxor x2 e36 = x0 from by decide,
    show SS.bxor x3 e36 = x1 from by decide]
  simp only [show SS.bdot (nbit 0) x0 = false from by decide,
    show SS.bdot (nbit 0) x1 = false from by decide,
    show SS.bdot (nbit 0) x2 = false from by decide,
    show SS.bdot (nbit 0) x3 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem diag_36_04 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e36 (nbit 4) = star (c x2) * c x0 + -star (c x3) * c x1 + -star (c x0) * c x2 + star (c x1) * c x3 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e36 ∈ S0) =
      ({x0,x1,x2,x3} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e36 = x2 from by decide,
    show SS.bxor x1 e36 = x3 from by decide,
    show SS.bxor x2 e36 = x0 from by decide,
    show SS.bxor x3 e36 = x1 from by decide]
  simp only [show SS.bdot (nbit 4) x0 = false from by decide,
    show SS.bdot (nbit 4) x1 = true from by decide,
    show SS.bdot (nbit 4) x2 = true from by decide,
    show SS.bdot (nbit 4) x3 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem diag_36_32 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e36 (nbit 32) = star (c x2) * c x0 + -star (c x3) * c x1 + -star (c x0) * c x2 + star (c x1) * c x3 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e36 ∈ S0) =
      ({x0,x1,x2,x3} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e36 = x2 from by decide,
    show SS.bxor x1 e36 = x3 from by decide,
    show SS.bxor x2 e36 = x0 from by decide,
    show SS.bxor x3 e36 = x1 from by decide]
  simp only [show SS.bdot (nbit 32) x0 = false from by decide,
    show SS.bdot (nbit 32) x1 = true from by decide,
    show SS.bdot (nbit 32) x2 = true from by decide,
    show SS.bdot (nbit 32) x3 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem diag_36_36 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e36 (nbit 36) = star (c x2) * c x0 + star (c x3) * c x1 + star (c x0) * c x2 + star (c x1) * c x3 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e36 ∈ S0) =
      ({x0,x1,x2,x3} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x0 e36 = x2 from by decide,
    show SS.bxor x1 e36 = x3 from by decide,
    show SS.bxor x2 e36 = x0 from by decide,
    show SS.bxor x3 e36 = x1 from by decide]
  simp only [show SS.bdot (nbit 36) x0 = false from by decide,
    show SS.bdot (nbit 36) x1 = false from by decide,
    show SS.bdot (nbit 36) x2 = false from by decide,
    show SS.bdot (nbit 36) x3 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem diag_48_00 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e48 (nbit 0) = star (c x4) * c x2 + star (c x5) * c x3 + star (c x2) * c x4 + star (c x3) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e48 ∈ S0) =
      ({x2,x3,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x2 e48 = x4 from by decide,
    show SS.bxor x3 e48 = x5 from by decide,
    show SS.bxor x4 e48 = x2 from by decide,
    show SS.bxor x5 e48 = x3 from by decide]
  simp only [show SS.bdot (nbit 0) x2 = false from by decide,
    show SS.bdot (nbit 0) x3 = false from by decide,
    show SS.bdot (nbit 0) x4 = false from by decide,
    show SS.bdot (nbit 0) x5 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem diag_48_16 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e48 (nbit 16) = star (c x4) * c x2 + -star (c x5) * c x3 + -star (c x2) * c x4 + star (c x3) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e48 ∈ S0) =
      ({x2,x3,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x2 e48 = x4 from by decide,
    show SS.bxor x3 e48 = x5 from by decide,
    show SS.bxor x4 e48 = x2 from by decide,
    show SS.bxor x5 e48 = x3 from by decide]
  simp only [show SS.bdot (nbit 16) x2 = false from by decide,
    show SS.bdot (nbit 16) x3 = true from by decide,
    show SS.bdot (nbit 16) x4 = true from by decide,
    show SS.bdot (nbit 16) x5 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem diag_48_32 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e48 (nbit 32) = -star (c x4) * c x2 + star (c x5) * c x3 + star (c x2) * c x4 + -star (c x3) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e48 ∈ S0) =
      ({x2,x3,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x2 e48 = x4 from by decide,
    show SS.bxor x3 e48 = x5 from by decide,
    show SS.bxor x4 e48 = x2 from by decide,
    show SS.bxor x5 e48 = x3 from by decide]
  simp only [show SS.bdot (nbit 32) x2 = true from by decide,
    show SS.bdot (nbit 32) x3 = false from by decide,
    show SS.bdot (nbit 32) x4 = false from by decide,
    show SS.bdot (nbit 32) x5 = true from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

theorem diag_48_48 (c : SS.BitString 6 → ℂ) :
    SixQubit.diagOn S0 c e48 (nbit 48) = -star (c x4) * c x2 + -star (c x5) * c x3 + -star (c x2) * c x4 + -star (c x3) * c x5 := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun s => SS.bxor s e48 ∈ S0) =
      ({x2,x3,x4,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor x2 e48 = x4 from by decide,
    show SS.bxor x3 e48 = x5 from by decide,
    show SS.bxor x4 e48 = x2 from by decide,
    show SS.bxor x5 e48 = x3 from by decide]
  simp only [show SS.bdot (nbit 48) x2 = true from by decide,
    show SS.bdot (nbit 48) x3 = true from by decide,
    show SS.bdot (nbit 48) x4 = true from by decide,
    show SS.bdot (nbit 48) x5 = true from by decide,
    SixQubit.signMul_true]
  ring

theorem dressing_pure (c d : SS.BitString 6 → ℂ) (g1 g2 g3 : ℝ)
    (hb : SixQubit.Orbit45Universal.BlockMasses c d g1 g2 g3) :
    dressingSum c e00 zPure = 3 * (g1^2 + g2^2 + g3^2) - 1/2 := by
  unfold dressingSum zPure
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, diag_pure_03, diag_pure_05, diag_pure_06, diag_pure_09, diag_pure_10, diag_pure_12, diag_pure_17, diag_pure_18, diag_pure_20, diag_pure_24, diag_pure_33, diag_pure_34, diag_pure_36, diag_pure_40, diag_pure_48]
  rw [hb.block1.1, hb.block1.2.1, hb.block2.1, hb.block2.2.1,
    hb.block3.1, hb.block3.2.1, hb.block4.1, hb.block4.2.1,
    hb.block5.1, hb.block5.2.1]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [hb.moving_sum]

theorem dressing_03 (c : SS.BitString 6 → ℂ) :
    dressingSum c e03 z03 = 8 * Complex.normSq (star (c x8) * c x7 + star (c x6) * c x9) := by
  unfold dressingSum z03
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, diag_03_00, diag_03_01, diag_03_02, diag_03_03]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem dressing_20 (c : SS.BitString 6 → ℂ) :
    dressingSum c e20 z20 = 8 * Complex.normSq (star (c x4) * c x0 + star (c x1) * c x5) := by
  unfold dressingSum z20
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, diag_20_00, diag_20_04, diag_20_16, diag_20_20]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem dressing_36 (c : SS.BitString 6 → ℂ) :
    dressingSum c e36 z36 = 8 * Complex.normSq (star (c x2) * c x0 + star (c x1) * c x3) := by
  unfold dressingSum z36
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, diag_36_00, diag_36_04, diag_36_32, diag_36_36]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem dressing_48 (c : SS.BitString 6 → ℂ) :
    dressingSum c e48 z48 = 8 * Complex.normSq (star (c x2) * c x4 + star (c x5) * c x3) := by
  unfold dressingSum z48
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, diag_48_00, diag_48_16, diag_48_32, diag_48_48]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-! ## Closing the `A_2` identity -/

theorem Aco_two_value (c d : SS.BitString 6 → ℂ) (g1 g2 g3 : ℝ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3)
    (hb : SixQubit.Orbit45Universal.BlockMasses c d g1 g2 g3)
    (hp : PhaseRelations c d) :
    Aco ![c,d] 2 = 8 * (g1^2 + g2^2 + g3^2) := by
  obtain ⟨ht123,ht45⟩ := bilinear_sums_zero c d g1 g2 g3 hb hp
  have hframe := SixQubit.Orbit45Gram.frame_potential
    (c x0) (c x1) (c x2) (c x3) (c x4) (c x5) g1 g2 g3
    hb.block1.1 hb.block1.2.1 hb.block2.1 hb.block2.2.1
    hb.block3.1 hb.block3.2.1 hb.moving_sum ht123
  have hpair := SixQubit.Orbit45Gram.pair_cross_norm
    (c x6) (c x7) (c x8) (c x9)
    (by rw [hb.block4.1, hb.block5.1])
    (by rw [hb.block4.2.1, hb.block5.2.1])
  have hpair0 :
      Complex.normSq (star (c x8) * c x7 + star (c x6) * c x9) = 0 := by
    rw [hpair, ht45, Complex.normSq_zero]
  rw [Aco_two_live_sum c d hc hd hdist,
    dressing_pure c d g1 g2 g3 hb, dressing_03, dressing_20,
    dressing_36, dressing_48, hpair0]
  nlinarith [hframe]

/-- **Code-level identification of the interval parameter.**  The witness is
not merely an abstract Gram parameter: it is exactly `Aco 2 / 4`. -/
theorem Aco_two_interval (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    ∃ t : ℝ, Aco ![c,d] 2 = 4*t ∧ (2/3 : ℝ) ≤ t ∧ t ≤ 1 := by
  obtain ⟨g1,g2,g3,r1,r2,r3,t,hcv⟩ :=
    SixQubit.Orbit45Universal.universal_converse c d hc hd hnc hnd hdist
  have hp := phase_relations c d hc hd hdist
  have hA := Aco_two_value c d g1 g2 g3 hc hd hdist hcv.blocks hp
  refine ⟨t,?_,hcv.lower,hcv.upper⟩
  rw [hA, hcv.t_mass]
  ring

end

end SixQubit.Orbit45A2
