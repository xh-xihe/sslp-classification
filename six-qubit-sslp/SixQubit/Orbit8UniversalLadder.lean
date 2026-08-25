import SixQubit.Orbit8UniversalCoordinates

/-!
# Orbit 8 universal converse, IV: the anti-linear ladder

This file realizes the manuscript's raising operator and even spin flip as
actual maps on the 64-dimensional state space.  The first ladder identity is
then obtained pointwise from the pair-cross KL equations.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

/-- The sign `(-1)^(|x|+1)` in the six-qubit spin flip. -/
def spinSign (x : SS.BitString 6) : ℤ :=
  if SS.hammingWt x % 2 = 0 then -1 else 1

/-- `J = Y^⊗6 K`, in the computational basis. -/
def spinJ (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => (spinSign x : ℂ) * star (f (SS.complement x))

/-- `R = Σ_i u_i σ_i^+`. -/
def raise (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => ∑ i, if x i = true then ud i * f (SS.bxor x (SS.stdBasis i)) else 0

/-- `R† = Σ_i conj(u_i) σ_i^-`. -/
def lower (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => ∑ i, if x i = false then star (ud i) * f (SS.bxor x (SS.stdBasis i)) else 0

def Qact (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  raise ud (lower ud f)

theorem spinSign_toggle : ∀ x : SS.BitString 6, ∀ i : Fin 6,
    spinSign (SS.bxor x (SS.stdBasis i)) = - spinSign x := by decide

theorem spinSign_complement : ∀ x : SS.BitString 6,
    spinSign (SS.complement x) = spinSign x := by decide

lemma complement_bxor_stdBasis (x : SS.BitString 6) (i : Fin 6) :
    SS.complement (SS.bxor x (SS.stdBasis i)) =
      SS.bxor (SS.complement x) (SS.stdBasis i) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [SS.bxor, SS.complement, SS.stdBasis]
  · simp [SS.bxor, SS.complement, SS.stdBasis]

@[simp] lemma spinJ_zero (f : SS.BitString 6 → ℂ) :
    spinJ f zero6 = -star (f ones6) := by
  unfold spinJ
  rw [show spinSign zero6 = -1 from by decide]
  rw [show SS.complement zero6 = ones6 from by decide]
  norm_num

theorem weight_four_is_complement_pair : ∀ x : SS.BitString 6,
    SS.hammingWt x = 4 →
      ∃ i j : Fin 6, i ≠ j ∧ x = SS.complement (pairMask i j) := by decide

theorem true_indices_singleton : ∀ i : Fin 6,
    Finset.univ.filter (fun k => SS.stdBasis i k = true) = {i} := by decide

theorem true_indices_complement_pair : ∀ i j : Fin 6, i ≠ j →
    Finset.univ.filter
      (fun k => SS.complement (pairMask i j) k = true) =
        Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j) := by decide

theorem spinJ_complement_pair_flip (c : SS.BitString 6 → ℂ) :
    ∀ i j k : Fin 6, i ≠ j → k ≠ i → k ≠ j →
      spinJ c (SS.bxor (SS.complement (pairMask i j)) (SS.stdBasis k)) =
        star (a c i j k) := by
  intro i j k hij hki hkj
  unfold spinJ a
  rw [show spinSign
      (SS.bxor (SS.complement (pairMask i j)) (SS.stdBasis k)) = 1 from by
    revert i j k
    decide]
  rw [show SS.complement
      (SS.bxor (SS.complement (pairMask i j)) (SS.stdBasis k)) =
        tripleMask i j k from by
    revert i j k
    decide]
  norm_num

theorem raise_vanishes_outside_S1 (ud : Fin 6 → ℂ) (c : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (x : SS.BitString 6) (hx : x ∉ S1) :
    raise ud (spinJ c) x = 0 := by
  classical
  unfold raise
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hxi : x i = true
  · rw [if_pos hxi]
    have hout : SS.complement (SS.bxor x (SS.stdBasis i)) ∉ S0 := by
      revert x i
      decide
    have hc0 : c (SS.complement (SS.bxor x (SS.stdBasis i))) = 0 := by
      apply hc
      simpa [S0] using hout
    simp [spinJ, hc0]
  · rw [if_neg hxi]

/-- **First anti-linear ladder identity.**  It uses only full-fibre support and
the weight-two cross rows supplied by genuine `HasDistance`. -/
theorem ladder01 (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    raise (u d) (spinJ c) = fun x => -(star (ball c)) * d x := by
  funext x
  by_cases hx : x ∈ S1
  · rcases S1_shells x hx with hwt | hwt
    · obtain ⟨i, rfl⟩ := hamming_one_is_stdBasis x hwt
      unfold raise u
      rw [← Finset.sum_filter]
      rw [true_indices_singleton]
      simp only [Finset.sum_singleton]
      rw [SS.bxor_self]
      change d (SS.stdBasis i) * spinJ c zero6 =
        -(star (ball c)) * d (SS.stdBasis i)
      rw [spinJ_zero]
      unfold ball
      ring
    · obtain ⟨i, j, hij, rfl⟩ := weight_four_is_complement_pair x hwt
      unfold raise
      rw [← Finset.sum_filter]
      rw [true_indices_complement_pair i j hij]
      have hcross := pair_cross c d hc hd hcode i j hij
      rw [Finset.sum_congr rfl (fun k hk => by
        have hk' := (Finset.mem_filter.mp hk).2
        rw [spinJ_complement_pair_flip c i j k hij hk'.1 hk'.2])]
      unfold v at hcross
      rw [Finset.sum_congr rfl (fun k hk => mul_comm (u d k) (star (a c i j k)))]
      linear_combination hcross
  · have hd0 : d x = 0 := by
      apply hd
      simpa [S1] using hx
    rw [hd0, mul_zero]
    exact raise_vanishes_outside_S1 (u d) c hc x hx

def complementEquiv : SS.BitString 6 ≃ SS.BitString 6 where
  toFun := SS.complement
  invFun := SS.complement
  left_inv := SS.complement_complement
  right_inv := SS.complement_complement

/-- The even six-qubit spin flip reverses the Hermitian inner product. -/
theorem spinJ_inner (f g : SS.BitString 6 → ℂ) :
    SS.innerC (spinJ f) (spinJ g) = SS.innerC g f := by
  classical
  unfold SS.innerC
  rw [← Equiv.sum_comp complementEquiv
    (fun x => star (g x) * f x)]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  unfold spinJ
  change star ((spinSign x : ℂ) * star (f (SS.complement x))) *
      ((spinSign x : ℂ) * star (g (SS.complement x))) =
    star (g (SS.complement x)) * f (SS.complement x)
  simp only [star_mul', star_star]
  by_cases hp : SS.hammingWt x % 2 = 0 <;>
    simp [spinSign, hp] <;> ring

@[simp] theorem spinJ_sq (f : SS.BitString 6 → ℂ) : spinJ (spinJ f) = f := by
  funext x
  unfold spinJ
  rw [spinSign_complement, SS.complement_complement]
  simp only [star_mul', star_star]
  by_cases hp : SS.hammingWt x % 2 = 0
  · simp [spinSign, hp]
  · simp [spinSign, hp]

theorem spinJ_smul (z : ℂ) (f : SS.BitString 6 → ℂ) :
    spinJ (fun x => z * f x) = fun x => star z * spinJ f x := by
  funext x
  unfold spinJ
  simp only [star_mul']
  ring

/-- On six qubits `R J = - J R†`, proved directly on all coordinates. -/
theorem raise_spinJ (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    raise ud (spinJ f) = fun x => -spinJ (lower ud f) x := by
  funext x
  classical
  unfold raise spinJ lower
  rw [star_sum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  by_cases hxi : x i = true
  · have hcomp : SS.complement x i = false := by simp [hxi]
    rw [if_pos hxi, if_pos hcomp]
    rw [spinSign_toggle, complement_bxor_stdBasis]
    simp only [star_mul', star_star]
    push_cast
    ring
  · have hxif : x i = false := Bool.eq_false_of_not_eq_true hxi
    have hcomp : SS.complement x i ≠ false := by simp [hxif]
    rw [if_neg hxi, if_neg hcomp]
    simp

/-- Raising and lowering are adjoint for the raw finite inner product. -/
theorem inner_raise_lower (ud : Fin 6 → ℂ)
    (f g : SS.BitString 6 → ℂ) :
    SS.innerC f (raise ud g) = SS.innerC (lower ud f) g := by
  classical
  calc
    SS.innerC f (raise ud g) =
        ∑ i : Fin 6, ∑ x : SS.BitString 6,
          star (f x) *
            (if x i = true then ud i * g (SS.bxor x (SS.stdBasis i)) else 0) := by
      unfold SS.innerC raise
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 6, ∑ x : SS.BitString 6,
          star (if x i = false then
            star (ud i) * f (SS.bxor x (SS.stdBasis i)) else 0) * g x := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← Equiv.sum_comp (SS.bxorEquiv (SS.stdBasis i))
        (fun x => star (if x i = false then
          star (ud i) * f (SS.bxor x (SS.stdBasis i)) else 0) * g x)]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      simp only [SS.bxorEquiv, Equiv.coe_fn_mk]
      by_cases hxi : x i = true
      · have htog : SS.bxor x (SS.stdBasis i) i = false := by
          simp [SS.bxor, SS.stdBasis, hxi]
        rw [if_pos hxi, if_pos htog]
        rw [SS.bxor_bxor_cancel]
        simp only [star_mul', star_star]
        ring
      · have hxif : x i = false := Bool.eq_false_of_not_eq_true hxi
        have htog : SS.bxor x (SS.stdBasis i) i ≠ false := by
          simp [SS.bxor, SS.stdBasis, hxif]
        rw [if_neg hxi, if_neg htog]
        simp
    _ = SS.innerC (lower ud f) g := by
      unfold SS.innerC lower
      simp_rw [star_sum, Finset.sum_mul]
      rw [Finset.sum_comm]

/-- The squared norm of `R J f` is the expectation of `Q=R R†`. -/
theorem ladder_norm (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    SS.innerC (raise ud (spinJ f)) (raise ud (spinJ f)) =
      SS.innerC f (Qact ud f) := by
  rw [raise_spinJ]
  have hspin := spinJ_inner (lower ud f) (lower ud f)
  rw [show SS.innerC (fun x => -spinJ (lower ud f) x)
      (fun x => -spinJ (lower ud f) x) =
      SS.innerC (spinJ (lower ud f)) (spinJ (lower ud f)) by
    unfold SS.innerC
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp]
  rw [hspin]
  exact (inner_raise_lower ud f (lower ud f)).symm

end

end SixQubit.Orbit8Universal
