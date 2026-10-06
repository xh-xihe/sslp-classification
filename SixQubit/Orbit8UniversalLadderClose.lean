import SixQubit.Orbit8UniversalQ

/-!
# Orbit 8 universal converse, VI: closing the anti-linear ladder

The low-weight Pauli expansion of `Q` makes the two `R J` norms equal.  The
antisymmetry of the induced bilinear form then saturates Cauchy--Schwarz and
gives the second ladder identity and `Q P = r P`.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

lemma innerC_star (f g : SS.BitString 6 → ℂ) :
    star (SS.innerC f g) = SS.innerC g f := by
  classical
  unfold SS.innerC
  rw [star_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  simp only [star_mul', star_star]
  ring

lemma innerC_neg_right (f g : SS.BitString 6 → ℂ) :
    SS.innerC f (fun x => -g x) = -SS.innerC f g := by
  unfold SS.innerC
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x hx => by ring)

lemma innerC_smul_right (f g : SS.BitString 6 → ℂ) (z : ℂ) :
    SS.innerC f (fun x => z * g x) = z * SS.innerC f g := by
  unfold SS.innerC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x hx => by ring)

lemma innerC_smul_self (f : SS.BitString 6 → ℂ) (z : ℂ) :
    SS.innerC (fun x => z * f x) (fun x => z * f x) =
      (Complex.normSq z : ℂ) * SS.innerC f f := by
  unfold SS.innerC
  push_cast [← SixQubit.star_mul_self]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x hx => by
    simp only [star_mul']
    ring)

/-- The bilinear form `<f|R J|g>` is antisymmetric. -/
theorem ladder_antisymmetric (ud : Fin 6 → ℂ)
    (f g : SS.BitString 6 → ℂ) :
    SS.innerC f (raise ud (spinJ g)) =
      -SS.innerC g (raise ud (spinJ f)) := by
  rw [inner_raise_lower]
  have hspin := spinJ_inner (spinJ (lower ud f)) g
  rw [spinJ_sq] at hspin
  have hr := raise_spinJ ud f
  have hjl : spinJ (lower ud f) = fun x => -raise ud (spinJ f) x := by
    funext x
    have hx := congrFun hr x
    linear_combination hx
  rw [hspin, hjl, innerC_neg_right]

lemma innerC_self_eq_normSum (f : SS.BitString 6 → ℂ) :
    SS.innerC f f = ((∑ x, Complex.normSq (f x) : ℝ) : ℂ) := by
  unfold SS.innerC
  push_cast [← SixQubit.star_mul_self]
  rfl

lemma state_eq_zero_of_innerC_self_zero (f : SS.BitString 6 → ℂ)
    (h : SS.innerC f f = 0) : f = 0 := by
  have hs := innerC_self_eq_normSum f
  rw [h] at hs
  have hreal : (∑ x, Complex.normSq (f x) : ℝ) = 0 := by exact_mod_cast hs.symm
  funext x
  have hx : Complex.normSq (f x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy => Complex.normSq_nonneg (f y))).mp hreal x (Finset.mem_univ x)
  exact Complex.normSq_eq_zero.mp hx

lemma innerC_sub_smul_self (g c : SS.BitString 6 → ℂ) (z : ℂ) :
    SS.innerC (fun x => g x - z * c x) (fun x => g x - z * c x) =
      SS.innerC g g - z * SS.innerC g c - star z * SS.innerC c g
        + star z * z * SS.innerC c c := by
  classical
  unfold SS.innerC
  simp only [star_sub, star_mul']
  calc
    _ = ∑ x, ((star (g x) * g x - z * (star (g x) * c x))
        - star z * (star (c x) * g x) + star z * z * (star (c x) * c x)) := by
          refine Finset.sum_congr rfl (fun x hx => by ring)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]

/-- Equality case needed for the second ladder, proved from a zero squared
norm rather than imported as an analytic black box. -/
lemma eq_smul_of_inner_data (g c : SS.BitString 6 → ℂ) (z : ℂ)
    (hc : SS.innerC c c = 1)
    (hg : SS.innerC g g = (Complex.normSq z : ℂ))
    (hcg : SS.innerC c g = z) : g = fun x => z * c x := by
  have hgc : SS.innerC g c = star z := by
    have h := innerC_star c g
    rw [hcg] at h
    exact h.symm
  have hz : SS.innerC (fun x => g x - z * c x)
      (fun x => g x - z * c x) = 0 := by
    rw [innerC_sub_smul_self, hg, hgc, hcg, hc]
    push_cast [← SixQubit.star_mul_self]
    ring
  have heq := state_eq_zero_of_innerC_self_zero _ hz
  funext x
  have hx := congrFun heq x
  simpa using sub_eq_zero.mp hx

/-- **Second anti-linear ladder identity**, with no phase gauge choice. -/
theorem ladder10 (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    raise (u d) (spinJ d) = fun x => star (ball c) * c x := by
  let beta : ℂ := star (ball c)
  have h01 := ladder01 c d hc hd hcode
  have hQ := Q_expect_eq c d hnc hnd hcode (u d)
  have hn0 := ladder_norm (u d) c
  have hn1 := ladder_norm (u d) d
  have hnormeq : SS.innerC (raise (u d) (spinJ c)) (raise (u d) (spinJ c)) =
      SS.innerC (raise (u d) (spinJ d)) (raise (u d) (spinJ d)) := by
    rw [hn0, hn1]
    exact hQ
  have hnorm0 : SS.innerC (raise (u d) (spinJ c)) (raise (u d) (spinJ c)) =
      (Complex.normSq beta : ℂ) := by
    rw [h01]
    change SS.innerC (fun x => (-beta) * d x) (fun x => (-beta) * d x) = _
    rw [innerC_smul_self, hnd]
    simp
  have hnorm1 : SS.innerC (raise (u d) (spinJ d)) (raise (u d) (spinJ d)) =
      (Complex.normSq beta : ℂ) := by
    rw [← hnormeq]
    exact hnorm0
  have hanti := ladder_antisymmetric (u d) c d
  have hinner : SS.innerC c (raise (u d) (spinJ d)) = beta := by
    rw [h01] at hanti
    change SS.innerC c (raise (u d) (spinJ d)) =
      -SS.innerC d (fun x => (-beta) * d x) at hanti
    rw [innerC_smul_right, hnd] at hanti
    simpa using hanti
  exact eq_smul_of_inner_data _ _ beta hnc hnorm1 hinner

lemma raise_neg (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    raise ud (fun x => -f x) = fun x => -raise ud f x := by
  funext x
  unfold raise
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  by_cases hxi : x i = true
  · simp [hxi]
  · simp [hxi]

lemma raise_smul (ud : Fin 6 → ℂ) (z : ℂ) (f : SS.BitString 6 → ℂ) :
    raise ud (fun x => z * f x) = fun x => z * raise ud f x := by
  funext x
  unfold raise
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  by_cases hxi : x i = true
  · simp [hxi]
    ring
  · simp [hxi]

lemma spinJ_raise_spinJ (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    spinJ (raise ud (spinJ f)) = fun x => -lower ud f x := by
  have hr := raise_spinJ ud f
  have hj := congrArg spinJ hr
  have hneg : spinJ (fun x => -spinJ (lower ud f) x) =
      fun x => -lower ud f x := by
    have h := spinJ_smul (-1) (spinJ (lower ud f))
    rw [spinJ_sq] at h
    simpa using h
  exact hj.trans hneg

lemma ladder_square (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    raise ud (spinJ (raise ud (spinJ f))) = fun x => -Qact ud f x := by
  rw [spinJ_raise_spinJ, raise_neg]
  rfl

/-- `Q` acts as `r=1/6` on both logical words. -/
theorem Q_eigen (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (Qact (u d) c = fun x => (1/6 : ℂ) * c x) ∧
      (Qact (u d) d = fun x => (1/6 : ℂ) * d x) := by
  have h01 := ladder01 c d hc hd hcode
  have h10 := ladder10 c d hc hd hnc hnd hcode
  have hb := (rigid_coordinate_norms c d hc hd hnc hnd hcode).1
  have hbC : star (ball c) * ball c = (1/6 : ℂ) := by
    have hcast := congrArg (fun t : ℝ => (t : ℂ)) hb
    push_cast at hcast
    rw [← SixQubit.star_mul_self] at hcast
    exact hcast
  constructor
  · have hs := ladder_square (u d) c
    rw [h01] at hs
    have hsm := spinJ_smul (-(star (ball c))) d
    rw [hsm] at hs
    simp only [star_neg, star_star] at hs
    rw [raise_smul, h10] at hs
    funext x
    have hx := congrFun hs x
    linear_combination hx + (c x) * hbC
  · have hs := ladder_square (u d) d
    rw [h10] at hs
    have hsm := spinJ_smul (star (ball c)) c
    rw [hsm] at hs
    simp only [star_star] at hs
    rw [raise_smul, h01] at hs
    funext x
    have hx := congrFun hs x
    linear_combination hx + (d x) * hbC

end

end SixQubit.Orbit8Universal
