import MainTheory.FiniteKrausChannel

/-! # Necessity of the Knill--Laflamme equations

An exact finite Kraus recovery on all encoded operators forces every composite
Kraus operator to be a scalar multiple of the encoder. Trace preservation of
the recovery then gives the scalar compression equations.
-/

namespace MainTheory.FiniteKrausChannel

noncomputable section

open scoped Matrix ComplexConjugate

variable {T A I J H L : Type*} [Fintype T] [Fintype I] [Fintype J]
  [Fintype H] [Fintype L]

private theorem zero_of_sum_mul_conj_zero (f : T → ℂ)
    (h : ∑ t, f t * conj (f t) = 0) (t : T) : f t = 0 := by
  have hr : ∑ t, Complex.normSq (f t) = 0 := by
    simpa only [Complex.mul_conj, ← Complex.ofReal_sum, Complex.ofReal_re, Complex.zero_re] using
      congrArg Complex.re h
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (f i))).mp hr
      t (Finset.mem_univ _))

private theorem rank_one_gram_cross_zero (f : T → A → ℂ) (g : A → ℂ)
    (h : ∀ a b, ∑ t, f t a * conj (f t b) = g a * conj (g b))
    (a b : A) (t : T) : g a * f t b - g b * f t a = 0 := by
  apply zero_of_sum_mul_conj_zero (fun s => g a * f s b - g b * f s a) _ t
  have he (s : T) :
      (g a * f s b - g b * f s a) * conj (g a * f s b - g b * f s a) =
        (g a * conj (g a)) * (f s b * conj (f s b)) -
        (g a * conj (g b)) * (f s b * conj (f s a)) -
        (g b * conj (g a)) * (f s a * conj (f s b)) +
        (g b * conj (g b)) * (f s a * conj (f s a)) := by
    simp only [map_sub, map_mul]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h]
  ring

/-- A finite Kraus representation of a rank-one Choi matrix has proportional
Kraus vectors. This includes the zero vector and empty finite index cases. -/
theorem proportional_of_rank_one_gram (f : T → A → ℂ) (g : A → ℂ)
    (h : ∀ a b, ∑ t, f t a * conj (f t b) = g a * conj (g b)) :
    ∃ c : T → ℂ, ∀ t a, f t a = c t * g a := by
  classical
  by_cases hg : ∃ a, g a ≠ 0
  · obtain ⟨a, ha⟩ := hg
    refine ⟨fun t => f t a / g a, fun t b => ?_⟩
    have hc := rank_one_gram_cross_zero f g h a b t
    field_simp
    linear_combination hc
  · refine ⟨fun _ => 0, fun t a => ?_⟩
    have hz : g a = 0 := by
      by_contra hne
      exact hg ⟨a, hne⟩
    have hs : ∑ t, f t a * conj (f t a) = 0 := by rw [h, hz, zero_mul]
    simpa using zero_of_sum_mul_conj_zero (fun t => f t a) hs t

omit [Fintype H] in
/-- Equality on all matrix units determines the rank-one Choi Gram matrix. -/
theorem proportional_of_action_eq [DecidableEq L]
    (F : T → Matrix H L ℂ) (V : Matrix H L ℂ)
    (h : ∀ X : Matrix L L ℂ, action F X = V * X * V.conjTranspose) :
    ∃ c : T → ℂ, ∀ t, F t = c t • V := by
  classical
  have hgram (a b : H × L) :
      ∑ t, F t a.1 a.2 * conj (F t b.1 b.2) =
        V a.1 a.2 * conj (V b.1 b.2) := by
    have he := congrArg (fun M : Matrix H H ℂ => M a.1 b.1)
      (h (Matrix.single a.2 b.2 1))
    simpa [action, Matrix.sum_apply, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply, ite_and, Finset.sum_mul, Finset.mul_sum] using he
  obtain ⟨c, hc⟩ := proportional_of_rank_one_gram
    (fun (t : T) (a : H × L) => F t a.1 a.2) (fun a : H × L => V a.1 a.2) hgram
  refine ⟨c, fun t => ?_⟩
  ext a b
  exact hc t (a, b)

/-- Every composite error/recovery Kraus operator acts by one scalar on the
entire code, with the same scalar for all logical basis vectors. -/
theorem composite_proportional_of_recovers [DecidableEq L]
    (V : Matrix H L ℂ) (E : I → Matrix H H ℂ) (R : J → Matrix H H ℂ)
    (h : Recovers V E R) :
    ∃ c : J × I → ℂ, ∀ j i, R j * E i * V = c (j, i) • V := by
  have heq (X : Matrix L L ℂ) :
      action (fun p : J × I => R p.1 * E p.2 * V) X = V * X * V.conjTranspose := by
    have he := h X
    rw [action_comp] at he
    simpa only [action, Matrix.conjTranspose_mul, Matrix.mul_assoc] using he
  obtain ⟨c, hc⟩ := proportional_of_action_eq
    (fun p : J × I => R p.1 * E p.2 * V) V heq
  exact ⟨c, fun j i => hc (j, i)⟩

/-- An actual trace-preserving Kraus recovery implies Knill--Laflamme. The
necessity direction does not require a trace-preserving hypothesis on E. -/
theorem knillLaflamme_of_recovers [DecidableEq H] [DecidableEq L]
    (V : Matrix H L ℂ) (E : I → Matrix H H ℂ) (R : J → Matrix H H ℂ)
    (hV : V.conjTranspose * V = 1) (hR : TracePreserving R)
    (hrec : Recovers V E R) : KnillLaflamme V E := by
  classical
  obtain ⟨c, hc⟩ := composite_proportional_of_recovers V E R hrec
  refine ⟨fun i j => ∑ t, conj (c (t, i)) * c (t, j), fun i j => ?_⟩
  calc
    V.conjTranspose * (E i).conjTranspose * E j * V =
        V.conjTranspose * (E i).conjTranspose *
          (∑ t, (R t).conjTranspose * R t) * E j * V := by
      rw [hR, Matrix.mul_one]
    _ = ∑ t, (R t * E i * V).conjTranspose * (R t * E j * V) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    _ = ∑ t, (conj (c (t, i)) * c (t, j)) • (1 : Matrix L L ℂ) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hc t i, hc t j, Matrix.conjTranspose_smul]
      simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV, mul_comm]
    _ = (∑ t, conj (c (t, i)) * c (t, j)) • (1 : Matrix L L ℂ) := by
      rw [Finset.sum_smul]

end

end MainTheory.FiniteKrausChannel
