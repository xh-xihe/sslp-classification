import MainTheory.Orbit45PhysicalPrintedRows

/-! The actual diagonal and cross equations force the literal fixed mass,
triangle probability domain, and the exact meaning of its positive stratum. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PhysicalProbabilityDomain
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open SixQubit.Orbit45Support
noncomputable section
variable (c d : SS.State 6 ℂ)
  (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hkl : SS.HasDistance ![c,d] 3)
include hc hd hnc hnd hkl
theorem matching_probabilities (i : Fin 10) : p c i=q d i := by
  obtain ⟨hp,hq⟩ := physical_normal c d hc hd hnc hnd hkl
  rw [hp,hq]
theorem product_magnitude (i : Fin 10) : ‖z c d i‖=p c i :=
  Orbit45PrintedAlgebra.cross_magnitude _ _ (matching_probabilities c d hc hd hnc hnd hkl i)
theorem fixed_alpha : p c 3=1/8 := by
  have hp4 := congrFun (physical_normal c d hc hd hnc hnd hkl).1 4
  change p c 4=1/4-p c 3 at hp4
  have hz4 := product_magnitude c d hc hd hnc hnd hkl 4
  rw [hp4] at hz4
  exact (Orbit45PrintedConsequences.fixed_mass (p c 3) (z c d)
    (physical_walsh c d hc hd hkl) (product_magnitude c d hc hd hnc hnd hkl 3) hz4).1
theorem physical_probabilities :
    p c=Orbit45PrintedMoments.pattern (1/8) (p c 1) (p c 0) ∧
    q d=Orbit45PrintedMoments.pattern (1/8) (p c 1) (p c 0) := by
  have he := physical_normal c d hc hd hnc hnd hkl
  rw [fixed_alpha c d hc hd hnc hnd hkl] at he
  exact he
theorem triangle_domain : Orbit45TrianglePolynomial.Domain (p c 1) (p c 0) (p c 2) := by
  have hp2 := congrFun (physical_probabilities c d hc hd hnc hnd hkl).1 2
  change p c 2=1/4-p c 1-p c 0 at hp2
  have hz2 := congrFun (physical_cross_kernel c d hc hd hkl) 2
  change z c d 2= -z c d 1-z c d 0 at hz2
  have hsum : z c d 2= -(z c d 1+z c d 0) := by linear_combination hz2
  have hs := product_magnitude c d hc hd hnc hnd hkl 2
  rw [hsum,norm_neg] at hs
  have ht : p c 1+p c 0+p c 2=1/4 := by linarith only [hp2]
  obtain ⟨hb,hg,hs0,hbu,hgu,hsu⟩ := Orbit45PrintedConsequences.triangle_bounds
    (p c 1) (p c 0) (p c 2) (z c d 1) (z c d 0)
    (product_magnitude c d hc hd hnc hnd hkl 1)
    (product_magnitude c d hc hd hnc hnd hkl 0) hs ht
  exact ⟨hb,hg,hs0,ht,hbu,hgu,hsu⟩
theorem positive_stratum :
    0<p c 1*p c 0*p c 2 ↔
      (∀ i : Fin 10, c (bottom i) ≠ 0) ∧ (∀ i : Fin 10, d (top i) ≠ 0) := by
  have hp := (physical_probabilities c d hc hd hnc hnd hkl).1
  have hq := (physical_probabilities c d hc hd hnc hnd hkl).2
  have hdomain := triangle_domain c d hc hd hnc hnd hkl
  have hp2 := congrFun hp 2
  change p c 2=1/4-p c 1-p c 0 at hp2
  constructor
  · intro hpos
    have hb : 0<p c 1 := by
      have h0 : p c 1 ≠ 0 := by intro he; rw [he,zero_mul,zero_mul] at hpos; exact lt_irrefl _ hpos
      exact lt_of_le_of_ne hdomain.beta_nonneg (Ne.symm h0)
    have hg : 0<p c 0 := by
      have h0 : p c 0 ≠ 0 := by intro he; rw [he,mul_zero,zero_mul] at hpos; exact lt_irrefl _ hpos
      exact lt_of_le_of_ne hdomain.gamma_nonneg (Ne.symm h0)
    have hs : 0<p c 2 := by
      have h0 : p c 2 ≠ 0 := by intro he; rw [he,mul_zero] at hpos; exact lt_irrefl _ hpos
      exact lt_of_le_of_ne hdomain.sigma_nonneg (Ne.symm h0)
    have hall : ∀ i : Fin 10, 0<Orbit45PrintedMoments.pattern (1/8) (p c 1) (p c 0) i := by
      intro i
      fin_cases i <;> norm_num [Orbit45PrintedMoments.pattern] <;> linarith
    constructor
    · intro i
      apply Complex.normSq_pos.mp
      change 0<p c i
      rw [hp]
      exact hall i
    · intro i
      apply Complex.normSq_pos.mp
      change 0<q d i
      rw [hq]
      exact hall i
  · rintro ⟨hbottom,_⟩
    exact mul_pos (mul_pos (Complex.normSq_pos.mpr (hbottom 1))
      (Complex.normSq_pos.mpr (hbottom 0))) (Complex.normSq_pos.mpr (hbottom 2))
end
end MainTheory.Orbit45PhysicalProbabilityDomain
