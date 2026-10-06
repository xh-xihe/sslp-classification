import Mathlib

/-! The exact triangle interval and path printed in the orbit-45 argument. -/

namespace MainTheory.Orbit45TrianglePolynomial

noncomputable section

structure Domain (b c s : ℝ) : Prop where
  beta_nonneg : 0 ≤ b
  gamma_nonneg : 0 ≤ c
  sigma_nonneg : 0 ≤ s
  sum : b+c+s=1/4
  beta_upper : b ≤ 1/8
  gamma_upper : c ≤ 1/8
  sigma_upper : s ≤ 1/8

def R (b c s : ℝ) : ℝ := b^2+c^2+s^2

theorem lower (b c s : ℝ) (H : Domain b c s) : 1/48 ≤ R b c s := by
  unfold R
  nlinarith [sq_nonneg (b-c),sq_nonneg (b-s),sq_nonneg (c-s),H.sum]

theorem lower_equality (b c s : ℝ) (H : Domain b c s) :
    R b c s=1/48 ↔ b=1/12 ∧ c=1/12 ∧ s=1/12 := by
  constructor
  · intro hr
    unfold R at hr
    have hbc : b=c := by
      nlinarith [sq_nonneg (b-c),sq_nonneg (b-s),sq_nonneg (c-s),H.sum]
    have hbs : b=s := by
      nlinarith [sq_nonneg (b-c),sq_nonneg (b-s),sq_nonneg (c-s),H.sum]
    exact ⟨by linarith [H.sum],by linarith [H.sum],by linarith [H.sum]⟩
  · rintro ⟨hb,hc,hs⟩
    norm_num [R,hb,hc,hs]

theorem upper (b c s : ℝ) (H : Domain b c s) : R b c s ≤ 1/32 := by
  have hb := mul_nonneg H.beta_nonneg (sub_nonneg.mpr H.beta_upper)
  have hc := mul_nonneg H.gamma_nonneg (sub_nonneg.mpr H.gamma_upper)
  have hs := mul_nonneg H.sigma_nonneg (sub_nonneg.mpr H.sigma_upper)
  unfold R
  nlinarith [H.sum]

theorem upper_equality (b c s : ℝ) (H : Domain b c s) :
    R b c s=1/32 ↔
      (b=0 ∧ c=1/8 ∧ s=1/8) ∨ (b=1/8 ∧ c=0 ∧ s=1/8) ∨
      (b=1/8 ∧ c=1/8 ∧ s=0) := by
  constructor
  · intro hr
    have hb := mul_nonneg H.beta_nonneg (sub_nonneg.mpr H.beta_upper)
    have hc := mul_nonneg H.gamma_nonneg (sub_nonneg.mpr H.gamma_upper)
    have hs := mul_nonneg H.sigma_nonneg (sub_nonneg.mpr H.sigma_upper)
    unfold R at hr
    have hbe : b*(1/8-b)=0 := by nlinarith [H.sum]
    have hce : c*(1/8-c)=0 := by nlinarith [H.sum]
    have hse : s*(1/8-s)=0 := by nlinarith [H.sum]
    have hb' : b=0 ∨ b=1/8 := (mul_eq_zero.mp hbe).imp id (by intro h; linarith)
    have hc' : c=0 ∨ c=1/8 := (mul_eq_zero.mp hce).imp id (by intro h; linarith)
    have hs' : s=0 ∨ s=1/8 := (mul_eq_zero.mp hse).imp id (by intro h; linarith)
    rcases hb' with hb' | hb' <;> rcases hc' with hc' | hc' <;>
      rcases hs' with hs' | hs' <;> simp_all <;> norm_num at *
  · rintro (⟨hb,hc,hs⟩ | ⟨hb,hc,hs⟩ | ⟨hb,hc,hs⟩) <;> norm_num [R,hb,hc,hs]

theorem interval (b c s : ℝ) (H : Domain b c s) :
    2/3 ≤ 32*R b c s ∧ 32*R b c s ≤ 1 := by
  exact ⟨by linarith [lower b c s H],by linarith [upper b c s H]⟩

def beta (r : ℝ) : ℝ := (1-r)/12
def gamma (r : ℝ) : ℝ := (2+r)/24
def sigma (r : ℝ) : ℝ := (2+r)/24

theorem path_domain (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Domain (beta r) (gamma r) (sigma r) where
  beta_nonneg := by unfold beta; linarith [hr.2]
  gamma_nonneg := by unfold gamma; linarith [hr.1]
  sigma_nonneg := by unfold sigma; linarith [hr.1]
  sum := by unfold beta gamma sigma; ring
  beta_upper := by unfold beta; linarith [hr.1]
  gamma_upper := by unfold gamma; linarith [hr.2]
  sigma_upper := by unfold sigma; linarith [hr.2]

theorem path_parameter (r : ℝ) : 32*R (beta r) (gamma r) (sigma r)=2/3+r^2/3 := by
  unfold R beta gamma sigma
  ring

end

end MainTheory.Orbit45TrianglePolynomial
