import MainTheory.DiagonalProofSteps
import SS.HilbertKL

/-! Common-mean phase replacement for arbitrary supports and distributions. -/
namespace MainTheory.CommonMeanReplacement

open scoped BigOperators
open Matrix
noncomputable section
variable {n : ℕ} {ι : Type*}

def meanDot (h mu : Fin n → ℝ) : ℝ := ∑ j, h j * mu j

theorem average (T : Finset (SS.BitString n)) (p : SS.BitString n → ℝ)
    (h mu : Fin n → ℝ)
    (hm : ∀ j, ∑ x ∈ T, p x * QECC.bitReal (x j) = mu j) :
    (∑ x ∈ T, p x * QECC.realSupportWeight h x) = meanDot h mu := by
  simp only [QECC.realSupportWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold meanDot
  apply Finset.sum_congr rfl
  intro j _
  rw [← hm j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem support_value (T : Finset (SS.BitString n)) (p : SS.BitString n → ℝ)
    (h mu : Fin n → ℝ) (hn : ∑ x ∈ T, p x = 1)
    (hm : ∀ j, ∑ x ∈ T, p x * QECC.bitReal (x j) = mu j)
    (hc : ∀ x ∈ T, ∀ y ∈ T, QECC.realSupportWeight h x = QECC.realSupportWeight h y)
    (x : SS.BitString n) (hx : x ∈ T) : QECC.realSupportWeight h x = meanDot h mu := by
  calc
    QECC.realSupportWeight h x = (∑ y ∈ T, p y) * QECC.realSupportWeight h x := by rw [hn, one_mul]
    _ = ∑ y ∈ T, p y * QECC.realSupportWeight h y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hc x hx y hy]
    _ = meanDot h mu := average T p h mu hm

def supportedUnion (T : ι → Finset (SS.BitString n)) : Submodule ℂ (SS.State n ℂ) where
  carrier := fun f => ∀ x, (¬ ∃ i, x ∈ T i) → f x = 0
  zero_mem' := by intro x _; rfl
  add_mem' := by intro f g hf hg x hx; simp [hf x hx, hg x hx]
  smul_mem' := by intro c f hf x hx; simp [hf x hx]

theorem replacement_on_supported_union
    (T : ι → Finset (SS.BitString n)) (p : ι → SS.BitString n → ℝ)
    (t delta mu : Fin n → ℝ)
    (hn : ∀ i, ∑ x ∈ T i, p i x = 1)
    (hm : ∀ i j, ∑ x ∈ T i, p i x * QECC.bitReal (x j) = mu j)
    (hc : ∀ i x, x ∈ T i → ∀ y, y ∈ T i →
      QECC.realSupportWeight delta x = QECC.realSupportWeight delta y)
    (f : SS.State n ℂ) (hf : f ∈ supportedUnion T) :
    (QECC.diagonalGate (fun j => ((t j + delta j : ℝ) : QECC.LocalPhase))) *ᵥ f =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (meanDot delta mu : ℂ)) •
        ((QECC.diagonalGate (fun j => (t j : QECC.LocalPhase))) *ᵥ f) := by
  classical
  funext x
  simp only [QECC.diagonalGate, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hx : ∃ i, x ∈ T i
  · obtain ⟨i, hxi⟩ := hx
    have hd := support_value (T i) (p i) delta mu (hn i) (hm i) (hc i) x hxi
    have ha : QECC.realSupportWeight (fun j => t j + delta j) x =
        QECC.realSupportWeight t x + QECC.realSupportWeight delta x := by
      simp [QECC.realSupportWeight, add_mul, Finset.sum_add_distrib]
    rw [QECC.supportPhase_coe_real, ha, hd, AddCircle.coe_add, AddCircle.toCircle_add]
    simp only [Circle.coe_mul]
    simp_rw [QECC.supportPhase_coe_real, MainTheory.DiagonalProofSteps.real_circle_exp]
    ring
  · rw [hf x hx]
    simp

theorem replacement_on_direct_sum
    (T : ι → Finset (SS.BitString n)) (p : ι → SS.BitString n → ℝ)
    (E : ι → Submodule ℂ (SS.State n ℂ))
    (hE : ∀ i f, f ∈ E i → ∀ x, x ∉ T i → f x = 0)
    (t delta mu : Fin n → ℝ)
    (hn : ∀ i, ∑ x ∈ T i, p i x = 1)
    (hm : ∀ i j, ∑ x ∈ T i, p i x * QECC.bitReal (x j) = mu j)
    (hc : ∀ i x, x ∈ T i → ∀ y, y ∈ T i →
      QECC.realSupportWeight delta x = QECC.realSupportWeight delta y)
    (f : SS.State n ℂ) (hf : f ∈ ⨆ i, E i) :
    (QECC.diagonalGate (fun j => ((t j + delta j : ℝ) : QECC.LocalPhase))) *ᵥ f =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (meanDot delta mu : ℂ)) •
        ((QECC.diagonalGate (fun j => (t j : QECC.LocalPhase))) *ᵥ f) := by
  apply replacement_on_supported_union T p t delta mu hn hm hc f
  have he : (⨆ i, E i) ≤ supportedUnion T := by
    apply iSup_le
    intro i f hfi x hx
    exact hE i f hfi x (fun hxi => hx ⟨i, hxi⟩)
  exact he hf

end
end MainTheory.CommonMeanReplacement
