import Orbit2.SplitPhysical
import Orbit2.ExactDistance

namespace Orbit2.SplitSeed
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.HilbertBridge
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def zPauli : SS.PauliString 6 := ⟨fun _ => false, ![false,false,true,false,false,false]⟩
def xxPauli : SS.PauliString 6 := ⟨![false,false,true,true,false,false], fun _ => false⟩

theorem label_identity : label (identityPauli 6) = (fun _ => 0) := by
  funext i; rfl
theorem label_z : label zPauli = splitZ := by
  funext i; fin_cases i <;> rfl
theorem label_xx : label xxPauli = splitXX := by
  funext i; fin_cases i <;> rfl
theorem z_weight : zPauli.wt = 1 := by decide +kernel
theorem xx_weight : xxPauli.wt = 2 := by decide +kernel

noncomputable def encoder (a b : ℝ) (hab : a^2+b^2=1) : Encoder where
  psi := words (code a b)
  orthonormal := by
    intro j k
    have h := compression (code a b) (identityPauli 6) j k
    rw [pauliAct_identity, label_identity, operator_zero, Matrix.mul_one,
      code_isometry a b hab] at h
    simpa [Matrix.one_apply] using h
  detects := by
    intro p hp
    have hw : weight (label p) = p.wt := label_weight p
    refine ⟨(scalar a b (label p) : ℂ), ?_⟩
    intro j k
    rw [compression, code_KL a b (label p) (by rw [hw]; exact hp)]
    simp [Matrix.smul_apply, Matrix.one_apply]
  logicalZ := by
    intro j
    funext x
    have h := pauli_action
      (⟨fun _ => false, ![false,false,true,true,true,true]⟩ : SS.PauliString 6)
      (words (code a b) j) x
    have hl : label (⟨fun _ => false, ![false,false,true,true,true,true]⟩ : SS.PauliString 6) =
        ![0,0,3,3,3,3] := by funext i; fin_cases i <;> rfl
    rw [hl] at h
    have hm := congrArg (fun M => M (bitsEquiv 6 x) j) (code_logical a b)
    simpa [words, Matrix.mul_apply] using h.symm.trans hm

theorem scalar_labels (a b : ℝ) (p : SS.PauliString 6) :
    scalar a b (label p) = if p = identityPauli 6 then a^2+b^2 else
      if p = zPauli then a^2-b^2 else if p = xxPauli then 2*a*b else 0 := by
  have hi : label p = (fun _ => 0) ↔ p = identityPauli 6 := by
    rw [← label_identity]; exact label_injective.eq_iff
  have hz : label p = splitZ ↔ p = zPauli := by
    rw [← label_z]; exact label_injective.eq_iff
  have hx : label p = splitXX ↔ p = xxPauli := by
    rw [← label_xx]; exact label_injective.eq_iff
  simp only [scalar, hi, hz, hx]

theorem trace_low (a b : ℝ) (hab : a^2+b^2=1) (p : SS.PauliString 6) (hp : p.wt ≤ 2) :
    SS.MacWilliams.trProj (encoder a b hab).psi p = 2*(scalar a b (label p) : ℂ) := by
  unfold SS.MacWilliams.trProj
  change (∑ j, SS.innerC (words (code a b) j) (SS.pauliAct p (words (code a b) j))) = _
  have hw : weight (label p) = p.wt := label_weight p
  simp_rw [compression, code_KL a b (label p) (by rw [hw]; exact hp)]
  simp [Matrix.smul_apply]

theorem enumerator_low (a b : ℝ) (hab : a^2+b^2=1) (w : ℕ) (hw : w ≤ 2) :
    (encoder a b hab).A w = ∑ p ∈ Finset.univ.filter (fun p : SS.PauliString 6 => p.wt = w),
      scalar a b (label p)^2 := by
  unfold Encoder.A SS.MacWilliams.Aco
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hpw := (Finset.mem_filter.mp hp).2
  rw [trace_low a b hab p (by omega)]
  norm_num [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem enumerator_one (a b : ℝ) (hab : a^2+b^2=1) :
    (encoder a b hab).A 1 = (a^2-b^2)^2 := by
  rw [enumerator_low a b hab 1 (by omega)]
  have he : ∀ p : SS.PauliString 6, p.wt=1 →
      scalar a b (label p)^2 = if p=zPauli then (a^2-b^2)^2 else 0 := by
    intro p hp
    have h0 : p ≠ identityPauli 6 := by intro h; subst p; simp [identityPauli,SS.PauliString.wt] at hp
    have hx : p ≠ xxPauli := by intro h; subst p; rw [xx_weight] at hp; omega
    simp [scalar_labels, h0, hx]
  rw [Finset.sum_congr rfl (fun p hp => he p (Finset.mem_filter.mp hp).2)]
  simp [z_weight]

theorem enumerator_two (a b : ℝ) (hab : a^2+b^2=1) :
    (encoder a b hab).A 2 = (2*a*b)^2 := by
  rw [enumerator_low a b hab 2 (by omega)]
  have he : ∀ p : SS.PauliString 6, p.wt=2 →
      scalar a b (label p)^2 = if p=xxPauli then (2*a*b)^2 else 0 := by
    intro p hp
    have h0 : p ≠ identityPauli 6 := by intro h; subst p; simp [identityPauli,SS.PauliString.wt] at hp
    have hz : p ≠ zPauli := by intro h; subst p; rw [z_weight] at hp; omega
    simp [scalar_labels, h0, hz]
  rw [Finset.sum_congr rfl (fun p hp => he p (Finset.mem_filter.mp hp).2)]
  simp [xx_weight]

theorem enumerator_family (a b : ℝ) (hab : a^2+b^2=1) :
    (fun w : Fin 7 => (encoder a b hab).A w.val) = enumeratorLine ((a^2-b^2)^2) := by
  have hs : (encoder a b hab).A 1 + (encoder a b hab).A 2 = 1 := by
    rw [enumerator_one, enumerator_two]
    calc
      _ = (a^2+b^2)^2 := by ring
      _ = 1 := by rw [hab]; norm_num
  have hshadow := (encoder a b hab).shadow
  have hnonneg := (encoder a b hab).A_nonneg 3
  have hz : (encoder a b hab).A 3 = 0 := by linarith
  have hf : (encoder a b hab).A 1 + (encoder a b hab).A 2 + (encoder a b hab).A 3 = 1 := by
    linarith
  have he := ((encoder a b hab).enumerator_of_A3_zero hf hz).2.2
  rwa [enumerator_one] at he

/-- Parameter coverage uses exact square-root identities, including both endpoints. -/
theorem parameters (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∃ a b : ℝ, a^2+b^2=1 ∧ (a^2-b^2)^2=α := by
  have hs0 := Real.sqrt_nonneg α
  have hs1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr h1
  have ha := Real.sq_sqrt (show 0 ≤ (1+Real.sqrt α)/2 by linarith)
  have hb := Real.sq_sqrt (show 0 ≤ (1-Real.sqrt α)/2 by linarith)
  have hs := Real.sq_sqrt h0
  refine ⟨Real.sqrt ((1+Real.sqrt α)/2), Real.sqrt ((1-Real.sqrt α)/2),
    by linarith, ?_⟩
  have hd : (Real.sqrt ((1+Real.sqrt α)/2))^2 -
      (Real.sqrt ((1-Real.sqrt α)/2))^2 = Real.sqrt α := by linarith
  rw [hd, hs]

/-- Unconditional attainment for genuine isometric six-qubit orbit-2 encoders. -/
theorem every_parameter_attained (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∃ V : Encoder, (fun w : Fin 7 => V.A w.val) = enumeratorLine α := by
  obtain ⟨a,b,hab,hα⟩ := parameters α h0 h1
  refine ⟨encoder a b hab, ?_⟩
  rw [enumerator_family, hα]

theorem every_parameter_attained_exact_distance (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∃ V : Encoder, (fun w : Fin 7 => V.A w.val) = enumeratorLine α ∧
      ¬ SS.HasDistance V.psi 4 := by
  obtain ⟨V,hV⟩ := every_parameter_attained α h0 h1
  exact ⟨V,hV,V.not_distance_four_of_line α h0 hV⟩

end Orbit2.SplitSeed
