import MainTheory.Orbit31PhaseRatios
import MainTheory.Orbit31SignedSupport

/-! Canonical cross rows imply the necessary support and phase constraints.
This algebra treats zero amplitudes explicitly and uses no final no-go.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31SupportSemantics (maskSet mem_maskSet)
open MainTheory.SignedPhaseSupport
open scoped BigOperators
noncomputable section

structure CrossSystem (c d : Fin 16 → ℂ) : Prop where
  reciprocal : ∀ i e, star (c (A e)) * d (B i e) = star (c (B i e)) * d (A e)
  weight_one : ∀ i, (∑ e : Fin 4, star (c (A e)) * d (B i e)) = 0
  rectangles : ∀ r k,
    let i := (rowPairs r).1
    let j := (rowPairs r).2
    let e := (colPairs k).1
    let f := (colPairs k).2
    star (c (B i e)) * d (B j f) + star (c (B j f)) * d (B i e) +
      star (c (B i f)) * d (B j e) + star (c (B j e)) * d (B i f) = 0

def AmplitudeSupport (mask : ℕ) (c : Fin 16 → ℂ) : Prop :=
  ∀ v, active mask v = true ↔ c v ≠ 0

theorem vertical_phase {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (i : Fin 3) (e : Fin 4)
    (ha : c (A e) ≠ 0) (hb : c (B i e) ≠ 0) :
    sigma c d (A e) = sigma c d (B i e) :=
  equal_from_reciprocal hp ha hb (hs.reciprocal i e)

theorem weight_one_phase_sum {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (i : Fin 3) :
    (∑ e : Fin 4, sigma c d (B i e) * c (A e) * c (B i e)) = 0 := by
  have h := congrArg star (hs.weight_one i)
  simp only [star_sum,star_mul,star_star,star_zero] at h
  simp_rw [reconstruct hp] at h
  simpa only [mul_comm,mul_left_comm,mul_assoc] using h

theorem rectangle_phase {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (r : Fin 3) (k : Fin 6) :
    let i := (rowPairs r).1
    let j := (rowPairs r).2
    let e := (colPairs k).1
    let f := (colPairs k).2
    (sigma c d (B i e) + sigma c d (B j f)) * c (B i e) * c (B j f) +
      (sigma c d (B i f) + sigma c d (B j e)) * c (B i f) * c (B j e) = 0 := by
  have h := congrArg star (hs.rectangles r k)
  dsimp only at h ⊢
  simp only [star_add,star_mul,star_star,star_zero] at h
  simp_rw [reconstruct hp] at h
  linear_combination h

theorem zero_of_inactive_pair {c : Fin 16 → ℂ} {mask : ℕ}
    (hm : AmplitudeSupport mask c) {a b : Fin 16}
    (h : ¬ (active mask a && active mask b) = true) : c a * c b = 0 := by
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  exact False.elim (h (by rw [(hm a).mpr ha,(hm b).mpr hb]; rfl))

theorem no_singleton {c d : Fin 16 → ℂ} {mask : ℕ}
    (hp : EqualProbabilities c d) (hs : CrossSystem c d)
    (hm : AmplitudeSupport mask c) : NoSingleton mask := by
  intro i hi
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hi
  have hz : ∀ f, f ∉ overlaps mask i → sigma c d (B i f) * c (A f) * c (B i f) = 0 := by
    intro f hf
    have hpair : ¬ (active mask (A f) && active mask (B i f)) = true := by
      intro h
      exact hf (by simpa only [overlaps,Finset.mem_filter,Finset.mem_univ,
        true_and,Bool.and_eq_true] using h)
    rw [mul_assoc,zero_of_inactive_pair hm hpair,mul_zero]
  have hsum : (∑ f ∈ overlaps mask i, sigma c d (B i f) * c (A f) * c (B i f)) = 0 := by
    calc
      _ = ∑ f : Fin 4, sigma c d (B i f) * c (A f) * c (B i f) :=
        Finset.sum_subset (Finset.subset_univ _) (fun f _ hf => hz f hf)
      _ = 0 := weight_one_phase_sum hp hs i
  rw [he,Finset.sum_singleton] at hsum
  have hmem : e ∈ overlaps mask i := by rw [he]; simp
  simp only [overlaps,Finset.mem_filter,Finset.mem_univ,true_and,Bool.and_eq_true] at hmem
  have ha := (hm (A e)).mp hmem.1
  have hb := (hm (B i e)).mp hmem.2
  exact (mul_ne_zero (mul_ne_zero (nonzero hp hb) ha) hb) hsum

theorem opposite_left {c d : Fin 16 → ℂ} {mask : ℕ}
    (hp : EqualProbabilities c d) (hs : CrossSystem c d)
    (hm : AmplitudeSupport mask c) (r : Fin 3) (k : Fin 6)
    (hl : (active mask (B (rowPairs r).1 (colPairs k).1) &&
      active mask (B (rowPairs r).2 (colPairs k).2)) = true)
    (hr : ¬ (active mask (B (rowPairs r).1 (colPairs k).2) &&
      active mask (B (rowPairs r).2 (colPairs k).1)) = true) :
    sigma c d (B (rowPairs r).1 (colPairs k).1) =
      -sigma c d (B (rowPairs r).2 (colPairs k).2) := by
  have h := rectangle_phase hp hs r k
  dsimp only at h
  rw [mul_assoc (sigma c d (B (rowPairs r).1 (colPairs k).2) +
      sigma c d (B (rowPairs r).2 (colPairs k).1)),zero_of_inactive_pair hm hr,
    mul_zero,add_zero] at h
  have hactive := hl
  simp only [Bool.and_eq_true] at hactive
  have ha := (hm _).mp hactive.1
  have hb := (hm _).mp hactive.2
  have hab : sigma c d (B (rowPairs r).1 (colPairs k).1) +
      sigma c d (B (rowPairs r).2 (colPairs k).2) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb)).resolve_right ha
  exact eq_neg_of_add_eq_zero_left hab

theorem opposite_right {c d : Fin 16 → ℂ} {mask : ℕ}
    (hp : EqualProbabilities c d) (hs : CrossSystem c d)
    (hm : AmplitudeSupport mask c) (r : Fin 3) (k : Fin 6)
    (hr : (active mask (B (rowPairs r).1 (colPairs k).2) &&
      active mask (B (rowPairs r).2 (colPairs k).1)) = true)
    (hl : ¬ (active mask (B (rowPairs r).1 (colPairs k).1) &&
      active mask (B (rowPairs r).2 (colPairs k).2)) = true) :
    sigma c d (B (rowPairs r).1 (colPairs k).2) =
      -sigma c d (B (rowPairs r).2 (colPairs k).1) := by
  have h := rectangle_phase hp hs r k
  dsimp only at h
  rw [mul_assoc (sigma c d (B (rowPairs r).1 (colPairs k).1) +
      sigma c d (B (rowPairs r).2 (colPairs k).2)),zero_of_inactive_pair hm hl,
    mul_zero,zero_add] at h
  have hactive := hr
  simp only [Bool.and_eq_true] at hactive
  have ha := (hm _).mp hactive.1
  have hb := (hm _).mp hactive.2
  have hab : sigma c d (B (rowPairs r).1 (colPairs k).2) +
      sigma c d (B (rowPairs r).2 (colPairs k).1) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb)).resolve_right ha
  exact eq_neg_of_add_eq_zero_left hab

theorem graph_assignment {c d : Fin 16 → ℂ} {mask : ℕ}
    (hp : EqualProbabilities c d) (hs : CrossSystem c d)
    (hm : AmplitudeSupport mask c) :
    Assignment (maskSet mask) (edges mask) (sigma c d) := by
  constructor
  · intro v hv
    exact nonzero hp ((hm v).mp ((mem_maskSet mask v).mp hv))
  · intro edge he
    rcases List.mem_append.mp he with he|he
    · rcases List.mem_flatMap.mp he with ⟨i,_,he⟩
      rcases List.mem_flatMap.mp he with ⟨e,_,he⟩
      split_ifs at he with hpos
      · simp only [List.mem_singleton] at he
        subst edge
        simp only [Bool.and_eq_true] at hpos
        exact vertical_phase hp hs i e ((hm _).mp hpos.1) ((hm _).mp hpos.2)
      · simp at he
    · rcases List.mem_flatMap.mp he with ⟨r,_,he⟩
      rcases List.mem_flatMap.mp he with ⟨k,_,he⟩
      dsimp only at he
      split_ifs at he with hl hr
      · simp only [List.mem_singleton] at he
        subst edge
        simp only [Bool.and_eq_true,Bool.not_eq_true_eq_eq_false] at hl
        exact opposite_left hp hs hm r k
          (by simpa only [Bool.and_eq_true] using hl.1) (by rw [hl.2]; decide)
      · simp only [List.mem_singleton] at he
        subst edge
        simp only [Bool.and_eq_true,Bool.not_eq_true_eq_eq_false] at hr
        exact opposite_right hp hs hm r k
          (by simpa only [Bool.and_eq_true] using hr.1) (by rw [hr.2]; decide)
      · simp at he

theorem graph_compatible {c d : Fin 16 → ℂ} {mask : ℕ}
    (hp : EqualProbabilities c d) (hs : CrossSystem c d)
    (hm : AmplitudeSupport mask c) : GraphCompatible mask :=
  ⟨sigma c d,graph_assignment hp hs hm⟩

end
end MainTheory.Orbit31CanonicalPhase
