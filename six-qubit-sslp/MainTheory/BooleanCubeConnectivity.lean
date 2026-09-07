import Mathlib

/-!
Positive superlevel sets of a linear functional on a Boolean cube are connected,
also after fixing arbitrary coordinates.  Adjacency is an actual one-coordinate
change; no abstract graph-connectivity hypothesis is assumed.
-/

namespace MainTheory.BooleanCube

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sign (b : Bool) : ℝ := if b then -1 else 1

def score (a : ι → ℝ) (c : ℝ) (x : ι → Bool) : ℝ :=
  c + ∑ i, a i * sign (x i)

def supportGraph (Q : (ι → Bool) → Prop) (f : (ι → Bool) → ℝ) :
    SimpleGraph {x // Q x ∧ 0 < f x} where
  Adj x y := ∃ i, x.val i ≠ y.val i ∧ ∀ j, j ≠ i → x.val j = y.val j
  symm := by
    rintro x y ⟨i, hi, h⟩
    exact ⟨i, Ne.symm hi, fun j hj => (h j hj).symm⟩
  loopless := by rintro x ⟨i, hi, _⟩; exact hi rfl

theorem supportGraph_preconnected_of_coordinate_maximum
    (Q : (ι → Bool) → Prop) (f : (ι → Bool) → ℝ) (m : ι → Bool)
    (hm : Q m ∧ 0 < f m)
    (hQ : ∀ x i, Q x → Q (Function.update x i (m i)))
    (hf : ∀ x i, Q x → f x ≤ f (Function.update x i (m i))) :
    (supportGraph Q f).Preconnected := by
  let v : {x // Q x ∧ 0 < f x} := ⟨m, hm⟩
  have path : ∀ s : Finset ι, ∀ x : {x // Q x ∧ 0 < f x},
      (∀ i, i ∉ s → x.val i = m i) → (supportGraph Q f).Reachable x v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      have : x = v := Subtype.ext (funext (fun i => hx i (by simp)))
      subst x
      exact SimpleGraph.Reachable.rfl
    | @insert i s his ih =>
      intro x hx
      let y : {x // Q x ∧ 0 < f x} :=
        ⟨Function.update x.val i (m i), hQ _ _ x.property.1,
          lt_of_lt_of_le x.property.2 (hf _ _ x.property.1)⟩
      have hxy : (supportGraph Q f).Reachable x y := by
        by_cases hi : x.val i = m i
        · have : x = y := by
            apply Subtype.ext
            funext j
            by_cases hji : j = i
            · subst j; simp [y, hi]
            · simp [y, Function.update_of_ne hji]
          rw [← this]
        · apply SimpleGraph.Adj.reachable
          refine ⟨i, ?_, ?_⟩
          · simpa [y] using hi
          · intro j hji
            simp [y, Function.update_of_ne hji]
      apply hxy.trans (ih y ?_)
      intro j hj
      by_cases hji : j = i
      · subst j; simp [y]
      · simpa [y, Function.update_of_ne hji] using hx j (by simp [hj, hji])
  intro x y
  exact (path Finset.univ x (by simp)).trans (path Finset.univ y (by simp)).symm

def preferred (a : ι → ℝ) (i : ι) : Bool := decide (a i < 0)

omit [Fintype ι] [DecidableEq ι] in
theorem preferred_max (a : ι → ℝ) (i : ι) (b : Bool) :
    a i * sign b ≤ a i * sign (preferred a i) := by
  unfold preferred sign
  by_cases h : a i < 0 <;> cases b <;> simp [h] <;> linarith

theorem score_update (a : ι → ℝ) (c : ℝ) (x : ι → Bool) (i : ι) (b : Bool) :
    score a c (Function.update x i b) - score a c x =
      a i * sign b - a i * sign (x i) := by
  unfold score
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i),
    Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  have heq : (∑ j ∈ Finset.univ \ {i}, a j * sign (Function.update x i b j)) =
      ∑ j ∈ Finset.univ \ {i}, a j * sign (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
    rw [Function.update_of_ne hj.2]
  rw [heq, Function.update_self]
  ring

def slice (fixed : Finset ι) (bits : ι → Bool) (x : ι → Bool) : Prop :=
  ∀ i ∈ fixed, x i = bits i

def sliceMaximum (a : ι → ℝ) (fixed : Finset ι) (bits : ι → Bool) : ι → Bool :=
  fun i => if i ∈ fixed then bits i else preferred a i

omit [Fintype ι] in
theorem sliceMaximum_mem (a : ι → ℝ) (fixed : Finset ι) (bits : ι → Bool) :
    slice fixed bits (sliceMaximum a fixed bits) := by
  intro i hi
  simp [sliceMaximum, hi]

theorem sliceMaximum_score (a : ι → ℝ) (c : ℝ) (fixed : Finset ι)
    (bits x : ι → Bool) (hx : slice fixed bits x) :
    score a c x ≤ score a c (sliceMaximum a fixed bits) := by
  unfold score
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ fixed
  · simp [sliceMaximum, hi, hx i hi]
  · simpa [sliceMaximum, hi] using preferred_max a i (x i)

theorem positive_slice_preconnected (a : ι → ℝ) (c : ℝ)
    (fixed : Finset ι) (bits : ι → Bool) :
    (supportGraph (slice fixed bits) (score a c)).Preconnected := by
  classical
  by_cases hne : Nonempty {x // slice fixed bits x ∧ 0 < score a c x}
  · obtain ⟨x⟩ := hne
    apply supportGraph_preconnected_of_coordinate_maximum _ _ (sliceMaximum a fixed bits)
    · exact ⟨sliceMaximum_mem _ _ _, lt_of_lt_of_le x.property.2
        (sliceMaximum_score _ _ _ _ _ x.property.1)⟩
    · intro z i hz j hj
      by_cases hji : j = i
      · subst j
        simp [sliceMaximum, hj]
      · simpa [Function.update_of_ne hji] using hz j hj
    · intro z i hz
      have h := score_update a c z i (sliceMaximum a fixed bits i)
      by_cases hi : i ∈ fixed
      · simp [sliceMaximum, hi, hz i hi] at h
        simp only [sliceMaximum, if_pos hi]
        linarith
      · have hm := preferred_max a i (z i)
        simp only [sliceMaximum, if_neg hi] at h
        simp only [sliceMaximum, if_neg hi]
        linarith
  · intro x
    exact (hne ⟨x⟩).elim

theorem positive_slice_empty_or_connected (a : ι → ℝ) (c : ℝ)
    (fixed : Finset ι) (bits : ι → Bool) :
    IsEmpty {x // slice fixed bits x ∧ 0 < score a c x} ∨
      (supportGraph (slice fixed bits) (score a c)).Connected := by
  classical
  by_cases h : Nonempty {x // slice fixed bits x ∧ 0 < score a c x}
  · letI := h
    exact Or.inr ⟨positive_slice_preconnected _ _ _ _⟩
  · exact Or.inl ⟨fun x => h ⟨x⟩⟩

omit [Fintype ι] [DecidableEq ι] in
theorem preferred_value (a : ι → ℝ) (i : ι) :
    a i * sign (preferred a i) = |a i| := by
  unfold preferred sign
  by_cases h : a i < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (le_of_not_gt h)]

def least (a : ι → ℝ) (i : ι) : Bool := !(preferred a i)

omit [Fintype ι] [DecidableEq ι] in
theorem least_value (a : ι → ℝ) (i : ι) :
    a i * sign (least a i) = -|a i| := by
  unfold least preferred sign
  by_cases h : a i < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (le_of_not_gt h)]

omit [DecidableEq ι] in
theorem score_nonneg_iff (a : ι → ℝ) (c : ℝ) :
    (∀ x, 0 ≤ score a c x) ↔ ∑ i, |a i| ≤ c := by
  constructor
  · intro h
    have hm := h (least a)
    simp only [score, least_value, Finset.sum_neg_distrib] at hm
    linarith
  · intro h x
    have hs : -(∑ i, |a i|) ≤ ∑ i, a i * sign (x i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i _
      cases hi : x i
      · simpa [sign] using neg_abs_le (a i)
      · simpa [sign] using neg_le_neg (le_abs_self (a i))
    unfold score
    linarith

theorem positive_support_connected (a : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    (supportGraph (slice ∅ (fun _ => false)) (score a c)).Connected := by
  have hp : 0 < score a c (preferred a) := by
    have hs : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    simp only [score, preferred_value]
    linarith
  letI : Nonempty {x // slice ∅ (fun _ => false) x ∧ 0 < score a c x} :=
    ⟨⟨preferred a, by simp [slice], hp⟩⟩
  exact ⟨positive_slice_preconnected _ _ _ _⟩

end
end MainTheory.BooleanCube
