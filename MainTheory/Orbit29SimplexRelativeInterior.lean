import MainTheory.Orbit29PrintedFaceAudit

/-! The positive-coordinate classes are exactly the relative interiors of
the fifteen nonempty coordinate faces of the orbit-29 probability simplex. -/
set_option autoImplicit false
namespace MainTheory.Orbit29SimplexRelativeInterior
open Orbit29PrintedFaceAudit
open scoped BigOperators
noncomputable section

def face (m : Fin 15) : Set (Fin 4 → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i)=1/8 ∧ ∀ i, i ∉ lambdaSupport m → p i=0}

def spanEquations (m : Fin 15) (p : Fin 4 → ℝ) : Prop :=
  (∑ i, p i)=1/8 ∧ ∀ i, i ∉ lambdaSupport m → p i=0

theorem span_equations (m : Fin 15) {p : Fin 4 → ℝ}
    (hp : p ∈ affineSpan ℝ (face m)) : spanEquations m p := by
  refine affineSpan_induction (p := spanEquations m) hp ?_ ?_
  · intro q hq
    exact hq.2
  · intro t q r s hq hr hs
    constructor
    · change (∑ i, (t*(q i-r i)+s i))=1/8
      simp only [mul_sub,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib]
      rw [hq.1,hr.1,hs.1]
      ring
    · intro i hi
      change t*(q i-r i)+s i=0
      rw [hq.2 i hi,hr.2 i hi,hs.2 i hi]
      ring

theorem strict_face_mem (m : Fin 15) (p : Fin 4 → ℝ)
    (hn : ∀ i, 0 ≤ p i) (hs : (∑ i, p i)=1/8) (hf : Face m p) : p ∈ face m := by
  refine ⟨hn,hs,?_⟩
  intro i hi
  have hb : maskBits m i ≠ true := by simpa only [lambdaSupport,Finset.mem_filter,
    Finset.mem_univ,true_and] using hi
  have hp : ¬ 0 < p i := fun h => hb ((hf i).mp h)
  exact le_antisymm (le_of_not_gt hp) (hn i)

theorem strict_in_relative_interior (m : Fin 15) (p : Fin 4 → ℝ)
    (hn : ∀ i, 0 ≤ p i) (hs : (∑ i, p i)=1/8) (hf : Face m p) :
    p ∈ intrinsicInterior ℝ (face m) := by
  classical
  have hp := strict_face_mem m p hn hs hf
  let q : affineSpan ℝ (face m) := ⟨p,subset_affineSpan ℝ _ hp⟩
  refine mem_intrinsicInterior.mpr ⟨q,?_,rfl⟩
  let positive : Set (affineSpan ℝ (face m)) :=
    {r | ∀ i ∈ lambdaSupport m, 0 < (r : Fin 4 → ℝ) i}
  have hopen : IsOpen positive := by
    simp only [positive,Set.setOf_forall]
    exact isOpen_biInter_finset fun i _ =>
      isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
  have hq : q ∈ positive := by
    intro i hi
    apply (hf i).mpr
    simpa only [lambdaSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hopen.mem_nhds hq)
  intro r hr
  have he := span_equations m r.property
  refine ⟨?_,he⟩
  intro i
  by_cases hi : i ∈ lambdaSupport m
  · exact le_of_lt (hr i hi)
  · rw [he.2 i hi]

theorem center_in_face (m : Fin 15) : faceCenter m ∈ face m :=
  strict_face_mem m _ (face_centers m).1 (face_centers m).2.1 (face_centers m).2.2

theorem relative_interior_strict (m : Fin 15) {p : Fin 4 → ℝ}
    (hp : p ∈ intrinsicInterior ℝ (face m)) : Face m p := by
  classical
  obtain ⟨q,hq,rfl⟩ := mem_intrinsicInterior.mp hp
  have hface : (q : Fin 4 → ℝ) ∈ face m :=
    (interior_subset (s := Subtype.val ⁻¹' face m) hq)
  intro j
  constructor
  · intro hj
    by_contra hb
    have hoff : j ∉ lambdaSupport m := by
      simpa only [lambdaSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hb
    rw [hface.2.2 j hoff] at hj
    exact (lt_irrefl 0) hj
  · intro hj
    by_contra hpos
    have hz : (q : Fin 4 → ℝ) j=0 := le_antisymm (le_of_not_gt hpos) (hface.1 j)
    have hcenter := subset_affineSpan ℝ (face m) (center_in_face m)
    let path : ℝ → affineSpan ℝ (face m) := fun t =>
      ⟨AffineMap.lineMap (faceCenter m) (q : Fin 4 → ℝ) t,
        AffineMap.lineMap_mem t hcenter q.property⟩
    have hcont : Continuous path :=
      AffineMap.lineMap_continuous.subtype_mk _
    have hone : path 1=q := by
      apply Subtype.ext
      exact AffineMap.lineMap_apply_one _ _
    obtain ⟨t,ht,hmem⟩ := (hcont.tendsto' 1 q hone).eventually_mem
      (mem_interior_iff_mem_nhds.mp hq) |>.exists_gt
    have hn : 0 ≤ (AffineMap.lineMap (faceCenter m) (q : Fin 4 → ℝ) t) j := hmem.1 j
    have hc : 0 < faceCenter m j := ((face_centers m).2.2 j).mpr hj
    simp only [AffineMap.lineMap_apply_module,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,
      mul_zero,add_zero] at hn
    exact (not_le_of_gt (mul_neg_of_neg_of_pos (sub_neg.mpr ht) hc)) hn

theorem relative_interior_iff (m : Fin 15) (p : Fin 4 → ℝ) :
    p ∈ intrinsicInterior ℝ (face m) ↔
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i)=1/8 ∧ Face m p := by
  constructor
  · intro hp
    have hm := intrinsicInterior_subset hp
    exact ⟨hm.1,hm.2.1,relative_interior_strict m hp⟩
  · rintro ⟨hn,hs,hf⟩
    exact strict_in_relative_interior m p hn hs hf

theorem fifteen_nonempty : ∀ m, (intrinsicInterior ℝ (face m)).Nonempty := by
  intro m
  exact ⟨faceCenter m,strict_in_relative_interior m _
    (face_centers m).1 (face_centers m).2.1 (face_centers m).2.2⟩

theorem exhaustive_relative_interiors (p : Fin 4 → ℝ)
    (hn : ∀ i, 0 ≤ p i) (hs : (∑ i, p i)=1/8) :
    ∃! m : Fin 15, p ∈ intrinsicInterior ℝ (face m) := by
  obtain ⟨m,hm⟩ := exhaustive_faces p hs
  refine ⟨m,strict_in_relative_interior m p hn hs hm,?_⟩
  intro n hnp
  exact distinct_faces n m p (relative_interior_strict n hnp) hm

end
end MainTheory.Orbit29SimplexRelativeInterior
