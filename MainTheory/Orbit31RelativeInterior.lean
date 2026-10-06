import MainTheory.Orbit31MomentFaces
import MainTheory.Orbit31SupportCoverageBase

/-! Strict support is in the relative interior of its coordinate face.
The union criterion requires a nonempty face; the empty mask is recorded
explicitly rather than silently counted as a normalized probability support. -/
set_option autoImplicit false
namespace MainTheory.Orbit31RelativeInterior
noncomputable section
open MainTheory.Orbit31MomentFaces
open MainTheory.Orbit31SupportBase
open MainTheory.Orbit31SupportSemantics
open MainTheory.MatrixPositiveSupportCertificates
open scoped Matrix BigOperators

def affineEquations (mask : ℕ) (p : Fin 16 → ℝ) : Prop :=
  M.mulVec p=b ∧ ∀ j, j ∉ maskSet mask → p j=0

theorem span_equations (mask : ℕ) {p : Fin 16 → ℝ}
    (hp : p ∈ affineSpan ℝ (face mask)) : affineEquations mask p := by
  refine affineSpan_induction (p := affineEquations mask) hp ?_ ?_
  · intro q hq
    exact ⟨hq.1.equations,hq.2⟩
  · intro t q r s hq hr hs
    constructor
    · change M.mulVecLin (t • (q-r)+s)=b
      rw [map_add,map_smul,map_sub]
      have hq' : M.mulVecLin q=b := hq.1
      have hr' : M.mulVecLin r=b := hr.1
      have hs' : M.mulVecLin s=b := hs.1
      rw [hq',hr',hs',sub_self,smul_zero,zero_add]
    · intro j hj
      change t*(q j-r j)+s j=0
      rw [hq.2 j hj,hr.2 j hj,hs.2 j hj]
      ring

theorem strict_support_in_relative_interior (mask : ℕ) {p : Fin 16 → ℝ}
    (hp : Feasible M b p) (hs : ExactSupport (maskSet mask) p) :
    p ∈ intrinsicInterior ℝ (face mask) := by
  classical
  have hface : p ∈ face mask := ⟨hp,fun _ hj => zero_off_support hp.nonneg hs hj⟩
  let q : affineSpan ℝ (face mask) := ⟨p,subset_affineSpan ℝ _ hface⟩
  refine mem_intrinsicInterior.mpr ⟨q,?_,rfl⟩
  let positive : Set (affineSpan ℝ (face mask)) :=
    {r | ∀ j ∈ maskSet mask, 0 < (r : Fin 16 → ℝ) j}
  have hopen : IsOpen positive := by
    simp only [positive,Set.setOf_forall]
    exact isOpen_biInter_finset fun j _ =>
      isOpen_lt continuous_const ((continuous_apply j).comp continuous_subtype_val)
  have hpos : q ∈ positive := fun j hj => (hs j).mpr hj
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hopen.mem_nhds hpos)
  intro r hr
  have he := span_equations mask r.property
  refine ⟨⟨?_,he.1⟩,he.2⟩
  intro j
  by_cases hj : j ∈ maskSet mask
  · exact le_of_lt (hr j hj)
  · rw [he.2 j hj]

theorem relative_interior_support_iff (mask : ℕ) :
    (∃ p, p ∈ intrinsicInterior ℝ (face mask) ∧ ExactSupport (maskSet mask) p) ↔
    ∃ p, Feasible M b p ∧ ExactSupport (maskSet mask) p := by
  constructor
  · rintro ⟨p,hp,hs⟩
    exact ⟨p,(intrinsicInterior_subset hp).1,hs⟩
  · rintro ⟨p,hp,hs⟩
    exact ⟨p,strict_support_in_relative_interior mask hp hs,hs⟩

theorem empty_mask_no_support :
    ¬ ∃ p, Feasible M b p ∧ ExactSupport (maskSet 0) p := by
  rintro ⟨p,hp,hs⟩
  have hz : ∀ j, p j=0 := fun j => zero_off_support hp.nonneg hs (by simp [mem_maskSet])
  have he := sum_one hp
  simp only [hz,Finset.sum_const_zero] at he
  norm_num at he

open MainTheory.Generated.Orbit31SupportArithmetic

def supportedVertices (mask : ℕ) : Finset (Fin 204) :=
  Finset.univ.filter fun v => maskSet (primalMasks v) ⊆ maskSet mask

def vertexUnion (mask : ℕ) : Finset (Fin 16) :=
  (supportedVertices mask).biUnion fun v => maskSet (primalMasks v)

theorem mem_vertexUnion (mask : ℕ) (j : Fin 16) :
    j ∈ vertexUnion mask ↔ ∃ v, maskSet (primalMasks v) ⊆ maskSet mask ∧
      j ∈ maskSet (primalMasks v) := by
  simp [vertexUnion,supportedVertices]

theorem vertexUnion_subset (mask : ℕ) : vertexUnion mask ⊆ maskSet mask := by
  intro j hj
  obtain ⟨v,hv,hj⟩ := (mem_vertexUnion mask j).mp hj
  exact hv hj

theorem exact_support_vertexUnion {mask : ℕ} {p : Fin 16 → ℝ}
    (hp : Feasible M b p) (hs : ExactSupport (maskSet mask) p) :
    vertexUnion mask=maskSet mask := by
  classical
  apply Finset.Subset.antisymm (vertexUnion_subset mask)
  intro j hj
  by_contra hnot
  have hz : ∀ v, maskSet (primalMasks v) ⊆ maskSet mask → primal v j=0 := by
    intro v hv
    apply zero_off_support (primal_feasible v).nonneg (primal_support v)
    exact fun h => hnot ((mem_vertexUnion mask j).mpr ⟨v,hv,h⟩)
  have hseed : primal '' {v | maskSet (primalMasks v) ⊆ maskSet mask} ⊆
      {q : Fin 16 → ℝ | q j=0} := by
    rintro _ ⟨v,hv,rfl⟩
    exact hz v hv
  have hconvex : Convex ℝ {q : Fin 16 → ℝ | q j=0} := by
    intro q hq r hr s t _ _ _
    change s*q j+t*r j=0
    rw [hq,hr]
    ring
  have hface : p ∈ face mask := ⟨hp,fun _ hj => zero_off_support hp.nonneg hs hj⟩
  rw [← convex_hull_supported_vertices] at hface
  have he := convexHull_min hseed hconvex hface
  have hpos := (hs j).mpr hj
  change p j=0 at he
  rw [he] at hpos
  exact (lt_irrefl 0) hpos

theorem exact_support_nonempty {mask : ℕ} {p : Fin 16 → ℝ}
    (hp : Feasible M b p) (hs : ExactSupport (maskSet mask) p) :
    (maskSet mask).Nonempty := by
  classical
  by_contra he
  have hz : ∀ j, p j=0 := fun j => zero_off_support hp.nonneg hs (fun hj => he ⟨j,hj⟩)
  have hsum := sum_one hp
  simp only [hz,Finset.sum_const_zero] at hsum
  norm_num at hsum

theorem support_iff_vertexUnion (mask : ℕ) :
    (∃ p, Feasible M b p ∧ ExactSupport (maskSet mask) p) ↔
    vertexUnion mask=maskSet mask ∧ (maskSet mask).Nonempty := by
  classical
  constructor
  · rintro ⟨p,hp,hs⟩
    exact ⟨exact_support_vertexUnion hp hs,exact_support_nonempty hp hs⟩
  · rintro ⟨he,j0,hj0⟩
    have hpos : ∀ j ∈ maskSet mask, ∃ v, maskSet (primalMasks v) ⊆ maskSet mask ∧
        0 < primal v j := by
      intro j hj
      obtain ⟨v,hv,hj⟩ := (mem_vertexUnion mask j).mp (he.symm ▸ hj)
      exact ⟨v,hv,(primal_support v j).mpr hj⟩
    obtain ⟨v0,hv0,_⟩ := hpos j0 hj0
    have hw : ∀ j : Fin 16, ∃ v : Fin 204,
        maskSet (primalMasks v) ⊆ maskSet mask ∧ (j ∈ maskSet mask → 0 < primal v j) := by
      intro j
      by_cases hj : j ∈ maskSet mask
      · obtain ⟨v,hv,hp⟩ := hpos j hj
        exact ⟨v,hv,fun _ => hp⟩
      · exact ⟨v0,hv0,fun h => False.elim (hj h)⟩
    choose w hw using hw
    refine ⟨average (fun j => primal (w j)),average_feasible M b _ (fun j => primal_feasible (w j)),?_⟩
    apply average_exact_support
    · intro i j
      exact (primal_feasible (w i)).nonneg j
    · intro i j hj
      exact zero_off_support (primal_feasible (w i)).nonneg (primal_support (w i))
        (fun h => hj ((hw i).1 h))
    · intro j hj
      exact (hw j).2 hj

theorem relative_interior_iff_vertexUnion (mask : ℕ) :
    (∃ p, p ∈ intrinsicInterior ℝ (face mask) ∧ ExactSupport (maskSet mask) p) ↔
    vertexUnion mask=maskSet mask ∧ (maskSet mask).Nonempty := by
  rw [relative_interior_support_iff,support_iff_vertexUnion]

theorem empty_vertexUnion : vertexUnion 0=maskSet 0 := by
  apply Finset.Subset.antisymm (vertexUnion_subset 0)
  simp [maskSet]

end
end MainTheory.Orbit31RelativeInterior
