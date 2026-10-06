import MainTheory.Generated.Orbit31VertexReconstructions.Aggregate
import MainTheory.Orbit31SupportMaskEquiv
import MainTheory.Orbit31ExactSupportClassification

/-! The complete set of extreme points of the actual real moment polytope.
There are 204 vertices: 108 with support six, and 96 with support seven. -/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit31MomentVertices
noncomputable section
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.MatrixPositiveSupportVertices
open MainTheory.Orbit31SupportBase
open MainTheory.Orbit31SupportSemantics
open MainTheory.Orbit31SupportCoverageBase
open MainTheory.Orbit31ExactSupportClassification
open MainTheory.Generated.Orbit31SupportArithmetic

def polytope : Set (Fin 16 → ℝ) := {p | Feasible M b p}

theorem certificate_valid (mask : Fin 65536) : Valid mask.val (certificate mask) := by
  have he : finProdFinEquiv (coordinates mask) = mask :=
    (finProdFinEquiv : Fin 16 × Fin 4096 ≃ Fin 65536).apply_symm_apply mask
  have hv : Valid (finProdFinEquiv (coordinates mask)).val (certificate mask) := by
    simpa only [certificate,finProdFinEquiv,Nat.add_comm] using
      MainTheory.Generated.Orbit31SupportCoverage.Aggregate.valid
        (coordinates mask).1 (coordinates mask).2
  simpa only [he] using hv

theorem complete_extreme (p : Fin 16 → ℝ) (hp : p ∈ polytope.extremePoints ℝ) :
    ∃ v : Fin 204, primal v = p := by
  obtain ⟨mask,hs⟩ := MainTheory.Orbit31SupportMaskEquiv.real_support_encoded p
  have hv := certificate_valid mask
  cases hc : certificate mask with
  | dual v j =>
    rw [hc] at hv
    exact False.elim (support_excluded_of_dual hv ⟨p,hp.1,hs⟩)
  | primal w =>
    rw [hc] at hv
    obtain ⟨v,hvm⟩ := List.exists_mem_of_ne_nil w hv.1
    have hsubset : primalMasks v &&& mask.val = primalMasks v := by
      rw [← hv.2]
      exact member_subset hvm
    refine ⟨v,extreme_unique_face hp (primal_feasible v) ?_⟩
    intro j hj
    apply zero_off_support (primal_feasible v).nonneg (primal_support v)
    intro hmem
    have hmask : j ∈ maskSet mask.val := (mem_maskSet _ _).mpr
      (subset_bit hsubset ((mem_maskSet _ _).mp hmem))
    have hpos := (hs j).mpr hmask
    rw [hj] at hpos
    exact (lt_irrefl 0) hpos

theorem extreme_points : polytope.extremePoints ℝ = Set.range primal := by
  ext p
  constructor
  · exact complete_extreme p
  · rintro ⟨v,rfl⟩
    exact MainTheory.Generated.Orbit31VertexReconstructions.Aggregate.every_candidate_extreme v

theorem primal_mask_bounds : ∀ v : Fin 204, primalMasks v < 65536 := by decide +kernel
theorem primal_masks_distinct : Function.Injective primalMasks := by decide +kernel
theorem candidate_support_counts :
    (Finset.univ.filter fun v : Fin 204 => (maskSet (primalMasks v)).card = 6).card = 108 ∧
    (Finset.univ.filter fun v : Fin 204 => (maskSet (primalMasks v)).card = 7).card = 96 := by
  decide +kernel

theorem primal_injective : Function.Injective primal := by
  intro v w he
  apply primal_masks_distinct
  have hs : maskSet (primalMasks v) = maskSet (primalMasks w) := by
    ext j
    rw [← primal_support v j,← primal_support w j,he]
  exact congrArg Fin.val (MainTheory.Orbit31SupportMaskEquiv.mask_injective
    (a₁ := ⟨primalMasks v,primal_mask_bounds v⟩)
    (a₂ := ⟨primalMasks w,primal_mask_bounds w⟩) hs)

def vertexMap (v : Fin 204) : {p : Fin 16 → ℝ // p ∈ polytope.extremePoints ℝ} :=
  ⟨primal v,MainTheory.Generated.Orbit31VertexReconstructions.Aggregate.every_candidate_extreme v⟩

theorem vertexMap_bijective : Function.Bijective vertexMap := by
  constructor
  · intro v w he
    exact primal_injective (congrArg Subtype.val he)
  · intro p
    obtain ⟨v,hv⟩ := complete_extreme p.val p.property
    exact ⟨v,Subtype.ext hv⟩

def vertexEquiv : {p : Fin 16 → ℝ // p ∈ polytope.extremePoints ℝ} ≃ Fin 204 :=
  (Equiv.ofBijective vertexMap vertexMap_bijective).symm

theorem vertex_count : Nat.card {p : Fin 16 → ℝ // p ∈ polytope.extremePoints ℝ} = 204 := by
  rw [Nat.card_congr vertexEquiv]
  simp

def supportSize (p : Fin 16 → ℝ) : ℕ :=
  (Finset.univ.filter fun j => 0 < p j).card

theorem primal_supportSize (v : Fin 204) : supportSize (primal v) = (maskSet (primalMasks v)).card := by
  unfold supportSize
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,primal_support v j]

def vertexSupportEquiv (size : ℕ) :
    {p : {p : Fin 16 → ℝ // p ∈ polytope.extremePoints ℝ} // supportSize p.val = size} ≃
    {v : Fin 204 // (maskSet (primalMasks v)).card = size} :=
  Equiv.subtypeEquiv vertexEquiv (by
    intro p
    have hp : primal (vertexEquiv p) = p.val :=
      congrArg Subtype.val ((Equiv.ofBijective vertexMap vertexMap_bijective).apply_symm_apply p)
    rw [← hp,primal_supportSize])

theorem vertex_support_counts :
    Nat.card {p : {p : Fin 16 → ℝ // p ∈ polytope.extremePoints ℝ} // supportSize p.val = 6} = 108 ∧
    Nat.card {p : {p : Fin 16 → ℝ // p ∈ polytope.extremePoints ℝ} // supportSize p.val = 7} = 96 := by
  classical
  constructor
  · rw [Nat.card_congr (vertexSupportEquiv 6),Nat.card_eq_fintype_card,Fintype.card_subtype]
    exact candidate_support_counts.1
  · rw [Nat.card_congr (vertexSupportEquiv 7),Nat.card_eq_fintype_card,Fintype.card_subtype]
    exact candidate_support_counts.2

end
end MainTheory.Orbit31MomentVertices
