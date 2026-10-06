import MainTheory.Orbit31MomentVertices

/-! Every coordinate face is the convex hull of exactly the vertices whose
supports it contains. The argument covers empty and high-support faces. -/
set_option autoImplicit false
namespace MainTheory.Orbit31MomentFaces
noncomputable section
open MainTheory.Orbit31MomentVertices
open MainTheory.Orbit31SupportBase
open MainTheory.Orbit31SupportSemantics
open MainTheory.MatrixPositiveSupportCertificates
open scoped BigOperators Matrix

theorem sum_one {p : Fin 16 → ℝ} (hp : Feasible M b p) : ∑ j, p j=1 := by
  have hrow : ∀ j : Fin 16, M 0 j=1 := by intro j; fin_cases j <;> norm_num [M,integerRows,Fin.succ]
  have he := congrFun hp.equations 0
  simpa only [Matrix.mulVec,dotProduct,hrow,one_mul] using he

theorem coordinate_bounds {p : Fin 16 → ℝ} (hp : Feasible M b p) (j : Fin 16) :
    0 ≤ p j ∧ p j ≤ 1 := by
  refine ⟨hp.nonneg j,?_⟩
  have h := Finset.single_le_sum (fun k _ => hp.nonneg k) (Finset.mem_univ j)
  simpa only [sum_one hp] using h

theorem polytope_closed : IsClosed polytope := by
  have he : polytope = {p : Fin 16 → ℝ | ∀ j, 0 ≤ p j} ∩ {p | M.mulVec p=b} := by
    ext p
    exact ⟨fun h => ⟨h.nonneg,h.equations⟩,fun h => ⟨h.1,h.2⟩⟩
  rw [he]
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_eq M.mulVecLin.continuous_of_finiteDimensional continuous_const

theorem polytope_compact : IsCompact polytope := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin 16 → ℝ) 1)).of_isClosed_subset polytope_closed
  intro p hp
  exact ⟨fun j => (coordinate_bounds hp j).1,fun j => (coordinate_bounds hp j).2⟩

theorem polytope_convex : Convex ℝ polytope := by
  intro p hp q hq s t hs ht hst
  constructor
  · intro j
    exact add_nonneg (mul_nonneg hs (hp.nonneg j)) (mul_nonneg ht (hq.nonneg j))
  · change M.mulVecLin (s • p+t • q)=b
    rw [map_add,map_smul,map_smul]
    have hep : M.mulVecLin p=b := hp.equations
    have heq : M.mulVecLin q=b := hq.equations
    rw [hep,heq,← add_smul,hst,one_smul]

def face (mask : ℕ) : Set (Fin 16 → ℝ) :=
  {p | Feasible M b p ∧ ∀ j, j ∉ maskSet mask → p j=0}

theorem face_closed (mask : ℕ) : IsClosed (face mask) := by
  have he : face mask = polytope ∩ {p : Fin 16 → ℝ | ∀ j, j ∉ maskSet mask → p j=0} := rfl
  rw [he]
  apply polytope_closed.inter
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_eq (continuous_apply j) continuous_const

theorem face_compact (mask : ℕ) : IsCompact (face mask) :=
  polytope_compact.of_isClosed_subset (face_closed mask) fun _ h => h.1

theorem face_convex (mask : ℕ) : Convex ℝ (face mask) := by
  intro p hp q hq s t hs ht hst
  refine ⟨polytope_convex hp.1 hq.1 hs ht hst,?_⟩
  intro j hj
  change s*p j+t*q j=0
  rw [hp.2 j hj,hq.2 j hj,mul_zero,mul_zero,add_zero]

theorem face_extreme (mask : ℕ) : IsExtreme ℝ polytope (face mask) := by
  refine ⟨fun _ hp => hp.1,?_⟩
  intro q hq r hr p hp hsegment
  refine ⟨hq,?_⟩
  intro j hj
  obtain ⟨s,t,hs,ht,_,he⟩ := hsegment
  have heq := congrFun he j
  change s*q j+t*r j=p j at heq
  rw [hp.2 j hj] at heq
  have hnq := hq.nonneg j
  have hnr := hr.nonneg j
  nlinarith

theorem face_vertices (mask : ℕ) : (face mask).extremePoints ℝ =
    face mask ∩ Set.range primal := by
  rw [(face_extreme mask).extremePoints_eq,extreme_points]

theorem convex_hull_face_vertices (mask : ℕ) :
    convexHull ℝ ((face mask).extremePoints ℝ)=face mask := by
  have hfinite : ((face mask).extremePoints ℝ).Finite := by
    rw [face_vertices]
    exact (Set.finite_range primal).subset (Set.inter_subset_right)
  have he := closure_convexHull_extremePoints (face_compact mask) (face_convex mask)
  rw [hfinite.isClosed_convexHull.closure_eq] at he
  exact he

theorem vertex_in_face (mask : ℕ) (v : Fin 204) :
    primal v ∈ face mask ↔ maskSet (MainTheory.Generated.Orbit31SupportArithmetic.primalMasks v) ⊆ maskSet mask := by
  constructor
  · intro hv j hj
    by_contra hnot
    have hz := hv.2 j hnot
    have hp := (primal_support v j).mpr hj
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hsub
    refine ⟨primal_feasible v,?_⟩
    intro j hj
    apply zero_off_support (primal_feasible v).nonneg (primal_support v)
    exact fun h => hj (hsub h)

theorem convex_hull_supported_vertices (mask : ℕ) :
    convexHull ℝ (primal '' {v | maskSet (MainTheory.Generated.Orbit31SupportArithmetic.primalMasks v) ⊆ maskSet mask}) =
    face mask := by
  have he : primal '' {v | maskSet (MainTheory.Generated.Orbit31SupportArithmetic.primalMasks v) ⊆ maskSet mask} =
      (face mask).extremePoints ℝ := by
    rw [face_vertices]
    ext p
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(vertex_in_face mask v).mpr hv,⟨v,rfl⟩⟩
    · rintro ⟨hp,v,rfl⟩
      exact ⟨v,(vertex_in_face mask v).mp hp,rfl⟩
  rw [he]
  exact convex_hull_face_vertices mask

end
end MainTheory.Orbit31MomentFaces
