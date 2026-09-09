import MainTheory.Orbit7JacobianRank
import MainTheory.Orbit7VertexScaling

set_option autoImplicit false

namespace MainTheory.Orbit7Jacobian

open SixQubit.Orbit7Universal

theorem edges_mem (j : Fin 10) : edges j ∈ edgePairs := by
  fin_cases j <;> decide

theorem jacobian_polar (x y : Fin 5 × Fin 5 → ℂ) (i : Fin 5) :
    (jacobian x).mulVec (fun j => y (edges j)) i = PolarHafnian5 x y i := by
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,jacobian,edges,PolarHafnian5,
    Fin.sum_univ_succ] <;> ring

theorem kernel_iff_vertex (x y : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x) (hH : ∀ i, Hafnian5 x i=0) :
    (jacobian x).mulVec (fun j => y (edges j)) = 0 ↔ IsVertexTangent x y := by
  constructor
  · intro h
    apply full_hafnian_tangent_is_vertex x y hx hH
    intro i
    rw [← jacobian_polar]
    exact congrFun h i
  · rintro ⟨r,hr⟩
    have he : (fun j => y (edges j)) =
        fun j => MainTheory.Orbit7VertexScaling.tangent x r (edges j) := by
      funext j
      exact hr _ (edges_mem j)
    rw [he]
    funext i
    rw [jacobian_polar]
    exact MainTheory.Orbit7VertexScaling.tangent_preserves x hH r i

theorem two_tangents (x y z : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x) (hH : ∀ i,Hafnian5 x i=0)
    (hy : ∀ i,PolarHafnian5 x y i=0) (hz : ∀ i,PolarHafnian5 x z i=0) :
    ∃ r q : Fin 5 → ℂ, ∀ e ∈ edgePairs,
      y e=(r e.1+r e.2)*x e ∧ z e=(q e.1+q e.2)*x e := by
  obtain ⟨r,hr⟩ := full_hafnian_tangent_is_vertex x y hx hH hy
  obtain ⟨q,hq⟩ := full_hafnian_tangent_is_vertex x z hx hH hz
  exact ⟨r,q,fun e he => ⟨hr e he,hq e he⟩⟩

end MainTheory.Orbit7Jacobian
