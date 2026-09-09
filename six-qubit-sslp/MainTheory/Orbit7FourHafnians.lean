import MainTheory.Orbit7MatchingDisplays
import MainTheory.Orbit7SpinorCoordinates

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit7FourHafnians

open SixQubit.Orbit7Universal MainTheory.Orbit7MatchingDisplays
open MainTheory.Orbit7SpinorCoordinates

noncomputable def bvec (x z : ℂ) : Spinor := ![-star x,star z]

noncomputable def parameterMatrix (c d : ℝ) (x y z : Edge → ℂ) (i : Fin 5) : Mat2 :=
  matchingMatrix (fun e => avec c d (x e) (y e)) (fun e => bvec (x e) (z e)) i

theorem entries (c d : ℝ) (x y z : Edge → ℂ) (i : Fin 5) :
    parameterMatrix c d x y z i =
      !![-2*(c : ℂ)*star (Hafnian5 x i)+(d : ℂ)*star (PolarHafnian5 x y i),
        -2*(d : ℂ)*star (Hafnian5 x i)-(c : ℂ)*star (PolarHafnian5 x y i);
        (c : ℂ)*star (PolarHafnian5 x z i)-(d : ℂ)*star (PolarHafnian5 y z i),
        (d : ℂ)*star (PolarHafnian5 x z i)+(c : ℂ)*star (PolarHafnian5 y z i)] := by
  funext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;>
    simp [parameterMatrix,matchingMatrix,matchings,avec,bvec,Hafnian5,PolarHafnian5,
      Fin.sum_univ_succ] <;> ring

theorem four_hafnians (c d : ℝ) (h : c^2+d^2=1) (x y z : Edge → ℂ) (i : Fin 5)
    (hm : ∀ p q, parameterMatrix c d x y z i p q = 0) :
    Hafnian5 x i = 0 ∧ PolarHafnian5 x y i = 0 ∧
    PolarHafnian5 x z i = 0 ∧ PolarHafnian5 y z i = 0 := by
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast h
  have he := entries c d x y z i
  have h00 := (congrFun (congrFun he 0) 0).symm.trans (hm 0 0)
  have h01 := (congrFun (congrFun he 0) 1).symm.trans (hm 0 1)
  have h10 := (congrFun (congrFun he 1) 0).symm.trans (hm 1 0)
  have h11 := (congrFun (congrFun he 1) 1).symm.trans (hm 1 1)
  change -2*(c : ℂ)*star (Hafnian5 x i)+(d : ℂ)*star (PolarHafnian5 x y i)=0 at h00
  change -2*(d : ℂ)*star (Hafnian5 x i)-(c : ℂ)*star (PolarHafnian5 x y i)=0 at h01
  change (c : ℂ)*star (PolarHafnian5 x z i)-(d : ℂ)*star (PolarHafnian5 y z i)=0 at h10
  change (d : ℂ)*star (PolarHafnian5 x z i)+(c : ℂ)*star (PolarHafnian5 y z i)=0 at h11
  have hx : star (Hafnian5 x i)=0 := by
    linear_combination (-(c : ℂ)/2)*h00+(-(d : ℂ)/2)*h01-star (Hafnian5 x i)*hC
  have hxy : star (PolarHafnian5 x y i)=0 := by
    linear_combination (d : ℂ)*h00-(c : ℂ)*h01-star (PolarHafnian5 x y i)*hC
  have hxz : star (PolarHafnian5 x z i)=0 := by
    linear_combination (c : ℂ)*h10+(d : ℂ)*h11-star (PolarHafnian5 x z i)*hC
  have hyz : star (PolarHafnian5 y z i)=0 := by
    linear_combination -(d : ℂ)*h10+(c : ℂ)*h11-star (PolarHafnian5 y z i)*hC
  exact ⟨star_eq_zero.mp hx,star_eq_zero.mp hxy,star_eq_zero.mp hxz,star_eq_zero.mp hyz⟩

theorem matching_edges : ∀ i : Fin 5, ∀ k : Fin 3,
    (matchings i k).1 ∈ edgePairs ∧ (matchings i k).2 ∈ edgePairs := by decide +kernel

theorem of_code_coordinates (C D : SS.State 6 ℂ)
    (hC : ∀ s, SS.weight uniformAv s ≠ 0 → C s = 0)
    (hD : ∀ s, SS.weight uniformAv s ≠ 2 → D s = 0)
    (hcode : SS.HasDistance ![C,D] 3)
    (c d : ℝ) (h : c^2+d^2=1) (x y z : Edge → ℂ)
    (hA : ∀ e ∈ edgePairs, spinor C (aBase e.1 e.2) = avec c d (x e) (y e))
    (hB : ∀ e ∈ edgePairs, spinor D (bBase e.1 e.2) = bvec (x e) (z e)) :
    ∀ i : Fin 5, Hafnian5 x i = 0 ∧ PolarHafnian5 x y i = 0 ∧
      PolarHafnian5 x z i = 0 ∧ PolarHafnian5 y z i = 0 := by
  intro i
  have he : oneFlipMat C D i = parameterMatrix c d x y z i := by
    rw [oneflip_expansion]
    funext p q
    simp only [parameterMatrix,matchingMatrix]
    apply Finset.sum_congr rfl
    intro k _
    rw [hA _ (matching_edges i k).1,hA _ (matching_edges i k).2,
      hB _ (matching_edges i k).1,hB _ (matching_edges i k).2]
  apply four_hafnians c d h x y z i
  intro p q
  rw [← he]
  exact oneflip_matrix C D hC hD hcode i p q

end MainTheory.Orbit7FourHafnians
