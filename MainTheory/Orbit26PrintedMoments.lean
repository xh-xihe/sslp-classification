import MainTheory.OrderFour26Support
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! The literal seventeen-by-sixteen tail moment system for SI orbit 26.
The integer entries are checked against the actual fibre tail coordinates.
The complete rational affine solution and rank fourteen are kernel proofs;
they do not depend on the final no-code theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace MainTheory.Orbit26PrintedMoments
open MainTheory.OrderFour26Support

def pairs : Fin 10 → Fin 5 × Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def values : List (List ℤ) := [[1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1],[0,0,1,1,0,0,1,1,-1,-1,0,0,-1,-1,0,0],[0,0,0,0,1,1,1,1,-1,-1,-1,-1,0,0,0,0],[0,1,0,1,0,1,0,1,-1,0,-1,0,-1,0,-1,0],[0,1,0,1,0,1,1,0,-1,0,-1,0,-1,0,0,-1],[0,0,1,1,1,1,0,0,-1,-1,0,0,0,0,-1,-1],[0,0,0,0,0,0,1,1,-1,-1,0,0,0,0,0,0],[0,0,0,1,0,0,0,1,-1,0,0,0,-1,0,0,0],[0,0,0,1,0,0,1,0,-1,0,0,0,-1,0,0,0],[0,0,1,1,0,0,0,0,-1,-1,0,0,0,0,0,0],[0,0,0,0,0,1,0,1,-1,0,-1,0,0,0,0,0],[0,0,0,0,0,1,1,0,-1,0,-1,0,0,0,0,0],[0,0,0,0,1,1,0,0,-1,-1,0,0,0,0,0,0],[0,1,0,1,0,1,0,0,-1,0,-1,0,-1,0,0,0],[0,0,0,1,0,1,0,0,-1,0,0,0,0,0,-1,0],[0,0,0,1,0,1,0,0,-1,0,0,0,0,0,0,-1]]
def rows : Matrix (Fin 17) (Fin 16) ℤ := fun i j => (values.getD i.val []).getD j.val 0
def actual : Matrix (Fin 17) (Fin 16) ℤ := fun i j =>
  if i.val = 0 then (if j.val < 8 then 1 else 0) else
  if i.val = 1 then (if j.val < 8 then 0 else 1) else
    let x := if h : j.val < 8 then bottomAt false ⟨j.val,h⟩
      else topAt false ⟨j.val-8,by omega⟩
    let sign : ℤ := if j.val < 8 then 1 else -1
    if h : i.val < 7 then
      sign * (if x (⟨i.val-2,by omega⟩ : Fin 5).succ then 1 else 0)
    else sign * (if x (pairs ⟨i.val-7,by omega⟩).1.succ then 1 else 0) *
      (if x (pairs ⟨i.val-7,by omega⟩).2.succ then 1 else 0)

theorem actual_rows : actual = rows := by decide +kernel

def M : Matrix (Fin 17) (Fin 16) ℚ := fun i j => rows i j
def homogeneous (a b : ℚ) : Fin 16 → ℚ :=
  ![a+b,-a-b,-a,a,-b,b,0,0,a+b,-a-b,-a,a,-b,b,0,0]

theorem kernel_iff (u : Fin 16 → ℚ) :
    M.mulVec u = 0 ↔ u = homogeneous (u 3) (u 5) := by
  constructor
  · intro h
    have h0 := congrFun h ((0 : Fin 17))
    have h1 := congrFun h ((0 : Fin 16).succ)
    have h2 := congrFun h ((0 : Fin 15).succ.succ)
    have h3 := congrFun h ((0 : Fin 14).succ.succ.succ)
    have h4 := congrFun h ((0 : Fin 13).succ.succ.succ.succ)
    have h5 := congrFun h ((0 : Fin 12).succ.succ.succ.succ.succ)
    have h6 := congrFun h ((0 : Fin 11).succ.succ.succ.succ.succ.succ)
    have h7 := congrFun h ((0 : Fin 10).succ.succ.succ.succ.succ.succ.succ)
    have h8 := congrFun h ((0 : Fin 9).succ.succ.succ.succ.succ.succ.succ.succ)
    have h9 := congrFun h ((0 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ.succ)
    have h10 := congrFun h ((0 : Fin 7).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
    have h11 := congrFun h ((0 : Fin 6).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
    have h13 := congrFun h ((0 : Fin 4).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
    have h15 := congrFun h ((0 : Fin 2).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
    norm_num [M,rows,values,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h13 h15
    change u 0+(u 1+(u 2+(u 3+(u 4+(u 5+(u 6+(u 7)))))))=0 at h0
    change u 8+(u 9+(u 10+(u 11+(u 12+(u 13+(u 14+(u 15)))))))=0 at h1
    change u 2+(u 3+(u 6+(u 7+(-u 8+(-u 9+(-u 12+(-u 13)))))))=0 at h2
    change u 4+(u 5+(u 6+(u 7+(-u 8+(-u 9+(-u 10+(-u 11)))))))=0 at h3
    change u 1+(u 3+(u 5+(u 7+(-u 8+(-u 10+(-u 12+(-u 14)))))))=0 at h4
    change u 1+(u 3+(u 5+(u 6+(-u 8+(-u 10+(-u 12+(-u 15)))))))=0 at h5
    change u 2+(u 3+(u 4+(u 5+(-u 8+(-u 9+(-u 14+(-u 15)))))))=0 at h6
    change u 6+(u 7+(-u 8+(-u 9)))=0 at h7
    change u 3+(u 7+(-u 8+(-u 12)))=0 at h8
    change u 3+(u 6+(-u 8+(-u 12)))=0 at h9
    change u 2+(u 3+(-u 8+(-u 9)))=0 at h10
    change u 5+(u 7+(-u 8+(-u 10)))=0 at h11
    change u 4+(u 5+(-u 8+(-u 9)))=0 at h13
    change u 3+(u 5+(-u 8+(-u 14)))=0 at h15
    have hu0 : u 0 = u 3+u 5 := by linear_combination 1 * h0 + (-9/8) * h1 + (-9/8) * h2 + (-9/8) * h3 + -1 * h5 + (-1/8) * h6 + (3/4) * h7 + (-1/2) * h8 + (3/2) * h9 + (1/4) * h10 + 1 * h11 + (1/4) * h13 + -1 * h15
    have hu1 : u 1 = -u 3-u 5 := by linear_combination (3/8) * h1 + (3/8) * h2 + (3/8) * h3 + 1 * h5 + (-5/8) * h6 + (-1/4) * h7 + (1/2) * h8 + (-3/2) * h9 + (1/4) * h10 + -1 * h11 + (1/4) * h13 + 1 * h15
    have hu2 : u 2 = -u 3 := by linear_combination (1/4) * h1 + (1/4) * h2 + (1/4) * h3 + (1/4) * h6 + (-1/2) * h7 + (1/2) * h10 + (-1/2) * h13
    have hu4 : u 4 = -u 5 := by linear_combination (1/4) * h1 + (1/4) * h2 + (1/4) * h3 + (1/4) * h6 + (-1/2) * h7 + (-1/2) * h10 + (1/2) * h13
    have hu6 : u 6 = 0 := by linear_combination (1/8) * h1 + (1/8) * h2 + (1/8) * h3 + (1/8) * h6 + (1/4) * h7 + (-1/2) * h8 + (1/2) * h9 + (-1/4) * h10 + (-1/4) * h13
    have hu7 : u 7 = 0 := by linear_combination (1/8) * h1 + (1/8) * h2 + (1/8) * h3 + (1/8) * h6 + (1/4) * h7 + (1/2) * h8 + (-1/2) * h9 + (-1/4) * h10 + (-1/4) * h13
    have hu8 : u 8 = u 3+u 5 := by linear_combination (-1/8) * h1 + (-1/8) * h2 + (-1/8) * h3 + (1/2) * h4 + (-1/2) * h5 + (3/8) * h6 + (1/4) * h7 + (-1/2) * h8 + (1/2) * h9 + (-1/4) * h10 + (-1/4) * h13 + -1 * h15
    have hu9 : u 9 = -u 3-u 5 := by linear_combination (3/8) * h1 + (3/8) * h2 + (3/8) * h3 + (-1/2) * h4 + (1/2) * h5 + (-1/8) * h6 + (-3/4) * h7 + (1/2) * h8 + (-1/2) * h9 + (-1/4) * h10 + (-1/4) * h13 + 1 * h15
    have hu10 : u 10 = -u 3 := by linear_combination (1/4) * h1 + (1/4) * h2 + (1/4) * h3 + (-1/2) * h4 + (1/2) * h5 + (-1/4) * h6 + 1 * h8 + -1 * h9 + -1 * h11 + 1 * h15
    have hu11 : u 11 = u 3 := by linear_combination -1 * h3 + (1/2) * h4 + (-1/2) * h5 + (1/2) * h6 + (1/2) * h7 + -1 * h8 + 1 * h9 + (-1/2) * h10 + 1 * h11 + (1/2) * h13 + -1 * h15
    have hu12 : u 12 = -u 5 := by linear_combination (1/4) * h1 + (1/4) * h2 + (1/4) * h3 + (-1/2) * h4 + (1/2) * h5 + (-1/4) * h6 + -1 * h9 + 1 * h15
    have hu13 : u 13 = u 5 := by linear_combination -1 * h2 + (1/2) * h4 + (-1/2) * h5 + (1/2) * h6 + (1/2) * h7 + 1 * h9 + (1/2) * h10 + (-1/2) * h13 + -1 * h15
    have hu14 : u 14 = 0 := by linear_combination (1/8) * h1 + (1/8) * h2 + (1/8) * h3 + (-1/2) * h4 + (1/2) * h5 + (-3/8) * h6 + (-1/4) * h7 + (1/2) * h8 + (-1/2) * h9 + (1/4) * h10 + (1/4) * h13
    have hu15 : u 15 = 0 := by linear_combination (1/8) * h1 + (1/8) * h2 + (1/8) * h3 + (1/2) * h4 + (-1/2) * h5 + (-3/8) * h6 + (-1/4) * h7 + (-1/2) * h8 + (1/2) * h9 + (1/4) * h10 + (1/4) * h13
    funext i
    fin_cases i <;> simp [homogeneous,hu0,hu1,hu2,hu4,hu6,hu7,hu8,hu9,hu10,hu11,hu12,hu13,hu14,hu15]
  · intro h
    rw [h]
    ext i
    fin_cases i <;> norm_num [M,rows,values,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,homogeneous] <;> ring

def particular : Fin 16 → ℚ :=
  ![-1/8,3/8,1/4,0,1/4,0,1/8,1/8,-1/8,3/8,1/4,0,1/4,0,1/8,1/8]
def target : Fin 17 → ℚ := ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def affine (a b : ℚ) : Fin 16 → ℚ :=
  ![a+b-1/8,3/8-a-b,1/4-a,a,1/4-b,b,1/8,1/8,
    a+b-1/8,3/8-a-b,1/4-a,a,1/4-b,b,1/8,1/8]

theorem particular_solution : M.mulVec particular = target := by
  ext i
  fin_cases i <;> norm_num [M,rows,values,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,particular,target]

theorem affine_iff (u : Fin 16 → ℚ) :
    M.mulVec u = target ↔ u = affine (u 3) (u 5) := by
  constructor
  · intro h
    have hz : M.mulVec (u-particular) = 0 := by
      rw [Matrix.mulVec_sub,h,particular_solution,sub_self]
    have hu := (kernel_iff (u-particular)).1 hz
    have ha : (u-particular) 3 = u 3 := by
      change u 3-particular ⟨3,by decide⟩ = u 3
      norm_num [particular]
    have hb : (u-particular) 5 = u 5 := by
      change u 5-particular ⟨5,by decide⟩ = u 5
      norm_num [particular]
    rw [ha,hb] at hu
    funext i
    have hi := congrFun hu i
    fin_cases i <;> norm_num [Pi.sub_apply,homogeneous,particular,affine,Fin.succ] at hi ⊢ <;> linarith
  · intro h
    rw [h]
    ext i
    fin_cases i <;> norm_num [M,rows,values,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,affine,target] <;> ring

noncomputable def parameters : (Fin 2 → ℚ) ≃ₗ[ℚ] LinearMap.ker M.mulVecLin where
  toFun p := ⟨homogeneous (p 0) (p 1), by
    change M.mulVec (homogeneous (p 0) (p 1)) = 0
    exact (kernel_iff _).2 rfl⟩
  invFun u := ![u.1 3,u.1 5]
  left_inv p := by funext i; fin_cases i <;> rfl
  right_inv u := by apply Subtype.ext; exact ((kernel_iff u.1).1 u.2).symm
  map_add' p q := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [homogeneous] <;> ring
  map_smul' a p := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [homogeneous] <;> ring

theorem kernel_dimension : Module.finrank ℚ (LinearMap.ker M.mulVecLin) = 2 := by
  simpa using (LinearEquiv.finrank_eq parameters).symm

theorem rank_fourteen : M.rank = 14 := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [kernel_dimension] at h
  change M.rank+2 = Module.finrank ℚ (Fin 16 → ℚ) at h
  norm_num at h
  omega

end MainTheory.Orbit26PrintedMoments
