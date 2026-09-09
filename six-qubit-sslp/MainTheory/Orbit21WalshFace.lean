import MainTheory.Orbit21MomentFace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.Orbit21WalshFace

open MainTheory.Orbit21MomentFace

def rows : Matrix (Fin 7) (Fin 8) ℤ :=
  !![1,1,1,1,1,1,1,1;
     1,1,1,1,-1,-1,-1,-1;
     1,1,-1,-1,1,1,-1,-1;
     1,-1,1,-1,1,-1,1,-1;
     1,1,-1,-1,-1,-1,1,1;
     1,1,-1,1,-1,1,-1,-1;
     1,-1,-1,1,-1,1,1,-1]

def walsh : Matrix (Fin 7) (Fin 8) ℤ := fun i j =>
  if h : i.val=0 then 1 else
    if bottom j ⟨i.val-1,by omega⟩ then -1 else 1

theorem actual_rows : walsh=rows := by decide +kernel

noncomputable def W : Matrix (Fin 7) (Fin 8) ℂ := fun i j => rows i j

def kernelPattern (alpha beta : ℂ) : Fin 8 → ℂ :=
  ![beta,-beta,alpha,-alpha,-alpha,alpha,-beta,beta]

theorem kernel_iff (z : Fin 8 → ℂ) :
    W.mulVec z=0 ↔ z=kernelPattern (z 2) (z 0) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h ((0 : Fin 5).succ.succ)
    have h3 := congrFun h ((0 : Fin 4).succ.succ.succ)
    have h4 := congrFun h ((0 : Fin 3).succ.succ.succ.succ)
    have h5 := congrFun h ((0 : Fin 2).succ.succ.succ.succ.succ)
    simp [W,rows,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
    change z 0+(z 1+(z 2+(z 3+(z 4+(z 5+(z 6+z 7))))))=0 at h0
    change z 0+(z 1+(z 2+(z 3+(-z 4+(-z 5+(-z 6+ -z 7))))))=0 at h1
    change z 0+(z 1+(-z 2+(-z 3+(z 4+(z 5+(-z 6+ -z 7))))))=0 at h2
    change z 0+(-z 1+(z 2+(-z 3+(z 4+(-z 5+(z 6+ -z 7))))))=0 at h3
    change z 0+(z 1+(-z 2+(-z 3+(-z 4+(-z 5+(z 6+z 7))))))=0 at h4
    change z 0+(z 1+(-z 2+(z 3+(-z 4+(z 5+(-z 6+ -z 7))))))=0 at h5
    have hz1 : z 1 = -z 0 := by linear_combination (h0+h1+h2+h4)/4
    have hz3 : z 3 = -z 2 := by linear_combination (h0+h1-h2-h4)/4
    have hz4 : z 4 = -z 2 := by linear_combination (h0+h1+h2-h4)/4-h5/2
    have hz5 : z 5 = z 2 := by linear_combination (-h1+h5)/2
    have hz6 : z 6 = -z 0 := by linear_combination (h0-h1-h2+h4)/4+(h3+h5)/2
    have hz7 : z 7 = z 0 := by linear_combination -(h3+h5)/2
    funext i
    fin_cases i <;> simp [kernelPattern,hz1,hz3,hz4,hz5,hz6,hz7]
  · intro h
    rw [h]
    ext i
    fin_cases i <;> simp [W,rows,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,kernelPattern]

def first : Fin 8 → ℂ := ![0,0,1,-1,-1,1,0,0]
def second : Fin 8 → ℂ := ![1,-1,0,0,0,0,-1,1]

theorem kernel_span (z : Fin 8 → ℂ) :
    W.mulVec z=0 ↔ ∃ alpha beta : ℂ,z=alpha • first+beta • second := by
  have hp (a b : ℂ) : kernelPattern a b=a • first+b • second := by
    funext i
    fin_cases i <;> simp [kernelPattern,first,second]
  constructor
  · intro h
    exact ⟨z 2,z 0,(kernel_iff z).1 h |>.trans (hp _ _)⟩
  · rintro ⟨a,b,rfl⟩
    rw [← hp]
    apply (kernel_iff _).2
    rfl

theorem uniform (alpha beta : ℝ) (z : Fin 8 → ℂ)
    (hz : W.mulVec z=0) (hm : ∀ i,‖z i‖=pattern alpha beta i) :
    alpha=1/8 ∧ beta=1/8 := by
  have hp := (kernel_iff z).1 hz
  have h1 : z 1= -z 0 := congrFun hp 1
  have h3 : z 3= -z 2 := congrFun hp 3
  have hm0 := hm 0
  have hm1 := hm 1
  have hm2 := hm 2
  have hm3 := hm 3
  rw [h1,norm_neg] at hm1
  rw [h3,norm_neg] at hm3
  change ‖z 0‖=alpha at hm0
  change ‖z 0‖=1/4-alpha at hm1
  change ‖z 2‖=beta at hm2
  change ‖z 2‖=1/4-beta at hm3
  constructor <;> linarith

end MainTheory.Orbit21WalshFace
