import MainTheory.RectangularFlipCharacters
import SixQubit.CodeOrbit18
import SixQubit.CodeOrbit41
import MainTheory.FlipCharacterObstruction

/-! Exact displayed shell systems on the actual fibers and the literal
restricted-Walsh projectors isolating their forced positive anchors. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.OrderTwoShellProjectors
open scoped BigOperators Matrix
noncomputable section
def characterQ (z x : SS.BitString 6) : ℚ := if SS.bdot z x then -1 else 1

namespace Orbit18
open SixQubit.Orbit18
def bottom : Fin 16 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def top : Fin 16 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]
def coordinates (x : SS.BitString 6) : ℕ × ℕ := ((∑ j : Fin 5, if x ⟨j.val,by omega⟩ then 1 else 0),if x ⟨5,by decide⟩ then 1 else 0)
def bottomTypes : Fin 3 → ℕ × ℕ := ![(0,0),(4,0),(2,1)]
def topTypes : Fin 3 → ℕ × ℕ := ![(2,0),(0,1),(4,1)]
theorem actual_coordinates :
    (∀ i, coordinates (bottom i)=![(0,0),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(4,0),(2,1),(2,1),(2,1),(4,0),(2,1),(4,0),(4,0),(4,0)] i) ∧
    (∀ i, coordinates (top i)=![(0,1),(2,0),(2,0),(2,0),(2,0),(2,0),(2,0),(4,1),(2,0),(2,0),(2,0),(4,1),(2,0),(4,1),(4,1),(4,1)] i) := by decide +kernel
theorem shell_types : (∀ x, x ∈ S0 ↔ ∃ j, coordinates x=bottomTypes j) ∧
    (∀ x, x ∈ S1 ↔ ∃ j, coordinates x=topTypes j) := by decide +kernel
theorem point_projector : ∀ x ∈ S1,
    (1-2*characterQ (SS.stdBasis ⟨5,by decide⟩) x+(∑ j : Fin 5, characterQ (SS.stdBasis ⟨j.val,by omega⟩) x))/8=(if x=z0 then 1 else 0) := by decide +kernel
def bottomMass (p : Fin 16 → ℝ) : Fin 3 → ℝ := ![(p ⟨0,by decide⟩),(p ⟨7,by decide⟩+p ⟨11,by decide⟩+p ⟨13,by decide⟩+p ⟨14,by decide⟩+p ⟨15,by decide⟩),(p ⟨1,by decide⟩+p ⟨2,by decide⟩+p ⟨3,by decide⟩+p ⟨4,by decide⟩+p ⟨5,by decide⟩+p ⟨6,by decide⟩+p ⟨8,by decide⟩+p ⟨9,by decide⟩+p ⟨10,by decide⟩+p ⟨12,by decide⟩)]
def topMass (q : Fin 16 → ℝ) : Fin 3 → ℝ := ![(q ⟨1,by decide⟩+q ⟨2,by decide⟩+q ⟨3,by decide⟩+q ⟨4,by decide⟩+q ⟨5,by decide⟩+q ⟨6,by decide⟩+q ⟨8,by decide⟩+q ⟨9,by decide⟩+q ⟨10,by decide⟩+q ⟨12,by decide⟩),(q ⟨0,by decide⟩),(q ⟨7,by decide⟩+q ⟨11,by decide⟩+q ⟨13,by decide⟩+q ⟨14,by decide⟩+q ⟨15,by decide⟩)]
theorem actual_shell_masses (p q : Fin 16 → ℝ) :
    (∀ j, bottomMass p j=∑ i : Fin 16, if coordinates (bottom i)=bottomTypes j then p i else 0) ∧
    (∀ j, topMass q j=∑ i : Fin 16, if coordinates (top i)=topTypes j then q i else 0) := by
  constructor
  · intro j
    simp_rw [actual_coordinates.1]
    fin_cases j <;> norm_num [bottomMass,bottomTypes,
      Fin.sum_univ_succ,Fin.succ] <;> ring
  · intro j
    simp_rw [actual_coordinates.2]
    fin_cases j <;> norm_num [topMass,topTypes,
      Fin.sum_univ_succ,Fin.succ] <;> ring
def Moment (p q : Fin 16 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (p ⟨10,by decide⟩) (p ⟨11,by decide⟩) (p ⟨12,by decide⟩) (p ⟨13,by decide⟩) (p ⟨14,by decide⟩) (p ⟨15,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩)
def ShellSystem (A B C D E F : ℝ) : Prop := A+B+C=1 ∧ D+E+F=1 ∧ C=E+F ∧ 2*C=4*F ∧ 4*B+2*C=2*D+4*F ∧ 6*B+C=D+6*F
theorem shell_system (p q : Fin 16 → ℝ) (hm : Moment p q) : ShellSystem (bottomMass p ⟨0,by decide⟩) (bottomMass p ⟨1,by decide⟩) (bottomMass p ⟨2,by decide⟩) (topMass q ⟨0,by decide⟩) (topMass q ⟨1,by decide⟩) (topMass q ⟨2,by decide⟩) := by
  change MomentSystem (p 0) (p 1) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (p ⟨10,by decide⟩) (p ⟨11,by decide⟩) (p ⟨12,by decide⟩) (p ⟨13,by decide⟩) (p ⟨14,by decide⟩) (p ⟨15,by decide⟩) (q 0) (q 1) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩) at hm
  unfold ShellSystem
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.n0
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.n1
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m6
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m16 + (1 : ℝ)*hm.m26 + (1 : ℝ)*hm.m36 + (1 : ℝ)*hm.m46 + (1 : ℝ)*hm.m56
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m1 + (1 : ℝ)*hm.m2 + (1 : ℝ)*hm.m3 + (1 : ℝ)*hm.m4 + (1 : ℝ)*hm.m5
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m12 + (1 : ℝ)*hm.m13 + (1 : ℝ)*hm.m14 + (1 : ℝ)*hm.m15 + (1 : ℝ)*hm.m23 + (1 : ℝ)*hm.m24 + (1 : ℝ)*hm.m25 + (1 : ℝ)*hm.m34 + (1 : ℝ)*hm.m35 + (1 : ℝ)*hm.m45
theorem character_sum : ∀ x : SS.BitString 6,
    (∑ j : Fin 5, characterQ (SS.stdBasis ⟨j.val,by omega⟩) x)=5-2*(coordinates x).1 := by decide +kernel
theorem shell_solution (A B C D E F : ℝ) (h : ShellSystem A B C D E F) :
    A=1/4 ∧ B=1/4 ∧ C=1/2 ∧ D=1/2 ∧ E=1/4 ∧ F=1/4 := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith only [h0,h1,h2,h3,h4,h5]
theorem physical_moment (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
  SixQubit.Orbit18.moments c d hc hd hnc hnd hkl
theorem physical_shell_system (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ShellSystem (bottomMass (fun i => Complex.normSq (c (bottom i))) ⟨0,by decide⟩) (bottomMass (fun i => Complex.normSq (c (bottom i))) ⟨1,by decide⟩) (bottomMass (fun i => Complex.normSq (c (bottom i))) ⟨2,by decide⟩)
      (topMass (fun i => Complex.normSq (d (top i))) ⟨0,by decide⟩) (topMass (fun i => Complex.normSq (d (top i))) ⟨1,by decide⟩) (topMass (fun i => Complex.normSq (d (top i))) ⟨2,by decide⟩) :=
  shell_system (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i)))
    (physical_moment c d hc hd hnc hnd hkl)
def flip : SS.BitString 6 := SS.stdBasis ⟨5,by decide⟩
def characters : Fin 7 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨5,by decide⟩,SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨1,by decide⟩,SS.stdBasis ⟨2,by decide⟩,SS.stdBasis ⟨3,by decide⟩,SS.stdBasis ⟨4,by decide⟩]
def W : Matrix (Fin 7) (Fin 16) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(-1),(1),(1),(1),(1),(1),(1),(-1),(1),(1),(1),(-1),(1),(-1),(-1),(-1)],![(1),(1),(1),(1),(1),(1),(1),(1),(-1),(-1),(-1),(-1),(-1),(-1),(-1),(-1)],![(1),(1),(1),(1),(-1),(-1),(-1),(-1),(1),(1),(1),(1),(-1),(-1),(-1),(-1)],![(1),(1),(-1),(-1),(1),(1),(-1),(-1),(1),(1),(-1),(-1),(1),(1),(-1),(-1)],![(1),(-1),(1),(-1),(1),(-1),(1),(-1),(1),(-1),(1),(-1),(1),(-1),(1),(-1)],![(1),(-1),(-1),(1),(-1),(1),(1),(-1),(-1),(1),(1),(-1),(1),(-1),(-1),(1)]]
def WC : Matrix (Fin 7) (Fin 16) ℂ := W.map (Rat.castHom ℂ)
def coefficients : Matrix (Fin 1) (Fin 7) ℚ := ![![(1/8),(-1/4),(1/8),(1/8),(1/8),(1/8),(1/8)]]
def coefficientsC : Matrix (Fin 1) (Fin 7) ℂ := coefficients.map (Rat.castHom ℂ)
def anchorRow : Matrix (Fin 1) (Fin 16) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0)]]
def anchorRowC : Matrix (Fin 1) (Fin 16) ℂ := anchorRow.map (Rat.castHom ℂ)
theorem actual_incidence : Finset.univ.image top=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=characterQ (characters i) (top j) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  unfold characterQ
  split <;> norm_num
theorem projector_checked : coefficients*W=anchorRow := by
  have he : ∀ i j, (coefficients*W) i j=anchorRow i j := by decide +kernel
  exact Matrix.ext he
theorem complex_projector : coefficientsC*WC=anchorRowC := by
  rw [coefficientsC,WC,anchorRowC,← Matrix.map_mul,projector_checked]
theorem anchor_extraction (v : Fin 16 → ℂ) : anchorRowC *ᵥ v=(fun _ => v 0) := by
  ext i
  fin_cases i
  norm_num [anchorRowC,anchorRow,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
def products (c d : SS.State 6 ℂ) : Fin 16 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_anchor_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : products c d 0=0 := by
  have he : anchorRowC *ᵥ products c d=0 := by
    rw [← complex_projector,← Matrix.mulVec_mulVec,physical_rows c d hc hd hkl,Matrix.mulVec_zero]
  rw [anchor_extraction] at he
  exact congrFun he 0
theorem physical_anchor_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Complex.normSq (products c d 0)=1/16 := by
  obtain ⟨hp,hq⟩ := (physical_moment c d hc hd hnc hnd hkl).endpoints
  change Complex.normSq (c (bottom 0))=1/4 at hp
  change Complex.normSq (d (top 0))=1/4 at hq
  unfold products
  rw [MainTheory.FlipCharacter.normSq_incidenceMonomial,actual_images,hp,hq]
  norm_num
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have he := physical_anchor_norm c d hc hd hnc hnd hkl
  rw [physical_anchor_zero c d hc hd hkl,Complex.normSq_zero] at he
  norm_num at he
end Orbit18

namespace Orbit41
open SixQubit.Orbit41
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def coordinates (x : SS.BitString 6) : ℕ × ℕ × ℕ := ((∑ j : Fin 4, if x ⟨j.val,by omega⟩ then 1 else 0),if x ⟨4,by decide⟩ then 1 else 0,if x ⟨5,by decide⟩ then 1 else 0)
def bottomTypes : Fin 4 → ℕ × ℕ × ℕ := ![(0,0,0),(1,1,1),(3,0,1),(4,1,0)]
def topTypes : Fin 4 → ℕ × ℕ × ℕ := ![(0,0,1),(1,1,0),(3,0,0),(4,1,1)]
theorem actual_coordinates :
    (∀ i, coordinates (bottom i)=![(0,0,0),(1,1,1),(1,1,1),(1,1,1),(3,0,1),(1,1,1),(3,0,1),(3,0,1),(3,0,1),(4,1,0)] i) ∧
    (∀ i, coordinates (top i)=![(0,0,1),(1,1,0),(1,1,0),(1,1,0),(3,0,0),(1,1,0),(3,0,0),(3,0,0),(3,0,0),(4,1,1)] i) := by decide +kernel
theorem shell_types : (∀ x, x ∈ S0 ↔ ∃ j, coordinates x=bottomTypes j) ∧
    (∀ x, x ∈ S1 ↔ ∃ j, coordinates x=topTypes j) := by decide +kernel
theorem point_projector : ∀ x ∈ S1,
    (1-characterQ (SS.stdBasis ⟨5,by decide⟩) x+characterQ (SS.stdBasis 0) x-characterQ (SS.bxor (SS.stdBasis 0) (SS.stdBasis ⟨5,by decide⟩)) x)/4=(if x=z0 then 1 else 0) := by decide +kernel
def bottomMass (p : Fin 10 → ℝ) : Fin 4 → ℝ := ![(p ⟨0,by decide⟩),(p ⟨1,by decide⟩+p ⟨2,by decide⟩+p ⟨3,by decide⟩+p ⟨5,by decide⟩),(p ⟨4,by decide⟩+p ⟨6,by decide⟩+p ⟨7,by decide⟩+p ⟨8,by decide⟩),(p ⟨9,by decide⟩)]
def topMass (q : Fin 10 → ℝ) : Fin 4 → ℝ := ![(q ⟨0,by decide⟩),(q ⟨1,by decide⟩+q ⟨2,by decide⟩+q ⟨3,by decide⟩+q ⟨5,by decide⟩),(q ⟨4,by decide⟩+q ⟨6,by decide⟩+q ⟨7,by decide⟩+q ⟨8,by decide⟩),(q ⟨9,by decide⟩)]
theorem actual_shell_masses (p q : Fin 10 → ℝ) :
    (∀ j, bottomMass p j=∑ i : Fin 10, if coordinates (bottom i)=bottomTypes j then p i else 0) ∧
    (∀ j, topMass q j=∑ i : Fin 10, if coordinates (top i)=topTypes j then q i else 0) := by
  constructor
  · intro j
    simp_rw [actual_coordinates.1]
    fin_cases j <;> norm_num [bottomMass,bottomTypes,
      Fin.sum_univ_succ,Fin.succ] <;> ring
  · intro j
    simp_rw [actual_coordinates.2]
    fin_cases j <;> norm_num [topMass,topTypes,
      Fin.sum_univ_succ,Fin.succ] <;> ring
def Moment (p q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
def ShellSystem (A B C D E F G H : ℝ) : Prop := A+B+C+D=1 ∧ E+F+G+H=1 ∧ B=H ∧ B+3*C=4*H ∧ 3*C+6*D=3*G+6*H ∧ B+C=E+H ∧ B+D=F+H ∧ B+3*C+4*D=F+3*G+4*H
theorem shell_system (p q : Fin 10 → ℝ) (hm : Moment p q) : ShellSystem (bottomMass p ⟨0,by decide⟩) (bottomMass p ⟨1,by decide⟩) (bottomMass p ⟨2,by decide⟩) (bottomMass p ⟨3,by decide⟩) (topMass q ⟨0,by decide⟩) (topMass q ⟨1,by decide⟩) (topMass q ⟨2,by decide⟩) (topMass q ⟨3,by decide⟩) := by
  change MomentSystem (p 0) (p 1) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q 0) (q 1) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) at hm
  unfold ShellSystem
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.n0
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.n1
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m56
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m16 + (1 : ℝ)*hm.m26 + (1 : ℝ)*hm.m36 + (1 : ℝ)*hm.m46
  · norm_num [bottomMass,topMass]
    linear_combination (-1 : ℝ)*hm.m1 + (1 : ℝ)*hm.m2 + (1 : ℝ)*hm.m3 + (1 : ℝ)*hm.m4 + (-1 : ℝ)*hm.m5 + (1 : ℝ)*hm.m12 + (1 : ℝ)*hm.m13 + (1 : ℝ)*hm.m14 + (2 : ℝ)*hm.m15
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m6
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m5
  · norm_num [bottomMass,topMass]
    linear_combination (1 : ℝ)*hm.m1 + (1 : ℝ)*hm.m2 + (1 : ℝ)*hm.m3 + (1 : ℝ)*hm.m4
theorem shell_chain (A B C D E F G H : ℝ) (h : ShellSystem A B C D E F G H) :
    C=B ∧ E=B ∧ F=D ∧ G=D ∧ D=B := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7]
theorem shell_solution (A B C D E F G H : ℝ) (h : ShellSystem A B C D E F G H) :
    A=1/4 ∧ B=1/4 ∧ C=1/4 ∧ D=1/4 ∧ E=1/4 ∧ F=1/4 ∧ G=1/4 ∧ H=1/4 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7]
theorem physical_moment (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
  SixQubit.Orbit41.moments c d hc hd hnc hnd hkl
theorem physical_shell_system (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ShellSystem (bottomMass (fun i => Complex.normSq (c (bottom i))) ⟨0,by decide⟩) (bottomMass (fun i => Complex.normSq (c (bottom i))) ⟨1,by decide⟩) (bottomMass (fun i => Complex.normSq (c (bottom i))) ⟨2,by decide⟩) (bottomMass (fun i => Complex.normSq (c (bottom i))) ⟨3,by decide⟩)
      (topMass (fun i => Complex.normSq (d (top i))) ⟨0,by decide⟩) (topMass (fun i => Complex.normSq (d (top i))) ⟨1,by decide⟩) (topMass (fun i => Complex.normSq (d (top i))) ⟨2,by decide⟩) (topMass (fun i => Complex.normSq (d (top i))) ⟨3,by decide⟩) :=
  shell_system (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i)))
    (physical_moment c d hc hd hnc hnd hkl)
def flip : SS.BitString 6 := SS.stdBasis ⟨5,by decide⟩
def characters : Fin 4 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨5,by decide⟩,SS.stdBasis ⟨0,by decide⟩,SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨5,by decide⟩)]
def W : Matrix (Fin 4) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(-1),(1),(1),(1),(1),(1),(1),(1),(1),(-1)],![(1),(1),(1),(1),(1),(-1),(-1),(-1),(-1),(-1)],![(-1),(1),(1),(1),(1),(-1),(-1),(-1),(-1),(1)]]
def WC : Matrix (Fin 4) (Fin 10) ℂ := W.map (Rat.castHom ℂ)
def coefficients : Matrix (Fin 1) (Fin 4) ℚ := ![![(1/4),(-1/4),(1/4),(-1/4)]]
def coefficientsC : Matrix (Fin 1) (Fin 4) ℂ := coefficients.map (Rat.castHom ℂ)
def anchorRow : Matrix (Fin 1) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)]]
def anchorRowC : Matrix (Fin 1) (Fin 10) ℂ := anchorRow.map (Rat.castHom ℂ)
theorem actual_incidence : Finset.univ.image top=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=characterQ (characters i) (top j) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  unfold characterQ
  split <;> norm_num
theorem projector_checked : coefficients*W=anchorRow := by
  have he : ∀ i j, (coefficients*W) i j=anchorRow i j := by decide +kernel
  exact Matrix.ext he
theorem complex_projector : coefficientsC*WC=anchorRowC := by
  rw [coefficientsC,WC,anchorRowC,← Matrix.map_mul,projector_checked]
theorem anchor_extraction (v : Fin 10 → ℂ) : anchorRowC *ᵥ v=(fun _ => v 0) := by
  ext i
  fin_cases i
  norm_num [anchorRowC,anchorRow,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
def products (c d : SS.State 6 ℂ) : Fin 10 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_anchor_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : products c d 0=0 := by
  have he : anchorRowC *ᵥ products c d=0 := by
    rw [← complex_projector,← Matrix.mulVec_mulVec,physical_rows c d hc hd hkl,Matrix.mulVec_zero]
  rw [anchor_extraction] at he
  exact congrFun he 0
theorem physical_anchor_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Complex.normSq (products c d 0)=1/16 := by
  obtain ⟨hp,hq⟩ := (physical_moment c d hc hd hnc hnd hkl).endpoints
  change Complex.normSq (c (bottom 0))=1/4 at hp
  change Complex.normSq (d (top 0))=1/4 at hq
  unfold products
  rw [MainTheory.FlipCharacter.normSq_incidenceMonomial,actual_images,hp,hq]
  norm_num
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have he := physical_anchor_norm c d hc hd hnc hnd hkl
  rw [physical_anchor_zero c d hc hd hkl,Complex.normSq_zero] at he
  norm_num at he
end Orbit41

end
end MainTheory.OrderTwoShellProjectors
