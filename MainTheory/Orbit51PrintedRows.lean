import MainTheory.OrderThreePrintedMoments
import MainTheory.RectangularFlipCharacters

/-! Every orbit-51 flip and incidence printed in the SI. Rectangular
character systems retain all incidences and all zero-amplitude boundaries.
Both directions of the printed kernels and row reductions are checked. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit51PrintedRows
open scoped BigOperators Matrix
open SixQubit.Orbit51
noncomputable section

namespace Row00
def flip : SS.BitString 6 := SS.stdBasis ⟨2,by decide⟩
def sources : Fin 4 → SS.BitString 6 := ![z9,z8,z1,z0]
def destinations : Fin 4 → SS.BitString 6 := ![y0,y1,y8,y9]
def characters : Fin 3 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨3,by decide⟩]
def W : Matrix (Fin 3) (Fin 4) ℚ := !![1,1,1,1;1,1,-1,-1;1,-1,1,-1]
def WC : Matrix (Fin 3) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem row_reduction (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ v 0=v ⟨3,by decide⟩ ∧ v 1=v ⟨2,by decide⟩ ∧ v 0+v 1=0 := by
  constructor
  · intro h
    have h0 := congrFun h ⟨0,by decide⟩
    have h1 := congrFun h ⟨1,by decide⟩
    have h2 := congrFun h ⟨2,by decide⟩
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    refine ⟨?_,?_,?_⟩
    · linear_combination (1/2 : ℂ)*h1 + (1/2 : ℂ)*h2
    · linear_combination (1/2 : ℂ)*h1 + (-1/2 : ℂ)*h2
    · linear_combination (1/2 : ℂ)*h0 + (1/2 : ℂ)*h1
  · rintro ⟨h0,h1,h2⟩
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (-1 : ℂ)*h0 + (-1 : ℂ)*h1 + (2 : ℂ)*h2
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (-1 : ℂ)*h1
theorem kernel_span (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ ∃ a : ℂ, v=![a,-a,-a,a] := by
  constructor
  · intro h
    obtain ⟨h0,h1,h2⟩ := (row_reduction v).1 h
    refine ⟨v 0,?_⟩
    ext i
    fin_cases i
    · rfl
    · change v 1= -v 0
      linear_combination h2
    · change v ⟨2,by decide⟩= -v 0
      linear_combination h2-h1
    · change v ⟨3,by decide⟩=v 0
      exact h0.symm
  · rintro ⟨a,rfl⟩
    apply (row_reduction _).2
    norm_num [Fin.succ]
theorem physical_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c y0)*d z9=star (c y9)*d z0 ∧ star (c y1)*d z8=star (c y8)*d z1 ∧ star (c y0)*d z9+star (c y1)*d z8=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row00

namespace Row01
def flip : SS.BitString 6 := SS.stdBasis ⟨5,by decide⟩
def sources : Fin 4 → SS.BitString 6 := ![z9,z8,z3,z2]
def destinations : Fin 4 → SS.BitString 6 := ![y2,y3,y8,y9]
def characters : Fin 3 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨3,by decide⟩]
def W : Matrix (Fin 3) (Fin 4) ℚ := !![1,1,1,1;1,1,-1,-1;1,-1,1,-1]
def WC : Matrix (Fin 3) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem row_reduction (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ v 0=v ⟨3,by decide⟩ ∧ v 1=v ⟨2,by decide⟩ ∧ v 0+v 1=0 := by
  constructor
  · intro h
    have h0 := congrFun h ⟨0,by decide⟩
    have h1 := congrFun h ⟨1,by decide⟩
    have h2 := congrFun h ⟨2,by decide⟩
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    refine ⟨?_,?_,?_⟩
    · linear_combination (1/2 : ℂ)*h1 + (1/2 : ℂ)*h2
    · linear_combination (1/2 : ℂ)*h1 + (-1/2 : ℂ)*h2
    · linear_combination (1/2 : ℂ)*h0 + (1/2 : ℂ)*h1
  · rintro ⟨h0,h1,h2⟩
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (-1 : ℂ)*h0 + (-1 : ℂ)*h1 + (2 : ℂ)*h2
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (-1 : ℂ)*h1
theorem kernel_span (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ ∃ a : ℂ, v=![a,-a,-a,a] := by
  constructor
  · intro h
    obtain ⟨h0,h1,h2⟩ := (row_reduction v).1 h
    refine ⟨v 0,?_⟩
    ext i
    fin_cases i
    · rfl
    · change v 1= -v 0
      linear_combination h2
    · change v ⟨2,by decide⟩= -v 0
      linear_combination h2-h1
    · change v ⟨3,by decide⟩=v 0
      exact h0.symm
  · rintro ⟨a,rfl⟩
    apply (row_reduction _).2
    norm_num [Fin.succ]
theorem physical_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c y2)*d z9=star (c y9)*d z2 ∧ star (c y3)*d z8=star (c y8)*d z3 ∧ star (c y2)*d z9+star (c y3)*d z8=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row01

namespace Row02
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)
def sources : Fin 4 → SS.BitString 6 := ![z6,z7,z8,z9]
def destinations : Fin 4 → SS.BitString 6 := ![y8,y9,y6,y7]
def characters : Fin 4 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨3,by decide⟩,SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)]
def W : Matrix (Fin 4) (Fin 4) ℚ := !![1,1,1,1;1,1,1,1;-1,1,-1,1;-1,1,-1,1]
def WC : Matrix (Fin 4) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem row_reduction (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ v 0+v ⟨2,by decide⟩=0 ∧ v 1+v ⟨3,by decide⟩=0 := by
  constructor
  · intro h
    have h0 := congrFun h ⟨0,by decide⟩
    have h1 := congrFun h ⟨1,by decide⟩
    have h2 := congrFun h ⟨2,by decide⟩
    have h3 := congrFun h ⟨3,by decide⟩
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    refine ⟨?_,?_⟩
    · linear_combination (1/2 : ℂ)*h0 + (-1/2 : ℂ)*h2
    · linear_combination (1/2 : ℂ)*h0 + (1/2 : ℂ)*h2
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (-1 : ℂ)*h0 + (1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (-1 : ℂ)*h0 + (1 : ℂ)*h1
theorem physical_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c y8)*d z6+star (c y6)*d z8=0 ∧ star (c y9)*d z7+star (c y7)*d z9=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row02

namespace Row03
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨4,by decide⟩)
def sources : Fin 4 → SS.BitString 6 := ![z6,z7,z8,z9]
def destinations : Fin 4 → SS.BitString 6 := ![y9,y8,y7,y6]
def characters : Fin 4 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨4,by decide⟩,SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨4,by decide⟩)]
def W : Matrix (Fin 4) (Fin 4) ℚ := !![1,1,1,1;1,1,1,1;1,-1,-1,1;1,-1,-1,1]
def WC : Matrix (Fin 4) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem row_reduction (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ v 0+v ⟨3,by decide⟩=0 ∧ v 1+v ⟨2,by decide⟩=0 := by
  constructor
  · intro h
    have h0 := congrFun h ⟨0,by decide⟩
    have h1 := congrFun h ⟨1,by decide⟩
    have h2 := congrFun h ⟨2,by decide⟩
    have h3 := congrFun h ⟨3,by decide⟩
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    refine ⟨?_,?_⟩
    · linear_combination (1/2 : ℂ)*h0 + (1/2 : ℂ)*h2
    · linear_combination (1/2 : ℂ)*h0 + (-1/2 : ℂ)*h2
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (-1 : ℂ)*h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0 + (-1 : ℂ)*h1
theorem physical_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c y9)*d z6+star (c y6)*d z9=0 ∧ star (c y8)*d z7+star (c y7)*d z8=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row03

namespace Row04
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨1,by decide⟩)
def sources : Fin 4 → SS.BitString 6 := ![z3,z2,z1,z0]
def destinations : Fin 4 → SS.BitString 6 := ![y0,y1,y2,y3]
def characters : Fin 4 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨1,by decide⟩,SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨1,by decide⟩)]
def W : Matrix (Fin 4) (Fin 4) ℚ := !![1,1,1,1;-1,-1,-1,-1;-1,-1,-1,-1;1,1,1,1]
def WC : Matrix (Fin 4) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem row_reduction (v : Fin 4 → ℂ) : WC *ᵥ v=0 ↔ v 0+v 1+v ⟨2,by decide⟩+v ⟨3,by decide⟩=0 := by
  constructor
  · intro h
    have h0 := congrFun h ⟨0,by decide⟩
    have h1 := congrFun h ⟨1,by decide⟩
    have h2 := congrFun h ⟨2,by decide⟩
    have h3 := congrFun h ⟨3,by decide⟩
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    linear_combination (1 : ℂ)*h0
  · intro h0
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (-1 : ℂ)*h0
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (-1 : ℂ)*h0
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination (1 : ℂ)*h0
theorem physical_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c y0)*d z3+star (c y1)*d z2+star (c y2)*d z1+star (c y3)*d z0=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row04

end
end MainTheory.Orbit51PrintedRows
