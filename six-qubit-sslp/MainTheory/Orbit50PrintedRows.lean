import MainTheory.OrderThreePrintedMoments
import MainTheory.RectangularFlipCharacters

/-! Literal orbit-50 tables in complementary top indexing. The native top
order is reversed; the Z4 row has an explicit harmless global sign change
to match the SI row-reduced convention. Every physical incidence is retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit50PrintedRows
open scoped BigOperators Matrix
open SixQubit.Orbit50
noncomputable section

namespace Row00
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨4,by decide⟩) (SS.stdBasis ⟨5,by decide⟩)
def printedSources : Fin 2 → Fin 11 := ![⟨10,by decide⟩,⟨0,by decide⟩]
def printedDestinations : Fin 2 → Fin 11 := ![⟨0,by decide⟩,⟨10,by decide⟩]
def sources : Fin 2 → SS.BitString 6 := ![z0,z10]
def destinations : Fin 2 → SS.BitString 6 := ![y0,y10]
def characters : Fin 1 → SS.BitString 6 := ![(fun _ => false)]
def rowSign : Fin 1 → ℚ := ![1]
def W : Matrix (Fin 1) (Fin 2) ℚ := !![1,1]
def WC : Matrix (Fin 1) (Fin 2) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 2 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin 1) (j : Fin 2) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 2) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
theorem row_reduction (v : Fin 2 → ℂ) : WC *ᵥ v=0 ↔ v 0+v 1=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
  · intro h0
    ext i
    fin_cases i
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y0)*d z0+star (c y10)*d z10=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row00

namespace Row01
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨1,by decide⟩)
def printedSources : Fin 2 → Fin 11 := ![⟨1,by decide⟩,⟨0,by decide⟩]
def printedDestinations : Fin 2 → Fin 11 := ![⟨0,by decide⟩,⟨1,by decide⟩]
def sources : Fin 2 → SS.BitString 6 := ![z9,z10]
def destinations : Fin 2 → SS.BitString 6 := ![y0,y1]
def characters : Fin 1 → SS.BitString 6 := ![(fun _ => false)]
def rowSign : Fin 1 → ℚ := ![1]
def W : Matrix (Fin 1) (Fin 2) ℚ := !![1,1]
def WC : Matrix (Fin 1) (Fin 2) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 2 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin 1) (j : Fin 2) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 2) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
theorem row_reduction (v : Fin 2 → ℂ) : WC *ᵥ v=0 ↔ v 0+v 1=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
  · intro h0
    ext i
    fin_cases i
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y0)*d z9+star (c y1)*d z10=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row01

namespace Row02
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨2,by decide⟩)
def printedSources : Fin 2 → Fin 11 := ![⟨2,by decide⟩,⟨0,by decide⟩]
def printedDestinations : Fin 2 → Fin 11 := ![⟨0,by decide⟩,⟨2,by decide⟩]
def sources : Fin 2 → SS.BitString 6 := ![z8,z10]
def destinations : Fin 2 → SS.BitString 6 := ![y0,y2]
def characters : Fin 1 → SS.BitString 6 := ![(fun _ => false)]
def rowSign : Fin 1 → ℚ := ![1]
def W : Matrix (Fin 1) (Fin 2) ℚ := !![1,1]
def WC : Matrix (Fin 1) (Fin 2) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 2 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin 1) (j : Fin 2) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 2) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
theorem row_reduction (v : Fin 2 → ℂ) : WC *ᵥ v=0 ↔ v 0+v 1=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
  · intro h0
    ext i
    fin_cases i
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y0)*d z8+star (c y2)*d z10=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row02

namespace Row03
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨1,by decide⟩) (SS.stdBasis ⟨2,by decide⟩)
def printedSources : Fin 2 → Fin 11 := ![⟨5,by decide⟩,⟨0,by decide⟩]
def printedDestinations : Fin 2 → Fin 11 := ![⟨0,by decide⟩,⟨5,by decide⟩]
def sources : Fin 2 → SS.BitString 6 := ![z5,z10]
def destinations : Fin 2 → SS.BitString 6 := ![y0,y5]
def characters : Fin 1 → SS.BitString 6 := ![(fun _ => false)]
def rowSign : Fin 1 → ℚ := ![1]
def W : Matrix (Fin 1) (Fin 2) ℚ := !![1,1]
def WC : Matrix (Fin 1) (Fin 2) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 2 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin 1) (j : Fin 2) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 2) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
theorem row_reduction (v : Fin 2 → ℂ) : WC *ᵥ v=0 ↔ v 0+v 1=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
  · intro h0
    ext i
    fin_cases i
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    exact h0
theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y0)*d z5+star (c y5)*d z10=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he
end Row03

namespace Row04
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨2,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)
def printedSources : Fin 6 → Fin 11 := ![⟨10,by decide⟩,⟨7,by decide⟩,⟨6,by decide⟩,⟨4,by decide⟩,⟨3,by decide⟩,⟨1,by decide⟩]
def printedDestinations : Fin 6 → Fin 11 := ![⟨1,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨10,by decide⟩]
def sources : Fin 6 → SS.BitString 6 := ![z0,z3,z4,z6,z7,z9]
def destinations : Fin 6 → SS.BitString 6 := ![y1,y3,y4,y6,y7,y10]
def characters : Fin 2 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨3,by decide⟩]
def rowSign : Fin 2 → ℚ := ![1,-1]
def W : Matrix (Fin 2) (Fin 6) ℚ := !![1,1,1,1,1,1;-1,1,1,1,1,-1]
def WC : Matrix (Fin 2) (Fin 6) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 6 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin 2) (j : Fin 6) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 6) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
theorem row_reduction (v : Fin 6 → ℂ) : WC *ᵥ v=0 ↔ v 0+v ⟨5,by decide⟩=0 ∧ v 1+v ⟨2,by decide⟩+v ⟨3,by decide⟩+v ⟨4,by decide⟩=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    constructor
    · linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1
    · linear_combination (1/2 : ℂ)*h0+(1/2 : ℂ)*h1
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination h0+h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination -h0+h1
theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y1)*d z0+star (c y10)*d z9=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he.1
end Row04

namespace Row05
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨1,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)
def printedSources : Fin 6 → Fin 11 := ![⟨10,by decide⟩,⟨9,by decide⟩,⟨8,by decide⟩,⟨4,by decide⟩,⟨3,by decide⟩,⟨2,by decide⟩]
def printedDestinations : Fin 6 → Fin 11 := ![⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩,⟨10,by decide⟩]
def sources : Fin 6 → SS.BitString 6 := ![z0,z1,z2,z6,z7,z8]
def destinations : Fin 6 → SS.BitString 6 := ![y2,y3,y4,y8,y9,y10]
def characters : Fin 2 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨3,by decide⟩]
def rowSign : Fin 2 → ℚ := ![1,-1]
def W : Matrix (Fin 2) (Fin 6) ℚ := !![1,1,1,1,1,1;-1,1,1,1,1,-1]
def WC : Matrix (Fin 2) (Fin 6) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 6 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin 2) (j : Fin 6) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 6) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
theorem row_reduction (v : Fin 6 → ℂ) : WC *ᵥ v=0 ↔ v 0+v ⟨5,by decide⟩=0 ∧ v 1+v ⟨2,by decide⟩+v ⟨3,by decide⟩+v ⟨4,by decide⟩=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    constructor
    · linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1
    · linear_combination (1/2 : ℂ)*h0+(1/2 : ℂ)*h1
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination h0+h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination -h0+h1
theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y2)*d z0+star (c y10)*d z8=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he.1
end Row05

namespace Row06
def flip : SS.BitString 6 := SS.bxor (SS.stdBasis ⟨0,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)
def printedSources : Fin 6 → Fin 11 := ![⟨10,by decide⟩,⟨9,by decide⟩,⟨8,by decide⟩,⟨7,by decide⟩,⟨6,by decide⟩,⟨5,by decide⟩]
def printedDestinations : Fin 6 → Fin 11 := ![⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩,⟨10,by decide⟩]
def sources : Fin 6 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5]
def destinations : Fin 6 → SS.BitString 6 := ![y5,y6,y7,y8,y9,y10]
def characters : Fin 2 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨3,by decide⟩]
def rowSign : Fin 2 → ℚ := ![1,-1]
def W : Matrix (Fin 2) (Fin 6) ℚ := !![1,1,1,1,1,1;-1,1,1,1,1,-1]
def WC : Matrix (Fin 2) (Fin 6) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 6 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem literal_indexing : ∀ j,
    sources j=MainTheory.OrderThreePrintedMoments.Orbit50.top
      (MainTheory.OrderThreePrintedMoments.Orbit50.complementIndex (printedSources j)) ∧
    destinations j=MainTheory.OrderThreePrintedMoments.Orbit50.bottom (printedDestinations j) := by decide +kernel
theorem actual_incidence : Finset.univ.image sources=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=rowSign i*(if SS.bdot (characters i) (sources j) then -1 else 1) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem printed_entry (i : Fin 2) (j : Fin 6) :
    WC i j=(rowSign i : ℂ)*MainTheory.RectangularFlipCharacters.matrix characters sources i j := by
  unfold WC
  rw [actual_characters]
  unfold MainTheory.RectangularFlipCharacters.matrix MainTheory.FlipCharacter.character
  split <;> push_cast <;> ring
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 6) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  have he := MainTheory.RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  change MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d=0 at he
  ext i
  change (∑ j, WC i j*products c d j)=0
  simp_rw [printed_entry,mul_assoc]
  rw [← Finset.mul_sum]
  change (rowSign i : ℂ)*(MainTheory.RectangularFlipCharacters.matrix characters sources *ᵥ products c d) i=0
  rw [he]
  simp only [Pi.zero_apply,mul_zero]
theorem row_reduction (v : Fin 6 → ℂ) : WC *ᵥ v=0 ↔ v 0+v ⟨5,by decide⟩=0 ∧ v 1+v ⟨2,by decide⟩+v ⟨3,by decide⟩+v ⟨4,by decide⟩=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
    constructor
    · linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1
    · linear_combination (1/2 : ℂ)*h0+(1/2 : ℂ)*h1
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination h0+h1
    · norm_num [WC,W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at *
      linear_combination -h0+h1
theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (c y5)*d z0+star (c y10)*d z5=0 := by
  have he := (row_reduction _).1 (physical_rows c d hc hd hkl)
  simpa only [product_expansion,sources,destinations] using he.1
end Row06

end
end MainTheory.Orbit50PrintedRows
