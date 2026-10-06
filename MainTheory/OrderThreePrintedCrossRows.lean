import MainTheory.OrderThreePrintedMoments
import MainTheory.FlipCharacterObstruction

/-! Literal physical cross-incidence systems of SI orbits 47, 48 and 52.
Every displayed intermediate row and probability product is exposed without
calling any final no-code theorem. The orbit-52 proof includes zero amplitudes.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderThreePrintedCrossRows
open scoped Matrix BigOperators
noncomputable section

namespace Orbit47
open SixQubit.Orbit47
def flip : SS.BitString 6 := SS.stdBasis ⟨4,by decide⟩
def sources : Fin 2 → SS.BitString 6 := ![z1,z8]
def destinations : Fin 2 → SS.BitString 6 := ![y0,y7]
def characters : Fin 2 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩]
def W : Matrix (Fin 2) (Fin 2) ℚ := !![1,1;1,-1]
def WC : Matrix (Fin 2) (Fin 2) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 2 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=
    S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j,
    W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem determinant : W.det=-2 := by decide +kernel
theorem determinant_complex : WC.det=-2 := by
  have he : WC.det=(W.det : ℂ) := ((algebraMap ℚ ℂ).map_det W).symm
  rw [he,determinant]
  norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 2) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem product_norm (c d : SS.State 6 ℂ) (j : Fin 2) :
    Complex.normSq (products c d j)=
    Complex.normSq (c (destinations j))*Complex.normSq (d (sources j)) := by
  rw [products,MainTheory.FlipCharacter.normSq_incidenceMonomial,actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  apply MainTheory.FlipCharacter.monomials_zero_of_det_ne_zero S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  rw [matrix_checked,determinant_complex]
  norm_num
theorem physical_first_product_positive (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (products c d 0)=1/18 ∧ 0<Complex.normSq (products c d 0) := by
  have hm := moments c d hc hd hnc hnd hkl
  have h0 := MainTheory.OrderThreePrintedMoments.Orbit47.consequence0 hm
  have h1 := MainTheory.OrderThreePrintedMoments.Orbit47.consequence10 hm
  have he : Complex.normSq (products c d 0)=1/18 := by
    rw [product_norm]
    norm_num [destinations,sources,h0,h1]
  exact ⟨he,by rw [he]; norm_num⟩
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hz := physical_products_zero c d hc hd hkl 0
  have hp := (physical_first_product_positive c d hc hd hnc hnd hkl).2
  rw [hz,Complex.normSq_zero] at hp
  exact (lt_irrefl 0) hp

end Orbit47

namespace Orbit48
open SixQubit.Orbit48
def flip : SS.BitString 6 := SS.stdBasis ⟨3,by decide⟩
def sources : Fin 4 → SS.BitString 6 := ![z2,z4,z6,z8]
def destinations : Fin 4 → SS.BitString 6 := ![y0,y2,y5,y8]
def characters : Fin 4 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨1,by decide⟩,SS.stdBasis ⟨2,by decide⟩]
def W : Matrix (Fin 4) (Fin 4) ℚ := !![1,1,1,1;1,1,-1,-1;1,-1,1,-1;1,-1,-1,1]
def WC : Matrix (Fin 4) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=
    S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j,
    W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem determinant : W.det=-16 := by decide +kernel
theorem determinant_complex : WC.det=-16 := by
  have he : WC.det=(W.det : ℂ) := ((algebraMap ℚ ℂ).map_det W).symm
  rw [he,determinant]
  norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem product_norm (c d : SS.State 6 ℂ) (j : Fin 4) :
    Complex.normSq (products c d j)=
    Complex.normSq (c (destinations j))*Complex.normSq (d (sources j)) := by
  rw [products,MainTheory.FlipCharacter.normSq_incidenceMonomial,actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  apply MainTheory.FlipCharacter.monomials_zero_of_det_ne_zero S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  rw [matrix_checked,determinant_complex]
  norm_num
theorem physical_first_product_positive (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (products c d 0)=1/18 ∧ 0<Complex.normSq (products c d 0) := by
  have hm := moments c d hc hd hnc hnd hkl
  have h0 := MainTheory.OrderThreePrintedMoments.Orbit48.consequence0 hm
  have h1 := MainTheory.OrderThreePrintedMoments.Orbit48.consequence13 hm
  have he : Complex.normSq (products c d 0)=1/18 := by
    rw [product_norm]
    norm_num [destinations,sources,h0,h1]
  exact ⟨he,by rw [he]; norm_num⟩
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hz := physical_products_zero c d hc hd hkl 0
  have hp := (physical_first_product_positive c d hc hd hnc hnd hkl).2
  rw [hz,Complex.normSq_zero] at hp
  exact (lt_irrefl 0) hp

end Orbit48

namespace Orbit52
open SixQubit.Orbit52
def flip : SS.BitString 6 := SS.stdBasis ⟨1,by decide⟩
def sources : Fin 4 → SS.BitString 6 := ![z2,z3,z8,z9]
def destinations : Fin 4 → SS.BitString 6 := ![y0,y1,y6,y7]
def characters : Fin 4 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨0,by decide⟩,SS.stdBasis ⟨2,by decide⟩,SS.stdBasis ⟨3,by decide⟩]
def W : Matrix (Fin 4) (Fin 4) ℚ := !![1,1,1,1;1,1,-1,-1;1,-1,1,-1;1,-1,-1,1]
def WC : Matrix (Fin 4) (Fin 4) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j)
theorem actual_incidence : Finset.univ.image sources=
    S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) flip=destinations j := by decide +kernel
theorem actual_characters : ∀ i j,
    W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters sources=WC := by
  ext i j
  change (if SS.bdot (characters i) (sources j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
theorem determinant : W.det=-16 := by decide +kernel
theorem determinant_complex : WC.det=-16 := by
  have he : WC.det=(W.det : ℂ) := ((algebraMap ℚ ℂ).map_det W).symm
  rw [he,determinant]
  norm_num
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 4) :
    products c d j=star (c (destinations j))*d (sources j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem product_norm (c d : SS.State 6 ℂ) (j : Fin 4) :
    Complex.normSq (products c d j)=
    Complex.normSq (c (destinations j))*Complex.normSq (d (sources j)) := by
  rw [products,MainTheory.FlipCharacter.normSq_incidenceMonomial,actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  apply MainTheory.FlipCharacter.monomials_zero_of_det_ne_zero S0 S1 c d hc hd hkl
    flip characters sources sources_injective actual_incidence weights
  rw [matrix_checked,determinant_complex]
  norm_num
theorem physical_half_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (c y0)=Complex.normSq (d z2)/2 ∧
    Complex.normSq (c y1)=Complex.normSq (d z3)/2 ∧
    Complex.normSq (d z2)+Complex.normSq (d z3)=1/3 := by
  have hm := moments c d hc hd hnc hnd hkl
  have h0 := MainTheory.OrderThreePrintedMoments.Orbit52.consequence0 hm
  have h1 := MainTheory.OrderThreePrintedMoments.Orbit52.consequence1 hm
  have h2 := MainTheory.OrderThreePrintedMoments.Orbit52.consequence12 hm
  refine ⟨?_,?_,?_⟩ <;> linarith only [h0,h1,h2]
theorem physical_squared_products (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (products c d 0)=1/2*(Complex.normSq (d z2))^2 ∧
    Complex.normSq (products c d 1)=1/2*(Complex.normSq (d z3))^2 := by
  have he := physical_half_relations c d hc hd hnc hnd hkl
  constructor
  · rw [product_norm]
    norm_num [destinations,sources]
    rw [he.1]
    ring
  · rw [product_norm]
    norm_num [destinations,sources]
    rw [he.2.1]
    ring
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hz0 := physical_products_zero c d hc hd hkl 0
  have hz1 := physical_products_zero c d hc hd hkl 1
  have hp := physical_squared_products c d hc hd hnc hnd hkl
  have hs := (physical_half_relations c d hc hd hnc hnd hkl).2.2
  rw [hz0,Complex.normSq_zero] at hp
  rw [hz1,Complex.normSq_zero] at hp
  have h0 : Complex.normSq (d z2)=0 := by nlinarith only [hp.1]
  have h1 : Complex.normSq (d z3)=0 := by nlinarith only [hp.2]
  linarith only [h0,h1,hs]

end Orbit52

end
end MainTheory.OrderThreePrintedCrossRows
