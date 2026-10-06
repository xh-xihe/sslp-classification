import MainTheory.OrderTwoPrintedMoments
import MainTheory.FlipCharacterObstruction
import Mathlib.LinearAlgebra.Matrix.Block

/-! The SI's actual ten-incidence, ten-character half-angle systems.
Literal signed determinants use kernel-checked LU factors. The final
physical exclusions follow the printed full-rank matched-flip argument. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.OrderTwoPrintedWalsh
open scoped BigOperators Matrix
noncomputable section
theorem norm_sq_matched_product (c d : ℂ) (hm : Complex.normSq d=Complex.normSq c) :
    Complex.normSq (star c*d)=(Complex.normSq c)^2 := by
  rw [Complex.normSq_mul]
  change Complex.normSq ((starRingEnd ℂ) c)*Complex.normSq d=(Complex.normSq c)^2
  rw [Complex.normSq_conj,hm,pow_two]

namespace Orbit42
open MainTheory.OrderTwoPrintedMoments.Orbit42
def flip : SS.BitString 6 := SS.stdBasis ⟨5,by decide⟩
def characters : Fin 10 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨5,by decide⟩,SS.stdBasis ⟨0,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨0,by decide⟩),SS.stdBasis ⟨1,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨1,by decide⟩),SS.stdBasis ⟨2,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨2,by decide⟩),SS.stdBasis ⟨3,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)]
def W : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(-1),(1),(1),(-1),(1),(-1),(1),(-1),(1),(-1)],![(1),(1),(1),(1),(-1),(-1),(-1),(-1),(-1),(-1)],![(-1),(1),(1),(-1),(-1),(1),(-1),(1),(-1),(1)],![(1),(1),(-1),(-1),(1),(1),(-1),(-1),(-1),(-1)],![(-1),(1),(-1),(1),(1),(-1),(-1),(1),(-1),(1)],![(1),(1),(-1),(-1),(-1),(-1),(1),(1),(-1),(-1)],![(-1),(1),(-1),(1),(-1),(1),(1),(-1),(-1),(1)],![(1),(1),(-1),(-1),(-1),(-1),(-1),(-1),(1),(1)],![(-1),(1),(-1),(1),(-1),(1),(-1),(1),(1),(-1)]]
def WC : Matrix (Fin 10) (Fin 10) ℂ := W.map (Rat.castHom ℂ)
def products (c d : SS.State 6 ℂ) : Fin 10 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem actual_incidence : Finset.univ.image top=
    SixQubit.Orbit42.S1.filter (fun y => SS.bxor y flip ∈ SixQubit.Orbit42.S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (top j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
def P : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(1),(0),(0),(0),(0)],![(0),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(1),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(1),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(1),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(1),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(1)]]
def L : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(1),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(1),(1),(0),(0),(0),(0),(0),(0)],![(1),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(1),(1),(0),(0),(0),(0)],![(1),(0),(1),(0),(1),(0),(1),(0),(0),(0)],![(-1),(1),(1),(1),(1),(1),(1),(1),(0),(0)],![(1),(0),(1),(0),(1),(0),(1/2),(0),(1),(0)],![(-1),(1),(1),(1),(1),(1),(1/2),(1/2),(1),(1)]]
def U : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(0),(2),(2),(0),(2),(0),(2),(0),(2),(0)],![(0),(0),(-2),(-2),(0),(0),(-2),(-2),(-2),(-2)],![(0),(0),(0),(4),(0),(0),(0),(4),(0),(4)],![(0),(0),(0),(0),(-2),(-2),(-2),(-2),(-2),(-2)],![(0),(0),(0),(0),(0),(4),(0),(4),(0),(4)],![(0),(0),(0),(0),(0),(0),(4),(4),(2),(2)],![(0),(0),(0),(0),(0),(0),(0),(-8),(0),(-4)],![(0),(0),(0),(0),(0),(0),(0),(0),(3),(3)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(-6)]]
theorem factorization : P*W=L*U := by
  have he : ∀ i j : Fin 10, (P*W) i j=(L*U) i j := by decide +kernel
  exact Matrix.ext he
theorem lower_triangular : L.BlockTriangular OrderDual.toDual := by
  change ∀ i j : Fin 10, i < j → L i j=0
  decide +kernel
theorem upper_triangular : U.BlockTriangular id := by
  change ∀ i j : Fin 10, j < i → U i j=0
  decide +kernel
theorem lower_diagonal : (∏ i : Fin 10, L i i)=1 := by decide +kernel
theorem upper_diagonal : (∏ i : Fin 10, U i i)=73728 := by decide +kernel
theorem lower_det : L.det=1 := by
  rw [Matrix.det_of_lowerTriangular L lower_triangular,lower_diagonal]
theorem upper_det : U.det=73728 := by
  rw [Matrix.det_of_upperTriangular upper_triangular,upper_diagonal]
def permFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def inverseFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def permutation : Equiv.Perm (Fin 10) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_matrix : P=(1 : Matrix (Fin 10) (Fin 10) ℚ).submatrix permutation id := by decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation=1 := by decide +kernel
theorem permutation_det : P.det=1 := by
  rw [permutation_matrix,Matrix.det_permute,Matrix.det_one,permutation_sign]
  norm_num
theorem determinant : W.det=73728 := by
  have he := congrArg Matrix.det factorization
  norm_num only [Matrix.det_mul,permutation_det,lower_det,upper_det,one_mul] at he
  linear_combination 1*he
theorem complex_determinant : WC.det=73728 := by
  change ((Rat.castHom ℂ).mapMatrix W).det=73728
  rw [← RingHom.map_det]
  change (W.det : ℂ)=73728
  exact_mod_cast determinant
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 10) :
    products c d j=star (c (bottom j))*d (top j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit42.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit42.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit42.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit42.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  have hdW : WC.det≠0 := by rw [complex_determinant]; norm_num
  have hu : IsUnit WC := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdW)
  have hz : products c d=0 := Matrix.mulVec_injective_of_isUnit hu (by simpa using physical_rows c d hc hd hkl)
  exact fun j => congrFun hz j
theorem physical_product_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit42.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit42.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 10) :
    Complex.normSq (products c d j)=(Complex.normSq (c (bottom j)))^2 := by
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit42.moments c d hc hd hnc hnd hkl
  have he : Complex.normSq (d (top j))=Complex.normSq (c (bottom j)) :=
    (congrFun (matched_probabilities _ _ hm) j).symm
  rw [product_expansion,Complex.normSq_mul]
  change Complex.normSq ((starRingEnd ℂ) (c (bottom j)))*Complex.normSq (d (top j))=
    (Complex.normSq (c (bottom j)))^2
  rw [Complex.normSq_conj,he,pow_two]
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit42.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit42.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hp : ∀ j, Complex.normSq (c (bottom j))=0 := by
    intro j
    have he := physical_product_norm c d hc hd hnc hnd hkl j
    rw [physical_products_zero c d hc hd hkl j,Complex.normSq_zero] at he
    exact (sq_eq_zero_iff).1 he.symm
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit42.moments c d hc hd hnc hnd hkl
  have hn := hm.n0
  simp only [hp] at hn
  norm_num at hn
end Orbit42

namespace Orbit43
open MainTheory.OrderTwoPrintedMoments.Orbit43
def flip : SS.BitString 6 := SS.stdBasis ⟨5,by decide⟩
def characters : Fin 10 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨5,by decide⟩,SS.stdBasis ⟨0,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨0,by decide⟩),SS.stdBasis ⟨1,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨1,by decide⟩),SS.stdBasis ⟨2,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨2,by decide⟩),SS.stdBasis ⟨3,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)]
def W : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(-1),(1),(1),(-1),(1),(-1),(1),(-1),(1),(-1)],![(1),(1),(1),(1),(1),(1),(-1),(-1),(-1),(-1)],![(-1),(1),(1),(-1),(1),(-1),(-1),(1),(-1),(1)],![(1),(1),(1),(1),(-1),(-1),(1),(1),(-1),(-1)],![(-1),(1),(1),(-1),(-1),(1),(1),(-1),(-1),(1)],![(1),(1),(-1),(-1),(1),(1),(1),(1),(-1),(-1)],![(-1),(1),(-1),(1),(1),(-1),(1),(-1),(-1),(1)],![(1),(1),(-1),(-1),(-1),(-1),(-1),(-1),(1),(1)],![(-1),(1),(-1),(1),(-1),(1),(-1),(1),(1),(-1)]]
def WC : Matrix (Fin 10) (Fin 10) ℂ := W.map (Rat.castHom ℂ)
def products (c d : SS.State 6 ℂ) : Fin 10 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem actual_incidence : Finset.univ.image top=
    SixQubit.Orbit43.S1.filter (fun y => SS.bxor y flip ∈ SixQubit.Orbit43.S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (top j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
def P : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(1),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(1),(0),(0)],![(0),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(1),(0),(0),(0),(0)],![(0),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(1),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(1),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(1)]]
def L : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(1),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(1),(1),(0),(0),(0),(0),(0),(0)],![(1),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(1),(1),(0),(0),(0),(0)],![(1),(0),(0),(0),(0),(0),(1),(0),(0),(0)],![(-1),(1),(0),(0),(0),(0),(1),(1),(0),(0)],![(1),(0),(1),(0),(1),(0),(1),(0),(1),(0)],![(-1),(1),(1),(1),(1),(1),(1),(1),(1),(1)]]
def U : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(0),(2),(2),(0),(2),(0),(2),(0),(2),(0)],![(0),(0),(-2),(-2),(0),(0),(0),(0),(-2),(-2)],![(0),(0),(0),(4),(0),(0),(0),(0),(0),(4)],![(0),(0),(0),(0),(-2),(-2),(0),(0),(-2),(-2)],![(0),(0),(0),(0),(0),(4),(0),(0),(0),(4)],![(0),(0),(0),(0),(0),(0),(-2),(-2),(-2),(-2)],![(0),(0),(0),(0),(0),(0),(0),(4),(0),(4)],![(0),(0),(0),(0),(0),(0),(0),(0),(6),(6)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(-12)]]
theorem factorization : P*W=L*U := by
  have he : ∀ i j : Fin 10, (P*W) i j=(L*U) i j := by decide +kernel
  exact Matrix.ext he
theorem lower_triangular : L.BlockTriangular OrderDual.toDual := by
  change ∀ i j : Fin 10, i < j → L i j=0
  decide +kernel
theorem upper_triangular : U.BlockTriangular id := by
  change ∀ i j : Fin 10, j < i → U i j=0
  decide +kernel
theorem lower_diagonal : (∏ i : Fin 10, L i i)=1 := by decide +kernel
theorem upper_diagonal : (∏ i : Fin 10, U i i)=73728 := by decide +kernel
theorem lower_det : L.det=1 := by
  rw [Matrix.det_of_lowerTriangular L lower_triangular,lower_diagonal]
theorem upper_det : U.det=73728 := by
  rw [Matrix.det_of_upperTriangular upper_triangular,upper_diagonal]
def permFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def inverseFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def permutation : Equiv.Perm (Fin 10) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_matrix : P=(1 : Matrix (Fin 10) (Fin 10) ℚ).submatrix permutation id := by decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation=1 := by decide +kernel
theorem permutation_det : P.det=1 := by
  rw [permutation_matrix,Matrix.det_permute,Matrix.det_one,permutation_sign]
  norm_num
theorem determinant : W.det=73728 := by
  have he := congrArg Matrix.det factorization
  norm_num only [Matrix.det_mul,permutation_det,lower_det,upper_det,one_mul] at he
  linear_combination 1*he
theorem complex_determinant : WC.det=73728 := by
  change ((Rat.castHom ℂ).mapMatrix W).det=73728
  rw [← RingHom.map_det]
  change (W.det : ℂ)=73728
  exact_mod_cast determinant
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 10) :
    products c d j=star (c (bottom j))*d (top j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit43.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit43.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit43.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit43.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  have hdW : WC.det≠0 := by rw [complex_determinant]; norm_num
  have hu : IsUnit WC := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdW)
  have hz : products c d=0 := Matrix.mulVec_injective_of_isUnit hu (by simpa using physical_rows c d hc hd hkl)
  exact fun j => congrFun hz j
theorem physical_product_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit43.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit43.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 10) :
    Complex.normSq (products c d j)=(Complex.normSq (c (bottom j)))^2 := by
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit43.moments c d hc hd hnc hnd hkl
  have he : Complex.normSq (d (top j))=Complex.normSq (c (bottom j)) :=
    (congrFun (matched_probabilities _ _ hm) j).symm
  rw [product_expansion,Complex.normSq_mul]
  change Complex.normSq ((starRingEnd ℂ) (c (bottom j)))*Complex.normSq (d (top j))=
    (Complex.normSq (c (bottom j)))^2
  rw [Complex.normSq_conj,he,pow_two]
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit43.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit43.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hp : ∀ j, Complex.normSq (c (bottom j))=0 := by
    intro j
    have he := physical_product_norm c d hc hd hnc hnd hkl j
    rw [physical_products_zero c d hc hd hkl j,Complex.normSq_zero] at he
    exact (sq_eq_zero_iff).1 he.symm
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit43.moments c d hc hd hnc hnd hkl
  have hn := hm.n0
  simp only [hp] at hn
  norm_num at hn
end Orbit43

namespace Orbit44
open MainTheory.OrderTwoPrintedMoments.Orbit44
def flip : SS.BitString 6 := SS.stdBasis ⟨4,by decide⟩
def characters : Fin 10 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨4,by decide⟩,SS.stdBasis ⟨0,by decide⟩,SS.bxor (SS.stdBasis ⟨4,by decide⟩) (SS.stdBasis ⟨0,by decide⟩),SS.stdBasis ⟨1,by decide⟩,SS.bxor (SS.stdBasis ⟨4,by decide⟩) (SS.stdBasis ⟨1,by decide⟩),SS.stdBasis ⟨2,by decide⟩,SS.bxor (SS.stdBasis ⟨4,by decide⟩) (SS.stdBasis ⟨2,by decide⟩),SS.stdBasis ⟨3,by decide⟩,SS.bxor (SS.stdBasis ⟨4,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)]
def W : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(-1),(1),(-1),(1),(1),(-1),(1),(-1),(-1),(1)],![(1),(1),(1),(1),(1),(1),(-1),(-1),(-1),(-1)],![(-1),(1),(-1),(1),(1),(-1),(-1),(1),(1),(-1)],![(1),(1),(1),(1),(-1),(-1),(1),(1),(-1),(-1)],![(-1),(1),(-1),(1),(-1),(1),(1),(-1),(1),(-1)],![(1),(1),(-1),(-1),(-1),(-1),(-1),(-1),(1),(1)],![(-1),(1),(1),(-1),(-1),(1),(-1),(1),(-1),(1)],![(1),(-1),(1),(-1),(1),(-1),(1),(-1),(1),(-1)],![(-1),(-1),(-1),(-1),(1),(1),(1),(1),(-1),(-1)]]
def WC : Matrix (Fin 10) (Fin 10) ℂ := W.map (Rat.castHom ℂ)
def products (c d : SS.State 6 ℂ) : Fin 10 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem actual_incidence : Finset.univ.image top=
    SixQubit.Orbit44.S1.filter (fun y => SS.bxor y flip ∈ SixQubit.Orbit44.S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (top j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
def P : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(1),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(1),(0),(0)],![(0),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(1),(0),(0),(0),(0)],![(0),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(1),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(1),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(1)]]
def L : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(1),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(-1),(1),(0),(0),(0),(0),(0),(0)],![(1),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(1),(1),(0),(0),(0),(0)],![(1),(0),(0),(0),(0),(0),(1),(0),(0),(0)],![(-1),(1),(0),(0),(0),(0),(1),(1),(0),(0)],![(1),(-1),(0),(0),(-1),(-1),(-1),(-1),(1),(0)],![(-1),(0),(0),(0),(-1),(0),(-1),(0),(-1),(1)]]
def U : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(0),(2),(0),(2),(2),(0),(2),(0),(0),(2)],![(0),(0),(-2),(-2),(-2),(-2),(-2),(-2),(0),(0)],![(0),(0),(0),(-4),(-4),(0),(-4),(0),(0),(0)],![(0),(0),(0),(0),(-2),(-2),(0),(0),(-2),(-2)],![(0),(0),(0),(0),(0),(4),(0),(0),(4),(0)],![(0),(0),(0),(0),(0),(0),(-2),(-2),(-2),(-2)],![(0),(0),(0),(0),(0),(0),(0),(4),(4),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(4),(-4)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(-8)]]
theorem factorization : P*W=L*U := by
  have he : ∀ i j : Fin 10, (P*W) i j=(L*U) i j := by decide +kernel
  exact Matrix.ext he
theorem lower_triangular : L.BlockTriangular OrderDual.toDual := by
  change ∀ i j : Fin 10, i < j → L i j=0
  decide +kernel
theorem upper_triangular : U.BlockTriangular id := by
  change ∀ i j : Fin 10, j < i → U i j=0
  decide +kernel
theorem lower_diagonal : (∏ i : Fin 10, L i i)=1 := by decide +kernel
theorem upper_diagonal : (∏ i : Fin 10, U i i)=-32768 := by decide +kernel
theorem lower_det : L.det=1 := by
  rw [Matrix.det_of_lowerTriangular L lower_triangular,lower_diagonal]
theorem upper_det : U.det=-32768 := by
  rw [Matrix.det_of_upperTriangular upper_triangular,upper_diagonal]
def permFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def inverseFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def permutation : Equiv.Perm (Fin 10) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_matrix : P=(1 : Matrix (Fin 10) (Fin 10) ℚ).submatrix permutation id := by decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation=1 := by decide +kernel
theorem permutation_det : P.det=1 := by
  rw [permutation_matrix,Matrix.det_permute,Matrix.det_one,permutation_sign]
  norm_num
theorem determinant : W.det=-32768 := by
  have he := congrArg Matrix.det factorization
  norm_num only [Matrix.det_mul,permutation_det,lower_det,upper_det,one_mul] at he
  linear_combination 1*he
theorem complex_determinant : WC.det=-32768 := by
  change ((Rat.castHom ℂ).mapMatrix W).det=-32768
  rw [← RingHom.map_det]
  change (W.det : ℂ)=-32768
  exact_mod_cast determinant
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 10) :
    products c d j=star (c (bottom j))*d (top j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit44.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit44.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit44.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit44.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  have hdW : WC.det≠0 := by rw [complex_determinant]; norm_num
  have hu : IsUnit WC := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdW)
  have hz : products c d=0 := Matrix.mulVec_injective_of_isUnit hu (by simpa using physical_rows c d hc hd hkl)
  exact fun j => congrFun hz j
theorem physical_product_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit44.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit44.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 10) :
    Complex.normSq (products c d j)=(Complex.normSq (c (bottom j)))^2 := by
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit44.moments c d hc hd hnc hnd hkl
  have he : Complex.normSq (d (top j))=Complex.normSq (c (bottom j)) :=
    (congrFun (matched_probabilities _ _ hm) j).symm
  rw [product_expansion,Complex.normSq_mul]
  change Complex.normSq ((starRingEnd ℂ) (c (bottom j)))*Complex.normSq (d (top j))=
    (Complex.normSq (c (bottom j)))^2
  rw [Complex.normSq_conj,he,pow_two]
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit44.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit44.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hp : ∀ j, Complex.normSq (c (bottom j))=0 := by
    intro j
    have he := physical_product_norm c d hc hd hnc hnd hkl j
    rw [physical_products_zero c d hc hd hkl j,Complex.normSq_zero] at he
    exact (sq_eq_zero_iff).1 he.symm
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit44.moments c d hc hd hnc hnd hkl
  have hn := hm.n0
  simp only [hp] at hn
  norm_num at hn
end Orbit44

namespace Orbit46
open MainTheory.OrderTwoPrintedMoments.Orbit46
def flip : SS.BitString 6 := SS.stdBasis ⟨5,by decide⟩
def characters : Fin 10 → SS.BitString 6 := ![(fun _ => false),SS.stdBasis ⟨5,by decide⟩,SS.stdBasis ⟨0,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨0,by decide⟩),SS.stdBasis ⟨1,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨1,by decide⟩),SS.stdBasis ⟨2,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨2,by decide⟩),SS.stdBasis ⟨3,by decide⟩,SS.bxor (SS.stdBasis ⟨5,by decide⟩) (SS.stdBasis ⟨3,by decide⟩)]
def W : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(-1),(1),(-1),(1),(1),(-1),(1),(-1),(1),(-1)],![(1),(1),(1),(1),(-1),(-1),(-1),(-1),(-1),(-1)],![(-1),(1),(-1),(1),(-1),(1),(-1),(1),(-1),(1)],![(1),(1),(-1),(-1),(1),(1),(1),(1),(-1),(-1)],![(-1),(1),(1),(-1),(1),(-1),(1),(-1),(-1),(1)],![(1),(1),(-1),(-1),(1),(1),(-1),(-1),(1),(1)],![(-1),(1),(1),(-1),(1),(-1),(-1),(1),(1),(-1)],![(1),(1),(-1),(-1),(-1),(-1),(1),(1),(1),(1)],![(-1),(1),(1),(-1),(-1),(1),(1),(-1),(1),(-1)]]
def WC : Matrix (Fin 10) (Fin 10) ℂ := W.map (Rat.castHom ℂ)
def products (c d : SS.State 6 ℂ) : Fin 10 → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem actual_incidence : Finset.univ.image top=
    SixQubit.Orbit46.S1.filter (fun y => SS.bxor y flip ∈ SixQubit.Orbit46.S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=if SS.bdot (characters i) (top j) then -1 else 1 := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.FlipCharacter.restrictedCharacterMatrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  split <;> norm_num
def P : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(1),(0),(0),(0),(0)],![(0),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(1),(0),(0),(0),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(1),(0),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(1),(0),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(1),(0)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(1)]]
def L : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(0),(0),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(0),(0),(0),(0),(0),(0)],![(1),(0),(1),(0),(0),(0),(0),(0),(0),(0)],![(-1),(1),(-1),(1),(0),(0),(0),(0),(0),(0)],![(1),(0),(0),(0),(1),(0),(0),(0),(0),(0)],![(-1),(1),(0),(0),(1),(1),(0),(0),(0),(0)],![(1),(0),(1),(0),(0),(0),(1),(0),(0),(0)],![(-1),(1),(-1),(1),(0),(0),(1),(1),(0),(0)],![(1),(0),(1),(0),(1),(0),(-1),(0),(1),(0)],![(-1),(1),(-1),(1),(1),(1),(-1),(-1),(1),(1)]]
def U : Matrix (Fin 10) (Fin 10) ℚ := ![![(1),(1),(1),(1),(1),(1),(1),(1),(1),(1)],![(0),(2),(0),(2),(2),(0),(2),(0),(2),(0)],![(0),(0),(-2),(-2),(0),(0),(0),(0),(-2),(-2)],![(0),(0),(0),(-4),(0),(0),(0),(0),(-4),(0)],![(0),(0),(0),(0),(-2),(-2),(-2),(-2),(-2),(-2)],![(0),(0),(0),(0),(0),(4),(0),(4),(0),(4)],![(0),(0),(0),(0),(0),(0),(-2),(-2),(2),(2)],![(0),(0),(0),(0),(0),(0),(0),(4),(0),(-4)],![(0),(0),(0),(0),(0),(0),(0),(0),(6),(6)],![(0),(0),(0),(0),(0),(0),(0),(0),(0),(-12)]]
theorem factorization : P*W=L*U := by
  have he : ∀ i j : Fin 10, (P*W) i j=(L*U) i j := by decide +kernel
  exact Matrix.ext he
theorem lower_triangular : L.BlockTriangular OrderDual.toDual := by
  change ∀ i j : Fin 10, i < j → L i j=0
  decide +kernel
theorem upper_triangular : U.BlockTriangular id := by
  change ∀ i j : Fin 10, j < i → U i j=0
  decide +kernel
theorem lower_diagonal : (∏ i : Fin 10, L i i)=1 := by decide +kernel
theorem upper_diagonal : (∏ i : Fin 10, U i i)=-73728 := by decide +kernel
theorem lower_det : L.det=1 := by
  rw [Matrix.det_of_lowerTriangular L lower_triangular,lower_diagonal]
theorem upper_det : U.det=-73728 := by
  rw [Matrix.det_of_upperTriangular upper_triangular,upper_diagonal]
def permFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def inverseFunction : Fin 10 → Fin 10 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩]
def permutation : Equiv.Perm (Fin 10) where
  toFun := permFunction
  invFun := inverseFunction
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem permutation_matrix : P=(1 : Matrix (Fin 10) (Fin 10) ℚ).submatrix permutation id := by decide +kernel
theorem permutation_sign : Equiv.Perm.sign permutation=1 := by decide +kernel
theorem permutation_det : P.det=1 := by
  rw [permutation_matrix,Matrix.det_permute,Matrix.det_one,permutation_sign]
  norm_num
theorem determinant : W.det=-73728 := by
  have he := congrArg Matrix.det factorization
  norm_num only [Matrix.det_mul,permutation_det,lower_det,upper_det,one_mul] at he
  linear_combination 1*he
theorem complex_determinant : WC.det=-73728 := by
  change ((Rat.castHom ℂ).mapMatrix W).det=-73728
  rw [← RingHom.map_det]
  change (W.det : ℂ)=-73728
  exact_mod_cast determinant
theorem product_expansion (c d : SS.State 6 ℂ) (j : Fin 10) :
    products c d j=star (c (bottom j))*d (top j) := by
  unfold products MainTheory.FlipCharacter.incidenceMonomial
  rw [actual_images]
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit46.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit46.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.FlipCharacter.restricted_matrix_times_monomials _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit46.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit46.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j, products c d j=0 := by
  have hdW : WC.det≠0 := by rw [complex_determinant]; norm_num
  have hu : IsUnit WC := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdW)
  have hz : products c d=0 := Matrix.mulVec_injective_of_isUnit hu (by simpa using physical_rows c d hc hd hkl)
  exact fun j => congrFun hz j
theorem physical_product_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit46.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit46.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 10) :
    Complex.normSq (products c d j)=(Complex.normSq (c (bottom j)))^2 := by
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit46.moments c d hc hd hnc hnd hkl
  have he : Complex.normSq (d (top j))=Complex.normSq (c (bottom j)) :=
    (congrFun (matched_probabilities _ _ hm) j).symm
  rw [product_expansion,Complex.normSq_mul]
  change Complex.normSq ((starRingEnd ℂ) (c (bottom j)))*Complex.normSq (d (top j))=
    (Complex.normSq (c (bottom j)))^2
  rw [Complex.normSq_conj,he,pow_two]
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit46.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit46.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hp : ∀ j, Complex.normSq (c (bottom j))=0 := by
    intro j
    have he := physical_product_norm c d hc hd hnc hnd hkl j
    rw [physical_products_zero c d hc hd hkl j,Complex.normSq_zero] at he
    exact (sq_eq_zero_iff).1 he.symm
  have hm : Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
    SixQubit.Orbit46.moments c d hc hd hnc hnd hkl
  have hn := hm.n0
  simp only [hp] at hn
  norm_num at hn
end Orbit46

end
end MainTheory.OrderTwoPrintedWalsh
