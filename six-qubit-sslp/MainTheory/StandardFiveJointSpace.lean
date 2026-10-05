import MainTheory.Orbit2StandardFiveQubit

/-! The complete joint +1 eigenspace of the four printed standard five-qubit
generators is precisely the span of their two actual seed words. The exact
16-term stabilizer projector and Gram matrix are ordinary kernel checks. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.StandardFiveJointSpace
open MainTheory.Orbit2StandardFiveQubit Orbit2.TensorPauli
open scoped BigOperators Matrix
noncomputable section
abbrev Basis := Fin 5 → Fin 2
def selected (s : Fin 16) (g : Fin 4) : Label 5 :=
  if s.val.testBit g.val then generators g else fun _ => 0
def words : Fin 16 → Label 5 := ![![0,0,0,0,0],![1,3,3,1,0],![0,1,3,3,1],![1,2,0,2,1],![1,0,1,3,3],![0,3,2,2,3],![1,1,2,0,2],![0,2,1,1,2],![3,1,0,1,3],![2,2,3,0,3],![3,0,3,2,2],![2,3,0,3,2],![2,1,1,2,0],![3,2,2,3,0],![2,0,2,1,1],![3,3,1,0,1]]
def coefficients : Fin 16 → GaussianInt := ![⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩]
def nestedLabel (s : Fin 16) : Label 5 :=
  product (product (product (selected s 0) (selected s 1)) (selected s 2)) (selected s 3)
def nestedPhase (s : Fin 16) : GaussianInt :=
  phase (selected s 0) (selected s 1)*
    phase (product (selected s 0) (selected s 1)) (selected s 2)*
    phase (product (product (selected s 0) (selected s 1)) (selected s 2)) (selected s 3)
theorem actual_words : ∀ s, nestedLabel s=words s ∧ nestedPhase s=coefficients s := by decide +kernel
theorem independent_generators : Function.Injective words ∧
    (∀ s, words s=(fun _ => 0) ↔ s=0) := by decide +kernel
def rawOperator (p : Label 5) : Matrix Basis Basis GaussianInt :=
  fun x y => ∏ j, localG (p j) (x j) (y j)
def rawSeed : Matrix Basis (Fin 2) GaussianInt := fun x j => standard j x
def rawProjector : Matrix Basis Basis GaussianInt :=
  ∑ s : Fin 16, coefficients s • rawOperator (words s)
theorem projector_checked : rawProjector=rawSeed*rawSeed.conjTranspose := by decide +kernel
theorem gram_checked : rawSeed.conjTranspose*rawSeed=16 • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by decide +kernel
theorem fixed_checked : ∀ g, rawOperator (generators g)*rawSeed=rawSeed := by decide +kernel
def R : Matrix Basis (Fin 2) ℂ := rawSeed.map GaussianInt.toComplex
def projector : Matrix Basis Basis ℂ := rawProjector.map GaussianInt.toComplex
def wordProduct (s : Fin 16) : Matrix Basis Basis ℂ :=
  operator (selected s 0)*operator (selected s 1)*operator (selected s 2)*operator (selected s 3)
theorem raw_operator_cast (p : Label 5) :
    (rawOperator p).map GaussianInt.toComplex=operator p := by
  ext x y
  simp [rawOperator,operator,tensor,localC,Matrix.map_apply,map_prod]
theorem seed_star_cast : rawSeed.conjTranspose.map GaussianInt.toComplex=R.conjTranspose := by
  ext x j
  simp [R,Matrix.conjTranspose_apply,Matrix.map_apply,GaussianInt.toComplex_star]
theorem word_product (s : Fin 16) :
    wordProduct s=(coefficients s : ℂ) • operator (words s) := by
  rw [wordProduct,operator_mul,Matrix.smul_mul,operator_mul,smul_smul,
    Matrix.smul_mul,operator_mul,smul_smul]
  rw [← GaussianInt.toComplex_mul,← GaussianInt.toComplex_mul]
  change (nestedPhase s : ℂ) • operator (nestedLabel s)=_
  rw [(actual_words s).1,(actual_words s).2]
theorem projector_sum : projector=∑ s : Fin 16, wordProduct s := by
  ext x y
  simp only [projector,rawProjector,Matrix.map_apply,Matrix.sum_apply,map_sum,Matrix.smul_apply,
    smul_eq_mul,GaussianInt.toComplex_mul,word_product]
  apply Finset.sum_congr rfl
  intro s _
  have he := congrArg (fun M => M x y) (raw_operator_cast (words s))
  change (rawOperator (words s) x y : ℂ)=operator (words s) x y at he
  rw [he]
theorem projector_factor : projector=R*R.conjTranspose := by
  rw [projector,projector_checked,Matrix.map_mul,seed_star_cast]
  rfl
theorem seed_gram : R.conjTranspose*R=(16 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← seed_star_cast,R,← Matrix.map_mul,gram_checked]
  ext i j
  simp only [Matrix.map_apply,Matrix.smul_apply,Matrix.one_apply]
  split_ifs <;> norm_num [GaussianInt.toComplex_def]
theorem seed_fixed (g : Fin 4) : operator (generators g)*R=R := by
  rw [← raw_operator_cast,R,← Matrix.map_mul,fixed_checked]
theorem fixed_word (v : Basis → ℂ) (hv : ∀ g, operator (generators g) *ᵥ v=v) (s : Fin 16) :
    wordProduct s *ᵥ v=v := by
  have he : ∀ g : Fin 4, operator (selected s g) *ᵥ v=v := by
    intro g
    unfold selected
    split
    · exact hv g
    · rw [operator_zero,Matrix.one_mulVec]
  rw [wordProduct]
  simp only [← Matrix.mulVec_mulVec,he]
theorem fixed_projector (v : Basis → ℂ) (hv : ∀ g, operator (generators g) *ᵥ v=v) :
    projector *ᵥ v=(16 : ℂ) • v := by
  rw [projector_sum,Matrix.sum_mulVec]
  simp_rw [fixed_word v hv]
  ext x
  norm_num [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
def jointSpace : Submodule ℂ (Basis → ℂ) where
  carrier := {v | ∀ g, operator (generators g) *ᵥ v=v}
  zero_mem' := by intro g; simp
  add_mem' := by intro u v hu hv g; rw [Matrix.mulVec_add,hu,hv]
  smul_mem' := by intro a v hv g; rw [Matrix.mulVec_smul,hv]
theorem joint_range : jointSpace=LinearMap.range R.mulVecLin := by
  ext v
  constructor
  · intro hv
    refine ⟨(1/16 : ℂ) • (R.conjTranspose *ᵥ v),?_⟩
    change R *ᵥ ((1/16 : ℂ) • (R.conjTranspose *ᵥ v))=v
    rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec,← projector_factor,fixed_projector v hv]
    simp [smul_smul]
  · rintro ⟨a,ha⟩
    change R *ᵥ a=v at ha
    rw [← ha]
    intro g
    rw [Matrix.mulVec_mulVec,seed_fixed]
theorem seed_injective : Function.Injective R.mulVecLin := by
  intro a b hab
  have he := congrArg (fun v => R.conjTranspose *ᵥ v) hab
  change R.conjTranspose *ᵥ (R *ᵥ a)=R.conjTranspose *ᵥ (R *ᵥ b) at he
  simp only [Matrix.mulVec_mulVec,seed_gram,Matrix.smul_mulVec,Matrix.one_mulVec] at he
  funext i
  have hi := congrFun he i
  change (16 : ℂ)*a i=(16 : ℂ)*b i at hi
  linear_combination hi/16
theorem joint_dimension : Module.finrank ℂ jointSpace=2 := by
  rw [joint_range,LinearMap.finrank_range_of_inj seed_injective]
  simp
end
end MainTheory.StandardFiveJointSpace
