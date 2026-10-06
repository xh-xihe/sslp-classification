import MainTheory.NativeArbitrarySplitSixQubit
import MainTheory.ArbitrarySplitSixQubit
import MainTheory.PrimitiveSplitDisplays
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.SplitFamilyLogicalCompletion
open scoped Matrix BigOperators Kronecker
open Orbit2.TensorPauli
noncomputable section
abbrev Tail := Fin 4 → Fin 2
def sigmaG (a : Fin 2) : GaussianInt := if a=0 then 1 else -1
def tailG (five : Bool) (t : Tail) : GaussianInt :=
  if five then ∏ i,sigmaG (t i) else sigmaG (t 0)*sigmaG (t 1)
def tailMask (five : Bool) : Label 4 := if five then ![3,3,3,3] else ![3,3,0,0]
def raw (five : Bool) (j a : Fin 2) (t : Tail) : GaussianInt :=
  if five then MainTheory.ArbitrarySplitPerfectCode.raw j a t
    else MainTheory.NativeArbitrarySplitPerfectCode.raw j a t
def seedC (five : Bool) : Matrix (Fin 2 × Tail) (Fin 2) ℂ :=
  if five then MainTheory.ArbitrarySplitPerfectCode.C else MainTheory.NativeArbitrarySplitPerfectCode.C
def tailD (five : Bool) : Matrix Tail Tail ℂ := Matrix.diagonal (fun t => (tailG five t : ℂ))
def physicalMask (five two : Bool) : Label 6 :=
  ![3,(if two then 3 else 0),(if five then 3 else 3),(if five then 3 else 3),
    (if five then 3 else 0),(if five then 3 else 0)]
def W (two : Bool) (theta : ℝ) : Matrix (Fin 4) (Fin 2) ℂ :=
  if two then MainTheory.Orbit2TrigonometricSplit.W theta else MainTheory.PrimitiveSplitDisplays.W3 theta
def pairZ (two : Bool) : Matrix (Fin 4) (Fin 4) ℂ := if two then Orbit2.zzFour else Orbit2.ziFour
def split (five : Bool) (w : Matrix (Fin 4) (Fin 2) ℂ) :=
  (w ⊗ₖ (1 : Matrix Tail Tail ℂ))*seedC five
def encoder (five two : Bool) (theta : ℝ) : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ :=
  if five then MainTheory.ArbitrarySplitSixQubit.code (W two theta)
    else MainTheory.NativeArbitrarySplitSixQubit.code (W two theta)

theorem raw_logical : ∀ (five : Bool) (j a : Fin 2) (t : Tail),
    sigmaG a*tailG five t*raw five j a t=sigmaG j*raw five j a t := by decide +kernel

theorem tail_diagonal_G : ∀ (five : Bool) (s t : Tail),
    (∏ i,localG (tailMask five i) (s i) (t i))=if s=t then tailG five s else 0 := by decide +kernel

theorem tail_operator (five : Bool) : operator (tailMask five)=tailD five := by
  ext s t
  have h := congrArg GaussianInt.toComplex (tail_diagonal_G five s t)
  change (∏ i,localC (tailMask five i) (s i) (t i))=if s=t then (tailG five s : ℂ) else 0
  simpa only [localC,Matrix.map_apply,map_prod,apply_ite,map_zero] using h

theorem seed_logical (five : Bool) : (Orbit2.zTwo ⊗ₖ tailD five)*seedC five=seedC five*Orbit2.zTwo := by
  unfold Orbit2.zTwo tailD
  rw [Matrix.diagonal_kronecker_diagonal]
  ext s j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
  rcases s with ⟨a,t⟩
  have h := congrArg GaussianInt.toComplex (raw_logical five j a t)
  cases five
  · fin_cases a <;> fin_cases j
    all_goals norm_num [seedC,MainTheory.NativeArbitrarySplitPerfectCode.C,raw,sigmaG] at h ⊢
    all_goals linear_combination (1/8 : ℂ)*h
  · fin_cases a <;> fin_cases j
    all_goals norm_num [seedC,MainTheory.ArbitrarySplitPerfectCode.C,raw,sigmaG] at h ⊢
    all_goals linear_combination (1/4 : ℂ)*h

theorem W_isometry (two : Bool) (theta : ℝ) : (W two theta).conjTranspose*W two theta=1 := by
  cases two
  · exact MainTheory.PrimitiveSplitDisplays.W3_isometry theta
  · exact MainTheory.Orbit2TrigonometricSplit.isometry theta

theorem W_logical (two : Bool) (theta : ℝ) : pairZ two*W two theta=W two theta*Orbit2.zTwo := by
  cases two
  · exact MainTheory.PrimitiveSplitDisplays.W3_logical theta
  · exact MainTheory.Orbit2TrigonometricSplit.logical_lift theta

theorem split_logical (five two : Bool) (theta : ℝ) :
    (pairZ two ⊗ₖ tailD five)*split five (W two theta)=split five (W two theta)*Orbit2.zTwo := by
  unfold split
  rw [← Matrix.mul_assoc,← Matrix.mul_kronecker_mul,Matrix.mul_one,W_logical]
  calc
    ((W two theta*Orbit2.zTwo) ⊗ₖ tailD five)*seedC five=
        ((W two theta ⊗ₖ (1 : Matrix Tail Tail ℂ))*(Orbit2.zTwo ⊗ₖ tailD five))*seedC five := by
      rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
    _=_ := by rw [Matrix.mul_assoc,seed_logical,← Matrix.mul_assoc]

theorem physical_factors (five two : Bool) :
    MainTheory.ArbitrarySplitSixQubit.pairOperator (physicalMask five two)=pairZ two ∧
      MainTheory.ArbitrarySplitSixQubit.tailLabel (physicalMask five two)=tailMask five := by
  cases five <;> cases two
  all_goals constructor
  all_goals try rfl
  all_goals ext s t
  all_goals fin_cases s <;> fin_cases t
  all_goals norm_num [MainTheory.ArbitrarySplitSixQubit.pairOperator,physicalMask,pairZ,
    localC,localG,Orbit2.ziFour,Orbit2.zzFour,Matrix.diagonal,GaussianInt.toComplex_def,
    Matrix.cons_val_three,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

theorem encoder_logical (five two : Bool) (theta : ℝ) :
    operator (physicalMask five two)*encoder five two theta=encoder five two theta*Orbit2.zTwo := by
  have h := split_logical five two theta
  rw [← tail_operator] at h
  rw [← (physical_factors five two).1,← (physical_factors five two).2] at h
  have he := congrArg (fun A => A.submatrix MainTheory.ArbitrarySplitSixQubit.basis.symm id) h
  cases five
  · change _*MainTheory.NativeArbitrarySplitSixQubit.code _=MainTheory.NativeArbitrarySplitSixQubit.code _*_ 
    rw [MainTheory.NativeArbitrarySplitSixQubit.operator_original]
    unfold MainTheory.NativeArbitrarySplitSixQubit.code
    rw [Matrix.submatrix_mul_equiv]
    exact he
  · change _*MainTheory.ArbitrarySplitSixQubit.code _=MainTheory.ArbitrarySplitSixQubit.code _*_
    rw [MainTheory.ArbitrarySplitSixQubit.operator_original]
    unfold MainTheory.ArbitrarySplitSixQubit.code
    rw [Matrix.submatrix_mul_equiv]
    exact he

theorem encoder_isometry (five two : Bool) (theta : ℝ) :
    (encoder five two theta).conjTranspose*encoder five two theta=1 := by
  cases five
  · exact MainTheory.NativeArbitrarySplitSixQubit.code_isometry _ (W_isometry two theta)
  · exact MainTheory.ArbitrarySplitSixQubit.code_isometry _ (W_isometry two theta)

theorem encoder_distance (five two : Bool) (theta : ℝ) :
    SS.HasDistance (Orbit2.HilbertBridge.words (encoder five two theta)) 3 := by
  cases five
  · exact MainTheory.NativeArbitrarySplitSixQubit.hilbert_distance_three _ (W_isometry two theta)
  · exact MainTheory.ArbitrarySplitSixQubit.hilbert_distance_three _ (W_isometry two theta)

end
end MainTheory.SplitFamilyLogicalCompletion
