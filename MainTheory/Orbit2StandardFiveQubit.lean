import Orbit2.FiveQubitPhysical
import MainTheory.QuaternionCliffordMatrixBridge

/-! The standard four stabilizer generators and the actual split-code seed. -/

namespace MainTheory.Orbit2StandardFiveQubit

open Orbit2.TensorPauli Orbit2.FiveQubit
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def generators : Fin 4 → Label 5 :=
  ![![1,3,3,1,0],![0,1,3,3,1],![1,0,1,3,3],![3,1,0,1,3]]

def vacuum (s : Fin 5 → Fin 2) : GaussianInt := if s=(fun _ => 0) then 1 else 0

def groundFromGenerators (s : Fin 5 → Fin 2) : GaussianInt :=
  let v1 := fun s => vacuum s+act (generators 0) vacuum s
  let v2 := fun s => v1 s+act (generators 1) v1 s
  let v3 := fun s => v2 s+act (generators 2) v2 s
  v3 s+act (generators 3) v3 s

def ground (s : Fin 5 → Fin 2) : GaussianInt :=
  ![![![![![1,0],![0,-1]],![![0,1],![-1,0]]],![![![0,1],![1,0]],![![-1,0],![0,-1]]]],![![![![0,-1],![1,0]],![![1,0],![0,-1]]],![![![-1,0],![0,-1]],![![0,-1],![-1,0]]]]] (s 0) (s 1) (s 2) (s 3) (s 4)

theorem ground_construction : ∀ s,ground s=groundFromGenerators s := by
  decide +kernel

def standard (j : Fin 2) (s : Fin 5 → Fin 2) : GaussianInt :=
  if j=0 then ground s else act ![1,1,1,1,1] ground s

def rotationG : Matrix (Fin 2) (Fin 2) GaussianInt :=
  ![![1,⟨0,-1⟩],![1,⟨0,1⟩]]

def rotateG (site : Fin 5) (v : (Fin 5 → Fin 2) → GaussianInt)
    (s : Fin 5 → Fin 2) : GaussianInt :=
  ∑ r : Fin 2,rotationG (s site) r*v (Function.update s site r)

def permuteBits (s : Fin 5 → Fin 2) : Fin 5 → Fin 2 :=
  ![s 0,s 3,s 4,s 1,s 2]

theorem permutation_involution : ∀ s,permuteBits (permuteBits s)=s := by
  decide +kernel

theorem fixed_generators : ∀ g j s,
    act (generators g) (standard j) s=standard j s := by
  decide +kernel

theorem standard_logical : ∀ j s,
    act ![3,3,3,3,3] (standard j) s=
      (if j=0 then 1 else -1)*standard j s := by
  decide +kernel

theorem multiplied_logical : ∀ s,
    act ![3,3,3,3,3] (fun s => act (generators 0) (standard 0) s) s=
      -act ![2,0,0,2,3] (standard 0) s := by
  decide +kernel

theorem seed_transport : ∀ j s,
    rotateG 3 (rotateG 0 (standard (if j=0 then 1 else 0))) (permuteBits s)=seed j s := by
  decide +kernel

theorem standard_pure_KL_G : ∀ p : Label 5,weight p ≤ 2 → ∀ j k : Fin 2,
    (∑ s,star (standard j s)*act p (standard k) s)=
      if p=(fun _ => 0) ∧ j=k then 16 else 0 := by
  decide +kernel

theorem rotation_unitary_G : rotationG.conjTranspose*rotationG=2 • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  decide +kernel

theorem rotation_paulis_G : ∀ p : Fin 3,
    rotationG*localG p.succ*rotationG.conjTranspose=
      2 • localG (![2,3,1] p) := by
  decide +kernel

noncomputable section

def code : Matrix (Fin 5 → Fin 2) (Fin 2) ℂ := fun s j => (standard j s : ℂ)/4

def rotation : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • rotationG.map GaussianInt.toComplex

theorem sqrt_squared : (Real.sqrt 2 : ℂ)^2=2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

theorem rotation_unitary : rotation.conjTranspose*rotation=1 := by
  have hG : (rotationG.map GaussianInt.toComplex).conjTranspose*
      rotationG.map GaussianInt.toComplex=(2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rotationG,Matrix.mul_apply,Matrix.map_apply,Matrix.conjTranspose_apply,
        Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
        GaussianInt.toComplex_def]
  rw [rotation,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,hG]
  have hr : star ((Real.sqrt 2 : ℂ)⁻¹)*(Real.sqrt 2 : ℂ)⁻¹*2=1 := by
    rw [star_inv₀,Complex.star_def,Complex.conj_ofReal,← pow_two,inv_pow,sqrt_squared]
    norm_num
  simp only [smul_smul]
  rw [← mul_assoc,hr,one_smul]

def unitaryRotation : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨rotation,Matrix.mem_unitaryGroup_iff'.mpr rotation_unitary⟩

theorem localC_pauli (p : Fin 4) : localC p=MainTheory.PauliTransferTwo.pauli p := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localC,localG,MainTheory.PauliTransferTwo.pauli,GaussianInt.toComplex_def]

theorem rotation_clifford : QuaternionCliffordMatrixBridge.IsClifford unitaryRotation := by
  intro p
  refine ⟨((![1,2,0] : Fin 3 → Fin 3) p),Or.inl ?_⟩
  have hp : ((![1,2,0] : Fin 3 → Fin 3) p).succ=(![2,3,1] p : Fin 4) := by fin_cases p <;> rfl
  change rotation*MainTheory.PauliTransferTwo.pauli p.succ*rotation.conjTranspose=
    MainTheory.PauliTransferTwo.pauli ((![1,2,0] : Fin 3 → Fin 3) p).succ
  rw [← localC_pauli,← localC_pauli]
  rw [hp,rotation,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.smul_mul,smul_smul]
  have hGc : rotationG.map GaussianInt.toComplex*localC p.succ*
      (rotationG.map GaussianInt.toComplex).conjTranspose=(2 : ℂ) • localC (![2,3,1] p) := by
    fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [rotationG,localC,localG,Matrix.mul_apply,Matrix.map_apply,
        Matrix.conjTranspose_apply,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,
        Fin.succ,GaussianInt.toComplex_def]
    all_goals ring
  rw [hGc,smul_smul]
  have hr : star ((Real.sqrt 2 : ℂ)⁻¹)*(Real.sqrt 2 : ℂ)⁻¹*2=1 := by
    simp only [star_inv₀,Complex.star_def,Complex.conj_ofReal]
    rw [← pow_two,inv_pow,sqrt_squared]
    norm_num
  rw [hr,one_smul]

end

end MainTheory.Orbit2StandardFiveQubit
