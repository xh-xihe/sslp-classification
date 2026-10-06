import Orbit2.PurificationKL
import Orbit2.PauliConjugation
import Orbit2.PurityDefinitions

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unusedSimpArgs false

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.HilbertBridge
open Orbit2.PurityReduction
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Gsign (p : Label 7) : ℤ := ∏ i, Quartic.character (G i) (p i)

theorem Gsign_site : ∀ (i : Fin 7) (a : Fin 4), Quartic.character (G i) a =
    if (i.val = 0 ∨ (3 ≤ i.val)) ∧ (a = 1 ∨ a = 2) then -1 else 1 := by decide +kernel

theorem Gsign_odd (p : Label 7) (hp : zeroParity p) : Gsign p = -1 := by
  unfold Gsign
  simp_rw [Gsign_site]
  rw [Finset.prod_ite,Finset.prod_const,Finset.prod_const_one,mul_one]
  have hn : ((∑ i : Fin 7, if (i.val = 0 ∨ (3 ≤ i.val)) ∧ (p i = 1 ∨ p i = 2)
      then 1 else 0) : ℕ) =
      (Finset.univ.filter (fun i : Fin 7 => (i.val = 0 ∨ (3 ≤ i.val)) ∧ (p i = 1 ∨ p i = 2))).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  unfold zeroParity at hp
  simp only [decide_eq_true_eq] at hp
  rw [hn] at hp
  exact (Nat.odd_iff.mpr hp).neg_one_pow

theorem G_conjugation (p : Label 7) : operator G * operator p * operator G =
    (Gsign p : ℂ) • operator p := by
  unfold operator
  rw [tensor_mul,tensor_mul]
  simp_rw [Quartic.localC_conjugation]
  rw [tensor_smul]
  simp [Gsign]

theorem local_phase_unit (a b : Fin 4) : Complex.normSq (localPhase a b : ℂ) = 1 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [localPhase,GaussianInt.toComplex_def,Complex.normSq_apply]

theorem phase_unit (p q : Label 7) : Complex.normSq (phase p q : ℂ) = 1 := by
  have h : ∀ s : Finset (Fin 7), Complex.normSq (∏ i ∈ s, (localPhase (p i) (q i) : ℂ)) = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi,Complex.normSq_mul,local_phase_unit,ih]
  simpa [phase,map_prod] using h Finset.univ

theorem Encoder.purification_G (V : Encoder) :
    operator G * referenceColumn V.tensorMatrix = referenceColumn V.tensorMatrix := by
  have he : Fin.cons (⟨3,by decide⟩ : Fin 4) (![0,0,3,3,3,3] : Label 6) = G := by
    funext i; fin_cases i <;> rfl
  rw [← he]
  ext s k
  fin_cases k
  change (operator (Fin.cons (⟨3,by decide⟩ : Fin 4) ![0,0,3,3,3,3]) *
    referenceColumn V.tensorMatrix) s 0 = referenceColumn V.tensorMatrix s 0
  rw [reference_action,V.tensor_logical]
  have hf : ∀ j : Fin 2, FiveQubit.flipSite (⟨3,by decide⟩ : Fin 4) j = j := by decide +kernel
  rw [hf]
  change localC ⟨3,by decide⟩ (s 0) (s 0) *
      ((if s 0 = 0 then 1 else -1) * V.tensorMatrix (fun i => s i.succ) (s 0)) =
    V.tensorMatrix (fun i => s i.succ) (s 0)
  generalize s 0 = j
  fin_cases j <;> norm_num [referenceColumn,localC,localG,GaussianInt.toComplex_def]

theorem Encoder.labelMass_pairing (V : Encoder) (p : Label 7) :
    V.labelMass (partner p) = V.labelMass p := by
  let Φ := referenceColumn V.tensorMatrix
  have he : Φ.conjTranspose * operator p * Φ =
      (phase p G : ℂ) • (Φ.conjTranspose * operator (partner p) * Φ) := by
    calc
      _ = Φ.conjTranspose * operator p * (operator G * Φ) := by rw [V.purification_G]
      _ = Φ.conjTranspose * (operator p * operator G) * Φ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [operator_mul]; simp [partner,Matrix.mul_smul,Matrix.smul_mul]
  have hentry := congrArg (fun M => M 0 0) he
  have hnorm := congrArg Complex.normSq hentry
  simp only [Matrix.smul_apply,smul_eq_mul,Complex.normSq_mul,phase_unit,one_mul] at hnorm
  unfold Encoder.labelMass Encoder.purificationMass
  rw [column_compression (referenceColumn V.tensorMatrix) V.purification V.purification_column,
    column_compression (referenceColumn V.tensorMatrix) V.purification V.purification_column]
  exact congrArg (fun r : ℝ => r/4) hnorm.symm

theorem Encoder.labelMass_parity_zero (V : Encoder) (p : Label 7) (hp : zeroParity p) :
    V.labelMass p = 0 := by
  let Φ := referenceColumn V.tensorMatrix
  have hG : operator G * Φ = Φ := V.purification_G
  have hGT : Φ.conjTranspose * operator G = Φ.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hG
    simpa [Matrix.conjTranspose_mul,operator_hermitian] using h
  have he : Φ.conjTranspose * operator p * Φ = -(Φ.conjTranspose * operator p * Φ) := by
    calc
      _ = (Φ.conjTranspose * operator G) * operator p * (operator G * Φ) := by rw [hG,hGT]
      _ = Φ.conjTranspose * (operator G * operator p * operator G) * Φ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [G_conjugation,Gsign_odd p hp]; simp [Matrix.mul_smul,Matrix.smul_mul]
  have hx := congrArg (fun M => M 0 0) he
  have hz : (Φ.conjTranspose * operator p * Φ) 0 0 = 0 := by
    simp only [Matrix.neg_apply] at hx
    linear_combination hx / 2
  unfold Encoder.labelMass Encoder.purificationMass
  rw [column_compression (referenceColumn V.tensorMatrix) V.purification V.purification_column,hz]
  norm_num

theorem Encoder.labelMass_forbidden_zero (V : Encoder) (p : Label 7) (hp : forbidden p) :
    V.labelMass p = 0 := by
  simp only [forbidden,Bool.or_eq_true] at hp
  rcases hp with hp|hp
  · unfold zeroKL at hp
    simp only [decide_eq_true_eq] at hp
    exact V.reference_KL_mass_zero p hp.1 hp.2
  · exact V.labelMass_parity_zero p hp

end Orbit2
