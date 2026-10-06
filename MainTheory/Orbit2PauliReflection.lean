import MainTheory.Orbit2PhysicalMarginals

/-! The actual active reflection and its literal 4/24/48 Pauli support. -/

namespace MainTheory.Orbit2PauliReflection

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic Orbit2.PurityReduction Orbit2.PhysicalFlatness
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def K (V : Encoder) : Matrix ActiveBits ActiveBits ℂ := (2 : ℂ) • V.activeProjector-1

def support (k : Fin 3) (p : Label 4) : Bool := decide
  (pauliWeight p=k.val+1 ∧ transverseCount p=(![0,2,2] k : ℕ))

theorem support_counts : ∀ k : Fin 3,
    (Finset.univ.filter (fun p : Label 4 => support k p)).card=(![4,24,48] k : ℕ) := by
  intro k
  fin_cases k
  all_goals decide +kernel

theorem hermitian (V : Encoder) : (K V).conjTranspose=K V := by
  simp only [K,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,star_ofNat,
    (MainTheory.Orbit2ActiveProjectorRank.projector V).1,Matrix.conjTranspose_one]

theorem involution (V : Encoder) : K V*K V=1 := by
  have hP := (MainTheory.Orbit2ActiveProjectorRank.projector V).2.1
  simp only [K,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
    hP,Matrix.one_mul,Matrix.mul_one]
  ext x y
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem commutes (V : Encoder) :
    MainTheory.Orbit2PhysicalMarginals.D*K V=K V*MainTheory.Orbit2PhysicalMarginals.D := by
  simp only [K,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,Matrix.one_mul,MainTheory.Orbit2PhysicalMarginals.active_commutes]

theorem normalization (V : Encoder) (p : Label 4) (hp : p≠(fun _ => 0)) :
    tau (operator p*K V)=SS.MacWilliams.trProj V.psi
      (decode (joinLabel (fun _ => 0) p))/2 := by
  have h := V.activeProjector_trace_transport p
  have ht : Matrix.trace (operator p*K V)=
      2*Matrix.trace (operator p*V.activeProjector)-Matrix.trace (operator p) := by
    rw [K,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_sub,Matrix.trace_smul]
    rfl
  unfold tau at h ⊢
  rw [ht,operator_trace,if_neg hp]
  norm_num at h ⊢
  linear_combination 2*h

theorem identity_zero (V : Encoder) : tau (operator (fun _ : Fin 4 => 0)*K V)=0 := by
  rw [operator_zero,Matrix.one_mul,K]
  simp only [tau,Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,
    (MainTheory.Orbit2ActiveProjectorRank.projector V).2.2.1,smul_eq_mul]
  norm_num [ActiveBits]

theorem support_reason : ∀ p : Label 4,p≠(fun _ => 0) →
    ¬(support 0 p ∨ support 1 p ∨ support 2 p) →
    forbidden (activeEmbedding p) ∨ forbidden (partner (activeEmbedding p)) ∨
      activeWeight p=4 := by
  decide +kernel

theorem outside_zero (V : Encoder) (p : Label 4)
    (hp : ¬(support 0 p ∨ support 1 p ∨ support 2 p)) : tau (operator p*K V)=0 := by
  by_cases h0 : p=(fun _ => 0)
  · subst p
    exact identity_zero V
  · have hm : V.labelMass (activeEmbedding p)=0 := by
      rcases support_reason p h0 hp with hf|hf|hw
      · exact V.labelMass_forbidden_zero _ hf
      · rw [← V.labelMass_pairing]
        exact V.labelMass_forbidden_zero _ hf
      · exact active_four_zero V p hw
    have ht := V.activeProjector_trace_zero p hm
    rw [V.activeProjector_trace_transport] at ht
    rw [normalization V p h0]
    linear_combination 2*ht

def part (V : Encoder) (k : Fin 3) : Matrix ActiveBits ActiveBits ℂ :=
  ∑ p : Label 4,if support k p then tau (operator p*K V) • operator p else 0

theorem support_disjoint : ∀ p : Label 4,
    ¬(support 0 p ∧ support 1 p) ∧ ¬(support 0 p ∧ support 2 p) ∧
      ¬(support 1 p ∧ support 2 p) := by
  decide +kernel

theorem expansion (V : Encoder) : K V=part V 0+part V 1+part V 2 := by
  rw [matrix_reconstruction (K V)]
  unfold part
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hd := support_disjoint p
  by_cases hp : support 0 p ∨ support 1 p ∨ support 2 p
  · split_ifs <;> simp_all
  · rw [outside_zero V p hp]
    simp_all

end

end MainTheory.Orbit2PauliReflection
