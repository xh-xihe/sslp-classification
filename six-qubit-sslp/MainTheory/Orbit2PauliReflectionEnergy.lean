import MainTheory.Orbit2PauliReflection
import MainTheory.Orbit2PrintedEnumeratorMasses

/-! The normalized traces of the three actual reflection parts are A1,A2,A3. -/

namespace MainTheory.Orbit2PauliReflectionEnergy

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic Orbit2.PhysicalFlatness
open MainTheory.Orbit2PauliReflection
open MainTheory.Orbit2PrintedPurityMasses MainTheory.Orbit2PrintedActiveMasses
open MainTheory.Orbit2PrintedEnumeratorMasses
open scoped BigOperators

theorem coefficient_real (V : Encoder) (p : Label 4) :
    star (tau (operator p*K V))=tau (operator p*K V) := by
  unfold tau
  rw [star_div₀]
  change star (Matrix.trace (operator p*K V))/star ((2 : ℂ)^4)=_
  rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hermitian,
    operator_hermitian,Matrix.trace_mul_comm,star_pow,star_ofNat]

theorem coefficient_square (V : Encoder) (p : Label 4) :
    (tau (operator p*K V))^2=(Complex.normSq (tau (operator p*K V)) : ℂ) := by
  rw [← SixQubit.CodeEquiv.star_mul_self]
  rw [coefficient_real,pow_two]

theorem part_coefficient (V : Encoder) (k : Fin 3) (p : Label 4) :
    tau (operator p*part V k)=if support k p then tau (operator p*K V) else 0 := by
  unfold part
  rw [Matrix.mul_sum,tau_sum]
  have he (q : Label 4) :
      tau (operator p*(if support k q then tau (operator q*K V) • operator q else 0))=
      if support k q then tau (operator q*K V)*(if p=q then 1 else 0) else 0 := by
    by_cases hq : support k q
    · rw [if_pos hq,Matrix.mul_smul,tau_smul,tau_operator_pair,if_pos hq]
    · simp [hq,tau]
  simp_rw [he]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [Ne.symm hq]
  · simp

theorem energy (V : Encoder) (k : Fin 3) :
    tau (part V k*part V k)=
      ((∑ p : Label 4,if support k p then Complex.normSq (tau (operator p*K V)) else 0 : ℝ) : ℂ) := by
  change tau ((∑ p : Label 4,if support k p then tau (operator p*K V) • operator p else 0)*part V k)=_
  rw [Matrix.sum_mul,tau_sum]
  have he (p : Label 4) :
      tau ((if support k p then tau (operator p*K V) • operator p else 0)*part V k)=
      if support k p then (tau (operator p*K V))^2 else 0 := by
    by_cases hp : support k p
    · rw [if_pos hp,Matrix.smul_mul,tau_smul,part_coefficient,if_pos hp,if_pos hp,pow_two]
    · simp [hp,tau]
  simp_rw [he]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · rw [coefficient_square]
  · simp

theorem support_matches_pattern : ∀ k : Fin 3,∀ q : Label 4,
    support k q=pattern k (Orbit2.PurityReduction.packed 0 0 0 q) := by
  intro k
  fin_cases k
  all_goals decide +kernel

theorem coefficient_mass (V : Encoder) (q : Label 4) (hq : q≠fun _ => 0) :
    Complex.normSq (tau (operator q*K V))=physicalMass V (joinLabel (fun _ => 0) q) := by
  rw [normalization V q hq]
  simp only [physicalMass,Complex.normSq_div,Complex.normSq_ofNat]
  norm_num

theorem part_mass (V : Encoder) (k : Fin 3) :
    (∑ q : Label 4,if support k q then Complex.normSq (tau (operator q*K V)) else 0)=
      mass V (pattern k) := by
  rw [mass_projection,sum_splitLabel64]
  have he (b : Label 2) :
      (∑ q : Label 4,if pattern k (Fin.cons (0 : Fin 4) (joinLabel b q))
        then physicalMass V (joinLabel b q) else 0)=
      if b=(fun _ => 0) then
        (∑ q : Label 4,if support k q then physicalMass V (joinLabel (fun _ => 0) q) else 0) else 0 := by
    by_cases hb : b=(fun _ => 0)
    · subst b
      have hp (q : Label 4) : Fin.cons (0 : Fin 4) (joinLabel (fun _ => 0) q)=
          Orbit2.PurityReduction.packed 0 0 0 q := by
        funext i
        fin_cases i <;> rfl
      simp only [if_true,hp,← support_matches_pattern]
    · have hn (q : Label 4) : ¬pattern k (Fin.cons (0 : Fin 4) (joinLabel b q)) := by
        intro h
        simp only [pattern,Bool.and_eq_true,active_support_split] at h
        exact hb h.1
      simp [hb,hn]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hs : support k q
  · have hq : q≠fun _ => 0 := by
      intro hq
      subst q
      simp [support,pauliWeight,transverseCount] at hs
    simp only [if_pos hs,coefficient_mass V q hq]
  · simp [hs]

theorem trace_enumerator (V : Encoder) (k : Fin 3) :
    tau (part V k*part V k)=(V.A (k.val+1) : ℂ) := by
  rw [energy,part_mass,← enumerator_mass]

end

end MainTheory.Orbit2PauliReflectionEnergy
