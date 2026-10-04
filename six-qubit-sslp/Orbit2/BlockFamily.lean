import Orbit2.Certificate

namespace Orbit2
open scoped BigOperators

/-- A checked shifted block, with its embedding in the 528 monomial coordinates. -/
structure CheckedBlock where
  n : ℕ
  M : Matrix (Fin n) (Fin n) ℚ
  certificate : LDLCertificate n n
  shifted : ∀ i j, certificate.A i j = M i j - if i = j then 4 else 0
  indices : Fin n → Fin 528

def blockEnergy (B : CheckedBlock) (z : Fin 528 → ℂ) : ℝ :=
  complexEnergy B.M (fun i => z (B.indices i))

def blockMass (B : CheckedBlock) (z : Fin 528 → ℂ) : ℝ :=
  ∑ i, Complex.normSq (z (B.indices i))

theorem CheckedBlock.coercivity (B : CheckedBlock) (z : Fin 528 → ℂ) :
    4 * blockMass B z ≤ blockEnergy B z :=
  shifted_coercivity B.M B.certificate B.shifted _

noncomputable def familyEnergy (B : Fin 111 → CheckedBlock) (z : Fin 528 → ℂ) : ℝ :=
  (∑ b, blockEnergy (B b) z) / 12

def familyMass (B : Fin 111 → CheckedBlock) (z : Fin 528 → ℂ) : ℝ :=
  ∑ b, blockMass (B b) z

theorem family_coercivity (B : Fin 111 → CheckedBlock) (z : Fin 528 → ℂ) :
    (1/3 : ℝ) * familyMass B z ≤ familyEnergy B z := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ => (B b).coercivity z)
  simp only [← Finset.mul_sum] at h
  unfold familyMass familyEnergy
  linarith

theorem familyMass_nonneg (B : Fin 111 → CheckedBlock) (z : Fin 528 → ℂ) :
    0 ≤ familyMass B z := by
  exact Finset.sum_nonneg (fun b _ => Finset.sum_nonneg
    (fun i _ => Complex.normSq_nonneg (z ((B b).indices i))))

/-- The full checked block family supplies coercivity here. Only the two
identities connecting this polynomial to the physical constraints remain inputs. -/
theorem family_rigidity (B : Fin 111 → CheckedBlock) (z : Fin 528 → ℂ)
    (c : Fin 48 → ℝ) (hidentity : familyEnergy B z = -(∑ e, c e ^ 2)) :
    (∀ e, c e = 0) ∧ (∀ b i, z ((B b).indices i) = 0) := by
  have hc := family_coercivity B z
  have hm := familyMass_nonneg B z
  have hs : 0 ≤ ∑ e, c e ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs0 : ∑ e, c e ^ 2 = 0 := by linarith
  have hm0 : familyMass B z = 0 := by linarith
  constructor
  · intro e
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (c e))).mp hs0
    exact eq_zero_of_pow_eq_zero (he e (Finset.mem_univ e))
  · have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
      Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (z ((B b).indices i))))).mp hm0
    intro b i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Complex.normSq_nonneg (z ((B b).indices i)))).mp (hb b (Finset.mem_univ b))
    exact Complex.normSq_eq_zero.mp (hi i (Finset.mem_univ i))

end Orbit2
