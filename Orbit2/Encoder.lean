import Orbit2.PhysicalShadow
import Orbit2.Analytic

namespace Orbit2
open scoped BigOperators
open SS.MacWilliams

/-- Actual normalized logical words, full Pauli KL detection, and the chosen
physical logical involution. No certificate or analytic reduction is a field. -/
structure Encoder where
  psi : Fin 2 → SS.State 6 ℂ
  orthonormal : ∀ j k, SS.innerC (psi j) (psi k) = if j = k then 1 else 0
  detects : SS.HasDistance psi 3
  logicalZ : ∀ j, SS.pauliAct
    (⟨fun _ => false, ![false, false, true, true, true, true]⟩ : SS.PauliString 6)
    (psi j) = fun x => (if j = 0 then 1 else -1) * psi j x

/-- The usual normalized Shor--Laflamme A enumerator, using genuine Pauli traces. -/
noncomputable def Encoder.A (V : Encoder) (w : ℕ) : ℝ := Aco V.psi w / 4

def identityPauli (n : ℕ) : SS.PauliString n := ⟨fun _ => false, fun _ => false⟩

theorem pauli_weight_zero_iff {n : ℕ} (p : SS.PauliString n) :
    p.wt = 0 ↔ p = identityPauli n := by
  constructor
  · intro h
    have hf : (Finset.univ.filter fun i => p.x i || p.z i) = ∅ :=
      Finset.card_eq_zero.mp h
    have hi : ∀ i, p.x i = false ∧ p.z i = false := by
      intro i
      have hm : i ∉ Finset.univ.filter (fun i => p.x i || p.z i) := by rw [hf]; simp
      simpa using hm
    cases p with
    | mk x z =>
      have hx : x = fun _ => false := funext fun i => (hi i).1
      have hz : z = fun _ => false := funext fun i => (hi i).2
      simp_all [identityPauli]
  · rintro rfl
    simp [identityPauli, SS.PauliString.wt]

theorem pauliAct_identity {n : ℕ} (u : SS.State n ℂ) :
    SS.pauliAct (identityPauli n) u = u := by
  funext x
  simp [SS.pauliAct, identityPauli, SS.PauliString.numY, SS.bdot, SS.signC]

theorem Encoder.A_zero (V : Encoder) : V.A 0 = 1 := by
  have hset : Finset.univ.filter (fun p : SS.PauliString 6 => p.wt = 0) =
      {identityPauli 6} := by
    ext p
    simp [pauli_weight_zero_iff]
  have ht : SS.MacWilliams.trProj V.psi (identityPauli 6) = 2 := by
    simp [SS.MacWilliams.trProj, pauliAct_identity, V.orthonormal]
  norm_num [Encoder.A, Aco, hset, ht]

theorem Encoder.A_nonneg (V : Encoder) (w : ℕ) : 0 ≤ V.A w := by
  unfold Encoder.A Aco
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (by norm_num)

theorem Encoder.macWilliams (V : Encoder) :
    V.A 4 = 15 - 4*V.A 2 - 3*V.A 3 ∧
    V.A 5 = 12 + 3*V.A 1 + 4*V.A 2 + 3*V.A 3 ∧
    V.A 6 = 4 - 4*V.A 1 - V.A 2 - V.A 3 := by
  have hA0 : Aco V.psi 0 = 4 := by have h := V.A_zero; unfold Encoder.A at h; linarith
  obtain ⟨h4,h5,h6⟩ := SS.MacWilliams.macwilliams_six V.psi V.detects hA0
  unfold Encoder.A
  exact ⟨by linarith, by linarith, by linarith⟩

theorem Encoder.shadow (V : Encoder) : V.A 1 + V.A 2 + V.A 3 ≤ 1 := by
  have hA0 : Aco V.psi 0 = 4 := by have h := V.A_zero; unfold Encoder.A at h; linarith
  have h := SS.Shadow.shadow_bound V.psi V.detects hA0
  unfold Encoder.A
  linarith

/-- The normalized Hilbert-family definition really is an isometric 64-by-2 encoder. -/
def Encoder.matrix (V : Encoder) : Matrix (SS.BitString 6) (Fin 2) ℂ := fun x j => V.psi j x

theorem Encoder.matrix_isometry (V : Encoder) : V.matrix.conjTranspose * V.matrix = 1 := by
  ext j k
  simpa [Encoder.matrix, Matrix.mul_apply, Matrix.conjTranspose_apply, SS.innerC,
    Matrix.one_apply] using V.orthonormal j k

/-- Once the orbit-specific mass/rigidity steps are supplied, there are no
remaining scalar enumerator hypotheses. This lemma is not the final theorem. -/
theorem Encoder.enumerator_of_A3_zero (V : Encoder)
    (hflat : V.A 1 + V.A 2 + V.A 3 = 1) (hz : V.A 3 = 0) :
    0 ≤ V.A 1 ∧ V.A 1 ≤ 1 ∧ (fun w : Fin 7 => V.A w.val) = enumeratorLine (V.A 1) := by
  obtain ⟨h4,h5,h6⟩ := V.macWilliams
  have hy : V.A 2 = 1 - V.A 1 := by linarith
  refine ⟨V.A_nonneg 1, by have h := V.A_nonneg 2; linarith, ?_⟩
  ext w
  fin_cases w <;> simp [enumeratorLine, V.A_zero, hy, hz, h4,h5,h6] <;> ring

end Orbit2
