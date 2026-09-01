import MainTheory.PermutationFrameBridge
import MainTheory.RankTwoGlobal

/-!
# Semantic transport through a physical-qubit permutation

The final outer record stores an angle vector only up to a coordinate
permutation.  This file certifies the corresponding semantic transport.  For
`permAct σ`, the transported angle is `a ∘ σ.symm`; this direction is fixed by
an explicit subset-sum identity, rather than inferred from notation.

The file transports states, exact SS fibres, the genuine distance-three KL
predicate, exact codes, and `FiniteGeneratorResolution`.  It concerns only a
physical coordinate permutation.  It does not assert transport through the
separate local-`X` or coprime unit-power normalization steps.
-/

namespace MainTheory.PermutationSemanticTransport

open MainTheory

noncomputable section

/-- The angle vector corresponding to `CodeEquiv.permAct σ`. -/
def permAngle {n q : ℕ} (σ : Equiv.Perm (Fin n))
    (a : Fin n → ZMod q) : Fin n → ZMod q :=
  fun j ↦ a (σ.symm j)

/-- Exact covariance of the subset-sum residue. -/
theorem weight_permStr {n q : ℕ} (σ : Equiv.Perm (Fin n))
    (a : Fin n → ZMod q) (s : SS.BitString n) :
    SS.weight (permAngle σ a) s =
      SS.weight a (SixQubit.CodeEquiv.permStr σ s) := by
  unfold SS.weight permAngle SixQubit.CodeEquiv.permStr
  simpa using
    (Equiv.sum_comp σ
      (fun j ↦ a (σ.symm j) * SS.bit (m := q) (s j))).symm

/-- Forward transport of an exact SS fibre. -/
theorem ssConditionState_permAct {n q : ℕ}
    (σ : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (r : ZMod q)
    (psi : SS.State n ℂ) (h : SS.SSConditionState a r psi) :
    SS.SSConditionState (permAngle σ a) r
      (SixQubit.CodeEquiv.permAct σ psi) := by
  intro s hs
  rw [weight_permStr]
  exact h (SixQubit.CodeEquiv.permStr σ s) hs

/-- Exact SS-fibre transport is reversible. -/
theorem ssConditionState_permAct_iff {n q : ℕ}
    (σ : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (r : ZMod q)
    (psi : SS.State n ℂ) :
    SS.SSConditionState (permAngle σ a) r
        (SixQubit.CodeEquiv.permAct σ psi) ↔
      SS.SSConditionState a r psi := by
  constructor
  · intro h
    have hback := ssConditionState_permAct σ.symm
      (permAngle σ a) r (SixQubit.CodeEquiv.permAct σ psi) h
    have hangle : permAngle σ.symm (permAngle σ a) = a := by
      funext i
      simp [permAngle]
    rw [hangle] at hback
    simpa only [SixQubit.CodeEquiv.permAct_inv] using hback
  · exact ssConditionState_permAct σ a r psi

/-- Forward transport of the genuine KL distance predicate, at every
requested distance.  Stated at arbitrary `d` because `thm:rank-two-sslp`
assumes only `d >= 2`. -/
theorem hasDistance_permAct {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Fin 2 → SS.State n ℂ) (h : SS.HasDistance p d) :
    SS.HasDistance (fun k ↦ SixQubit.CodeEquiv.permAct σ (p k)) d := by
  apply (RankTwoGlobal.detects_iff_raw _ _).mpr
  exact SixQubit.CodeEquiv.detectsRaw_permAct σ
    ((RankTwoGlobal.detects_iff_raw _ _).mp h)

/-- The KL distance is invariant in both directions under a coordinate
permutation. -/
theorem hasDistance_permAct_iff {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Fin 2 → SS.State n ℂ) :
    SS.HasDistance (fun k ↦ SixQubit.CodeEquiv.permAct σ (p k)) d ↔
      SS.HasDistance p d := by
  constructor
  · intro h
    have hback := hasDistance_permAct σ.symm
      (fun k ↦ SixQubit.CodeEquiv.permAct σ (p k)) h
    simpa only [SixQubit.CodeEquiv.permAct_inv] using hback
  · exact hasDistance_permAct σ p

/-- The permutation action as a complex-linear map on physical states. -/
def permActLinear {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    SS.State n ℂ →ₗ[ℂ] SS.State n ℂ where
  toFun := SixQubit.CodeEquiv.permAct σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The span of a permuted frame is the linear image of the original span. -/
theorem map_codeSpan_permFrame {n K : ℕ}
    (F : CodeSpec.OrthonormalFrame n K) (σ : Equiv.Perm (Fin n)) :
    Submodule.map (permActLinear σ) (CodeSpec.codeSpan F) =
      CodeSpec.codeSpan (PermutationFrameBridge.permFrame F σ) := by
  unfold CodeSpec.codeSpan
  rw [Submodule.map_span]
  congr 1
  ext psi
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨F.vec k, ⟨k, rfl⟩, rfl⟩

/-- Equality of frame spans is preserved by applying the same physical-qubit
permutation to both frames. -/
theorem codeSpan_permFrame_eq_of_eq {n K : ℕ}
    (F G : CodeSpec.OrthonormalFrame n K) (σ : Equiv.Perm (Fin n))
    (hspan : CodeSpec.codeSpan F = CodeSpec.codeSpan G) :
    CodeSpec.codeSpan (PermutationFrameBridge.permFrame F σ) =
      CodeSpec.codeSpan (PermutationFrameBridge.permFrame G σ) := by
  rw [← map_codeSpan_permFrame, ← map_codeSpan_permFrame, hspan]

/-- Exact codes remain exact after permuting physical qubits. -/
def permExactCode {n : ℕ} (C : CodeSpec.ExactCode n 2 3)
    (σ : Equiv.Perm (Fin n)) : CodeSpec.ExactCode n 2 3 where
  positiveRank := C.positiveRank
  frame := PermutationFrameBridge.permFrame C.frame σ
  hasDistance := hasDistance_permAct σ C.frame.vec C.hasDistance

/-- Covariance of the finite diagonal gate under the paired state/angle
permutation. -/
theorem gate_permAct {n q : ℕ} [NeZero q]
    (σ : Equiv.Perm (Fin n)) (zeta : ℂ) (a : Fin n → ZMod q)
    (psi : SS.State n ℂ) :
    Gate.gate zeta (permAngle σ a)
        (SixQubit.CodeEquiv.permAct σ psi) =
      SixQubit.CodeEquiv.permAct σ (Gate.gate zeta a psi) := by
  funext s
  unfold Gate.gate Gate.diag SixQubit.CodeEquiv.permAct
  rw [weight_permStr]

/-- Primitivity of an angle vector is invariant under coordinate
permutation. -/
theorem primitive_permAngle {n q : ℕ}
    (σ : Equiv.Perm (Fin n)) (a : Fin n → ZMod q)
    (hprim : Gate.Primitive q a) : Gate.Primitive q (permAngle σ a) := by
  intro d hd hall
  apply hprim d hd
  intro j
  have hj := hall (σ j)
  simpa [permAngle] using hj

/-- Full transport of finite-generator semantic data through a physical-qubit
permutation.  The modulus, root, logical eigenvalues, and projective
nontriviality are unchanged; states and the angle vector are transported in
the paired convention proved above. -/
def permFiniteGeneratorResolution {n q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (σ : Equiv.Perm (Fin n)) :
    RankTwoGlobal.FiniteGeneratorResolution (permExactCode C σ) q where
  zeta := G.zeta
  primitiveRoot := G.primitiveRoot
  angle := permAngle σ G.angle
  primitive := primitive_permAngle σ G.angle G.primitive
  eigenFrame := PermutationFrameBridge.permFrame G.eigenFrame σ
  span_eq := codeSpan_permFrame_eq_of_eq C.frame G.eigenFrame σ G.span_eq
  eigenvalue := G.eigenvalue
  eigen := by
    intro k
    change Gate.gate G.zeta (permAngle σ G.angle)
        (SixQubit.CodeEquiv.permAct σ (G.eigenFrame.vec k)) =
      fun x ↦ G.eigenvalue k *
        SixQubit.CodeEquiv.permAct σ (G.eigenFrame.vec k) x
    rw [gate_permAct, G.eigen k]
    rfl
  projectively_nontrivial := G.projectively_nontrivial

end

end MainTheory.PermutationSemanticTransport
