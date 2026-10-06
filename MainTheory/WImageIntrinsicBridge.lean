import MainTheory.GlobalClassificationBridge
import SixQubit.Orbit36Code

/-!
# From a positive `WImage` witness to an intrinsic group element

`Levels.WImage` contains genuine normalized states and the genuine
Knill--Laflamme predicate, but it is a level-(iii) object.  This file performs
the missing semantic packaging needed to use a positive image witness at
level (i): the identity Knill--Laflamme equation supplies orthogonality, the
two states form an `ExactCode`, their residue support makes them eigenvectors
of the finite diagonal gate, and a primitive finite generator then produces
an element of the actual intrinsic quotient group.

The final theorem specializes this construction to the lightweight explicit
orbit-36 completion in `SixQubit.Orbit36Code`.  It proves existence of a
genuine exact `((6,2,3))` code carrying a nontrivial intrinsic element of
group-theoretic order five.  It deliberately does not import the much heavier
orbit-36 enumerator-rigidity tree: existence needs only the explicit positive
code, not uniqueness of its weight enumerator.  It also makes no claim about
uniqueness of the code or about the order of its whole intrinsic group.
-/

namespace MainTheory.WImageIntrinsicBridge

open MainTheory
open MainTheory.GlobalClassificationBridge

noncomputable section

/-! ## An exact code from the state data stored by `WImage` -/

/-- The identity Pauli on six qubits. -/
def identityPauli : SS.PauliString 6 :=
  ⟨fun _ => false, fun _ => false⟩

@[simp] theorem identityPauli_wt : identityPauli.wt = 0 := by
  simp [identityPauli, SS.PauliString.wt]

@[simp] theorem identityPauli_numY : identityPauli.numY = 0 := by
  simp [identityPauli, SS.PauliString.numY]

/-- The explicit identity Pauli acts as the identity on every state. -/
@[simp] theorem pauliAct_identity (psi : SS.State 6 ℂ) :
    SS.pauliAct identityPauli psi = psi := by
  funext x
  simp only [SS.pauliAct, identityPauli_numY, pow_zero, one_mul]
  simp [identityPauli, SS.bdot]

/-- The identity instance of the genuine KL predicate forces the two
normalized logical words in a `WImage` witness to be mutually orthogonal. -/
theorem pair_orthogonal_of_hasDistance
    (c d : SS.State 6 ℂ) (hdist : SS.HasDistance ![c, d] 3) :
    SS.innerC c d = 0 ∧ SS.innerC d c = 0 := by
  have hwt : identityPauli.wt ≤ 3 - 1 := by simp
  obtain ⟨lambda, hkl⟩ := hdist identityPauli hwt
  constructor
  · have h := hkl 0 1
    rw [if_neg (by decide)] at h
    simpa using h
  · have h := hkl 1 0
    rw [if_neg (by decide)] at h
    simpa using h

/-- The ordered orthonormal frame carried by a positive `WImage` witness. -/
def pairFrame (c d : SS.State 6 ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    CodeSpec.OrthonormalFrame 6 2 where
  vec := ![c, d]
  orthonormal := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hnc
    · simpa using (pair_orthogonal_of_hasDistance c d hdist).1
    · simpa using (pair_orthogonal_of_hasDistance c d hdist).2
    · simpa using hnd

/-- The genuine exact code carried by the same witness. -/
def exactCodeOfPair (c d : SS.State 6 ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : CodeSpec.ExactCode 6 2 3 where
  positiveRank := by decide
  frame := pairFrame c d hnc hnd hdist
  hasDistance := by
    simpa [pairFrame] using hdist

/-! ## Residue support gives a genuine finite generator -/

/-- The contrapositive support convention used by `WImage` is exactly
`SSConditionState`. -/
theorem ssConditionState_of_support {q : ℕ} [NeZero q]
    (a : Fin 6 → ZMod q) (r : ZMod q) (psi : SS.State 6 ℂ)
    (hsupport : ∀ x, SS.weight a x ≠ r → psi x = 0) :
    SS.SSConditionState a r psi := by
  intro x hx
  by_contra hweight
  exact hx (hsupport x hweight)

/-- Package two normalized supported words as a primitive finite generator
of the exact code they define.  Distinctness of the two displayed root
powers is the honest projective-nontriviality premise. -/
def finiteGeneratorOfSupportedPair {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin 6 → ZMod q) (hprimitive : Gate.Primitive q a)
    (r0 r1 : ZMod q) (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight a x ≠ r0 → c x = 0)
    (hd : ∀ x, SS.weight a x ≠ r1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3)
    (hneigen : zeta ^ r0.val ≠ zeta ^ r1.val) :
    RankTwoGlobal.FiniteGeneratorResolution
      (exactCodeOfPair c d hnc hnd hdist) q where
  zeta := zeta
  primitiveRoot := hzeta
  angle := a
  primitive := hprimitive
  eigenFrame := pairFrame c d hnc hnd hdist
  span_eq := rfl
  eigenvalue := ![zeta ^ r0.val, zeta ^ r1.val]
  eigen := by
    intro k
    fin_cases k
    · simpa [pairFrame] using
        (PhaseSector.eigen_of_ssCondition zeta a c r0
          (ssConditionState_of_support a r0 c hc))
    · simpa [pairFrame] using
        (PhaseSector.eigen_of_ssCondition zeta a d r1
          (ssConditionState_of_support a r1 d hd))
  projectively_nontrivial := by
    simpa using hneigen

/-! ## The attained order-five sector -/

/-- The standard primitive fifth root used for the paper representative. -/
def rootFive : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (5 : ℂ))

theorem rootFive_primitive : IsPrimitiveRoot rootFive 5 := by
  exact Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The lightweight explicit code's angle vector is primitive because its
first coordinate is one. -/
theorem orbit36_angle_primitive :
    Gate.Primitive 5 SixQubit.Orbit36Code.av := by
  intro divisor _ hall
  have h0 := hall 0
  have hav : (SixQubit.Orbit36Code.av 0).val = 1 := by decide
  rw [hav] at h0
  exact Nat.dvd_one.mp h0

/-- Residues zero and four give distinct fifth-root eigenvalues. -/
theorem rootFive_zero_four_distinct :
    rootFive ^ ((0 : ZMod 5).val) ≠
      rootFive ^ ((4 : ZMod 5).val) := by
  change (1 : ℂ) ≠ rootFive ^ 4
  intro hone
  have hp : rootFive ^ 4 = 1 := hone.symm
  have hdvd : 5 ∣ 4 := (rootFive_primitive.pow_eq_one_iff_dvd 4).1 hp
  norm_num at hdvd

/-- The explicit bottom word is supported in residue zero. -/
theorem orbit36_c36_support :
    ∀ x, SS.weight SixQubit.Orbit36Code.av x ≠ 0 →
      SixQubit.Orbit36Code.c36 x = 0 := by
  intro x hweight
  apply SixQubit.Orbit36Code.c36_vanishes_off_S0 x
  intro hx
  have hfiber : x ∈
      (Finset.univ : Finset (SS.BitString 6)).filter
        (fun y => SS.weight SixQubit.Orbit36Code.av y = 0) := by
    simpa only [SixQubit.Orbit36Code.S0_eq_fiber] using hx
  exact hweight (Finset.mem_filter.mp hfiber).2

/-- The explicit top word is supported in residue four. -/
theorem orbit36_d36_support :
    ∀ x, SS.weight SixQubit.Orbit36Code.av x ≠ 4 →
      SixQubit.Orbit36Code.d36 x = 0 := by
  intro x hweight
  apply SixQubit.Orbit36Code.d36_vanishes_off_S1 x
  intro hx
  have hfiber : x ∈
      (Finset.univ : Finset (SS.BitString 6)).filter
        (fun y => SS.weight SixQubit.Orbit36Code.av y = 4) := by
    simpa only [SixQubit.Orbit36Code.S1_eq_fiber] using hx
  exact hweight (Finset.mem_filter.mp hfiber).2

/-- **A genuine realized order-five intrinsic element.**

The existential code is built from the explicit positive orbit-36 states
`c36,d36`.  The element is the quotient class of their primitive finite
diagonal generator, and `orderOf = 5` follows inside the kernel from the
generator's two-fibre certificate, not from the paper label `m = 5`. -/
theorem exists_exact_six_qubit_intrinsic_order_five :
    ∃ C : CodeSpec.ExactCode 6 2 3,
      ∃ g : IntrinsicGroup C, g ≠ 1 ∧ orderOf g = 5 := by
  let C : CodeSpec.ExactCode 6 2 3 :=
    exactCodeOfPair SixQubit.Orbit36Code.c36 SixQubit.Orbit36Code.d36
      SixQubit.Orbit36Code.c36_normalized
      SixQubit.Orbit36Code.d36_normalized
      SixQubit.Orbit36Code.canonical_is_code
  let G : RankTwoGlobal.FiniteGeneratorResolution C 5 :=
    finiteGeneratorOfSupportedPair rootFive rootFive_primitive
      SixQubit.Orbit36Code.av orbit36_angle_primitive
      0 4 SixQubit.Orbit36Code.c36 SixQubit.Orbit36Code.d36
      orbit36_c36_support orbit36_d36_support
      SixQubit.Orbit36Code.c36_normalized
      SixQubit.Orbit36Code.d36_normalized
      SixQubit.Orbit36Code.canonical_is_code
      rootFive_zero_four_distinct
  let T : RankTwoGlobal.TwoFiberCertificate G :=
    Classical.choice (RankTwoGlobal.finiteGenerator_twoFiber G)
  have hdiv : T.logicalOrder ∣ 5 := T.logicalOrder_dvd_physical
  have hle : T.logicalOrder ≤ 5 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have htwo : 2 ≤ T.logicalOrder := T.two_le_logicalOrder
  have hcases : T.logicalOrder = 2 ∨ T.logicalOrder = 3 ∨
      T.logicalOrder = 4 ∨ T.logicalOrder = 5 := by
    omega
  have hm : T.logicalOrder = 5 := by
    rcases hcases with h2 | h3 | h4 | h5
    · exfalso
      rw [h2] at hdiv
      norm_num at hdiv
    · exfalso
      rw [h3] at hdiv
      norm_num at hdiv
    · exfalso
      rw [h4] at hdiv
      norm_num at hdiv
    · exact h5
  refine ⟨C, G.intrinsicClass, T.intrinsic_class_ne_one, ?_⟩
  exact T.intrinsic_order_eq.trans hm

end

end MainTheory.WImageIntrinsicBridge
