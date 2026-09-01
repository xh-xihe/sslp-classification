import MainTheory.D3NormalizedFreshPhase
import MainTheory.Cyclic

/-!
# Exact real representative of a normalized finite gate

A primitive complex `q`-th root is a coprime power of the standard root
`exp(2*pi*i/q)`.  Choosing that exponent gives a literal real phase vector
for any normalized `ZMod q` angle.  This file proves equality of the complete
finite and real diagonal actions, then uses that equality to discharge the
last real-eigenvalue premise of `D3NormalizedFreshPhase.freshSparsePhase`.

All choices are made from kernel-proved finite root-of-unity statements.  No
floating-point argument, branch of a numerical logarithm, or equality of
informal phase representatives is used.
-/

namespace MainTheory.D3NormalizedFiniteToReal

variable {n : ℕ}

open MainTheory
open MainTheory.SixQubitSemanticEntrance
open MainTheory.D3FreshSparseAssembly
open MainTheory.D3NormalizedFreshPhase
open scoped BigOperators

noncomputable section

/-- The standard primitive `q`-th root, independent of any sparse system. -/
def canonicalRoot (q : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ))

theorem canonicalRoot_primitive (q : ℕ) [NeZero q] :
    IsPrimitiveRoot (canonicalRoot q) q := by
  exact Complex.isPrimitiveRoot_exp q (NeZero.ne q)

private theorem exists_rootExponent {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    ∃ i < q, i.Coprime q ∧ canonicalRoot q ^ i = zeta :=
  (canonicalRoot_primitive q).isPrimitiveRoot_iff.mp hzeta

/-- Exponent expressing a supplied primitive root as a power of the standard
root. -/
def rootExponent {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) : ℕ :=
  Classical.choose (exists_rootExponent zeta hzeta)

theorem rootExponent_lt {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    rootExponent zeta hzeta < q :=
  (Classical.choose_spec (exists_rootExponent zeta hzeta)).1

theorem rootExponent_coprime {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    (rootExponent zeta hzeta).Coprime q :=
  (Classical.choose_spec (exists_rootExponent zeta hzeta)).2.1

theorem canonicalRoot_pow_rootExponent {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    canonicalRoot q ^ rootExponent zeta hzeta = zeta :=
  (Classical.choose_spec (exists_rootExponent zeta hzeta)).2.2

/-- Exact real representative of the normalized modular angle carried by a
two-fibre certificate. -/
def normalizedRealPhase
    {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) : Fin n → ℝ :=
  fun j ↦
    ((rootExponent G.zeta G.primitiveRoot *
        (normalizedFiniteAngle G T j).val : ℕ) : ℝ) / (q : ℝ)

/-- Coordinate-level equality between the real representative and the
supplied primitive root. -/
theorem exp_normalizedRealPhase
    {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) (j : Fin n) :
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (normalizedRealPhase T j : ℂ)) =
      G.zeta ^ (normalizedFiniteAngle G T j).val := by
  let i := rootExponent G.zeta G.primitiveRoot
  let v := (normalizedFiniteAngle G T j).val
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hroot : canonicalRoot q ^ i = G.zeta := by
    exact canonicalRoot_pow_rootExponent G.zeta G.primitiveRoot
  calc
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (normalizedRealPhase T j : ℂ)) =
        Complex.exp
          ((i * v : ℕ) *
            (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ))) := by
      congr 1
      simp only [normalizedRealPhase, i, v]
      push_cast
      field_simp [hq]
    _ = canonicalRoot q ^ (i * v) := by
      rw [canonicalRoot, Complex.exp_nat_mul]
    _ = (canonicalRoot q ^ i) ^ v := by
      rw [pow_mul]
    _ = G.zeta ^ v := by
      rw [hroot]

private theorem prod_chi_eq_chi_sum {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (s : SS.BitString n) (S : Finset (Fin n)) :
    (∏ j ∈ S, if s j then Cyclic.chi zeta (a j) else 1) =
      Cyclic.chi zeta (∑ j ∈ S, a j * SS.bit (s j)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Cyclic.chi]
  | @insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        Cyclic.chi_add zeta hzeta, ih]
      cases s j <;> simp [SS.bit, Cyclic.chi]

/-- Equality of the complete diagonal values, not merely their values on the
two logical supports. -/
theorem normalizedDiag_eq_realPhase
    {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) (s : SS.BitString n) :
    Gate.diag G.zeta (normalizedFiniteAngle G T) s =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (MainTheory.RealGate.angle (normalizedRealPhase T) s : ℂ)) := by
  rw [Cyclic.diag_eq_chi]
  let A : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  calc
    Cyclic.chi G.zeta
        (SS.weight (normalizedFiniteAngle G T) s) =
        ∏ j : Fin n,
          if s j then
            G.zeta ^ (normalizedFiniteAngle G T j).val
          else 1 := by
      simpa [SS.weight, Cyclic.chi] using
        (prod_chi_eq_chi_sum G.zeta G.primitiveRoot
          (normalizedFiniteAngle G T) s Finset.univ).symm
    _ = ∏ j : Fin n,
          Complex.exp
            (A *
              ((if s j then normalizedRealPhase T j else 0 : ℝ) : ℂ)) := by
      apply Finset.prod_congr rfl
      intro j _
      cases s j <;> simp [A, exp_normalizedRealPhase]
    _ = Complex.exp
        (∑ j : Fin n,
          A * ((if s j then normalizedRealPhase T j else 0 : ℝ) : ℂ)) := by
      exact (Complex.exp_sum Finset.univ _).symm
    _ = Complex.exp
        (A *
          (MainTheory.RealGate.angle (normalizedRealPhase T) s : ℂ)) := by
      congr 1
      simp only [MainTheory.RealGate.angle]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      cases s j <;> simp

/-- Equality of the normalized finite and real gates on the full physical
state space. -/
theorem normalizedGate_eq_realGate
    {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    Gate.gate G.zeta (normalizedFiniteAngle G T) =
      MainTheory.RealGate.realGate (normalizedRealPhase T) := by
  funext psi s
  rw [Gate.gate, MainTheory.RealGate.realGate,
    normalizedDiag_eq_realPhase]

/-- The normalized left state is fixed by the exact real representative. -/
theorem normalizedRealPhase_leftEigen
    {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    MainTheory.RealGate.realGate (normalizedRealPhase T)
        (normalizedState T 0) =
      normalizedState T 0 := by
  calc
    MainTheory.RealGate.realGate (normalizedRealPhase T)
        (normalizedState T 0) =
        Gate.gate G.zeta (normalizedFiniteAngle G T)
          (normalizedState T 0) :=
      congrFun (normalizedGate_eq_realGate T).symm
        (normalizedState T 0)
    _ = (fun s ↦ (1 : ℂ) * normalizedState T 0 s) := by
      simpa [normalizedState, normalizedFiniteAngle] using
        T.normalizedLeftEigen
    _ = normalizedState T 0 := by
      simp

/-- The normalized right state has its stored nontrivial finite eigenvalue
under the same real representative. -/
theorem normalizedRealPhase_rightEigen
    {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    MainTheory.RealGate.realGate (normalizedRealPhase T)
        (normalizedState T 1) =
      fun s ↦ Cyclic.chi G.zeta
          (((q / T.logicalOrder : ℕ) : ZMod q)) *
        normalizedState T 1 s := by
  calc
    MainTheory.RealGate.realGate (normalizedRealPhase T)
        (normalizedState T 1) =
        Gate.gate G.zeta (normalizedFiniteAngle G T)
          (normalizedState T 1) :=
      congrFun (normalizedGate_eq_realGate T).symm
        (normalizedState T 1)
    _ = fun s ↦ Cyclic.chi G.zeta
          (((q / T.logicalOrder : ℕ) : ZMod q)) *
        normalizedState T 1 s := by
      simpa [normalizedState, normalizedFiniteAngle] using
        T.normalizedRightEigen

/-- There is now no semantic premise left in the fresh sparse construction
once a genuine finite generator resolution has reached its proved normalized
two-fibre certificate. -/
def automaticFreshSparsePhase
    {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    FreshSparsePhase
      (normalizedState T 0) (normalizedState T 1)
      (normalizedRealPhase T) :=
  freshSparsePhase T (normalizedRealPhase T)
    (normalizedRealPhase_leftEigen T)

end

end MainTheory.D3NormalizedFiniteToReal
