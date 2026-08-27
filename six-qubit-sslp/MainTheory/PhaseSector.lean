import Mathlib
import SS.Basic
import SS.DiagonalAction
import MainTheory.Gate

/-!
# Phase sectors

Lemma 2.3 of `main.tex` says that if a diagonal gate preserves a code, then each
logical eigenspace is supported inside a single *phase sector*: a set of basis
strings on which the gate's eigenvalue is constant.  In the SSLP setting that
sector is exactly a residue fiber of the angle vector.

The paper states the lemma for an arbitrary logical dimension and derives the
eigenspace decomposition from the spectral theorem for a unitary operator.
Mathlib has no such theorem -- only the Hermitian case -- so that route is not
available.  It is also not needed for what the paper actually uses the lemma
for.  Theorem 2.6, the two-fiber normal form, works with `K = 2` and with the
logical *eigenbasis* already chosen; there the diagonalization is a hypothesis
rather than something to be produced, and no spectral theorem appears.

That is the version formalized here, and it does real work: it *derives* the
support condition that the whole six-qubit development takes as its hypothesis.
Every theorem in `SixQubit/` begins "let `c` be supported in the fiber of
residue `r`".  What justifies assuming that is `weight_eq_of_eigen` below: a
logical word on which the gate acts as a scalar is automatically supported in a
single fiber.  The converse is `SS.Dact_eq_global_of_SS`, already in the
repository, so the two conditions are equivalent.
-/

namespace MainTheory.PhaseSector

open SS MainTheory.Gate

variable {n q : ℕ} [NeZero q]

/-! ## The eigenvalue is the gate's diagonal entry -/

omit [NeZero q] in
/-- If the gate acts on `c` as multiplication by `lam`, then its diagonal entry
equals `lam` at every string `c` is supported on.  This is clause (ii) of
Lemma 2.3, before the residues are read off. -/
theorem diag_eq_of_eigen (zeta : ℂ) (a : Fin n → ZMod q) (c : SS.State n ℂ)
    (lam : ℂ) (h : gate zeta a c = fun s => lam * c s)
    (x : BitString n) (hx : c x ≠ 0) :
    diag zeta a x = lam := by
  have hxv := congrFun h x
  rw [gate] at hxv
  exact mul_right_cancel₀ hx hxv

/-! ## The support lies in one fiber -/

/-- **The fiber condition, derived rather than assumed.**

If a primitive `q`-th root of unity is used and the gate acts on `c` as a
scalar, then the subset-sum residue is constant on the support of `c`.

This is what licenses the standing hypothesis of the six-qubit development.
There a logical word is *assumed* supported in a fiber; here that follows from
the gate acting on it diagonally, which is the actual physical assumption. -/
theorem weight_eq_of_eigen (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (c : SS.State n ℂ) (lam : ℂ)
    (h : gate zeta a c = fun s => lam * c s)
    (x y : BitString n) (hx : c x ≠ 0) (hy : c y ≠ 0) :
    SS.weight a x = SS.weight a y := by
  have hdx : diag zeta a x = lam := diag_eq_of_eigen zeta a c lam h x hx
  have hdy : diag zeta a y = lam := diag_eq_of_eigen zeta a c lam h y hy
  have hpow : zeta ^ (SS.weight a x).val = zeta ^ (SS.weight a y).val := by
    rw [← diag, ← diag, hdx, hdy]
  have := hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow
  exact (ZMod.val_injective q) this

/-- The same fact in the form the repository already uses: the eigenvector
satisfies the subset-sum condition for the residue of any supported string. -/
theorem ssCondition_of_eigen (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (c : SS.State n ℂ) (lam : ℂ)
    (h : gate zeta a c = fun s => lam * c s)
    (x : BitString n) (hx : c x ≠ 0) :
    SS.SSConditionState a (SS.weight a x) c :=
  fun s hs => weight_eq_of_eigen zeta hz a c lam h s x hs hx

/-! ## Distinct eigenvalues give disjoint sectors -/

omit [NeZero q] in
/-- Clause (i) of Lemma 2.3: two logical words with different gate eigenvalues
have disjoint supports, because their fibers differ. -/
theorem disjoint_of_ne (zeta : ℂ) (a : Fin n → ZMod q)
    (c d : SS.State n ℂ) (lc ld : ℂ) (hne : lc ≠ ld)
    (hc : gate zeta a c = fun s => lc * c s)
    (hd : gate zeta a d = fun s => ld * d s)
    (x : BitString n) (hx : c x ≠ 0) : d x = 0 := by
  by_contra hdx
  have h1 : diag zeta a x = lc := diag_eq_of_eigen zeta a c lc hc x hx
  have h2 : diag zeta a x = ld := diag_eq_of_eigen zeta a d ld hd x hdx
  exact hne (h1 ▸ h2)

/-! ## The converse, and the resulting equivalence -/

omit [NeZero q] in
/-- The gate acts as a scalar on anything supported in a single fiber.  This is
`SS.Dact_eq_global_of_SS` transported to `gate`. -/
theorem eigen_of_ssCondition (zeta : ℂ) (a : Fin n → ZMod q)
    (c : SS.State n ℂ) (b : ZMod q) (hSS : SS.SSConditionState a b c) :
    gate zeta a c = fun s => zeta ^ b.val * c s := by
  funext s
  rw [gate, diag]
  by_cases hs : c s = 0
  · simp [hs]
  · rw [hSS s hs]

/-- **Acting as a scalar and being supported in a fiber are the same thing.**

The forward direction is what the six-qubit development needs and had to assume;
the backward direction is what makes the assumption harmless. -/
theorem eigen_iff_ssCondition (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (c : SS.State n ℂ)
    (x : BitString n) (hx : c x ≠ 0) :
    (∃ lam : ℂ, gate zeta a c = fun s => lam * c s)
      ↔ SS.SSConditionState a (SS.weight a x) c := by
  constructor
  · rintro ⟨ lam, h ⟩
    exact ssCondition_of_eigen zeta hz a c lam h x hx
  · intro hSS
    exact ⟨ zeta ^ (SS.weight a x).val, eigen_of_ssCondition zeta a c _ hSS ⟩

/-! ## Non-vacuity

The equivalence is exhibited on a state that actually exists: for any basis
string, the state concentrated there is an eigenvector, so neither side of
`eigen_iff_ssCondition` is empty. -/

omit [NeZero q] in
/-- Every basis string carries an eigenvector of the gate. -/
theorem exists_eigen (zeta : ℂ) (a : Fin n → ZMod q) (x : BitString n) :
    ∃ c : SS.State n ℂ, c x ≠ 0 ∧
      gate zeta a c = fun s => zeta ^ (SS.weight a x).val * c s := by
  classical
  refine ⟨ (fun s => if s = x then 1 else 0), by simp, ?_ ⟩
  refine eigen_of_ssCondition zeta a _ _ (fun s hs => ?_)
  by_cases h : s = x
  · rw [h]
  · simp [h] at hs

/-- So the derived fiber condition is a statement about something. -/
theorem ssCondition_nonvacuous (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (x : BitString n) :
    ∃ c : SS.State n ℂ, c x ≠ 0 ∧ SS.SSConditionState a (SS.weight a x) c := by
  obtain ⟨ c, hcx, hc ⟩ := exists_eigen zeta a x
  exact ⟨ c, hcx, ssCondition_of_eigen zeta hz a c _ hc x hcx ⟩

/-! ## The bridge to the six-qubit hypothesis

Every theorem in `SixQubit/` states its support hypothesis contrapositively, as
`forall s, weight av s <> r -> c s = 0`.  That is the same condition, and the
translation is recorded here so that the claim "this justifies the six-qubit
standing hypothesis" is checkable rather than rhetorical. -/

omit [NeZero q] in
/-- The subset-sum condition, in the contrapositive form the six-qubit modules
use. -/
theorem support_of_ssCondition (a : Fin n → ZMod q) (b : ZMod q)
    (c : SS.State n ℂ) (h : SS.SSConditionState a b c) :
    ∀ s, SS.weight a s ≠ b → c s = 0 := by
  intro s hs
  by_contra hc
  exact hs (h s hc)

/-- **What the six-qubit development assumes, obtained from the physical
hypothesis.**

Given only that the gate acts on the logical word as a scalar, the word is
supported where the six-qubit theorems require it to be. -/
theorem support_of_eigen (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (c : SS.State n ℂ) (lam : ℂ)
    (h : gate zeta a c = fun s => lam * c s)
    (x : BitString n) (hx : c x ≠ 0) :
    ∀ s, SS.weight a s ≠ SS.weight a x → c s = 0 :=
  support_of_ssCondition a _ c (ssCondition_of_eigen zeta hz a c lam h x hx)

end MainTheory.PhaseSector
