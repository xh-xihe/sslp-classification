import DyadicLifts.Ladder
import DyadicLifts.CyclicOrder
import DyadicLifts.SelfComplement

/-!
# The logical action of the transversal operators on a rung code

This module closes the binary-dihedral clause of the two-anchor theorem
(`dyadic_lifts.tex`, Theorem (two-anchor); `dyadic_theorem_lean.tex`,
`lem:bd-relations`, `cor:bd-growth-one-step`) by connecting the **abstract** `2×2`
matrices `Dm`, `Rm`, `Jmat` of `CyclicOrder` to the **actual logical action** of the
physical transversal operators on the rung-`r` code space `span{|0^{(r)}⟩, |1^{(r)}⟩}`.

* `logicalState`        — the encoding `c ↦ c₀|0^{(r)}⟩ + c₁|1^{(r)}⟩`.
* `logicalState_Udiag`  — the transversal diagonal `U_{m_r}(a^{(r)})` acts on the code
                          as the matrix `D_{m_r}`.
* `logicalState_Xstring`— the transversal bit flip `X^{⊗n_r}` acts as the logical swap.
* `logicalState_Rm`, `logicalState_Jmat` — the binary-dihedral generators `R_{m_r}`
                          and `J = iX` are realized (up to a global phase) by these
                          physical operators.
* `logical_diagonal_order_doubles` — the projective order of the logical diagonal is
                          exactly `m_r = 2^r m_0`, and `m_{r+1} = 2 m_r`.
* `rung_binary_dihedral` — the capstone: the realized generators satisfy the
                          binary-dihedral relations.
-/

open scoped BigOperators
open ComplexConjugate Matrix

namespace DyadicLifts

open SS

variable {n : ℕ}

/-! ## Linearity of the diagonal and involutivity of the bit flip -/

@[simp] lemma Udiag_add (m : ℕ) (a : Fin n → ℕ) (ψ φ : Hil n) :
    Udiag m a (ψ + φ) = Udiag m a ψ + Udiag m a φ := by
  funext s; simp only [Udiag, Pi.add_apply]; ring

@[simp] lemma Udiag_smul (m : ℕ) (a : Fin n → ℕ) (c : ℂ) (ψ : Hil n) :
    Udiag m a (c • ψ) = c • Udiag m a ψ := by
  funext s; simp only [Udiag, Pi.smul_apply, smul_eq_mul]; ring

/-- `X^{⊗n}` is an involution: `X^{⊗n} (X^{⊗n} ψ) = ψ`. -/
lemma papply_Xstring_involutive (ψ : Hil n) :
    papply (Xstring n) (papply (Xstring n) ψ) = ψ := by
  simp only [papply_Xstring, complement_complement]

/-- The logical swap matrix `[[0,1],[1,0]]` (the logical Pauli `X`). -/
def Sw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

@[simp] lemma Sw_mulVec_zero (c : Fin 2 → ℂ) : (Sw *ᵥ c) 0 = c 1 := by
  simp [Sw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] lemma Sw_mulVec_one (c : Fin 2 → ℂ) : (Sw *ᵥ c) 1 = c 0 := by
  simp [Sw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The determinant-one generator is the projective diagonal times a global phase:
`R_m = e^{πi/m} · D_m`. -/
lemma Rm_eq_smul_Dm (m : ℕ) : Rm m = Complex.exp ((Real.pi : ℂ) * Complex.I / m) • Dm m := by
  have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I / m)
        * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / m))
      = Complex.exp (-((Real.pi : ℂ) * Complex.I / m)) := by
    rw [← Complex.exp_add]; congr 1; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rm, Dm, Matrix.diagonal_apply, Matrix.smul_apply, hexp]

/-- The binary-dihedral generator `J = iX` is `i` times the logical swap. -/
lemma Jmat_eq_smul_Sw : Jmat = Complex.I • Sw := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jmat, Sw, Matrix.smul_apply]

/-- **Order doubling (`cor:diagonal-order-doubles`).** The logical diagonal `D_{m_r}`
has projective order exactly `m_r = 2^r m_0`, and `m_{r+1} = 2 m_r`: each dyadic lift
doubles the order of the transversal diagonal. -/
theorem logical_diagonal_order_doubles {m0 : ℕ} (hm0 : 0 < m0) (r : ℕ) :
    (∀ t : ℕ, (∃ k : ℂ, Dm (mr m0 r) ^ t = k • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ↔ mr m0 r ∣ t)
      ∧ mr m0 r = 2 ^ r * m0 ∧ mr m0 (r + 1) = 2 * mr m0 r := by
  have hmr : 0 < mr m0 r := by rw [mr_eq]; exact Nat.mul_pos (pow_pos (by norm_num) r) hm0
  exact ⟨fun t => Dm_pow_smul_one_iff hmr t, mr_eq m0 r, rfl⟩

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ₀ ψ₁ : Hil n0}

/-- Encode a logical coordinate vector `c : Fin 2 → ℂ` into the rung-`r` code space:
`logicalState c = c₀ |0^{(r)}⟩ + c₁ |1^{(r)}⟩`. -/
noncomputable def logicalState (m0 : ℕ) (a0 : Fin n0 → ℕ) (ψ₀ ψ₁ : Hil n0) (r : ℕ)
    (c : Fin 2 → ℂ) : Hil (nr n0 r) :=
  c 0 • psr m0 a0 ψ₀ false r + c 1 • psr m0 a0 ψ₁ true r

/-- The encoding is ℂ-linear in the coordinate vector. -/
lemma logicalState_smul (r : ℕ) (k : ℂ) (c : Fin 2 → ℂ) :
    logicalState m0 a0 ψ₀ ψ₁ r (k • c) = k • logicalState m0 a0 ψ₀ ψ₁ r c := by
  simp only [logicalState, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]

/-- **The transversal diagonal acts on the rung code as `D_{m_r}`.** -/
theorem logicalState_Udiag (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ₀ (S0 a0 m0)) (hsupp1 : SuppIn ψ₁ (S1 a0 m0)) (r : ℕ) (c : Fin 2 → ℂ) :
    Udiag (mr m0 r) (ar m0 a0 r) (logicalState m0 a0 ψ₀ ψ₁ r c)
      = logicalState m0 a0 ψ₀ ψ₁ r (Dm (mr m0 r) *ᵥ c) := by
  unfold logicalState
  rw [Udiag_add, Udiag_smul, Udiag_smul, iterated_diagonal_S0 hss hsupp0 r,
    iterated_diagonal_S1 hss hsupp1 r]
  have h0 : (Dm (mr m0 r) *ᵥ c) 0 = c 0 := by
    rw [Dm, Matrix.mulVec_diagonal]; simp
  have h1 : (Dm (mr m0 r) *ᵥ c) 1
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / (mr m0 r))) * c 1 := by
    rw [Dm, Matrix.mulVec_diagonal]; simp
  rw [h0, h1, smul_smul, mul_comm]

/-- **The transversal bit flip `X^{⊗n_r}` acts on the rung code as the logical swap.** -/
theorem logicalState_Xstring (hss : StrongSeed n0 m0 a0) (hsc : SelfComp ψ₀ ψ₁)
    (r : ℕ) (c : Fin 2 → ℂ) :
    papply (Xstring (nr n0 r)) (logicalState m0 a0 ψ₀ ψ₁ r c)
      = logicalState m0 a0 ψ₀ ψ₁ r (Sw *ᵥ c) := by
  have hX0 : papply (Xstring (nr n0 r)) (psr m0 a0 ψ₀ false r) = psr m0 a0 ψ₁ true r :=
    (selfComp_iff _ _ |>.mp (psr_selfComp hss hsc r)).symm
  have hX1 : papply (Xstring (nr n0 r)) (psr m0 a0 ψ₁ true r) = psr m0 a0 ψ₀ false r := by
    rw [← hX0, papply_Xstring_involutive]
  unfold logicalState
  rw [papply_add, papply_smul, papply_smul, hX0, hX1, Sw_mulVec_zero, Sw_mulVec_one, add_comm]

/-- **The binary-dihedral diagonal generator `R_{m_r}` is realized** (up to the global
phase `e^{πi/m_r}`) by the physical transversal diagonal `U_{m_r}(a^{(r)})` on the code. -/
theorem logicalState_Rm (hss : StrongSeed n0 m0 a0)
    (hsupp0 : SuppIn ψ₀ (S0 a0 m0)) (hsupp1 : SuppIn ψ₁ (S1 a0 m0)) (r : ℕ) (c : Fin 2 → ℂ) :
    logicalState m0 a0 ψ₀ ψ₁ r (Rm (mr m0 r) *ᵥ c)
      = Complex.exp ((Real.pi : ℂ) * Complex.I / (mr m0 r))
        • Udiag (mr m0 r) (ar m0 a0 r) (logicalState m0 a0 ψ₀ ψ₁ r c) := by
  rw [Rm_eq_smul_Dm, Matrix.smul_mulVec_assoc, logicalState_smul,
    ← logicalState_Udiag hss hsupp0 hsupp1 r c]

/-- **The binary-dihedral flip generator `J = iX` is realized** (up to the global phase
`i`) by the physical transversal bit flip `X^{⊗n_r}` on the code. -/
theorem logicalState_Jmat (hss : StrongSeed n0 m0 a0) (hsc : SelfComp ψ₀ ψ₁)
    (r : ℕ) (c : Fin 2 → ℂ) :
    logicalState m0 a0 ψ₀ ψ₁ r (Jmat *ᵥ c)
      = Complex.I • papply (Xstring (nr n0 r)) (logicalState m0 a0 ψ₀ ψ₁ r c) := by
  rw [Jmat_eq_smul_Sw, Matrix.smul_mulVec_assoc, logicalState_smul,
    ← logicalState_Xstring hss hsc r]

/-- **Capstone: every rung admits the binary-dihedral transversal group `BD_{2m_r}`.**
The generators `R = R_{m_r}` and `J = iX` satisfy the binary-dihedral relations
(`R^{2m_r}=I`, `J²=R^{m_r}=-I`, `J R J⁻¹ = R⁻¹`), and each is realized on the rung code
(up to a global phase) by a physical transversal operator: `R` by the diagonal
`U_{m_r}(a^{(r)})`, and `J` by the bit flip `X^{⊗n_r}`. -/
theorem rung_binary_dihedral (hss : StrongSeed n0 m0 a0) (hsc : SelfComp ψ₀ ψ₁)
    (hsupp0 : SuppIn ψ₀ (S0 a0 m0)) (hsupp1 : SuppIn ψ₁ (S1 a0 m0)) (r : ℕ) :
    Rm (mr m0 r) ^ (2 * mr m0 r) = 1 ∧
      Jmat * Jmat = -1 ∧
      Rm (mr m0 r) ^ (mr m0 r) = -1 ∧
      Jmat * Rm (mr m0 r) * Jmat⁻¹ = Rminv (mr m0 r) ∧
      (∀ c, logicalState m0 a0 ψ₀ ψ₁ r (Rm (mr m0 r) *ᵥ c)
        = Complex.exp ((Real.pi : ℂ) * Complex.I / (mr m0 r))
          • Udiag (mr m0 r) (ar m0 a0 r) (logicalState m0 a0 ψ₀ ψ₁ r c)) ∧
      (∀ c, logicalState m0 a0 ψ₀ ψ₁ r (Jmat *ᵥ c)
        = Complex.I • papply (Xstring (nr n0 r)) (logicalState m0 a0 ψ₀ ψ₁ r c)) := by
  have hmr : mr m0 r ≠ 0 := by
    rw [mr_eq]; exact Nat.mul_ne_zero (pow_ne_zero r (by norm_num)) (by have := hss.hm; omega)
  exact ⟨Rm_pow_two_m hmr, Jmat_sq, Rm_pow_m hmr, Jmat_conj_Rm,
    fun c => logicalState_Rm hss hsupp0 hsupp1 r c,
    fun c => logicalState_Jmat hss hsc r c⟩

end Seed

end DyadicLifts
