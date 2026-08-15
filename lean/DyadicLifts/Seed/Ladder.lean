import DyadicLifts.Seed.Checks
import DyadicLifts.DistanceTheorem
import DyadicLifts.LogicalGroup

/-!
# The seed of the dyadic Bell ladder, checked in the kernel alone

`Examples.D3.BD16Ladder` of the search release instantiates the two-anchor ladder theorem on the
`((7,2,3))` code `BD16v1` of arXiv:2504.20847 and closes its finite checks with
`native_decide`, which adds `Lean.ofReduceBool` and `Lean.trustCompiler` to the
axiom set.  This file proves the same statements with no compiled evaluation.
The amplitudes are carried as elements of `ℤ[√2,√3,√5,i]` scaled by a single
rational factor (`DyadicLifts.Seed.Defs`), every finite check is decided by
the kernel on the integer side (`DyadicLifts.Seed.Checks`), and the results
are transported back by `SS.ZSeedKL`.

The seed is

```
4·|0_L⟩ = |0000000⟩ + √3|0111100⟩ + √3|1001110⟩ + √2|1010101⟩
        + √2|1011001⟩ + |1110010⟩ + 2i|0100011⟩,
```

with angle vector `a = (1,2,2,2,2,3,3)` and modulus `m = 8`, and
`|1_L⟩ = X^{⊗7}|0_L⟩`.  The scale is `q = 1/4` at the seed and `q = 1/8` after
the lift, which appends a Bell pair carrying a factor `1/√2 = (√2)/2`.

`exists_distance3_family` below has the same statement as the one in
`BD16Ladder` and depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

open DyadicLifts SS SS.ZSqrt235i

namespace BD16Kernel

/-! ## The finite checks, decided by the kernel over the integers -/

/-- Both codewords are supported on the residue class the ladder needs. -/
theorem hsupp0 : SuppIn ψ0 (S0 a0 8) := by
  have hZ : ∀ s, ψ0Z s ≠ zero → Asum a0 s % 8 = 0 := by decide +kernel
  intro s hs; rw [mem_S0]; exact hZ s (ne_zero_of_ψ0 hs)

theorem hsupp1 : SuppIn ψ1 (S1 a0 8) := by
  have hZ : ∀ s, ψ1Z s ≠ zero → Asum a0 s % 8 = (8 - 1) % 8 := by decide +kernel
  intro s hs; rw [mem_S1]; exact hZ s (ne_zero_of_ψ1 hs)

/-- The integer diagonal is `4² = 16`, so the codeword is a unit vector. -/
theorem hn0 : ⟪ψ0, ψ0⟫ = 1 := by
  have hZ : melZ S7Z ψ0Z (Istr 7) ψ0Z = intZ 16 := by decide +kernel
  have hK : melK S7Z ψ0K (Istr 7) ψ0K = 1 := by
    rw [ψ0K_def, melK_of_melZ, hZ, toQ_intZ, QSqrt235i.smul_ofRat]
    rw [show (q0 * q0 * ((16 : Int) : ℚ)) = 1 by norm_num [q0]]
    exact QSqrt235i.ofRat_one
  calc ⟪ψ0, ψ0⟫ = mel ψ0 (Istr 7) ψ0 := (mel_Istr ψ0 ψ0).symm
    _ = ιK (melK S7Z ψ0K (Istr 7) ψ0K) := (ιK_melK (Istr 7) h0_off_S7 h0_off_S7).symm
    _ = ιK 1 := by rw [hK]
    _ = 1 := ιK_one

theorem hn1 : ⟪ψ1, ψ1⟫ = 1 := by
  have hZ : melZ S7Z ψ1Z (Istr 7) ψ1Z = intZ 16 := by decide +kernel
  have hK : melK S7Z ψ1K (Istr 7) ψ1K = 1 := by
    rw [ψ1K_def, melK_of_melZ, hZ, toQ_intZ, QSqrt235i.smul_ofRat]
    rw [show (q0 * q0 * ((16 : Int) : ℚ)) = 1 by norm_num [q0]]
    exact QSqrt235i.ofRat_one
  calc ⟪ψ1, ψ1⟫ = mel ψ1 (Istr 7) ψ1 := (mel_Istr ψ1 ψ1).symm
    _ = ιK (melK S7Z ψ1K (Istr 7) ψ1K) := (ιK_melK (Istr 7) h1_off_S7 h1_off_S7).symm
    _ = ιK 1 := by rw [hK]
    _ = 1 := ιK_one

theorem hss : StrongSeed 7 8 a0 := ⟨by decide, by decide, by decide⟩

lemma ιK_ofRat (q : ℚ) : ιK (QSqrt235i.ofRat q) = (q : ℂ) := by
  show ιC23 (QSqrt23i.ofRat q) + ιC23 0 * s5 = (q : ℂ)
  rw [ιC23_zero, zero_mul, add_zero]
  simp only [ιC23, QSqrt23i.ofRat]; push_cast; ring

/-- The two anchor strings carry amplitude `1/4`, and nothing else in their
subset-sum sector carries any amplitude at all. -/
noncomputable def hanchor : AnchorHyp 8 a0 ψ0 ψ1 where
  α₀ := 1 / 4
  β₀ := 1 / 4
  hα := by norm_num
  hβ := by norm_num
  hcoeff0 := by
    have hZ : ψ0Z (zeros 7) = one := by decide +kernel
    show ιK (ψ0K (zeros 7)) = _
    rw [ψ0K_def]
    simp only []
    rw [hZ, toQ_one, QSqrt235i.smul_one_ofRat, ιK_ofRat]
    norm_num [q0]
  hcoeff1 := by
    have hZ : ψ1Z (ones 7) = one := by decide +kernel
    show ιK (ψ1K (ones 7)) = _
    rw [ψ1K_def]
    simp only []
    rw [hZ, toQ_one, QSqrt235i.smul_one_ofRat, ιK_ofRat]
    norm_num [q0]
  hunique0 := by
    have hZ : ∀ s, ψ0Z s ≠ zero → Asum a0 s = 0 → s = zeros 7 := by decide +kernel
    intro s hs; exact hZ s (ne_zero_of_ψ0 hs)
  hunique1 := by
    have hZ : ∀ s, ψ1Z s ≠ zero → Asum a0 s = 2 * 8 - 1 → s = ones 7 := by decide +kernel
    intro s hs; exact hZ s (ne_zero_of_ψ1 hs)

/-! ## The two Knill--Laflamme checks -/

/-- Rung 0: the seed itself.  The `211` Paulis of weight at most two, in the
three-case form of `KLmatK_of_sites`, decided by the kernel on the integer
mirror. -/
theorem hKL0 : KLmat (psr 8 a0 ψ0 false 0) (psr 8 a0 ψ1 true 0) := by
  have hK : KLmatK S7Z ψ0K ψ1K :=
    KLmatK_of_sites q0 k7_id k7_one k7_two
  exact KLmat_of_KLmatK h0_off_S7 h1_off_S7 hK

/-- Rung 1: the first Bell lift.  `352` Paulis on nine qubits. -/
theorem hKL1 : KLmat (psr 8 a0 ψ0 false 1) (psr 8 a0 ψ1 true 1) := by
  have e0 : psr 8 a0 ψ0 false 1 = fun w => ιK (liftVecK 8 a0 false ψ0K w) := by
    show liftVec 8 a0 false ψ0 = _
    funext w
    simp only [ψ0, liftVec, liftVecK, ιK_mul, ιK_bflagK]
  have e1 : psr 8 a0 ψ1 true 1 = fun w => ιK (liftVecK 8 a0 true ψ1K w) := by
    show liftVec 8 a0 true ψ1 = _
    funext w
    simp only [ψ1, liftVec, liftVecK, ιK_mul, ιK_bflagK]
  rw [e0, e1]
  have hK : KLmatK S9Z (liftVecK 8 a0 false ψ0K) (liftVecK 8 a0 true ψ1K) := by
    rw [liftK_eq0, liftK_eq1]
    exact KLmatK_of_sites q1 k9_id k9_one k9_two
  exact KLmat_of_KLmatK h0_off_S9 h1_off_S9 hK

/-- **Unconditional distance-3 family, kernel-checked.**  Every rung of the
dyadic Bell ladder built from the `BD16v1` seed satisfies the full distance-3
Knill--Laflamme conditions.  Rung `r` is a `((7+2r, 2, 3))` code -- nonadditive,
so the doubled-parenthesis notation, not `[[.,.,.]]` -- carrying a
transversal diagonal gate of order `2^{3+r}`. -/
theorem exists_distance3_family (r : ℕ) :
    KL (psr 8 a0 ψ0 false r) (psr 8 a0 ψ1 true r) :=
  two_anchor_ladder hss hanchor hn0 hn1 hsupp0 hsupp1 hKL0 hKL1 r

/-! ## The transversal gate carried by each rung

Distance is one half of the corollary; the other half is the gate.  The two
statements below are instances of the general theorems, whose hypotheses are
already discharged above.  The seed is self-complementary by construction ---
`ψ1Z` is defined as `ψ0Z ∘ complement` --- so `SelfComp` holds definitionally. -/

theorem hsc : SelfComp ψ0 ψ1 := fun _ => rfl

/-- **The diagonal gate.**  At rung `r` the tensor-product diagonal
`Udiag` of modulus `m_r = 2^{r}·8` fixes the logical zero and multiplies the
logical one by `exp(-2πi/m_r)`: the induced logical gate has projective order
`m_r = 2^{3+r}`. -/
theorem seed_rung_diagonal (r : ℕ) :
    Udiag (mr 8 r) (ar 8 a0 r) (psr 8 a0 ψ0 false r) = psr 8 a0 ψ0 false r ∧
      Udiag (mr 8 r) (ar 8 a0 r) (psr 8 a0 ψ1 true r)
        = Complex.exp (-(2 * Real.pi * Complex.I / ((mr 8 r : ℕ) : ℂ)))
          • psr 8 a0 ψ1 true r :=
  rung_diagonal hss hsupp0 hsupp1 r

open Matrix in
/-- **The binary-dihedral transversal group.**  At rung `r` the logical action
generated by the diagonal and by `X^{⊗n_r}` is the binary dihedral group
`BD_{2·m_r} = BD_{2^{4+r}}`: the generators satisfy its presentation and act on
the logical space as stated. -/
theorem seed_rung_binary_dihedral (r : ℕ) :
    Rm (mr 8 r) ^ (2 * mr 8 r) = 1 ∧
      Jmat * Jmat = -1 ∧
      Rm (mr 8 r) ^ (mr 8 r) = -1 ∧
      Jmat * Rm (mr 8 r) * Jmat⁻¹ = Rminv (mr 8 r) ∧
      (∀ c, logicalState 8 a0 ψ0 ψ1 r (Rm (mr 8 r) *ᵥ c)
        = Complex.exp ((Real.pi : ℂ) * Complex.I / (mr 8 r))
          • Udiag (mr 8 r) (ar 8 a0 r) (logicalState 8 a0 ψ0 ψ1 r c)) ∧
      (∀ c, logicalState 8 a0 ψ0 ψ1 r (Jmat *ᵥ c)
        = Complex.I • papply (Xstring (nr 7 r)) (logicalState 8 a0 ψ0 ψ1 r c)) :=
  rung_binary_dihedral hss hsc hsupp0 hsupp1 r

end BD16Kernel

/-! ## Axiom audit

The whole chain --- the ladder theorem, the seed's hypotheses, and the two
Knill--Laflamme checks --- rests on the three standard axioms of Mathlib and
nothing else.  In particular neither `Lean.ofReduceBool` nor
`Lean.trustCompiler` appears, so no compiled evaluation is trusted. -/

/-- info: 'BD16Kernel.hKL0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hKL0

/-- info: 'BD16Kernel.hKL1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hKL1

/-- info: 'BD16Kernel.exists_distance3_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.exists_distance3_family

/-- info: 'BD16Kernel.seed_rung_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.seed_rung_diagonal

/-- info: 'BD16Kernel.seed_rung_binary_dihedral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.seed_rung_binary_dihedral
