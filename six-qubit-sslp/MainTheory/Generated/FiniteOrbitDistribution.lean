import MainTheory.Generated.FiniteOrbitBase

/-!
# Exact logical-order distributions in the 215-to-66 orbit directory

The two vectors displayed in `main.tex` are checked here directly from the
kernel-facing literal inputs and orbit representatives.  No external manifest
or headline count is consulted.
-/

namespace MainTheory.Generated.FiniteOrbitDistribution

open MainTheory.FiniteOrbitPipeline

/-!
The table in `main.tex` is grouped by the *targeted logical order* `m`, not
by the controlled lift order `q`.  These labels differ precisely in the rows
where a lift of order 4 or 6 realizes logical order 2 or 3.  Counting `.q`
therefore checks a different statement and is a false-green hazard.

The 215-row reduction is split along the generated source's contiguous
logical-order blocks, with every computational slice containing at most
fifteen rows.  This keeps ordinary kernel `decide` shallow without replacing
it by `native_decide` or increasing the global recursion limit.  Every slice
still reads the literal generated `inputAt`; no copied order manifest is
trusted.
-/

private def countAtM {k : Nat} (mAt : Fin k → Nat) (m : Nat) : Nat :=
  (Finset.univ.filter (fun i => mAt i = m)).card

private def inputSlice (offset size : Nat) (h : offset + size ≤ 215) :
    Fin size → MainTheory.FinitePipeline.FiberPair :=
  fun i => MainTheory.Generated.FiniteOrbitBase.inputAt
    ⟨offset + i.1, by omega⟩

/-! The slices follow the contiguous `m`-blocks in the generated source and
are at most 15 rows long.  Their endpoint arithmetic is part of each type. -/

private def inputM2a := inputSlice 0 4 (by omega)
private def inputM3a := inputSlice 4 15 (by omega)
private def inputM2b := inputSlice 19 13 (by omega)
private def inputM2c := inputSlice 32 13 (by omega)
private def inputM2d := inputSlice 45 13 (by omega)
private def inputM4a := inputSlice 58 12 (by omega)
private def inputM4b := inputSlice 70 11 (by omega)
private def inputM5a := inputSlice 81 15 (by omega)
private def inputM5b := inputSlice 96 15 (by omega)
private def inputM2e := inputSlice 111 15 (by omega)
private def inputM2f := inputSlice 126 15 (by omega)
private def inputM3b := inputSlice 141 11 (by omega)
private def inputM3c := inputSlice 152 10 (by omega)
private def inputM6 := inputSlice 162 13 (by omega)
private def inputM7a := inputSlice 175 9 (by omega)
private def inputM7b := inputSlice 184 9 (by omega)
private def inputM4c := inputSlice 193 8 (by omega)
private def inputM8 := inputSlice 201 9 (by omega)
private def inputM9 := inputSlice 210 5 (by omega)

@[simp] private theorem inputM2a_order : ∀ i, (inputM2a i).m = 2 := by decide
@[simp] private theorem inputM3a_order : ∀ i, (inputM3a i).m = 3 := by decide
@[simp] private theorem inputM2b_order : ∀ i, (inputM2b i).m = 2 := by decide
@[simp] private theorem inputM2c_order : ∀ i, (inputM2c i).m = 2 := by decide
@[simp] private theorem inputM2d_order : ∀ i, (inputM2d i).m = 2 := by decide
@[simp] private theorem inputM4a_order : ∀ i, (inputM4a i).m = 4 := by decide
@[simp] private theorem inputM4b_order : ∀ i, (inputM4b i).m = 4 := by decide
@[simp] private theorem inputM5a_order : ∀ i, (inputM5a i).m = 5 := by decide
@[simp] private theorem inputM5b_order : ∀ i, (inputM5b i).m = 5 := by decide
@[simp] private theorem inputM2e_order : ∀ i, (inputM2e i).m = 2 := by decide
@[simp] private theorem inputM2f_order : ∀ i, (inputM2f i).m = 2 := by decide
@[simp] private theorem inputM3b_order : ∀ i, (inputM3b i).m = 3 := by decide
@[simp] private theorem inputM3c_order : ∀ i, (inputM3c i).m = 3 := by decide
@[simp] private theorem inputM6_order : ∀ i, (inputM6 i).m = 6 := by decide
@[simp] private theorem inputM7a_order : ∀ i, (inputM7a i).m = 7 := by decide
@[simp] private theorem inputM7b_order : ∀ i, (inputM7b i).m = 7 := by decide
@[simp] private theorem inputM4c_order : ∀ i, (inputM4c i).m = 4 := by decide
@[simp] private theorem inputM8_order : ∀ i, (inputM8 i).m = 8 := by decide
@[simp] private theorem inputM9_order : ∀ i, (inputM9 i).m = 9 := by decide

/-- Number of labelled, rank-compatible input pairs with logical order `m`. -/
def labeledPairCountAtM (m : Nat) : Nat :=
  countAtM (fun i => (inputM2a i).m) m +
  countAtM (fun i => (inputM3a i).m) m +
  countAtM (fun i => (inputM2b i).m) m +
  countAtM (fun i => (inputM2c i).m) m +
  countAtM (fun i => (inputM2d i).m) m +
  countAtM (fun i => (inputM4a i).m) m +
  countAtM (fun i => (inputM4b i).m) m +
  countAtM (fun i => (inputM5a i).m) m +
  countAtM (fun i => (inputM5b i).m) m +
  countAtM (fun i => (inputM2e i).m) m +
  countAtM (fun i => (inputM2f i).m) m +
  countAtM (fun i => (inputM3b i).m) m +
  countAtM (fun i => (inputM3c i).m) m +
  countAtM (fun i => (inputM6 i).m) m +
  countAtM (fun i => (inputM7a i).m) m +
  countAtM (fun i => (inputM7b i).m) m +
  countAtM (fun i => (inputM4c i).m) m +
  countAtM (fun i => (inputM8 i).m) m +
  countAtM (fun i => (inputM9 i).m) m

private def keyBlock0 (i : Fin 33) :=
  MainTheory.Generated.FiniteOrbitBase.keyAt
    ⟨i.1, by omega⟩

private def keyBlock1 (i : Fin 33) :=
  MainTheory.Generated.FiniteOrbitBase.keyAt
    ⟨33 + i.1, by omega⟩

/-- Number of inequivalent orbit keys with logical order `m`. -/
def orbitCountAtM (m : Nat) : Nat :=
  countAtM (fun i => (keyBlock0 i).m) m +
  countAtM (fun i => (keyBlock1 i).m) m

/-! Each bucket is reduced separately.  The final headline conjunction below
contains no further table computation; it merely packages these eight small
kernel proofs. -/

theorem labeledPairCountAtM_two : labeledPairCountAtM 2 = 73 := by
  simp [labeledPairCountAtM, countAtM]

theorem labeledPairCountAtM_three : labeledPairCountAtM 3 = 36 := by
  simp [labeledPairCountAtM, countAtM]

theorem labeledPairCountAtM_four : labeledPairCountAtM 4 = 31 := by
  simp [labeledPairCountAtM, countAtM]

theorem labeledPairCountAtM_five : labeledPairCountAtM 5 = 30 := by
  simp [labeledPairCountAtM, countAtM]

theorem labeledPairCountAtM_six : labeledPairCountAtM 6 = 13 := by
  simp [labeledPairCountAtM, countAtM]

theorem labeledPairCountAtM_seven : labeledPairCountAtM 7 = 18 := by
  simp [labeledPairCountAtM, countAtM]

theorem labeledPairCountAtM_eight : labeledPairCountAtM 8 = 9 := by
  simp [labeledPairCountAtM, countAtM]

theorem labeledPairCountAtM_nine : labeledPairCountAtM 9 = 5 := by
  simp [labeledPairCountAtM, countAtM]

/-- The 215 labelled pairs have the logical-order distribution stated in
`main.tex`: `(73,36,31,30,13,18,9,5)` for `m=2,...,9`. -/
theorem labeled_pair_order_distribution :
    labeledPairCountAtM 2 = 73 ∧
    labeledPairCountAtM 3 = 36 ∧
    labeledPairCountAtM 4 = 31 ∧
    labeledPairCountAtM 5 = 30 ∧
    labeledPairCountAtM 6 = 13 ∧
    labeledPairCountAtM 7 = 18 ∧
    labeledPairCountAtM 8 = 9 ∧
    labeledPairCountAtM 9 = 5 :=
  ⟨labeledPairCountAtM_two, labeledPairCountAtM_three,
    labeledPairCountAtM_four, labeledPairCountAtM_five,
    labeledPairCountAtM_six, labeledPairCountAtM_seven,
    labeledPairCountAtM_eight, labeledPairCountAtM_nine⟩

theorem orbitCountAtM_two : orbitCountAtM 2 = 25 := by decide
theorem orbitCountAtM_three : orbitCountAtM 3 = 11 := by decide
theorem orbitCountAtM_four : orbitCountAtM 4 = 10 := by decide
theorem orbitCountAtM_five : orbitCountAtM 5 = 8 := by decide
theorem orbitCountAtM_six : orbitCountAtM 6 = 4 := by decide
theorem orbitCountAtM_seven : orbitCountAtM 7 = 5 := by decide
theorem orbitCountAtM_eight : orbitCountAtM 8 = 2 := by decide
theorem orbitCountAtM_nine : orbitCountAtM 9 = 1 := by decide

/-- The 66 inequivalent labelled orbits have the logical-order distribution
stated in `main.tex`: `(25,11,10,8,4,5,2,1)` for `m=2,...,9`. -/
theorem orbit_order_distribution :
    orbitCountAtM 2 = 25 ∧
    orbitCountAtM 3 = 11 ∧
    orbitCountAtM 4 = 10 ∧
    orbitCountAtM 5 = 8 ∧
    orbitCountAtM 6 = 4 ∧
    orbitCountAtM 7 = 5 ∧
    orbitCountAtM 8 = 2 ∧
    orbitCountAtM 9 = 1 :=
  ⟨orbitCountAtM_two, orbitCountAtM_three, orbitCountAtM_four,
    orbitCountAtM_five, orbitCountAtM_six, orbitCountAtM_seven,
    orbitCountAtM_eight, orbitCountAtM_nine⟩

end MainTheory.Generated.FiniteOrbitDistribution
