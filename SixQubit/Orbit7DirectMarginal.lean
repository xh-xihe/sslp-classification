import SixQubit.Orbit7GaugeRank

/-!
# Orbit 7: direct finite-sum two-qubit marginals

This module closes the semantic boundary left explicit in
`Orbit7GaugeRank`.  It defines the normalized two-state projector marginal on
physical qubits `0` and `s.succ` directly from amplitudes.  The four traced
bits are an environment `SS.BitString 4`; `assemblePair` inserts the two
retained computational-basis values into that environment.  Thus every matrix
entry below is literally the finite partial-trace sum, rather than an alias
for the matrix normal form `pairMarginal`.
-/

namespace SixQubit.Orbit7DirectMarginal

open scoped BigOperators ComplexConjugate
open SixQubit.CodeEquiv
open SixQubit.Orbit7Universal
open SixQubit.Orbit7Gauge

noncomputable section

/-- Insert retained bits `(A,s)` into the four-bit traced environment. -/
def assemblePair (s : Fin 5) (p : Fin 2 × Fin 2)
    (env : SS.BitString 4) : SS.BitString 6 :=
  Fin.cons (finTwoEquiv p.1)
    (Fin.insertNth s (finTwoEquiv p.2) env)

/-- The unnormalized reduced rank-one projector `|psi><psi|` on `(A,s)`,
written as its literal finite environment sum. -/
def directPurePairMarginal (psi : SS.State 6 ℂ) (s : Fin 5) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => ∑ env : SS.BitString 4,
    psi (assemblePair s p env) * star (psi (assemblePair s q env))

/-- The partial trace of `P/2` for a two-vector family `code`.  When `code`
is an orthonormal logical basis this is the normalized code-projector
marginal.  The definition itself is valid for an arbitrary family. -/
def directPairMarginal (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => (1 / 2 : ℂ) * ∑ k : Fin 2,
    directPurePairMarginal (code k) s p q

/-- The two active-bit blocks contributed by the residue-zero logical state
before averaging the two logical projectors. -/
private def uniformCBlocks (c : SS.State 6 ℂ) (s : Fin 5) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.blockDiagonal ![
    (fun i j => U c i j + starA c s i j),
    (fun i j => sumA c i j - starA c s i j)]

/-- The two active-bit blocks contributed by the residue-two logical state
before averaging the two logical projectors. -/
private def uniformDBlocks (d : SS.State 6 ℂ) (s : Fin 5) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.blockDiagonal ![
    (fun i j => sumB d i j - starB d s i j),
    (fun i j => W d i j + starB d s i j)]

private theorem uniform_weight_bxor_abit (x : SS.BitString 6) :
    SS.weight uniformAv (SS.bxor x abit) = SS.weight uniformAv x := by
  decide +revert

private lemma block_zero_of_outside_fiber
    (psi : SS.State 6 ℂ) (r : ZMod 3)
    (hsupp : ∀ x, SS.weight uniformAv x ≠ r → psi x = 0)
    (y : SS.BitString 6) (hy : SS.weight uniformAv y ≠ r) :
    block psi y = 0 := by
  funext i j
  unfold block outer spinor
  rw [hsupp y hy]
  have hy' : SS.weight uniformAv (SS.bxor y abit) ≠ r := by
    rw [uniform_weight_bxor_abit]
    exact hy
  rw [hsupp (SS.bxor y abit) hy']
  fin_cases i <;> fin_cases j <;> simp

private theorem spinor_assemblePair
    (psi : SS.State 6 ℂ) (s : Fin 5) (b : Fin 2)
    (env : SS.BitString 4) (i : Fin 2) :
    spinor psi (assemblePair s (0, b) env) i =
      psi (assemblePair s (i, b) env) := by
  fin_cases i
  · rfl
  · change psi (SS.bxor (assemblePair s (0, b) env) abit) =
      psi (assemblePair s (1, b) env)
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · change xor (finTwoEquiv 0) (abit 0) = finTwoEquiv 1
      norm_num [finTwoEquiv, abit, SixQubit.Realize.bs]
    · have hactive : abit j.succ = false := by decide +revert
      simp [assemblePair, SS.bxor_apply, hactive]

private theorem directPurePairMarginal_diagonal
    (psi : SS.State 6 ℂ) (s : Fin 5) (b i j : Fin 2) :
    directPurePairMarginal psi s (i, b) (j, b) =
      ∑ env : SS.BitString 4,
        block psi (assemblePair s (0, b) env) i j := by
  unfold directPurePairMarginal block outer
  refine Finset.sum_congr rfl (fun env _ => ?_)
  rw [spinor_assemblePair, spinor_assemblePair]

private def environmentBases (s : Fin 5) (b : Fin 2) :
    Finset (SS.BitString 6) :=
  Finset.univ.image (assemblePair s (0, b))

private def fiberEnvironmentBases (r : ZMod 3) (s : Fin 5) (b : Fin 2) :
    Finset (SS.BitString 6) :=
  (environmentBases s b).filter (fun y => SS.weight uniformAv y = r)

private theorem assemblePair_environment_injective (s : Fin 5) (b : Fin 2) :
    Function.Injective (assemblePair s (0, b)) := by
  intro x y hxy
  funext k
  have h := congrFun hxy ((s.succAbove k).succ)
  simpa [assemblePair] using h

private lemma sum_environment_blocks_eq_fiber
    (psi : SS.State 6 ℂ) (r : ZMod 3)
    (hsupp : ∀ x, SS.weight uniformAv x ≠ r → psi x = 0)
    (s : Fin 5) (b i j : Fin 2) :
    (∑ env : SS.BitString 4,
        block psi (assemblePair s (0, b) env) i j) =
      ∑ y ∈ fiberEnvironmentBases r s b, block psi y i j := by
  calc
    (∑ env : SS.BitString 4,
        block psi (assemblePair s (0, b) env) i j) =
        ∑ y ∈ environmentBases s b, block psi y i j := by
      unfold environmentBases
      rw [Finset.sum_image (assemblePair_environment_injective s b).injOn]
    _ = ∑ y ∈ fiberEnvironmentBases r s b, block psi y i j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro y hy hnot
      have hne : SS.weight uniformAv y ≠ r := by
        simp only [Finset.mem_filter, hy, true_and] at hnot
        exact hnot
      rw [block_zero_of_outside_fiber psi r hsupp y hne]
      rfl

private def aBaseMap (e : Fin 5 × Fin 5) : SS.BitString 6 :=
  aBase e.1 e.2

private theorem aBaseMap_injective_on :
    Set.InjOn aBaseMap (↑edgePairs : Set (Fin 5 × Fin 5)) := by
  decide

private theorem cFiberBases_zero (s : Fin 5) :
    fiberEnvironmentBases 0 s 0 =
      {zero} ∪ (incidentPairs s).image aBaseMap := by
  fin_cases s <;> decide

private theorem cFiberBases_one (s : Fin 5) :
    fiberEnvironmentBases 0 s 1 =
      (nonincidentPairs s).image aBaseMap := by
  fin_cases s <;> decide

private theorem zero_disjoint_incident_aBases (s : Fin 5) :
    Disjoint ({zero} : Finset (SS.BitString 6))
      ((incidentPairs s).image aBaseMap) := by
  fin_cases s <;> decide

private lemma nonincident_AMat_sum (c : SS.State 6 ℂ)
    (s : Fin 5) (i j : Fin 2) :
    (∑ e ∈ nonincidentPairs s, AMat c e i j) =
      sumA c i j - starA c s i j := by
  let pred : Fin 5 × Fin 5 → Prop := fun e => e.1 = s ∨ e.2 = s
  have hpart := Finset.sum_filter_add_sum_filter_not edgePairs pred
    (fun e => AMat c e i j)
  have hnot : edgePairs.filter (fun e => ¬ pred e) = nonincidentPairs s := by
    ext e
    simp [pred, nonincidentPairs]
  rw [hnot] at hpart
  change starA c s i j +
      (∑ e ∈ nonincidentPairs s, AMat c e i j) = sumA c i j at hpart
  linear_combination hpart

private theorem uniformC_cross_support
    (s : Fin 5) (env : SS.BitString 4) (i j : Fin 2) :
    SS.weight uniformAv (assemblePair s (i, 0) env) ≠ 0 ∨
      SS.weight uniformAv (assemblePair s (j, 1) env) ≠ 0 := by
  decide +revert

private theorem directPure_uniformC_cross
    (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal c s (i, 0) (j, 1) = 0 := by
  unfold directPurePairMarginal
  apply Finset.sum_eq_zero
  intro env _
  rcases uniformC_cross_support s env i j with hi | hj
  · rw [hc _ hi]
    simp
  · rw [hc _ hj]
    simp

private theorem directPure_uniformC_cross'
    (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal c s (i, 1) (j, 0) = 0 := by
  unfold directPurePairMarginal
  apply Finset.sum_eq_zero
  intro env _
  rcases uniformC_cross_support s env j i with hj | hi
  · rw [hc _ hj]
    simp
  · rw [hc _ hi]
    simp

private theorem directPure_uniformC_zero
    (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal c s (i, 0) (j, 0) =
      U c i j + starA c s i j := by
  rw [directPurePairMarginal_diagonal,
    sum_environment_blocks_eq_fiber c 0 hc, cFiberBases_zero]
  rw [Finset.sum_union (zero_disjoint_incident_aBases s),
    Finset.sum_singleton,
    Finset.sum_image (aBaseMap_injective_on.mono (incident_subset s))]
  rfl

private theorem directPure_uniformC_one
    (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal c s (i, 1) (j, 1) =
      sumA c i j - starA c s i j := by
  rw [directPurePairMarginal_diagonal,
    sum_environment_blocks_eq_fiber c 0 hc, cFiberBases_one]
  rw [Finset.sum_image (aBaseMap_injective_on.mono (nonincident_subset s))]
  exact nonincident_AMat_sum c s i j

private theorem directPure_uniformC
    (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (s : Fin 5) :
    directPurePairMarginal c s = uniformCBlocks c s := by
  ext p q
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, b'⟩
  fin_cases b <;> fin_cases b'
  · simpa [uniformCBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformC_zero c hc s i j
  · simpa [uniformCBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformC_cross c hc s i j
  · simpa [uniformCBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformC_cross' c hc s i j
  · simpa [uniformCBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformC_one c hc s i j

private def bBaseMap (e : Fin 5 × Fin 5) : SS.BitString 6 :=
  bBase e.1 e.2

private theorem bBaseMap_injective_on :
    Set.InjOn bBaseMap (↑edgePairs : Set (Fin 5 × Fin 5)) := by
  decide

private theorem dFiberBases_zero (s : Fin 5) :
    fiberEnvironmentBases 2 s 0 =
      (nonincidentPairs s).image bBaseMap := by
  fin_cases s <;> decide

private theorem dFiberBases_one (s : Fin 5) :
    fiberEnvironmentBases 2 s 1 =
      {activeAll} ∪ (incidentPairs s).image bBaseMap := by
  fin_cases s <;> decide

private theorem activeAll_disjoint_incident_bBases (s : Fin 5) :
    Disjoint ({activeAll} : Finset (SS.BitString 6))
      ((incidentPairs s).image bBaseMap) := by
  fin_cases s <;> decide

private lemma nonincident_BMat_sum (d : SS.State 6 ℂ)
    (s : Fin 5) (i j : Fin 2) :
    (∑ e ∈ nonincidentPairs s, BMat d e i j) =
      sumB d i j - starB d s i j := by
  let pred : Fin 5 × Fin 5 → Prop := fun e => e.1 = s ∨ e.2 = s
  have hpart := Finset.sum_filter_add_sum_filter_not edgePairs pred
    (fun e => BMat d e i j)
  have hnot : edgePairs.filter (fun e => ¬ pred e) = nonincidentPairs s := by
    ext e
    simp [pred, nonincidentPairs]
  rw [hnot] at hpart
  change starB d s i j +
      (∑ e ∈ nonincidentPairs s, BMat d e i j) = sumB d i j at hpart
  linear_combination hpart

private theorem uniformD_cross_support
    (s : Fin 5) (env : SS.BitString 4) (i j : Fin 2) :
    SS.weight uniformAv (assemblePair s (i, 0) env) ≠ 2 ∨
      SS.weight uniformAv (assemblePair s (j, 1) env) ≠ 2 := by
  decide +revert

private theorem directPure_uniformD_cross
    (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal d s (i, 0) (j, 1) = 0 := by
  unfold directPurePairMarginal
  apply Finset.sum_eq_zero
  intro env _
  rcases uniformD_cross_support s env i j with hi | hj
  · rw [hd _ hi]
    simp
  · rw [hd _ hj]
    simp

private theorem directPure_uniformD_cross'
    (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal d s (i, 1) (j, 0) = 0 := by
  unfold directPurePairMarginal
  apply Finset.sum_eq_zero
  intro env _
  rcases uniformD_cross_support s env j i with hj | hi
  · rw [hd _ hj]
    simp
  · rw [hd _ hi]
    simp

private theorem directPure_uniformD_zero
    (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal d s (i, 0) (j, 0) =
      sumB d i j - starB d s i j := by
  rw [directPurePairMarginal_diagonal,
    sum_environment_blocks_eq_fiber d 2 hd, dFiberBases_zero]
  rw [Finset.sum_image (bBaseMap_injective_on.mono (nonincident_subset s))]
  exact nonincident_BMat_sum d s i j

private theorem directPure_uniformD_one
    (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (s : Fin 5) (i j : Fin 2) :
    directPurePairMarginal d s (i, 1) (j, 1) =
      W d i j + starB d s i j := by
  rw [directPurePairMarginal_diagonal,
    sum_environment_blocks_eq_fiber d 2 hd, dFiberBases_one]
  rw [Finset.sum_union (activeAll_disjoint_incident_bBases s),
    Finset.sum_singleton,
    Finset.sum_image (bBaseMap_injective_on.mono (incident_subset s))]
  rfl

private theorem directPure_uniformD
    (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (s : Fin 5) :
    directPurePairMarginal d s = uniformDBlocks d s := by
  ext p q
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, b'⟩
  fin_cases b <;> fin_cases b'
  · simpa [uniformDBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformD_zero d hd s i j
  · simpa [uniformDBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformD_cross d hd s i j
  · simpa [uniformDBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformD_cross' d hd s i j
  · simpa [uniformDBlocks, Matrix.blockDiagonal_apply] using
      directPure_uniformD_one d hd s i j

private theorem uniformCBlocks_eq_pairMarginal
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (s : Fin 5) :
    uniformCBlocks c s = pairMarginal c d s := by
  rcases global_frames c d hc hd hcode with ⟨hA, _hB⟩
  have hstar := star_identity c d hc hd hcode
  ext p q
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, b'⟩
  fin_cases b <;> fin_cases b'
  · rfl
  · rfl
  · rfl
  · change sumA c i j - starA c s i j = W d i j + starB d s i j
    linear_combination hA i j - hstar s i j

private theorem uniformDBlocks_eq_pairMarginal
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (s : Fin 5) :
    uniformDBlocks d s = pairMarginal c d s := by
  rcases global_frames c d hc hd hcode with ⟨_hA, hB⟩
  have hstar := star_identity c d hc hd hcode
  ext p q
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, b'⟩
  fin_cases b <;> fin_cases b'
  · change sumB d i j - starB d s i j = U c i j + starA c s i j
    linear_combination hB i j - hstar s i j
  · rfl
  · rfl
  · rfl

/-- For arbitrary states on the two complete uniform fibres, genuine
distance three identifies the literal amplitude-level partial trace of `P/2`
with the matrix normal form `pairMarginal`. -/
theorem direct_uniform_eq_pairMarginal
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (s : Fin 5) :
    directPairMarginal ![c,d] s = pairMarginal c d s := by
  ext p q
  simp only [directPairMarginal, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [directPure_uniformC c hc s, directPure_uniformD d hd s,
    uniformCBlocks_eq_pairMarginal c d hc hd hcode s,
    uniformDBlocks_eq_pairMarginal c d hc hd hcode s]
  ring

/-- The restriction of `flip45` to the four traced active coordinates. -/
def tracedFlip45 (s : Fin 5) : SS.BitString 4 :=
  fun i => flip45 (s.succAbove i).succ

private theorem finTwoEquiv_swapIdx (b : Bool) (i : Fin 2) :
    finTwoEquiv (swapIdx b i) = xor (finTwoEquiv i) b := by
  cases b <;> fin_cases i <;> rfl

/-- Decomposing the physical `flip45` across the retained pair and traced
environment: qubit zero stays fixed, the retained active bit is toggled by
`retainedPairEquiv`, and all other toggles are absorbed into `tracedFlip45`.
-/
theorem assemblePair_flip45 (s : Fin 5) (p : Fin 2 × Fin 2)
    (env : SS.BitString 4) :
    SS.bxor (assemblePair s p env) flip45 =
      assemblePair s (retainedPairEquiv s p)
        (SS.bxor env (tracedFlip45 s)) := by
  rcases p with ⟨a, b⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [assemblePair, flip45, SixQubit.Realize.bs, SS.bxor_apply,
      retainedPairEquiv]
  · refine Fin.succAboveCases s ?_ (fun k => ?_) j
    · simp only [SS.bxor_apply, assemblePair, Fin.cons_succ,
        Fin.insertNth_apply_same, retainedPairEquiv_apply]
      change xor (finTwoEquiv b) (retainedActiveFlip s) =
        finTwoEquiv (swapIdx (retainedActiveFlip s) b)
      rw [finTwoEquiv_swapIdx]
    · simp [assemblePair, tracedFlip45, SS.bxor_apply]

/-- A physical `flip45` becomes precisely the retained local basis relabelling
after the traced-environment sum is reindexed. -/
theorem directPurePairMarginal_flip45
    (psi : SS.State 6 ℂ) (s : Fin 5) (p q : Fin 2 × Fin 2) :
    directPurePairMarginal (flipAct flip45 psi) s p q =
      directPurePairMarginal psi s
        (retainedPairEquiv s p) (retainedPairEquiv s q) := by
  unfold directPurePairMarginal flipAct
  simp_rw [assemblePair_flip45]
  exact Equiv.sum_comp (SS.bxorEquiv (tracedFlip45 s))
    (fun env =>
      psi (assemblePair s (retainedPairEquiv s p) env) *
        star (psi (assemblePair s (retainedPairEquiv s q) env)))

/-- The direct marginal of the uniform-gauge code is the direct marginal of
the original logical projector with the retained local `X` basis relabelled.
The logical swap disappears because the projector sum is invariant under
reordering its two summands. -/
theorem direct_uniformCode_eq_submatrix_original
    (c d : SS.State 6 ℂ) (s : Fin 5) :
    directPairMarginal (uniformCode c d) s =
      (directPairMarginal ![c,d] s).submatrix
        (retainedPairEquiv s) (retainedPairEquiv s) := by
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', b'⟩
  simp only [directPairMarginal, Matrix.submatrix_apply,
    Fin.sum_univ_two, uniformCode, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  change 1 / 2 *
      (directPurePairMarginal (flipAct flip45 d) s (a, b) (a', b') +
        directPurePairMarginal (flipAct flip45 c) s (a, b) (a', b')) = _
  rw [directPurePairMarginal_flip45, directPurePairMarginal_flip45]
  ring

private theorem retainedPairEquiv_involutive (s : Fin 5)
    (p : Fin 2 × Fin 2) :
    retainedPairEquiv s (retainedPairEquiv s p) = p := by
  rcases p with ⟨a, b⟩
  simp only [retainedPairEquiv_apply]
  rw [swapIdx_involutive]

/-- The gauge-transported matrix from `Orbit7GaugeRank` is exactly the direct
amplitude-level partial trace of the original code projector.  This is the
definition-level bridge that was intentionally absent from that earlier
module: uniform KL identifies the inner marginal with `pairMarginal`, while
the two occurrences of the involutive retained `X` relabelling cancel. -/
theorem direct_original_eq_gaugeTransported
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (s : Fin 5) :
    directPairMarginal ![c,d] s = gaugeTransportedPairMarginal c d s := by
  have huniform :
      directPairMarginal (uniformCode c d) s =
        pairMarginal (bottom d) (top c) s := by
    simpa [uniformCode] using direct_uniform_eq_pairMarginal
      (bottom d) (top c) (bottom_full_fiber d hd) (top_full_fiber c hc)
      (SixQubit.Orbit7Gauge.hasDistance c d hcode) s
  unfold gaugeTransportedPairMarginal
  rw [← huniform, direct_uniformCode_eq_submatrix_original]
  ext p q
  simp only [Matrix.submatrix_apply]
  rw [retainedPairEquiv_involutive, retainedPairEquiv_involutive]

/-- Consequently the literal direct original marginal and the uniform matrix
normal form have equal kernel `Matrix.rank`. -/
theorem direct_original_rank_eq_uniform_pairMarginal
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (s : Fin 5) :
    (directPairMarginal ![c,d] s).rank =
      (pairMarginal (bottom d) (top c) s).rank := by
  rw [direct_original_eq_gaugeTransported c d hc hd hcode s]
  exact gaugeTransportedPairMarginal_rank c d s

/-- A uniform-gauge rank-two witness therefore gives a genuine rank-two
partial trace of the original normalized code projector.  The conclusion is
stated directly with the amplitude-level marginal, not through a transported
surrogate definition. -/
theorem direct_original_hasPairRankTwo_of_uniform
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (hrank : HasPairRankTwo (bottom d) (top c)) :
    ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2 := by
  rcases hrank with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [direct_original_rank_eq_uniform_pairMarginal c d hc hd hcode s]
  exact hs

/-- Normalized-code wrapper for the preceding transport theorem.  The two
norm hypotheses, together with the identity-error instance of `HasDistance`,
make `![c,d]` an orthonormal logical basis, so the amplitude sum in the
conclusion is the normalized projector marginal `Tr(P/2)`. -/
theorem direct_original_normalized_hasPairRankTwo_of_uniform
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 → d x = 0)
    (_hnc : SS.innerC c c = 1) (_hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hrank : HasPairRankTwo (bottom d) (top c)) :
    ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2 :=
  direct_original_hasPairRankTwo_of_uniform c d hc hd hcode hrank

end

end SixQubit.Orbit7DirectMarginal
