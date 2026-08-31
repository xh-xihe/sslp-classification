import MainTheory.FinitePipeline
import MainTheory.CubeAction
import MainTheory.DistanceSignature

/-!
# Fully kernel checked finite-orbit directory API
-/

namespace MainTheory.FiniteOrbitPipeline

open scoped BigOperators

namespace FP
export MainTheory.FinitePipeline (Word6 InMask FiberPair)
end FP

namespace CA
export MainTheory.CubeAction (FiberPair actFibers)
end CA

namespace DS
export MainTheory.DistanceSignature
  (Signature signature LabeledEquivalent not_labeledEquivalent_of_signature_ne
    labeledEquivalent_trans labeledEquivalent_symm)
end DS

abbrev Word6 := FP.Word6
abbrev Cube6 := SS.BitString 6

/-- The six Boolean coordinates of a finite-pipeline word. -/
def wordBits (x : Word6) : Cube6 := fun j => x.1.testBit j.1

/-- Exact image of the selected `Fin 64` words.  There is no truncating cast
and no default word. -/
def fiberOfMask (mask : ℕ) : Finset Cube6 :=
  (Finset.univ.filter fun x : Word6 => FP.InMask mask x).image wordBits

theorem mem_fiberOfMask_iff (mask : ℕ) (z : Cube6) :
    z ∈ fiberOfMask mask ↔
      ∃ x : Word6, FP.InMask mask x ∧ wordBits x = z := by
  simp [fiberOfMask]

/-- Convert both exact finite-pipeline masks, with `false` corresponding to
`mask0` and `true` to `mask1`. -/
def fibersOfPair (pair : FP.FiberPair) : CA.FiberPair 6
  | false => fiberOfMask pair.mask0
  | true => fiberOfMask pair.mask1

@[simp] theorem fibersOfPair_false (pair : FP.FiberPair) :
    fibersOfPair pair false = fiberOfMask pair.mask0 := rfl

@[simp] theorem fibersOfPair_true (pair : FP.FiberPair) :
    fibersOfPair pair true = fiberOfMask pair.mask1 := rfl

/-! ## Explicit list permutations -/

/-- Kernel-checkable conditions saying that a raw list is a permutation of
`0, ..., 5`. -/
structure PermutationValid (values : List ℕ) : Prop where
  length_eq : values.length = 6
  nodup : values.Nodup
  range : ∀ i : Fin values.length, values.get i < 6

private def permutationFun (values : List ℕ) (h : PermutationValid values) :
    Fin 6 → Fin 6 := fun i =>
  let ii : Fin values.length := Fin.cast h.length_eq.symm i
  ⟨values.get ii, h.range ii⟩

private theorem permutationFun_injective (values : List ℕ)
    (h : PermutationValid values) : Function.Injective (permutationFun values h) := by
  intro i j hij
  have hget : values.get (Fin.cast h.length_eq.symm i) =
      values.get (Fin.cast h.length_eq.symm j) := congrArg Fin.val hij
  have hindex := (List.nodup_iff_injective_get.mp h.nodup) hget
  exact (Fin.cast_injective h.length_eq.symm) hindex

/-- The actual coordinate permutation certified by the list. -/
noncomputable def permutationOfList (values : List ℕ) (h : PermutationValid values) :
    Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (permutationFun values h)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨permutationFun_injective values h, rfl⟩)

/-- A raw shift below 64, decoded by the same `Nat.testBit` convention. -/
def shiftBits (shift : ℕ) : Cube6 := fun j => shift.testBit j.1

/-! ## Individual orbit witnesses -/

structure OrbitKey where
  q : ℕ
  m : ℕ
  mask0 : ℕ
  mask1 : ℕ
  deriving DecidableEq, Repr

def OrbitKey.pair (key : OrbitKey) : FP.FiberPair where
  q := key.q
  m := key.m
  mask0 := key.mask0
  mask1 := key.mask1

def OrbitKey.fibers (key : OrbitKey) : CA.FiberPair 6 := fibersOfPair key.pair

/-- Raw witness data.  Both references are bounded; lists are never read with
`getD` or another fallback. -/
structure OrbitWitness (inputCount keyCount : ℕ) where
  input : Fin inputCount
  key : Fin keyCount
  q : ℕ
  m : ℕ
  permutation : List ℕ
  shift : ℕ
  swap : Bool
  deriving Repr

/-- Transport only the two bounded indices when the ambient finite list
lengths are propositionally (rather than definitionally) equal. -/
def OrbitWitness.cast {inputCount inputCount' keyCount keyCount' : ℕ}
    (hInput : inputCount = inputCount') (hKey : keyCount = keyCount')
    (w : OrbitWitness inputCount keyCount) :
    OrbitWitness inputCount' keyCount' where
  input := Fin.cast hInput w.input
  key := Fin.cast hKey w.key
  q := w.q
  m := w.m
  permutation := w.permutation
  shift := w.shift
  swap := w.swap

@[simp] theorem OrbitWitness.cast_input_val
    {inputCount inputCount' keyCount keyCount' : ℕ}
    (hInput : inputCount = inputCount') (hKey : keyCount = keyCount')
    (w : OrbitWitness inputCount keyCount) :
    (w.cast hInput hKey).input.1 = w.input.1 := rfl

@[simp] theorem OrbitWitness.cast_key_val
    {inputCount inputCount' keyCount keyCount' : ℕ}
    (hInput : inputCount = inputCount') (hKey : keyCount = keyCount')
    (w : OrbitWitness inputCount keyCount) :
    (w.cast hInput hKey).key.1 = w.key.1 := rfl

def OrbitWitness.ValidFor {inputCount keyCount : ℕ}
    (w : OrbitWitness inputCount keyCount) (source : FP.FiberPair)
    (target : OrbitKey) : Prop :=
  w.q = source.q ∧ w.m = source.m ∧
  w.q = target.q ∧ w.m = target.m ∧
  ∃ hp : PermutationValid w.permutation,
    w.shift < 64 ∧
    CA.actFibers
      { perm := permutationOfList w.permutation hp
        shift := shiftBits w.shift
        swap := w.swap }
      (fibersOfPair source) = target.fibers

def OrbitWitness.Valid {inputs : List FP.FiberPair} {keys : List OrbitKey}
    (w : OrbitWitness inputs.length keys.length) : Prop :=
  w.ValidFor (inputs.get w.input) (keys.get w.key)

theorem OrbitWitness.valid_of_validFor {inputs : List FP.FiberPair}
    {keys : List OrbitKey} {w : OrbitWitness inputs.length keys.length}
    {source : FP.FiberPair} {target : OrbitKey}
    (hsource : inputs.get w.input = source)
    (htarget : keys.get w.key = target) (h : w.ValidFor source target) :
    w.Valid := by
  unfold OrbitWitness.Valid
  rw [hsource, htarget]
  exact h

/-- A witness checked against concrete source and target payloads gives their
exact labelled cube-action equivalence.  This payload-level form is useful
when a generated witness is consumed without first rebuilding list wrappers. -/
theorem OrbitWitness.labeledEquivalent_of_validFor
    {inputCount keyCount : ℕ} {w : OrbitWitness inputCount keyCount}
    {source : FP.FiberPair} {target : OrbitKey}
    (h : w.ValidFor source target) :
    DS.LabeledEquivalent source.q source.m (fibersOfPair source)
      target.q target.m target.fibers := by
  dsimp [OrbitWitness.ValidFor] at h
  rcases h with ⟨hqS, hmS, hqT, hmT, hp, _hshift, hact⟩
  refine ⟨hqS.symm.trans hqT, hmS.symm.trans hmT, ?_⟩
  exact ⟨
    { perm := permutationOfList w.permutation hp
      shift := shiftBits w.shift
      swap := w.swap }, hact⟩

/-- Every valid raw witness gives the exact labelled equivalence asserted by
the orbit directory. -/
theorem OrbitWitness.labeledEquivalent {inputs : List FP.FiberPair}
    {keys : List OrbitKey} {w : OrbitWitness inputs.length keys.length}
    (h : w.Valid) :
    DS.LabeledEquivalent
      (inputs.get w.input).q (inputs.get w.input).m
      (fibersOfPair (inputs.get w.input))
      (keys.get w.key).q (keys.get w.key).m (keys.get w.key).fibers := by
  exact w.labeledEquivalent_of_validFor h

/-- A generated witness together with the ordinary-kernel proof that it acts
on the exact input and key lists supplied as parameters.  Parameterizing the
wrapper by the lists (not merely their lengths) prevents a certificate proved
against a dummy directory from being reused in the final directory. -/
structure CertifiedOrbitWitness (inputs : List FP.FiberPair)
    (keys : List OrbitKey) where
  witness : OrbitWitness inputs.length keys.length
  valid : witness.Valid (inputs := inputs) (keys := keys)

theorem CertifiedOrbitWitness.labeledEquivalent
    {inputs : List FP.FiberPair} {keys : List OrbitKey}
    (cert : CertifiedOrbitWitness inputs keys) :
    DS.LabeledEquivalent
      (inputs.get cert.witness.input).q (inputs.get cert.witness.input).m
      (fibersOfPair (inputs.get cert.witness.input))
      (keys.get cert.witness.key).q (keys.get cert.witness.key).m
      (keys.get cert.witness.key).fibers :=
  cert.witness.labeledEquivalent cert.valid

/-! ## Whole-directory validity and consequences -/

structure Directory where
  inputCount : ℕ
  keyCount : ℕ
  witnessCount : ℕ
  inputs : Fin inputCount → FP.FiberPair
  keys : Fin keyCount → OrbitKey
  witnesses : Fin witnessCount → OrbitWitness inputCount keyCount
  compatible : Fin inputCount → Prop

def Directory.inputFibers (d : Directory) (i : Fin d.inputCount) :
    CA.FiberPair 6 := fibersOfPair (d.inputs i)

def Directory.keySignature (d : Directory) (k : Fin d.keyCount) :
    DS.Signature 6 :=
  let key := d.keys k
  DS.signature key.q key.m key.fibers

/-- A complete finite directory certificate.  `witness_valid` is the exact
q/m/F check for every stored witness.  The next two fields rule out missing
compatible inputs and ghost keys, respectively. -/
structure Directory.Valid (d : Directory) : Prop where
  witness_valid : ∀ w : Fin d.witnessCount,
    (d.witnesses w).ValidFor
      (d.inputs (d.witnesses w).input) (d.keys (d.witnesses w).key)
  covers : ∀ i : Fin d.inputCount, d.compatible i →
    ∃ w : Fin d.witnessCount, (d.witnesses w).input = i
  key_has_input : ∀ k : Fin d.keyCount,
    ∃ w : Fin d.witnessCount,
      (d.witnesses w).key = k ∧ d.compatible (d.witnesses w).input
  signatures_ne : ∀ k l : Fin d.keyCount, k ≠ l →
    d.keySignature k ≠ d.keySignature l

/-! ## A fixed-cardinality generated certificate

The generated orbit audit starts after the rank filter, so every entry in its
input vector is compatible.  Keeping the source data as `Fin`-indexed
functions makes completeness non-vacuous: there is exactly one certified
witness for every input index, and a representative input is supplied for
every key.
-/

/-- Proof-carrying fixed-size data from which a valid directory is obtained.
The `signatures` field contains small literal invariants; `signature_exact`
checks each literal against the actual finite-set signature, while
`signatures_injective` proves that no two declared keys can be equivalent. -/
structure FiniteCertificate (inputCount keyCount : ℕ) where
  inputAt : Fin inputCount → FP.FiberPair
  keyAt : Fin keyCount → OrbitKey
  witnessAt : Fin inputCount → OrbitWitness inputCount keyCount
  witness_valid : ∀ i,
    (witnessAt i).ValidFor
      (inputAt (witnessAt i).input) (keyAt (witnessAt i).key)
  witness_input : ∀ i, (witnessAt i).input = i
  representative : Fin keyCount → Fin inputCount
  representative_key : ∀ k, (witnessAt (representative k)).key = k
  signatures : Fin keyCount → DS.Signature 6
  signature_exact : ∀ k,
    let key := keyAt k
    DS.signature key.q key.m key.fibers = signatures k
  signatures_injective : Function.Injective signatures

/-- Forget the proofs and expose the concrete directory classified by a
fixed-size generated certificate. -/
def FiniteCertificate.directory {inputCount keyCount : ℕ}
    (cert : FiniteCertificate inputCount keyCount) : Directory where
  inputCount := inputCount
  keyCount := keyCount
  witnessCount := inputCount
  inputs := cert.inputAt
  keys := cert.keyAt
  witnesses := cert.witnessAt
  compatible := fun _ => True

/-- The fixed-size obligations imply all four non-vacuity and separation
conditions of `Directory.Valid`. -/
theorem FiniteCertificate.directory_valid {inputCount keyCount : ℕ}
    (cert : FiniteCertificate inputCount keyCount) : cert.directory.Valid := by
  refine {
    witness_valid := cert.witness_valid
    covers := ?_
    key_has_input := ?_
    signatures_ne := ?_ }
  · intro i _
    exact ⟨i, cert.witness_input i⟩
  · intro k
    exact ⟨cert.representative k, cert.representative_key k, trivial⟩
  · intro k l hkl hsig
    have hk := cert.signature_exact k
    have hl := cert.signature_exact l
    have hs : cert.signatures k = cert.signatures l := by
      rw [← hk, ← hl]
      simpa [Directory.keySignature, FiniteCertificate.directory] using hsig
    exact hkl (cert.signatures_injective hs)

theorem Directory.Valid.witness_labeledEquivalent {d : Directory}
    (h : d.Valid) (w : Fin d.witnessCount) :
    let witness := d.witnesses w
    let source := d.inputs witness.input
    let key := d.keys witness.key
    DS.LabeledEquivalent source.q source.m (fibersOfPair source)
      key.q key.m key.fibers := by
  dsimp only
  have hv := h.witness_valid w
  dsimp [OrbitWitness.ValidFor] at hv
  rcases hv with ⟨hqS, hmS, hqT, hmT, hp, hshift, hact⟩
  refine ⟨hqS.symm.trans hqT, hmS.symm.trans hmT, ?_⟩
  exact ⟨
    { perm := permutationOfList (d.witnesses w).permutation hp
      shift := shiftBits (d.witnesses w).shift
      swap := (d.witnesses w).swap }, hact⟩

/-- Every compatible input row is covered by one declared key orbit. -/
theorem Directory.Valid.orbit_coverage {d : Directory} (h : d.Valid)
    (i : Fin d.inputCount) (hi : d.compatible i) :
    ∃ k : Fin d.keyCount,
      let source := d.inputs i
      let key := d.keys k
      DS.LabeledEquivalent source.q source.m (fibersOfPair source)
        key.q key.m key.fibers := by
  obtain ⟨w, hw⟩ := h.covers i hi
  let witness := d.witnesses w
  refine ⟨witness.key, ?_⟩
  have he := h.witness_labeledEquivalent w
  subst i
  simpa [witness] using he

/-- Every key is witnessed by a compatible input; there are no directory-only
or "ghost" representatives. -/
theorem Directory.Valid.no_ghost_key {d : Directory} (h : d.Valid)
    (k : Fin d.keyCount) :
    ∃ i : Fin d.inputCount, d.compatible i ∧
      let source := d.inputs i
      let key := d.keys k
      DS.LabeledEquivalent source.q source.m (fibersOfPair source)
        key.q key.m key.fibers := by
  obtain ⟨w, hwk, hwc⟩ := h.key_has_input k
  let witness := d.witnesses w
  refine ⟨witness.input, hwc, ?_⟩
  have he := h.witness_labeledEquivalent w
  subst k
  simpa [witness] using he

/-- Distinct directory keys represent inequivalent labelled orbits. -/
theorem Directory.Valid.keys_pairwise_inequivalent {d : Directory}
    (h : d.Valid) {k l : Fin d.keyCount} (hkl : k ≠ l) :
    let keyK := d.keys k
    let keyL := d.keys l
    ¬ DS.LabeledEquivalent keyK.q keyK.m keyK.fibers
      keyL.q keyL.m keyL.fibers := by
  apply DS.not_labeledEquivalent_of_signature_ne
  exact h.signatures_ne k l hkl

private def CoveredByKey (d : Directory) (i : Fin d.inputCount)
    (k : Fin d.keyCount) : Prop :=
  let source := d.inputs i
  let key := d.keys k
  DS.LabeledEquivalent source.q source.m (fibersOfPair source)
    key.q key.m key.fibers

private theorem Directory.Valid.existsUnique_key {d : Directory} (h : d.Valid)
    (i : Fin d.inputCount) (hi : d.compatible i) :
    ∃! k : Fin d.keyCount, CoveredByKey d i k := by
  obtain ⟨k, hk⟩ := h.orbit_coverage i hi
  refine ⟨k, hk, ?_⟩
  intro l hl
  by_contra hkl
  have hkeys :
      let keyK := d.keys k
      let keyL := d.keys l
      DS.LabeledEquivalent keyK.q keyK.m keyK.fibers
        keyL.q keyL.m keyL.fibers := by
    exact DS.labeledEquivalent_trans (DS.labeledEquivalent_symm hk) hl
  have hne : k ≠ l := fun hEq => hkl hEq.symm
  exact h.keys_pairwise_inequivalent (k := k) (l := l) hne hkeys

abbrev CompatibleInput (d : Directory) :=
  {i : Fin d.inputCount // d.compatible i}

/-- An explicit finite classification map: equal class labels are equivalent
to labelled orbit equivalence, and every label is attained. -/
def HasExactlyClasses (d : Directory) (n : ℕ) : Prop :=
  ∃ classify : CompatibleInput d → Fin d.keyCount,
    Function.Surjective classify ∧
    (∀ i j,
      classify i = classify j ↔
        DS.LabeledEquivalent
          (d.inputs i.1).q (d.inputs i.1).m (d.inputFibers i.1)
          (d.inputs j.1).q (d.inputs j.1).m (d.inputFibers j.1)) ∧
    Fintype.card (Fin d.keyCount) = n

noncomputable def Directory.Valid.classify {d : Directory} (h : d.Valid) :
    CompatibleInput d → Fin d.keyCount := fun i =>
  Classical.choose (h.existsUnique_key i.1 i.2)

private theorem Directory.Valid.classify_spec {d : Directory} (h : d.Valid)
    (i : CompatibleInput d) : CoveredByKey d i.1 (h.classify i) :=
  (Classical.choose_spec (h.existsUnique_key i.1 i.2)).1

private theorem Directory.Valid.classify_unique {d : Directory} (h : d.Valid)
    (i : CompatibleInput d) {k : Fin d.keyCount}
    (hk : CoveredByKey d i.1 k) : h.classify i = k :=
  ((Classical.choose_spec (h.existsUnique_key i.1 i.2)).2 k hk).symm

/-- Coverage, no-ghostness, and signature separation together prove that the
number of labelled equivalence classes is exactly `keys.length`. -/
theorem Directory.Valid.hasExactlyClasses {d : Directory} (h : d.Valid) :
    HasExactlyClasses d d.keyCount := by
  refine ⟨h.classify, ?_, ?_, by simp⟩
  · intro k
    obtain ⟨i, hi, hik⟩ := h.no_ghost_key k
    let ci : CompatibleInput d := ⟨i, hi⟩
    refine ⟨ci, ?_⟩
    exact h.classify_unique ci hik
  · intro i j
    constructor
    · intro hij
      have hi := h.classify_spec i
      have hj := h.classify_spec j
      rw [hij] at hi
      exact DS.labeledEquivalent_trans hi (DS.labeledEquivalent_symm hj)
    · intro hij
      have hi := h.classify_spec i
      have hj := h.classify_spec j
      have hkeys := DS.labeledEquivalent_trans
        (DS.labeledEquivalent_symm hi)
        (DS.labeledEquivalent_trans hij hj)
      by_contra hne
      exact h.keys_pairwise_inequivalent hne hkeys

end MainTheory.FiniteOrbitPipeline
