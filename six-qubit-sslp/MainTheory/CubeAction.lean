import Mathlib
import MainTheory.ActiveFace
import SixQubit.CodeEquiv

/-!
# Boolean-cube actions used by the six-qubit orbit reduction

Section 7 of `main.tex` quotients coloured pairs of Boolean fibres by three
operations: a permutation of the six coordinates, a common XOR translation,
and interchange of the two colours.  This file defines that finite action and
proves its structural invariants.  It intentionally makes no claim that a
particular certificate list has 66 orbits; that separate numerical statement
requires the classification data.
-/

namespace MainTheory.CubeAction

open scoped BigOperators
open SixQubit.CodeEquiv

variable {n : ℕ}

/-! ## Action parameters and their action on masks -/

/-- A coordinate permutation, common cube translation, and optional colour
swap. -/
structure Parameter (n : ℕ) where
  perm : Equiv.Perm (Fin n)
  shift : SS.BitString n
  swap : Bool
  deriving DecidableEq, Fintype

/-- Relabel, then XOR-translate, a Boolean mask. -/
def actPoint (g : Parameter n) (x : SS.BitString n) : SS.BitString n :=
  SS.bxor (permStr g.perm x) g.shift

/-- The colour action; XOR by `true` interchanges the two fibres. -/
def actColor (g : Parameter n) (c : Bool) : Bool := xor c g.swap

/-- The point action is a genuine equivalence. -/
def pointEquiv (g : Parameter n) : SS.BitString n ≃ SS.BitString n where
  toFun := actPoint g
  invFun y := permStr g.perm.symm (SS.bxor y g.shift)
  left_inv := by
    intro x
    funext i
    simp [actPoint, permStr, SS.bxor]
  right_inv := by
    intro y
    funext i
    simp [actPoint, permStr, SS.bxor]

/-- Identity action parameter. -/
def one : Parameter n :=
  ⟨Equiv.refl _, fun _ => false, false⟩

/-- Composition in action order: `comp g h` acts first by `h`, then by `g`. -/
def comp (g h : Parameter n) : Parameter n :=
  ⟨g.perm.trans h.perm,
    SS.bxor (permStr g.perm h.shift) g.shift,
    xor g.swap h.swap⟩

/-- Inverse cube action. -/
def inv (g : Parameter n) : Parameter n :=
  ⟨g.perm.symm, permStr g.perm.symm g.shift, g.swap⟩

@[simp] theorem actPoint_one (x : SS.BitString n) : actPoint one x = x := by
  funext i
  simp [actPoint, one, permStr, SS.bxor]

@[simp] theorem actColor_one (c : Bool) : actColor (one : Parameter n) c = c := by
  simp [actColor, one]

theorem actPoint_comp (g h : Parameter n) (x : SS.BitString n) :
    actPoint (comp g h) x = actPoint g (actPoint h x) := by
  funext i
  simp only [actPoint, comp, permStr, SS.bxor, Equiv.trans_apply]
  exact (Bool.xor_assoc _ _ _).symm

theorem actColor_comp (g h : Parameter n) (c : Bool) :
    actColor (comp g h) c = actColor h (actColor g c) := by
  simp only [actColor, comp]
  exact (Bool.xor_assoc _ _ _).symm

@[simp] theorem actPoint_inv_left (g : Parameter n) (x : SS.BitString n) :
    actPoint (inv g) (actPoint g x) = x := by
  funext i
  simp [actPoint, inv, permStr, SS.bxor]

@[simp] theorem actPoint_inv_right (g : Parameter n) (x : SS.BitString n) :
    actPoint g (actPoint (inv g) x) = x := by
  funext i
  simp [actPoint, inv, permStr, SS.bxor]

@[simp] theorem actColor_inv_left (g : Parameter n) (c : Bool) :
    actColor (inv g) (actColor g c) = c := by
  simp [actColor, inv]

@[simp] theorem actColor_inv_right (g : Parameter n) (c : Bool) :
    actColor g (actColor (inv g) c) = c := by
  simp [actColor, inv]

/-! ## Hamming distance -/

/-- Hamming distance written as the weight of the XOR difference. -/
def hammingDistance (x y : SS.BitString n) : ℕ :=
  SS.hammingWt (SS.bxor x y)

/-- Coordinate relabelling preserves Hamming weight. -/
theorem hammingWt_permStr (σ : Equiv.Perm (Fin n)) (x : SS.BitString n) :
    SS.hammingWt (permStr σ x) = SS.hammingWt x := by
  simp only [SS.hammingWt, Finset.card_filter, permStr_apply]
  exact Equiv.sum_comp σ (fun j => if x j = true then 1 else 0)

/-- A common translation cancels from an XOR difference. -/
theorem actPoint_xor (g : Parameter n) (x y : SS.BitString n) :
    SS.bxor (actPoint g x) (actPoint g y) =
      permStr g.perm (SS.bxor x y) := by
  funext i
  simp only [actPoint, SS.bxor_apply, permStr_apply]
  cases x (g.perm i) <;> cases y (g.perm i) <;> cases g.shift i <;> rfl

/-- Every cube action is an isometry of Hamming space. -/
theorem hammingDistance_actPoint (g : Parameter n) (x y : SS.BitString n) :
    hammingDistance (actPoint g x) (actPoint g y) = hammingDistance x y := by
  rw [hammingDistance, hammingDistance, actPoint_xor, hammingWt_permStr]

/-! ## Coloured fibre pairs and their orbit relation -/

/-- A pair of finite Boolean fibres, indexed by the two Boolean colours. -/
abbrev FiberPair (n : ℕ) := Bool → Finset (SS.BitString n)

/-- Push both fibres through the same cube isometry and optionally swap them. -/
def actFibers (g : Parameter n) (F : FiberPair n) : FiberPair n :=
  fun c => (F (actColor g c)).map (pointEquiv g).toEmbedding

theorem mem_actFibers_iff (g : Parameter n) (F : FiberPair n)
    (c : Bool) (y : SS.BitString n) :
    y ∈ actFibers g F c ↔
      ∃ x ∈ F (actColor g c), actPoint g x = y := by
  rw [actFibers, Finset.mem_map]
  rfl

@[simp] theorem actFibers_one (F : FiberPair n) : actFibers one F = F := by
  funext c
  ext y
  simp [mem_actFibers_iff]

theorem actFibers_comp (g h : Parameter n) (F : FiberPair n) :
    actFibers (comp g h) F = actFibers g (actFibers h F) := by
  funext c
  ext y
  constructor
  · rw [mem_actFibers_iff]
    rintro ⟨x, hx, rfl⟩
    rw [actColor_comp] at hx
    rw [mem_actFibers_iff]
    refine ⟨actPoint h x, ?_, ?_⟩
    · exact (mem_actFibers_iff h F _ _).2 ⟨x, hx, rfl⟩
    · exact (actPoint_comp g h x).symm
  · rw [mem_actFibers_iff]
    rintro ⟨z, hz, hzy⟩
    rw [mem_actFibers_iff] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    rw [← hzy, ← hxz, ← actPoint_comp]
    exact (mem_actFibers_iff (comp g h) F c _).2
      ⟨x, by simpa [actColor_comp] using hx, rfl⟩

@[simp] theorem actFibers_inv_left (g : Parameter n) (F : FiberPair n) :
    actFibers (inv g) (actFibers g F) = F := by
  funext c
  ext y
  constructor
  · rw [mem_actFibers_iff]
    rintro ⟨z, hz, hzy⟩
    rw [mem_actFibers_iff] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    have hcolor : actColor g (actColor (inv g) c) = c := actColor_inv_right g c
    have hpoint : actPoint (inv g) (actPoint g x) = x := actPoint_inv_left g x
    rw [← hzy, ← hxz, hpoint]
    simpa [hcolor] using hx
  · intro hy
    rw [mem_actFibers_iff]
    refine ⟨actPoint g y, ?_, actPoint_inv_left g y⟩
    exact (mem_actFibers_iff g F _ _).2
      ⟨y, by simpa using hy, rfl⟩

@[simp] theorem actFibers_inv_right (g : Parameter n) (F : FiberPair n) :
    actFibers g (actFibers (inv g) F) = F := by
  funext c
  ext y
  constructor
  · rw [mem_actFibers_iff]
    rintro ⟨z, hz, hzy⟩
    rw [mem_actFibers_iff] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    rw [← hzy, ← hxz, actPoint_inv_right]
    simpa using hx
  · intro hy
    rw [mem_actFibers_iff]
    refine ⟨actPoint (inv g) y, ?_, actPoint_inv_right g y⟩
    exact (mem_actFibers_iff (inv g) F _ _).2
      ⟨y, by simpa using hy, rfl⟩

/-- Orbit equivalence of coloured fibre pairs under the finite cube action. -/
def FiberEquivalent (F G : FiberPair n) : Prop :=
  ∃ g : Parameter n, actFibers g F = G

theorem fiberEquivalent_refl (F : FiberPair n) : FiberEquivalent F F :=
  ⟨one, actFibers_one F⟩

theorem fiberEquivalent_symm {F G : FiberPair n}
    (h : FiberEquivalent F G) : FiberEquivalent G F := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨inv g, actFibers_inv_left g F⟩

theorem fiberEquivalent_trans {F G H : FiberPair n}
    (hFG : FiberEquivalent F G) (hGH : FiberEquivalent G H) :
    FiberEquivalent F H := by
  obtain ⟨g, rfl⟩ := hFG
  obtain ⟨h, rfl⟩ := hGH
  exact ⟨comp h g, actFibers_comp h g F⟩

theorem fiberEquivalent_equivalence : Equivalence (@FiberEquivalent n) :=
  ⟨fiberEquivalent_refl, fiberEquivalent_symm, fiberEquivalent_trans⟩

/-- Exact canonical orbit key: the complete finite orbit of a fibre pair. -/
noncomputable def orbitKey (F : FiberPair n) : Finset (FiberPair n) :=
  Finset.univ.image fun g : Parameter n => actFibers g F

theorem mem_orbitKey_iff (F G : FiberPair n) :
    G ∈ orbitKey F ↔ FiberEquivalent F G := by
  classical
  simp [orbitKey, FiberEquivalent]

theorem orbitKey_eq_of_equivalent {F G : FiberPair n}
    (hFG : FiberEquivalent F G) : orbitKey F = orbitKey G := by
  classical
  ext H
  rw [mem_orbitKey_iff, mem_orbitKey_iff]
  constructor
  · exact fun hFH => fiberEquivalent_trans (fiberEquivalent_symm hFG) hFH
  · exact fun hGH => fiberEquivalent_trans hFG hGH

/-- Equality of canonical orbit keys is exactly cube-action equivalence. -/
theorem orbitKey_eq_iff (F G : FiberPair n) :
    orbitKey F = orbitKey G ↔ FiberEquivalent F G := by
  constructor
  · intro hkey
    have hmem : F ∈ orbitKey F :=
      (mem_orbitKey_iff F F).2 (fiberEquivalent_refl F)
    rw [hkey] at hmem
    exact fiberEquivalent_symm ((mem_orbitKey_iff G F).1 hmem)
  · exact orbitKey_eq_of_equivalent

/-! ## Degree-at-most-two moment feasibility -/

/-- The real Walsh sign attached to a Boolean value. -/
def boolSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem boolSign_xor (a b : Bool) :
    boolSign (xor a b) = boolSign a * boolSign b := by
  cases a <;> cases b <;> norm_num [boolSign]

/-- Walsh character indexed by a Boolean mask.  Masks of Hamming weight at
most two span exactly the constants, linear moments and quadratic moments on
the Boolean cube. -/
def character (z x : SS.BitString n) : ℝ := boolSign (SS.bdot z x)

/-- Pull a character mask back through the coordinate permutation. -/
def pullMask (g : Parameter n) (z : SS.BitString n) : SS.BitString n :=
  permStr g.perm.symm z

theorem bdot_permStr_right (σ : Equiv.Perm (Fin n))
    (z x : SS.BitString n) :
    SS.bdot z (permStr σ x) = SS.bdot (permStr σ.symm z) x := by
  have h := bdot_permStr σ (permStr σ.symm z) x
  have hz : permStr σ (permStr σ.symm z) = z := by
    funext i
    simp [permStr]
  rwa [hz] at h

theorem pullMask_weight (g : Parameter n) (z : SS.BitString n) :
    SS.hammingWt (pullMask g z) = SS.hammingWt z := by
  exact hammingWt_permStr g.perm.symm z

/-- A Walsh character transforms by a common translation sign and a relabelled
mask.  The common sign cancels when the two colours have equal moments. -/
theorem character_actPoint (g : Parameter n) (z x : SS.BitString n) :
    character z (actPoint g x) =
      boolSign (SS.bdot z g.shift) * character (pullMask g z) x := by
  unfold character
  rw [actPoint, bdot_bxor_right, bdot_permStr_right]
  simp only [pullMask, boolSign_xor]
  ring

/-- A normalized nonnegative two-colour distribution supported on `F`, with
all Walsh moments of degree at most two equal between the colours. -/
structure MomentWitness (F : FiberPair n) where
  weight : Bool → SS.BitString n → ℝ
  nonneg : ∀ c x, 0 ≤ weight c x
  supported : ∀ c x, weight c x ≠ 0 → x ∈ F c
  normalized : ∀ c, ∑ x, weight c x = 1
  moments : ∀ z, SS.hammingWt z ≤ 2 →
    ∑ x, weight false x * character z x =
      ∑ x, weight true x * character z x

/-- Exact degree-at-most-two moment feasibility of a coloured fibre pair. -/
def DegreeTwoFeasible (F : FiberPair n) : Prop := Nonempty (MomentWitness F)

/-- Pullback formula for the weights of the pushed-forward distribution. -/
def pushWeight {F : FiberPair n} (W : MomentWitness F) (g : Parameter n)
    (c : Bool) (y : SS.BitString n) : ℝ :=
  W.weight (actColor g c) ((pointEquiv g).symm y)

@[simp] theorem pointEquiv_apply (g : Parameter n) (x : SS.BitString n) :
    pointEquiv g x = actPoint g x := rfl

@[simp] theorem pushWeight_actPoint {F : FiberPair n}
    (W : MomentWitness F) (g : Parameter n) (c : Bool) (x : SS.BitString n) :
    pushWeight W g c (actPoint g x) = W.weight (actColor g c) x := by
  change W.weight (actColor g c) ((pointEquiv g).symm ((pointEquiv g) x)) = _
  rw [Equiv.symm_apply_apply]

/-- Expectation of one Walsh character. -/
def expectation (p : Bool → SS.BitString n → ℝ) (c : Bool)
    (z : SS.BitString n) : ℝ :=
  ∑ x, p c x * character z x

theorem expectation_pushWeight {F : FiberPair n}
    (W : MomentWitness F) (g : Parameter n) (c : Bool)
    (z : SS.BitString n) :
    expectation (pushWeight W g) c z =
      boolSign (SS.bdot z g.shift) *
        expectation W.weight (actColor g c) (pullMask g z) := by
  classical
  unfold expectation
  rw [← Equiv.sum_comp (pointEquiv g)
    (fun y => pushWeight W g c y * character z y)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [pointEquiv_apply, pushWeight_actPoint, character_actPoint]
  ring

/-- Push a complete feasible moment witness through a cube action. -/
def pushWitness {F : FiberPair n} (W : MomentWitness F) (g : Parameter n) :
    MomentWitness (actFibers g F) where
  weight := pushWeight W g
  nonneg c y := W.nonneg (actColor g c) ((pointEquiv g).symm y)
  supported := by
    intro c y hy
    apply (mem_actFibers_iff g F c y).2
    refine ⟨(pointEquiv g).symm y, ?_, (pointEquiv g).apply_symm_apply y⟩
    exact W.supported _ _ (by simpa [pushWeight] using hy)
  normalized := by
    intro c
    rw [← Equiv.sum_comp (pointEquiv g) (fun y => pushWeight W g c y)]
    simpa only [pointEquiv_apply, pushWeight_actPoint] using
      W.normalized (actColor g c)
  moments := by
    intro z hz
    change expectation (pushWeight W g) false z =
      expectation (pushWeight W g) true z
    rw [expectation_pushWeight, expectation_pushWeight]
    have hz' : SS.hammingWt (pullMask g z) ≤ 2 := by
      simpa [pullMask_weight] using hz
    have hm := W.moments (pullMask g z) hz'
    cases hs : g.swap
    · simpa [actColor, hs] using
        congrArg (fun t => boolSign (SS.bdot z g.shift) * t) hm
    · simpa [actColor, hs] using
        congrArg (fun t => boolSign (SS.bdot z g.shift) * t) hm.symm

/-- Degree-at-most-two moment feasibility is invariant under every coordinate
permutation, common XOR translation and colour swap. -/
theorem degreeTwoFeasible_actFibers_iff (g : Parameter n) (F : FiberPair n) :
    DegreeTwoFeasible (actFibers g F) ↔ DegreeTwoFeasible F := by
  constructor
  · rintro ⟨W⟩
    have Winv := pushWitness W (inv g)
    refine ⟨?_⟩
    simpa using Winv
  · rintro ⟨W⟩
    exact ⟨pushWitness W g⟩

/-- A mask is active when some feasible witness gives it positive mass. -/
def ActiveMask (F : FiberPair n) (c : Bool) (x : SS.BitString n) : Prop :=
  ∃ W : MomentWitness F, 0 < W.weight c x

theorem activeMask_push {F : FiberPair n} {c : Bool} {x : SS.BitString n}
    (g : Parameter n) (h : ActiveMask F (actColor g c) x) :
    ActiveMask (actFibers g F) c (actPoint g x) := by
  obtain ⟨W, hx⟩ := h
  refine ⟨pushWitness W g, ?_⟩
  change 0 < pushWeight W g c (actPoint g x)
  simpa using hx

/-- Active masks are carried bijectively to active masks (with the expected
colour interchange). -/
theorem activeMask_actPoint_iff (g : Parameter n) (F : FiberPair n)
    (c : Bool) (x : SS.BitString n) :
    ActiveMask (actFibers g F) c (actPoint g x) ↔
      ActiveMask F (actColor g c) x := by
  constructor
  · intro h
    have h' := activeMask_push (F := actFibers g F)
      (c := actColor g c) (x := actPoint g x) (inv g) (by simpa using h)
    simpa using h'
  · exact activeMask_push g

/-! ## Active affine rank -/

/-- Embed a Boolean mask as its zero-one vertex in real affine space. -/
def bitVec (x : SS.BitString n) : Fin n → ℝ :=
  fun i => if x i then 1 else 0

/-- Coordinate relabelling as a linear equivalence of the ambient real
space. -/
def permLinearEquiv (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun i => v (σ i)
  invFun v := fun i => v (σ.symm i)
  left_inv := by
    intro v
    funext i
    simp
  right_inv := by
    intro v
    funext i
    simp
  map_add' := by
    intro u v
    rfl
  map_smul' := by
    intro r v
    rfl

/-- Sign changes in the translated coordinates form the linear part of a
cube translation. -/
def flipLinearEquiv (t : SS.BitString n) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun i => if t i then -v i else v i
  invFun v := fun i => if t i then -v i else v i
  left_inv := by
    intro v
    funext i
    by_cases hi : t i <;> simp [hi]
  right_inv := by
    intro v
    funext i
    by_cases hi : t i <;> simp [hi]
  map_add' := by
    intro u v
    funext i
    by_cases hi : t i
    · simp [hi]
      ring
    · simp [hi]
  map_smul' := by
    intro r v
    funext i
    by_cases hi : t i <;> simp [hi]

/-- Reflection `vᵢ ↦ 1-vᵢ` in every translated coordinate. -/
def flipAffineEquiv (t : SS.BitString n) :
    (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) where
  toEquiv :=
    { toFun := fun v i => if t i then 1 - v i else v i
      invFun := fun v i => if t i then 1 - v i else v i
      left_inv := by
        intro v
        funext i
        by_cases hi : t i <;> simp [hi]
      right_inv := by
        intro v
        funext i
        by_cases hi : t i <;> simp [hi] }
  linear := flipLinearEquiv t
  map_vadd' := by
    intro p v
    funext i
    by_cases hi : t i <;> simp [flipLinearEquiv, hi]
    ring

/-- The affine extension of the Boolean-cube isometry. -/
def bitAffineEquiv (g : Parameter n) :
    (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) :=
  (permLinearEquiv g.perm).toAffineEquiv.trans (flipAffineEquiv g.shift)

/-- The real zero-one embedding intertwines the Boolean and affine actions. -/
theorem bitVec_actPoint (g : Parameter n) (x : SS.BitString n) :
    bitVec (actPoint g x) = bitAffineEquiv g (bitVec x) := by
  funext i
  cases hx : x (g.perm i) <;> cases ht : g.shift i <;>
    simp [bitVec, actPoint, SS.bxor, permStr, bitAffineEquiv,
      permLinearEquiv, flipAffineEquiv, hx, ht]

/-- Real active point set in one colour. -/
def activePointSet (F : FiberPair n) (c : Bool) : Set (Fin n → ℝ) :=
  bitVec '' {x | ActiveMask F c x}

/-- Active points transform by the ambient affine cube equivalence. -/
theorem activePointSet_actFibers (g : Parameter n) (F : FiberPair n)
    (c : Bool) :
    activePointSet (actFibers g F) c =
      bitAffineEquiv g '' activePointSet F (actColor g c) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    let x := (pointEquiv g).symm z
    have hzx : actPoint g x = z := (pointEquiv g).apply_symm_apply z
    have hnew : ActiveMask (actFibers g F) c (actPoint g x) := by
      rwa [hzx]
    have hold : ActiveMask F (actColor g c) x :=
      (activeMask_actPoint_iff g F c x).1 hnew
    refine ⟨bitVec x, ⟨x, hold, rfl⟩, ?_⟩
    rw [← bitVec_actPoint]
    exact congrArg bitVec hzx
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨actPoint g x, (activeMask_actPoint_iff g F c x).2 hx, ?_⟩
    exact bitVec_actPoint g x

/-- Affine rank is invariant under any affine equivalence of the ambient
space. -/
theorem affineRank_image_affineEquiv
    (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) (S : Set (Fin n → ℝ)) :
    ActiveFace.affineRank (e '' S) = ActiveFace.affineRank S := by
  unfold ActiveFace.affineRank
  have hspan : (affineSpan ℝ S).map e.toAffineMap = affineSpan ℝ (e '' S) := by
    simpa only [AffineEquiv.coe_toAffineMap] using
      (AffineSubspace.map_span (f := e.toAffineMap) S)
  rw [← hspan, AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq e.linear (affineSpan ℝ S).direction

/-- Intrinsic active affine rank of one colour of a feasible fibre pair. -/
noncomputable def activeAffineRank (F : FiberPair n) (c : Bool) : ℕ :=
  ActiveFace.affineRank (activePointSet F c)

/-- The active affine rank is preserved, with the two ranks interchanged when
the logical colours are swapped. -/
theorem activeAffineRank_actFibers (g : Parameter n) (F : FiberPair n)
    (c : Bool) :
    activeAffineRank (actFibers g F) c =
      activeAffineRank F (actColor g c) := by
  unfold activeAffineRank
  rw [activePointSet_actFibers, affineRank_image_affineEquiv]

/-! ## Exact parameter counts for six qubits -/

/-- Parameters of the Boolean-cube isometry itself (before the separate
logical colour interchange). -/
abbrev IsometryParameter (n : ℕ) :=
  Equiv.Perm (Fin n) × SS.BitString n

/-- The structure used above is exactly an isometry parameter together with
one Boolean colour-swap flag. -/
def parameterEquiv (n : ℕ) :
    Parameter n ≃ IsometryParameter n × Bool where
  toFun g := ((g.perm, g.shift), g.swap)
  invFun g := ⟨g.1.1, g.1.2, g.2⟩
  left_inv := by intro g; cases g; rfl
  right_inv := by intro g; rcases g with ⟨⟨σ, t⟩, s⟩; rfl

/-- Symbolic cardinality of the cube-isometry parameters. -/
theorem isometryParameter_card (n : ℕ) :
    Fintype.card (IsometryParameter n) = n.factorial * 2 ^ n := by
  simp [IsometryParameter, Fintype.card_perm]

/-- Equation `six:eq:cubegroup`: there are exactly `2^6·6! = 46,080`
Boolean-cube isometries on six masks. -/
theorem six_cube_isometry_count :
    Fintype.card (IsometryParameter 6) = 46080 := by
  rw [isometryParameter_card]
  norm_num [Nat.factorial]

/-- The complete finite isometry list used before treating the colours as
unordered. -/
def allSixCubeIsometries : Finset (IsometryParameter 6) := Finset.univ

theorem allSixCubeIsometries_card : allSixCubeIsometries.card = 46080 := by
  simpa [allSixCubeIsometries] using six_cube_isometry_count

/-- Including the independent colour-swap flag doubles the enumeration.  This
separate theorem prevents confusing the `46,080` cube-isometry order with the
number of triples `(σ,t,swap)` used by `orbitKey`. -/
theorem six_colored_parameter_count : Fintype.card (Parameter 6) = 92160 := by
  calc
    Fintype.card (Parameter 6) =
        Fintype.card (IsometryParameter 6 × Bool) :=
      Fintype.card_congr (parameterEquiv 6)
    _ = Fintype.card (IsometryParameter 6) * Fintype.card Bool := by
      rw [Fintype.card_prod]
    _ = 46080 * 2 := by rw [six_cube_isometry_count]; norm_num
    _ = 92160 := by norm_num

end MainTheory.CubeAction
