import MainTheory.Levels
import MainTheory.CubeAction
import SixQubit.CodeEquiv

/-!
# Transport of exact distance-three completions along cube actions

The finite orbit directory acts on two-colour support pairs.  To use a paper
no-go theorem on a generated key, one must also transport the *actual quantum
states*, their norms, and the genuine Knill--Laflamme predicate.  Integer ids
or moment feasibility alone do not provide that bridge.

This file supplies the missing semantic transport.  The state action is the
inverse pullback of `CubeAction.pointEquiv`; it is exactly a physical-qubit
permutation followed by a common local `X` flip, with the optional colour swap
implemented as a logical-basis swap.  `CodeEquiv` then proves preservation of
the genuine `SS.HasDistance _ 3` predicate.
-/

namespace MainTheory.CubeCompletionTransport

open MainTheory.CubeAction

noncomputable section

/-- The Boolean colour corresponding to a two-dimensional logical index. -/
def finColor (k : Fin 2) : Bool := k.1 == 1

@[simp] theorem finColor_zero : finColor 0 = false := rfl
@[simp] theorem finColor_one : finColor 1 = true := rfl

@[simp] theorem finColor_swapIdx (b : Bool) (k : Fin 2) :
    finColor (SixQubit.CodeEquiv.swapIdx b k) = xor (finColor k) b := by
  cases b <;> fin_cases k <;> decide

/-- An exact ordered, normalized distance-three pair supported on `F`.
This is data, so it lives in `Type`; the proposition that no such data exist
is exposed separately as `NoCompletion`. -/
structure Completion {n : Nat} (F : FiberPair n) : Type where
  states : Fin 2 → SS.State n ℂ
  supported : ∀ k x, x ∉ F (finColor k) → states k x = 0
  normalized : ∀ k, SS.innerC (states k) (states k) = 1
  hasDistance : SS.HasDistance states 3

/-- Existence of exact normalized distance-three completion data. -/
def HasCompletion {n : Nat} (F : FiberPair n) : Prop := Nonempty (Completion F)

/-- There is no exact normalized distance-three completion supported on `F`. -/
def NoCompletion {n : Nat} (F : FiberPair n) : Prop := ¬ HasCompletion F

/-- Pull a state back through the inverse of the concrete cube isometry. -/
def pushState {n : Nat} (g : Parameter n) (psi : SS.State n ℂ) :
    SS.State n ℂ :=
  SixQubit.CodeEquiv.flipAct g.shift
    (SixQubit.CodeEquiv.permAct g.perm.symm psi)

@[simp] theorem pushState_apply {n : Nat} (g : Parameter n)
    (psi : SS.State n ℂ) (y : SS.BitString n) :
    pushState g psi y = psi ((pointEquiv g).symm y) := rfl

/-- Pullback by a cube bijection preserves the exact complex inner product. -/
theorem innerC_pushState {n : Nat} (g : Parameter n)
    (psi phi : SS.State n ℂ) :
    SS.innerC (pushState g psi) (pushState g phi) = SS.innerC psi phi := by
  unfold SS.innerC
  simp only [pushState_apply]
  exact Equiv.sum_comp (pointEquiv g).symm
    (fun x => star (psi x) * phi x)

/-- Apply the physical cube pullback and its matching logical colour swap. -/
def pushPair {n : Nat} (g : Parameter n) (p : Fin 2 → SS.State n ℂ) :
    Fin 2 → SS.State n ℂ :=
  fun k => pushState g (p (SixQubit.CodeEquiv.swapIdx g.swap k))

/-- **A cube move is a code equivalence.**

`pushPair` moves supports, norms and the Knill--Laflamme predicate, but nothing
said the move is one of the paper's own code equivalences.  It is: the cube
parameter is exactly a local monomial unitary with unit phases -- qubit
permutation `g.perm.symm`, local `X` string `g.shift` -- together with the
logical interchange `g.swap`.

The inverse permutation is not a slip.  `pushState` is the *pullback* through
`pointEquiv`, so it flips first and then permutes back, while `actPoint`
permutes first and then flips; the local monomial that matches it therefore
carries `g.perm.symm`. -/
theorem equivalent_pushPair {n : Nat} (g : Parameter n)
    (p : Fin 2 → SS.State n ℂ) :
    SixQubit.CodeEquiv.Equivalent p (pushPair g p) := by
  refine ⟨⟨g.perm.symm, g.shift, fun _ => 1, fun _ => 1, fun _ => by simp,
    fun _ => by simp⟩, fun _ => 1, g.swap, fun _ => by simp, ?_⟩
  intro k
  funext s
  simp only [pushPair, SixQubit.CodeEquiv.scal,
    SixQubit.CodeEquiv.LocalMonomial.act_apply, pushState_apply]
  simp [pointEquiv]

/-- Push an actual completion through the cube action.  The proof transports
support, both norm equations, and the genuine distance-three condition. -/
def pushCompletion {n : Nat} {F : FiberPair n}
    (W : Completion F) (g : Parameter n) : Completion (actFibers g F) where
  states := pushPair g W.states
  supported := by
    intro k y hy
    have hpre : (pointEquiv g).symm y ∉ F (actColor g (finColor k)) := by
      intro hx
      apply hy
      exact (mem_actFibers_iff g F (finColor k) y).2
        ⟨(pointEquiv g).symm y, hx, (pointEquiv g).apply_symm_apply y⟩
    have hpre' :
        (pointEquiv g).symm y ∉
          F (finColor (SixQubit.CodeEquiv.swapIdx g.swap k)) := by
      simpa only [finColor_swapIdx, actColor] using hpre
    change W.states (SixQubit.CodeEquiv.swapIdx g.swap k)
      ((pointEquiv g).symm y) = 0
    exact W.supported _ _ hpre'
  normalized := by
    intro k
    change SS.innerC
      (pushState g (W.states (SixQubit.CodeEquiv.swapIdx g.swap k)))
      (pushState g (W.states (SixQubit.CodeEquiv.swapIdx g.swap k))) = 1
    rw [innerC_pushState]
    exact W.normalized _
  hasDistance := by
    have hraw := (SixQubit.CodeEquiv.hasDistance_iff W.states).mp W.hasDistance
    have hswap := SixQubit.CodeEquiv.detectsRaw_swap g.swap hraw
    have hperm := SixQubit.CodeEquiv.detectsRaw_permAct g.perm.symm hswap
    have hflip := SixQubit.CodeEquiv.detectsRaw_flipAct g.shift hperm
    apply (SixQubit.CodeEquiv.hasDistance_iff (pushPair g W.states)).mpr
    simpa only [pushPair, pushState] using hflip

/-- Completion existence is invariant, in both directions, under every
generated cube action. -/
theorem completion_actFibers_iff {n : Nat} (g : Parameter n)
    (F : FiberPair n) :
    HasCompletion (actFibers g F) ↔ HasCompletion F := by
  constructor
  · rintro ⟨W⟩
    have Winv := pushCompletion W (inv g)
    exact ⟨by simpa using Winv⟩
  · rintro ⟨W⟩
    exact ⟨pushCompletion W g⟩

/-- A no-completion result transports across an actual fibre equivalence. -/
theorem not_completion_of_fiberEquivalent {n : Nat} {F G : FiberPair n}
    (hF : NoCompletion F) (hFG : FiberEquivalent F G) :
    NoCompletion G := by
  obtain ⟨g, rfl⟩ := hFG
  intro hG
  exact hF ((completion_actFibers_iff g F).mp hG)

/-- Completion existence transports in the forward direction across an actual
fibre equivalence. -/
theorem completion_of_fiberEquivalent {n : Nat} {F G : FiberPair n}
    (W : HasCompletion F) (hFG : FiberEquivalent F G) : HasCompletion G := by
  obtain ⟨W⟩ := W
  obtain ⟨g, hg⟩ := hFG
  exact ⟨by
    rw [← hg]
    exact pushCompletion W g⟩

/-- An empty paper `WImage` rules out an exact completion of the corresponding
literal support pair.  The enumerator itself is reconstructed from the
alleged completion, so emptiness is used semantically rather than as a label. -/
theorem not_completion_of_WImage_empty
    {q : Nat} [NeZero q] (av : Fin 6 → ZMod q) (r0 r1 : ZMod q)
    (F : FiberPair 6)
    (hF0 : (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = r0) = F false)
    (hF1 : (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = r1) = F true)
    (hEmpty : MainTheory.Levels.WImage av r0 r1 = ∅) :
    NoCompletion F := by
  rintro ⟨W⟩
  let A : Fin 7 → ℝ := fun j => SS.MacWilliams.Aco
    ![W.states 0, W.states 1] j / 4
  have hmem : A ∈ MainTheory.Levels.WImage av r0 r1 := by
    refine ⟨W.states 0, W.states 1, ?_, ?_, W.normalized 0,
      W.normalized 1, ?_, fun _ => rfl⟩
    · intro s hs
      apply W.supported 0 s
      change s ∉ F false
      rw [← hF0]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hs
    · intro s hs
      apply W.supported 1 s
      change s ∉ F true
      rw [← hF1]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hs
    · have hp : ![W.states 0, W.states 1] = W.states := by
        funext k
        fin_cases k <;> rfl
      rw [hp]
      exact W.hasDistance
  rw [hEmpty] at hmem
  exact hmem

/-- Conversely, every member of a paper `WImage` supplies an actual completion
of its literal support pair.  The enumerator coordinates are irrelevant to
this direction; the witnessing states, support equations, norms and genuine
distance predicate are retained. -/
theorem completion_of_mem_WImage
    {q : Nat} [NeZero q] (av : Fin 6 → ZMod q) (r0 r1 : ZMod q)
    (F : FiberPair 6)
    (hF0 : (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = r0) = F false)
    (hF1 : (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = r1) = F true)
    {A : Fin 7 → ℝ} (hA : A ∈ MainTheory.Levels.WImage av r0 r1) :
    HasCompletion F := by
  obtain ⟨c, d, hc, hd, hnc, hnd, hdist, _hcoeff⟩ := hA
  refine ⟨
    { states := ![c, d]
      supported := ?_
      normalized := ?_
      hasDistance := hdist }⟩
  · intro k x hx
    fin_cases k
    · apply hc x
      intro heq
      apply hx
      change x ∈ F false
      rw [← hF0]
      simp [heq]
    · apply hd x
      intro heq
      apply hx
      change x ∈ F true
      rw [← hF1]
      simp [heq]
  · intro k
    fin_cases k
    · exact hnc
    · exact hnd

end

end MainTheory.CubeCompletionTransport
