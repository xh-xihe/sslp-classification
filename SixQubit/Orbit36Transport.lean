import Mathlib

import SixQubit.CodeOrbit36

/-!
# Kernel transport for the table representative of orbit 36

The rigidity proof in `SixQubit.CodeOrbit36` is carried out in the symmetric
gauge

```
  a* = (1,1,1,1,2,3),       (S_0,S_4).
```

The representative printed in the classification table is instead

```
  a = (1,1,1,2,2,4),        (S_0,S_1).
```

This file closes that change-of-representative gap in the Lean kernel.  Flip
the last coefficient-`2` coordinate and the coefficient-`4` coordinate.  The
signed vector is then `(1,1,1,2,3,1)` and the residue is shifted by `1`.
Finally cycle the last three coordinates to obtain `a*`.  Consequently the
old residue-`1` word becomes the new residue-`0` word and the old residue-`0`
word becomes the new residue-`4` word; the logical words are interchanged.

All finite identities below use kernel `decide`.  In particular, neither the
Python orbit manifest nor a precomputed support list is trusted for the
transport.
-/

namespace SixQubit.Orbit36Transport

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## 1. The original table representative -/

/-- The angle vector printed for orbit 36 in the classification table. -/
def originalAv : Fin 6 → ZMod 5 := ![1, 1, 1, 2, 2, 4]

/-- The full residue-`0` fiber of the table representative. -/
def originalS0 : Finset (SS.BitString 6) :=
  Finset.univ.filter (fun x => SS.weight originalAv x = 0)

/-- The full residue-`1` fiber of the table representative. -/
def originalS1 : Finset (SS.BitString 6) :=
  Finset.univ.filter (fun x => SS.weight originalAv x = 1)

theorem originalS0_card : originalS0.card = 12 := by decide
theorem originalS1_card : originalS1.card = 12 := by decide

/-! ## 2. The affine cube isometry -/

/--
The coordinate relabelling used by `CodeEquiv.permStr`.  Its values mean

```
 old coordinate : 0 1 2 3 4 5
 new coordinate : 0 1 2 4 5 3.
```

Thus the coefficient vector `(1,1,1,2,3,1)` becomes
`(1,1,1,1,2,3)` in the new coordinates.
-/
def perm : Equiv.Perm (Fin 6) :=
  ⟨![0, 1, 2, 4, 5, 3], ![0, 1, 2, 5, 3, 4], by decide, by decide⟩

/-- In the new coordinates, flip positions `3` and `5`. -/
def flipMask : SS.BitString 6 := ![false, false, false, true, false, true]

/-- The old basis string read at a new-gauge basis string. -/
def transportStr (s : SS.BitString 6) : SS.BitString 6 :=
  CodeEquiv.permStr perm (SS.bxor s flipMask)

/-- `transportStr` as an honest equivalence of the 64 basis strings. -/
def transportEquiv : SS.BitString 6 ≃ SS.BitString 6 :=
  (SS.bxorEquiv flipMask).trans (CodeEquiv.permStrEquiv perm)

@[simp] theorem transportEquiv_apply (s : SS.BitString 6) :
    transportEquiv s = transportStr s := rfl

/-- The exact residue-shift identity, checked on all 64 strings by the kernel. -/
theorem weight_transport (s : SS.BitString 6) :
    SS.weight originalAv (transportStr s) = SS.weight Orbit36.av s + 1 := by
  revert s
  decide

/-- Old residue `0` is exactly new residue `4`. -/
theorem transport_mem_originalS0_iff (s : SS.BitString 6) :
    transportStr s ∈ originalS0 ↔ s ∈ Orbit36.S1 := by
  revert s
  decide

/-- Old residue `1` is exactly new residue `0`. -/
theorem transport_mem_originalS1_iff (s : SS.BitString 6) :
    transportStr s ∈ originalS1 ↔ s ∈ Orbit36.S0 := by
  revert s
  decide

/-- Finset form of the first exact preimage statement. -/
theorem preimage_originalS0 :
    Finset.univ.filter (fun s => transportStr s ∈ originalS0) = Orbit36.S1 := by
  decide

/-- Finset form of the second exact preimage statement. -/
theorem preimage_originalS1 :
    Finset.univ.filter (fun s => transportStr s ∈ originalS1) = Orbit36.S0 := by
  decide

/-! ## 3. The physical and logical action -/

/-- The local physical unitary: the above permutation followed by the two
local `X` gates.  All diagonal entries are `1`. -/
def physical : CodeEquiv.LocalMonomial 6 where
  perm := perm
  flip := flipMask
  al := fun _ => 1
  be := fun _ => 1
  al_unit := fun _ => by simp
  be_unit := fun _ => by simp

@[simp] theorem physical_act_apply (ψ : SS.State 6 ℂ) (s : SS.BitString 6) :
    physical.act ψ s = ψ (transportStr s) := by
  simp [physical, CodeEquiv.LocalMonomial.act_apply, transportStr]

/-- The old logical residue-`1` word is the new bottom word. -/
def bottom (_c d : SS.State 6 ℂ) : SS.State 6 ℂ := physical.act d

/-- The old logical residue-`0` word is the new top word. -/
def top (c _d : SS.State 6 ℂ) : SS.State 6 ℂ := physical.act c

@[simp] theorem bottom_apply (c d : SS.State 6 ℂ) (s : SS.BitString 6) :
    bottom c d s = d (transportStr s) := by
  simp [bottom]

@[simp] theorem top_apply (c d : SS.State 6 ℂ) (s : SS.BitString 6) :
    top c d s = c (transportStr s) := by
  simp [top]

/-- The complete operation (physical transform plus logical interchange) is an
instance of the code-equivalence relation used by the rigidity theorem. -/
theorem equivalent_transport (c d : SS.State 6 ℂ) :
    CodeEquiv.Equivalent ![c, d] ![bottom c d, top c d] := by
  refine ⟨physical, (fun _ => 1), true, (fun _ => by simp), ?_⟩
  intro k
  fin_cases k <;> funext s <;>
    simp [bottom, top, CodeEquiv.scal, CodeEquiv.swapIdx]

/-! ## 4. Support, norm and distance transport -/

theorem bottom_vanishes (c d : SS.State 6 ℂ)
    (hd : ∀ y, y ∉ originalS1 → d y = 0) :
    ∀ s, s ∉ Orbit36.S0 → bottom c d s = 0 := by
  intro s hs
  rw [bottom_apply]
  exact hd _ (fun hmem => hs ((transport_mem_originalS1_iff s).mp hmem))

theorem top_vanishes (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ originalS0 → c x = 0) :
    ∀ s, s ∉ Orbit36.S1 → top c d s = 0 := by
  intro s hs
  rw [top_apply]
  exact hc _ (fun hmem => hs ((transport_mem_originalS0_iff s).mp hmem))

/-- The affine basis relabelling preserves the Hermitian inner product. -/
theorem inner_physical (ψ φ : SS.State 6 ℂ) :
    SS.innerC (physical.act ψ) (physical.act φ) = SS.innerC ψ φ := by
  unfold SS.innerC
  rw [← Equiv.sum_comp transportEquiv (fun s => star (ψ s) * φ s)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp

theorem bottom_norm (c d : SS.State 6 ℂ) (hnd : SS.innerC d d = 1) :
    SS.innerC (bottom c d) (bottom c d) = 1 := by
  rw [bottom, inner_physical, hnd]

theorem top_norm (c d : SS.State 6 ℂ) (hnc : SS.innerC c c = 1) :
    SS.innerC (top c d) (top c d) = 1 := by
  rw [top, inner_physical, hnc]

theorem transported_hasDistance (c d : SS.State 6 ℂ)
    (hdist : SS.HasDistance ![c, d] 3) :
    SS.HasDistance ![bottom c d, top c d] 3 :=
  CodeEquiv.hasDistance_of_equivalent (equivalent_transport c d) hdist

/-! ## 5. A non-vacuous code on the original table fibers -/

/-- Pull the canonical symmetric top word back to the original residue-`0`
fiber. -/
def originalCanonicalC (x : SS.BitString 6) : ℂ :=
  Orbit36Code.d36 (transportEquiv.symm x)

/-- Pull the canonical symmetric bottom word back to the original residue-`1`
fiber. -/
def originalCanonicalD (x : SS.BitString 6) : ℂ :=
  Orbit36Code.c36 (transportEquiv.symm x)

theorem bottom_originalCanonical :
    bottom originalCanonicalC originalCanonicalD = Orbit36Code.c36 := by
  funext s
  rw [bottom_apply]
  simp [originalCanonicalD, ← transportEquiv_apply]

theorem top_originalCanonical :
    top originalCanonicalC originalCanonicalD = Orbit36Code.d36 := by
  funext s
  rw [top_apply]
  simp [originalCanonicalC, ← transportEquiv_apply]

theorem originalCanonicalC_vanishes :
    ∀ x, x ∉ originalS0 → originalCanonicalC x = 0 := by
  intro x hx
  apply Orbit36Code.d36_vanishes_off_S1
  intro hs
  apply hx
  let s := transportEquiv.symm x
  have htau : transportStr s = x := by
    change transportEquiv s = x
    exact transportEquiv.apply_symm_apply x
  have hsold : transportStr s ∈ originalS0 :=
    (transport_mem_originalS0_iff s).mpr (by simpa only [s] using hs)
  simpa only [htau] using hsold

theorem originalCanonicalD_vanishes :
    ∀ x, x ∉ originalS1 → originalCanonicalD x = 0 := by
  intro x hx
  apply Orbit36Code.c36_vanishes_off_S0
  intro hs
  apply hx
  let s := transportEquiv.symm x
  have htau : transportStr s = x := by
    change transportEquiv s = x
    exact transportEquiv.apply_symm_apply x
  have hsold : transportStr s ∈ originalS1 :=
    (transport_mem_originalS1_iff s).mpr (by simpa only [s] using hs)
  simpa only [htau] using hsold

theorem originalCanonicalC_normalized :
    SS.innerC originalCanonicalC originalCanonicalC = 1 := by
  calc
    SS.innerC originalCanonicalC originalCanonicalC =
        SS.innerC (physical.act originalCanonicalC) (physical.act originalCanonicalC) :=
      (inner_physical _ _).symm
    _ = SS.innerC Orbit36Code.d36 Orbit36Code.d36 := by
      rw [show physical.act originalCanonicalC = top originalCanonicalC originalCanonicalD
        from rfl, top_originalCanonical]
    _ = 1 := Orbit36Code.d36_normalized

theorem originalCanonicalD_normalized :
    SS.innerC originalCanonicalD originalCanonicalD = 1 := by
  calc
    SS.innerC originalCanonicalD originalCanonicalD =
        SS.innerC (physical.act originalCanonicalD) (physical.act originalCanonicalD) :=
      (inner_physical _ _).symm
    _ = SS.innerC Orbit36Code.c36 Orbit36Code.c36 := by
      rw [show physical.act originalCanonicalD = bottom originalCanonicalC originalCanonicalD
        from rfl, bottom_originalCanonical]
    _ = 1 := Orbit36Code.c36_normalized

/-- The pulled-back table representative satisfies every genuine
weight-at-most-two Knill--Laflamme equation. -/
theorem originalCanonical_is_code :
    SS.HasDistance ![originalCanonicalC, originalCanonicalD] 3 := by
  have hE := equivalent_transport originalCanonicalC originalCanonicalD
  apply (CodeEquiv.hasDistance_iff_of_equivalent hE).mpr
  simpa only [bottom_originalCanonical, top_originalCanonical] using
    Orbit36Code.canonical_is_code

/-- Orbit 36 is nonempty already at the exact representative printed in the
table, not merely after an externally checked change of gauge. -/
theorem original_table_nonempty :
    ∃ c d : SS.State 6 ℂ,
      (∀ x, x ∉ originalS0 → c x = 0)
        ∧ (∀ y, y ∉ originalS1 → d y = 0)
        ∧ SS.innerC c c = 1
        ∧ SS.innerC d d = 1
        ∧ SS.HasDistance ![c, d] 3 := by
  exact ⟨originalCanonicalC, originalCanonicalD,
    originalCanonicalC_vanishes, originalCanonicalD_vanishes,
    originalCanonicalC_normalized, originalCanonicalD_normalized,
    originalCanonical_is_code⟩

/-! ## 6. Application of the existing kernel rigidity theorem -/

/-- Every exact code on the two *original table fibers* transports to a code
on the two symmetric fibers to which `O36.rigid_code` applies. -/
theorem transported_equivalent_canonical (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ originalS0 → c x = 0)
    (hd : ∀ y, y ∉ originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    CodeEquiv.Equivalent ![bottom c d, top c d]
      ![Orbit36Code.c36, Orbit36Code.d36] := by
  have hr := Orbit36.rigid_code (bottom c d) (top c d)
    (bottom_vanishes c d hd) (top_vanishes c d hc)
    (bottom_norm c d hnd) (top_norm c d hnc)
    (transported_hasDistance c d hdist)
  exact hr.2.2.1

/-- The magnitude conclusion of rigidity, stated back on the *original* table
fibers.  `transportStr yᵢ` and `transportStr zᵢ` are old-gauge basis strings,
so no informal relabelling remains in this statement. -/
def OriginalMagnitudes (c d : SS.State 6 ℂ) : Prop :=
    Complex.normSq (d (transportStr Orbit36.y0)) = 1/10
      ∧ Complex.normSq (d (transportStr Orbit36.y1)) = 1/10
      ∧ Complex.normSq (d (transportStr Orbit36.y2)) = 1/10
      ∧ Complex.normSq (d (transportStr Orbit36.y3)) = 1/10
      ∧ Complex.normSq (d (transportStr Orbit36.y4)) = 1/10
      ∧ Complex.normSq (d (transportStr Orbit36.y5)) = 1/10
      ∧ Complex.normSq (d (transportStr Orbit36.y6)) = 1/15
      ∧ Complex.normSq (d (transportStr Orbit36.y7)) = 1/15
      ∧ Complex.normSq (d (transportStr Orbit36.y8)) = 1/15
      ∧ Complex.normSq (d (transportStr Orbit36.y9)) = 1/15
      ∧ Complex.normSq (d (transportStr Orbit36.y10)) = 1/15
      ∧ Complex.normSq (d (transportStr Orbit36.y11)) = 1/15
      ∧ Complex.normSq (c (transportStr Orbit36.z0)) = 1/10
      ∧ Complex.normSq (c (transportStr Orbit36.z1)) = 1/10
      ∧ Complex.normSq (c (transportStr Orbit36.z2)) = 1/10
      ∧ Complex.normSq (c (transportStr Orbit36.z3)) = 1/10
      ∧ Complex.normSq (c (transportStr Orbit36.z4)) = 1/10
      ∧ Complex.normSq (c (transportStr Orbit36.z5)) = 1/10
      ∧ Complex.normSq (c (transportStr Orbit36.z6)) = 1/15
      ∧ Complex.normSq (c (transportStr Orbit36.z7)) = 1/15
      ∧ Complex.normSq (c (transportStr Orbit36.z8)) = 1/15
      ∧ Complex.normSq (c (transportStr Orbit36.z9)) = 1/15
      ∧ Complex.normSq (c (transportStr Orbit36.z10)) = 1/15
      ∧ Complex.normSq (c (transportStr Orbit36.z11)) = 1/15

theorem original_magnitudes (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ originalS0 → c x = 0)
    (hd : ∀ y, y ∉ originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : OriginalMagnitudes c d := by
  have hr := Orbit36.rigid_code (bottom c d) (top c d)
    (bottom_vanishes c d hd) (top_vanishes c d hc)
    (bottom_norm c d hnd) (top_norm c d hnc)
    (transported_hasDistance c d hdist)
  simpa only [OriginalMagnitudes, bottom_apply, top_apply] using hr.1

/-- Rigidity also proves that no boundary point of either original table fiber
survives: support containment upgrades to equality with the full fibers. -/
def OriginalFullSupport (c d : SS.State 6 ℂ) : Prop :=
  (∀ x, c x ≠ 0 ↔ x ∈ originalS0) ∧ (∀ y, d y ≠ 0 ↔ y ∈ originalS1)

theorem original_full_support (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ originalS0 → c x = 0)
    (hd : ∀ y, y ∉ originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : OriginalFullSupport c d := by
  dsimp only [OriginalFullSupport]
  have hr := Orbit36.rigid_code (bottom c d) (top c d)
    (bottom_vanishes c d hd) (top_vanishes c d hc)
    (bottom_norm c d hnd) (top_norm c d hnc)
    (transported_hasDistance c d hdist)
  rcases hr.2.1 with
    ⟨hby0, hby1, hby2, hby3, hby4, hby5, hby6, hby7, hby8, hby9, hby10, hby11,
      htz0, htz1, htz2, htz3, htz4, htz5, htz6, htz7, htz8, htz9, htz10, htz11⟩
  have hbot : ∀ s ∈ Orbit36.S0, bottom c d s ≠ 0 := by
    intro s hs
    simp only [Orbit36.S0, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hby0
    · exact hby1
    · exact hby2
    · exact hby3
    · exact hby4
    · exact hby5
    · exact hby6
    · exact hby7
    · exact hby8
    · exact hby9
    · exact hby10
    · exact hby11
  have htop : ∀ s ∈ Orbit36.S1, top c d s ≠ 0 := by
    intro s hs
    simp only [Orbit36.S1, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact htz0
    · exact htz1
    · exact htz2
    · exact htz3
    · exact htz4
    · exact htz5
    · exact htz6
    · exact htz7
    · exact htz8
    · exact htz9
    · exact htz10
    · exact htz11
  constructor
  · intro x
    constructor
    · intro hx
      by_contra hmem
      exact hx (hc x hmem)
    · intro hmem
      let s := transportEquiv.symm x
      have htau : transportStr s = x := by
        change transportEquiv s = x
        exact transportEquiv.apply_symm_apply x
      have hsold : transportStr s ∈ originalS0 := by simpa only [htau] using hmem
      have hsnew : s ∈ Orbit36.S1 := (transport_mem_originalS0_iff s).mp hsold
      have hs := htop s hsnew
      rw [top_apply, htau] at hs
      exact hs
  · intro y
    constructor
    · intro hy
      by_contra hmem
      exact hy (hd y hmem)
    · intro hmem
      let s := transportEquiv.symm y
      have htau : transportStr s = y := by
        change transportEquiv s = y
        exact transportEquiv.apply_symm_apply y
      have hsold : transportStr s ∈ originalS1 := by simpa only [htau] using hmem
      have hsnew : s ∈ Orbit36.S0 := (transport_mem_originalS1_iff s).mp hsold
      have hs := hbot s hsnew
      rw [bottom_apply, htau] at hs
      exact hs

/-- The transported code has exactly the normalized A-enumerator proved by
the orbit-36 rigidity theorem. -/
theorem transported_AEnum (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ originalS0 → c x = 0)
    (hd : ∀ y, y ∉ originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    Orbit36Phase.AEnum (bottom c d) (top c d) 0 = 1
      ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 1 = 0
      ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 2 = 21/25
      ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 3 = 0
      ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 4 = 291/25
      ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 5 = 384/25
      ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 6 = 79/25 := by
  have hr := Orbit36.rigid_code (bottom c d) (top c d)
    (bottom_vanishes c d hd) (top_vanishes c d hc)
    (bottom_norm c d hnd) (top_norm c d hnc)
    (transported_hasDistance c d hdist)
  exact hr.2.2.2.2

/-- A compact end-to-end bridge statement: the table representative is
kernel-equivalent to the symmetric representative, the latter is
kernel-equivalent to the canonical code, and it has the claimed enumerator. -/
theorem table_representative_certified (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ originalS0 → c x = 0)
    (hd : ∀ y, y ∉ originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    CodeEquiv.Equivalent ![c, d] ![bottom c d, top c d]
      ∧ CodeEquiv.Equivalent ![bottom c d, top c d]
          ![Orbit36Code.c36, Orbit36Code.d36]
      ∧ SS.HasDistance ![bottom c d, top c d] 3
      ∧ (Orbit36Phase.AEnum (bottom c d) (top c d) 0 = 1
        ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 1 = 0
        ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 2 = 21/25
        ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 3 = 0
        ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 4 = 291/25
        ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 5 = 384/25
        ∧ Orbit36Phase.AEnum (bottom c d) (top c d) 6 = 79/25) := by
  exact ⟨equivalent_transport c d,
    transported_equivalent_canonical c d hc hd hnc hnd hdist,
    transported_hasDistance c d hdist,
    transported_AEnum c d hc hd hnc hnd hdist⟩

end

end SixQubit.Orbit36Transport
