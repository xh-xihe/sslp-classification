import MainTheory.CubeCompletionTransport
import MainTheory.Generated.FiniteOrbitBase
import SixQubit.Orbit11Real
import SixQubit.Orbit22Real
import SixQubit.Orbit23Real

/-!
# The four remaining orbits are realized

`DirectoryOrbitStatus.openKeys = [0, 1, 2, 3]`, the paper's orbits `1, 2, 3`
and `4`, were the only directory keys with neither a no-go theorem nor a
completion.  The 20260822 draft left them open, and its Result III said only
that `62` of the `66` orbit *images* are settled.  The 20260902 revision makes
a stronger claim: `thm:six-15-sslp-realization-orbits` asserts that all
fifteen realization orbits, these four included, contain an exact physical
`((6,2,3))` code.  Their weight-enumerator images stay open
(`rem:four-open-orbits`); only nonemptiness is new.

Nonemptiness needs no new code.  `Completion` asks for support *inside* the
key's two fibres, not for equality with them, and the paper's own construction
file realizes orbits `1`--`4` from base codes it already uses elsewhere.  The
same thing is true here, key by key: the supports of three codes that this
repository has already certified as exact `((6,2,3))` codes sit inside the
four open keys' fibres.

* `key00` (paper orbit `1`) and `key01` (orbit `2`) are covered by
  `SixQubit.Orbit11Real`, the second with the two logical words interchanged;
* `key02` (orbit `3`) and `key03` (orbit `4`) by `SixQubit.Orbit22Real` and
  `SixQubit.Orbit23Real`.

This is exactly the phenomenon the construction file describes for orbit `1`:
a code can realize a moment orbit without occupying the full `32 + 32` fibres
of its moment skeleton, which is why distinct full-fibre moment orbits can
collapse once amplitudes are allowed to vanish.
-/

namespace MainTheory.OpenOrbitsRealized

open MainTheory
open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline
open MainTheory.Generated.FiniteOrbitBase

/-! ## Interchanging the two logical words -/

/-- Distance is symmetric in the two logical basis vectors: the
Knill--Laflamme scalar of a Pauli does not depend on their order. -/
theorem hasDistance_swap {c d : SS.State 6 ℂ}
    (h : SS.HasDistance ![c, d] 3) : SS.HasDistance ![d, c] 3 := by
  intro P hP
  obtain ⟨z, hz⟩ := h P hP
  refine ⟨z, ?_⟩
  intro j k
  fin_cases j <;> fin_cases k
  · simpa using hz 1 1
  · simpa using hz 1 0
  · simpa using hz 0 1
  · simpa using hz 0 0

/-! ## Key 00: paper orbit 1 -/

set_option maxRecDepth 100000 in
theorem orbit11_L0_in_key00_mask0 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit11Real.L0 →
      x ∈ fiberOfMask key00.mask0 := by decide

set_option maxRecDepth 100000 in
theorem orbit11_L1_in_key00_mask1 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit11Real.L1 →
      x ∈ fiberOfMask key00.mask1 := by decide

theorem keyAt00_eq : keyAt 0 = key00 := by decide

/-- **Paper orbit 1 is realized.** -/
theorem key00_hasCompletion : HasCompletion (keyAt 0).fibers := by
  rw [keyAt00_eq]
  refine ⟨{ states := ![SixQubit.Orbit11Real.w0, SixQubit.Orbit11Real.w1]
          , supported := ?_, normalized := ?_, hasDistance := ?_ }⟩
  · intro k x hx
    fin_cases k
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit11Real.c0z_vanishes x
        (fun hmem => hx (orbit11_L0_in_key00_mask0 x hmem))
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit11Real.c1z_vanishes x
        (fun hmem => hx (orbit11_L1_in_key00_mask1 x hmem))
  · intro k
    fin_cases k
    · exact SixQubit.Orbit11Real.w0_normalized
    · exact SixQubit.Orbit11Real.w1_normalized
  · exact SixQubit.Orbit11Real.is_code

/-! ## Key 01: paper orbit 2, with the words interchanged -/

set_option maxRecDepth 100000 in
theorem orbit11_L1_in_key01_mask0 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit11Real.L1 →
      x ∈ fiberOfMask key01.mask0 := by decide

set_option maxRecDepth 100000 in
theorem orbit11_L0_in_key01_mask1 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit11Real.L0 →
      x ∈ fiberOfMask key01.mask1 := by decide

theorem keyAt01_eq : keyAt 1 = key01 := by decide

/-- **Paper orbit 2 is realized.** -/
theorem key01_hasCompletion : HasCompletion (keyAt 1).fibers := by
  rw [keyAt01_eq]
  refine ⟨{ states := ![SixQubit.Orbit11Real.w1, SixQubit.Orbit11Real.w0]
          , supported := ?_, normalized := ?_, hasDistance := ?_ }⟩
  · intro k x hx
    fin_cases k
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit11Real.c1z_vanishes x
        (fun hmem => hx (orbit11_L1_in_key01_mask0 x hmem))
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit11Real.c0z_vanishes x
        (fun hmem => hx (orbit11_L0_in_key01_mask1 x hmem))
  · intro k
    fin_cases k
    · exact SixQubit.Orbit11Real.w1_normalized
    · exact SixQubit.Orbit11Real.w0_normalized
  · exact hasDistance_swap SixQubit.Orbit11Real.is_code

/-! ## Key 02: paper orbit 3 -/

set_option maxRecDepth 100000 in
theorem orbit22_L0_in_key02_mask0 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit22Real.L0 →
      x ∈ fiberOfMask key02.mask0 := by decide

set_option maxRecDepth 100000 in
theorem orbit22_L1_in_key02_mask1 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit22Real.L1 →
      x ∈ fiberOfMask key02.mask1 := by decide

theorem keyAt02_eq : keyAt 2 = key02 := by decide

/-- **Paper orbit 3 is realized.** -/
theorem key02_hasCompletion : HasCompletion (keyAt 2).fibers := by
  rw [keyAt02_eq]
  refine ⟨{ states := ![SixQubit.Orbit22Real.w0, SixQubit.Orbit22Real.w1]
          , supported := ?_, normalized := ?_, hasDistance := ?_ }⟩
  · intro k x hx
    fin_cases k
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit22Real.c0z_vanishes x
        (fun hmem => hx (orbit22_L0_in_key02_mask0 x hmem))
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit22Real.c1z_vanishes x
        (fun hmem => hx (orbit22_L1_in_key02_mask1 x hmem))
  · intro k
    fin_cases k
    · exact SixQubit.Orbit22Real.w0_normalized
    · exact SixQubit.Orbit22Real.w1_normalized
  · exact SixQubit.Orbit22Real.is_code

/-! ## Key 03: paper orbit 4, with the words interchanged -/

set_option maxRecDepth 100000 in
theorem orbit23_L1_in_key03_mask0 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit23Real.L1 →
      x ∈ fiberOfMask key03.mask0 := by decide

set_option maxRecDepth 100000 in
theorem orbit23_L0_in_key03_mask1 :
    ∀ x : SS.BitString 6, x ∈ SixQubit.Orbit23Real.L0 →
      x ∈ fiberOfMask key03.mask1 := by decide

theorem keyAt03_eq : keyAt 3 = key03 := by decide

/-- **Paper orbit 4 is realized.** -/
theorem key03_hasCompletion : HasCompletion (keyAt 3).fibers := by
  rw [keyAt03_eq]
  refine ⟨{ states := ![SixQubit.Orbit23Real.w1, SixQubit.Orbit23Real.w0]
          , supported := ?_, normalized := ?_, hasDistance := ?_ }⟩
  · intro k x hx
    fin_cases k
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit23Real.c1z_vanishes x
        (fun hmem => hx (orbit23_L1_in_key03_mask0 x hmem))
    · exact SixQubit.Realize.stC_vanishes _ _ _
        SixQubit.Orbit23Real.c0z_vanishes x
        (fun hmem => hx (orbit23_L0_in_key03_mask1 x hmem))
  · intro k
    fin_cases k
    · exact SixQubit.Orbit23Real.w1_normalized
    · exact SixQubit.Orbit23Real.w0_normalized
  · exact hasDistance_swap SixQubit.Orbit23Real.is_code

/-! ## All four -/

/-- **The four previously open keys all admit an exact completion.** -/
theorem openKeys_hasCompletion :
    HasCompletion (keyAt 0).fibers ∧ HasCompletion (keyAt 1).fibers ∧
      HasCompletion (keyAt 2).fibers ∧ HasCompletion (keyAt 3).fibers :=
  ⟨key00_hasCompletion, key01_hasCompletion,
    key02_hasCompletion, key03_hasCompletion⟩

end MainTheory.OpenOrbitsRealized
