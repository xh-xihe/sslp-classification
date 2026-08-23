import SixQubit.BEnumerator
import SixQubit.CodeEquivEnum
import SixQubit.Orbit36Transport

/-!
# Orbit 36 from the table representative, end to end

`SixQubit.Orbit36Transport` proves the finite change of gauge from the angle
vector printed in the classification table to the symmetric gauge used by the
rigidity argument.  This file closes the two remaining interfaces:

* the two physical Clifford operations and the logical interchange preserve
  both Shor--Laflamme enumerators;
* the two concrete `Equivalent` witnesses compose.

Consequently the final theorem is stated directly for
`a = (1,1,1,2,2,4)` and its residue-`0`/residue-`1` fibers.  Its only
hypotheses are support, normalization and the genuine distance-three
Knill--Laflamme predicate.

No `sorry`, no `native_decide`.
-/

namespace SixQubit.Orbit36Certified

open SS.MacWilliams

noncomputable section

/-! ## 1. Enumerator transport for the fixed table-to-symmetric map -/

lemma physical_act_eq (psi : SS.State 6 ℂ) :
    Orbit36Transport.physical.act psi = CodeEquiv.flipAct Orbit36Transport.flipMask
      (CodeEquiv.permAct Orbit36Transport.perm psi) := by
  funext s
  rw [Orbit36Transport.physical_act_apply]
  rfl

lemma transported_family_eq (c d : SS.State 6 ℂ) :
    ![Orbit36Transport.bottom c d, Orbit36Transport.top c d] =
      fun k => CodeEquiv.flipAct Orbit36Transport.flipMask
        (CodeEquiv.permAct Orbit36Transport.perm
          ((![c, d] : Fin 2 → SS.State 6 ℂ) (CodeEquiv.swapIdx true k))) := by
  funext k
  fin_cases k <;>
    simp [CodeEquiv.swapIdx, Orbit36Transport.bottom, Orbit36Transport.top,
      physical_act_eq]

/-- The unnormalised `A` coefficients are unchanged by the explicit physical
permutation, the two local `X` gates and the logical-word interchange. -/
theorem Aco_transport (c d : SS.State 6 ℂ) (j : ℕ) :
    Aco ![Orbit36Transport.bottom c d, Orbit36Transport.top c d] j =
      Aco ![c, d] j := by
  rw [transported_family_eq]
  calc
    Aco (fun k => CodeEquiv.flipAct Orbit36Transport.flipMask
        (CodeEquiv.permAct Orbit36Transport.perm
          ((![c, d] : Fin 2 → SS.State 6 ℂ) (CodeEquiv.swapIdx true k)))) j
        = Aco (fun k => CodeEquiv.permAct Orbit36Transport.perm
            ((![c, d] : Fin 2 → SS.State 6 ℂ) (CodeEquiv.swapIdx true k))) j :=
          CodeEquiv.Aco_flipAct Orbit36Transport.flipMask _ j
    _ = Aco (fun k => (![c, d] : Fin 2 → SS.State 6 ℂ)
        (CodeEquiv.swapIdx true k)) j :=
          CodeEquiv.Aco_permAct Orbit36Transport.perm _ j
    _ = Aco ![c, d] j := CodeEquiv.Aco_swap ![c, d] true j

/-- The unnormalised `B` coefficients obey the same exact transport. -/
theorem Bco_transport (c d : SS.State 6 ℂ) (j : ℕ) :
    Bco ![Orbit36Transport.bottom c d, Orbit36Transport.top c d] j =
      Bco ![c, d] j := by
  rw [transported_family_eq]
  calc
    Bco (fun k => CodeEquiv.flipAct Orbit36Transport.flipMask
        (CodeEquiv.permAct Orbit36Transport.perm
          ((![c, d] : Fin 2 → SS.State 6 ℂ) (CodeEquiv.swapIdx true k)))) j
        = Bco (fun k => CodeEquiv.permAct Orbit36Transport.perm
            ((![c, d] : Fin 2 → SS.State 6 ℂ) (CodeEquiv.swapIdx true k))) j :=
          CodeEquiv.Bco_flipAct Orbit36Transport.flipMask _ j
    _ = Bco (fun k => (![c, d] : Fin 2 → SS.State 6 ℂ)
        (CodeEquiv.swapIdx true k)) j :=
          CodeEquiv.Bco_permAct Orbit36Transport.perm _ j
    _ = Bco ![c, d] j := CodeEquiv.Bco_swap ![c, d] true j

/-! ## 2. The exact rational enumerator pair -/

/-- Four times the manuscript's unique orbit-36 `A` vector. -/
def IsOrbit36A (psi : Fin 2 → SS.State 6 ℂ) : Prop :=
  Aco psi 0 = 4 ∧ Aco psi 1 = 0 ∧ Aco psi 2 = 84/25 ∧ Aco psi 3 = 0 ∧
    Aco psi 4 = 1164/25 ∧ Aco psi 5 = 1536/25 ∧ Aco psi 6 = 316/25

/-- Four times the manuscript's unique orbit-36 `B` vector. -/
def IsOrbit36B (psi : Fin 2 → SS.State 6 ℂ) : Prop :=
  Bco psi 0 = 4 ∧ Bco psi 1 = 0 ∧ Bco psi 2 = 84/25 ∧
    Bco psi 3 = 2336/25 ∧ Bco psi 4 = 732/5 ∧
    Bco psi 5 = 3936/25 ∧ Bco psi 6 = 2684/25

/-- The full quantum MacWilliams transform at the orbit-36 rational point. -/
theorem orbit36B_of_A (psi : Fin 2 → SS.State 6 ℂ)
    (hA : IsOrbit36A psi) : IsOrbit36B psi := by
  rcases hA with ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩
  rcases bco_transform_six psi with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  dsimp only [IsOrbit36B]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The unique `A` vector, now stated directly on an arbitrary code supported
in the two fibers of the table representative. -/
theorem original_A (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ Orbit36Transport.originalS0 → c x = 0)
    (hd : ∀ y, y ∉ Orbit36Transport.originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    IsOrbit36A ![c, d] := by
  rcases Orbit36Transport.transported_AEnum c d hc hd hnc hnd hdist with
    ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have hscale (j : ℕ) : Aco ![c, d] j =
      4 * Orbit36Phase.AEnum (Orbit36Transport.bottom c d)
        (Orbit36Transport.top c d) j := by
    calc
      Aco ![c, d] j =
          Aco ![Orbit36Transport.bottom c d, Orbit36Transport.top c d] j :=
        (Aco_transport c d j).symm
      _ = 4 * Orbit36Phase.AEnum (Orbit36Transport.bottom c d)
          (Orbit36Transport.top c d) j := Orbit36MacWilliams.Aco_pair _ _ _
  dsimp only [IsOrbit36A]
  exact ⟨by rw [hscale 0, h0]; norm_num,
    by rw [hscale 1, h1]; norm_num,
    by rw [hscale 2, h2]; norm_num,
    by rw [hscale 3, h3]; norm_num,
    by rw [hscale 4, h4]; norm_num,
    by rw [hscale 5, h5]; norm_num,
    by rw [hscale 6, h6]; norm_num⟩

/-- The exact `A`/`B` enumerator pair on the original table representative. -/
theorem original_enumerator_pair (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ Orbit36Transport.originalS0 → c x = 0)
    (hd : ∀ y, y ∉ Orbit36Transport.originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    IsOrbit36A ![c, d] ∧ IsOrbit36B ![c, d] := by
  have hA := original_A c d hc hd hnc hnd hdist
  exact ⟨hA, orbit36B_of_A _ hA⟩

/-! ## 3. The direct code-level rigidity theorem -/

/-- The two concrete equivalences compose, so the code on the table fibers is
directly equivalent to the canonical code. -/
theorem original_equivalent_canonical (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ Orbit36Transport.originalS0 → c x = 0)
    (hd : ∀ y, y ∉ Orbit36Transport.originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    CodeEquiv.Equivalent ![c, d]
      ![Orbit36Code.c36, Orbit36Code.d36] :=
  CodeEquiv.Equivalent.trans (Orbit36Transport.equivalent_transport c d)
    (Orbit36Transport.transported_equivalent_canonical c d hc hd hnc hnd hdist)

/-- **Fully kernel-certified rigidity for the representative printed in the
orbit table.**  Magnitudes, absence of boundary support, the single
local-monomial class, and both Shor--Laflamme enumerators all follow from the
code-level hypotheses alone. -/
theorem table_representative_rigid (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ Orbit36Transport.originalS0 → c x = 0)
    (hd : ∀ y, y ∉ Orbit36Transport.originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    Orbit36Transport.OriginalMagnitudes c d
      ∧ Orbit36Transport.OriginalFullSupport c d
      ∧ CodeEquiv.Equivalent ![c, d]
        ![Orbit36Code.c36, Orbit36Code.d36]
      ∧ IsOrbit36A ![c, d]
      ∧ IsOrbit36B ![c, d] := by
  have hE := original_equivalent_canonical c d hc hd hnc hnd hdist
  have hAB := original_enumerator_pair c d hc hd hnc hnd hdist
  exact ⟨Orbit36Transport.original_magnitudes c d hc hd hnc hnd hdist,
    Orbit36Transport.original_full_support c d hc hd hnc hnd hdist,
    hE, hAB.1, hAB.2⟩

/-- The table-level theorem is non-vacuous and its exact enumerator pair is
attained by a code whose support is in the original two fibers. -/
theorem table_representative_attained :
    ∃ c d : SS.State 6 ℂ,
      (∀ x, x ∉ Orbit36Transport.originalS0 → c x = 0)
        ∧ (∀ y, y ∉ Orbit36Transport.originalS1 → d y = 0)
        ∧ SS.innerC c c = 1
        ∧ SS.innerC d d = 1
        ∧ SS.HasDistance ![c, d] 3
        ∧ IsOrbit36A ![c, d]
        ∧ IsOrbit36B ![c, d] := by
  refine ⟨Orbit36Transport.originalCanonicalC, Orbit36Transport.originalCanonicalD,
    Orbit36Transport.originalCanonicalC_vanishes,
    Orbit36Transport.originalCanonicalD_vanishes,
    Orbit36Transport.originalCanonicalC_normalized,
    Orbit36Transport.originalCanonicalD_normalized,
    Orbit36Transport.originalCanonical_is_code, ?_⟩
  exact original_enumerator_pair _ _
    Orbit36Transport.originalCanonicalC_vanishes
    Orbit36Transport.originalCanonicalD_vanishes
    Orbit36Transport.originalCanonicalC_normalized
    Orbit36Transport.originalCanonicalD_normalized
    Orbit36Transport.originalCanonical_is_code

end

end SixQubit.Orbit36Certified
