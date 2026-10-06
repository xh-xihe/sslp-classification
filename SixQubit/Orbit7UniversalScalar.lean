import SixQubit.Orbit7UniversalShell
import SixQubit.Realize

/-!
# Orbit 7 universal converse, II: scalar edge coordinates

This file coordinatizes the four rigid active shells by the ten edges of
`K_5`.  Each active pattern carries a two-component spinor on coordinate
zero; `spinMass` is its squared norm.  The shell decompositions below are
finite set identities checked by the kernel, not assumptions on a chosen
support.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators
open SixQubit SixQubit.Realize

noncomputable section

def abit : SS.BitString 6 := bs true false false false false false
def zero : SS.BitString 6 := bs false false false false false false
def activeAll : SS.BitString 6 := bs false true true true true true

def edgePairs : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter (fun e => e.1 < e.2)

def tenEdges : Finset (Fin 5 × Fin 5) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)].toFinset

theorem edgePairs_eq : edgePairs = tenEdges := by decide

def activeEdge (i j : Fin 5) : SS.BitString 6 :=
  SS.bxor (SS.stdBasis i.succ) (SS.stdBasis j.succ)

def aBase (i j : Fin 5) : SS.BitString 6 :=
  SS.bxor activeAll (activeEdge i j)

def bBase (i j : Fin 5) : SS.BitString 6 := activeEdge i j

def spinSupport (y : SS.BitString 6) : Finset (SS.BitString 6) :=
  {y, SS.bxor y abit}

def spinMass (f : SS.State 6 ℂ) (y : SS.BitString 6) : ℝ :=
  Complex.normSq (f y) + Complex.normSq (f (SS.bxor y abit))

def uMass (c : SS.State 6 ℂ) : ℝ := spinMass c zero
def vMass (d : SS.State 6 ℂ) : ℝ := spinMass d activeAll
def aMass (c : SS.State 6 ℂ) (i j : Fin 5) : ℝ := spinMass c (aBase i j)
def bMass (d : SS.State 6 ℂ) (i j : Fin 5) : ℝ := spinMass d (bBase i j)

def aShellSupport : Finset (SS.BitString 6) :=
  edgePairs.biUnion (fun e => spinSupport (aBase e.1 e.2))

def bShellSupport : Finset (SS.BitString 6) :=
  edgePairs.biUnion (fun e => spinSupport (bBase e.1 e.2))

def incidentPairs (i : Fin 5) : Finset (Fin 5 × Fin 5) :=
  edgePairs.filter (fun e => e.1 = i ∨ e.2 = i)

def nonincidentPairs (i : Fin 5) : Finset (Fin 5 × Fin 5) :=
  edgePairs.filter (fun e => e.1 ≠ i ∧ e.2 ≠ i)

def nonincidentBoth (e : Fin 5 × Fin 5) : Finset (Fin 5 × Fin 5) :=
  edgePairs.filter (fun f =>
    f.1 ≠ e.1 ∧ f.2 ≠ e.1 ∧ f.1 ≠ e.2 ∧ f.2 ≠ e.2)

/-- Edges incident on `e.2` but not on `e.1`. -/
def otherStar (e : Fin 5 × Fin 5) : Finset (Fin 5 × Fin 5) :=
  edgePairs.filter (fun f =>
    f.1 ≠ e.1 ∧ f.2 ≠ e.1 ∧ (f.1 = e.2 ∨ f.2 = e.2))

def aSupportFor (E : Finset (Fin 5 × Fin 5)) : Finset (SS.BitString 6) :=
  E.biUnion (fun e => spinSupport (aBase e.1 e.2))

def bSupportFor (E : Finset (Fin 5 × Fin 5)) : Finset (SS.BitString 6) :=
  E.biUnion (fun e => spinSupport (bBase e.1 e.2))

def totalA (c : SS.State 6 ℂ) : ℝ :=
  ∑ e ∈ edgePairs, aMass c e.1 e.2

def totalB (d : SS.State 6 ℂ) : ℝ :=
  ∑ e ∈ edgePairs, bMass d e.1 e.2

def degreeA (c : SS.State 6 ℂ) (i : Fin 5) : ℝ :=
  ∑ e ∈ incidentPairs i, aMass c e.1 e.2

def degreeB (d : SS.State 6 ℂ) (i : Fin 5) : ℝ :=
  ∑ e ∈ incidentPairs i, bMass d e.1 e.2

theorem shell0_support :
    S0.filter (fun x => activeWt x = 0) = spinSupport zero := by decide

theorem shell3_support :
    S0.filter (fun x => activeWt x = 3) = aShellSupport := by decide

theorem shell2_support :
    S2.filter (fun x => activeWt x = 2) = bShellSupport := by decide

theorem shell5_support :
    S2.filter (fun x => activeWt x = 5) = spinSupport activeAll := by decide

theorem occ0_support : ∀ i : Fin 5,
    S0.filter (fun x => x i.succ = true) =
      aSupportFor (nonincidentPairs i) := by decide

theorem occ2_support : ∀ i : Fin 5,
    S2.filter (fun x => x i.succ = true) =
      bSupportFor (incidentPairs i) ∪ spinSupport activeAll := by decide

theorem occ20_support : ∀ e ∈ edgePairs,
    S0.filter (fun x => x e.1.succ = true ∧ x e.2.succ = true) =
      aSupportFor (nonincidentBoth e) := by decide

theorem occ22_support : ∀ e ∈ edgePairs,
    S2.filter (fun x => x e.1.succ = true ∧ x e.2.succ = true) =
      spinSupport (bBase e.1 e.2) ∪ spinSupport activeAll := by decide

theorem nonincident_partition : ∀ e ∈ edgePairs,
    nonincidentPairs e.1 = nonincidentBoth e ∪ otherStar e := by decide

theorem nonincident_partition_disjoint : ∀ e ∈ edgePairs,
    Disjoint (nonincidentBoth e) (otherStar e) := by decide

theorem incident_partition : ∀ e ∈ edgePairs,
    incidentPairs e.2 = {e} ∪ otherStar e := by decide

theorem incident_partition_disjoint : ∀ e ∈ edgePairs,
    Disjoint ({e} : Finset (Fin 5 × Fin 5)) (otherStar e) := by decide

theorem spin_flip_ne : ∀ y : SS.BitString 6, SS.bxor y abit ≠ y := by decide

lemma sum_spinSupport (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    ∑ x ∈ spinSupport y, Complex.normSq (f x) = spinMass f y := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  simp [spinSupport, spinMass, hne]

theorem aShell_disjoint : ∀ e ∈ edgePairs, ∀ f ∈ edgePairs, e ≠ f ->
    Disjoint (spinSupport (aBase e.1 e.2)) (spinSupport (aBase f.1 f.2)) := by
  decide

theorem bShell_disjoint : ∀ e ∈ edgePairs, ∀ f ∈ edgePairs, e ≠ f ->
    Disjoint (spinSupport (bBase e.1 e.2)) (spinSupport (bBase f.1 f.2)) := by
  decide

lemma sum_aSupportFor (c : SS.State 6 ℂ) (E : Finset (Fin 5 × Fin 5))
    (hE : E ⊆ edgePairs) :
    ∑ x ∈ aSupportFor E, Complex.normSq (c x) =
      ∑ e ∈ E, aMass c e.1 e.2 := by
  unfold aSupportFor
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact aShell_disjoint e (hE he) f (hE hf) hef)]
  unfold aMass
  exact Finset.sum_congr rfl (fun e he => sum_spinSupport c (aBase e.1 e.2))

lemma sum_bSupportFor (d : SS.State 6 ℂ) (E : Finset (Fin 5 × Fin 5))
    (hE : E ⊆ edgePairs) :
    ∑ x ∈ bSupportFor E, Complex.normSq (d x) =
      ∑ e ∈ E, bMass d e.1 e.2 := by
  unfold bSupportFor
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e (hE he) f (hE hf) hef)]
  unfold bMass
  exact Finset.sum_congr rfl (fun e he => sum_spinSupport d (bBase e.1 e.2))

theorem bOcc_disjoint : ∀ i : Fin 5,
    Disjoint (bSupportFor (incidentPairs i)) (spinSupport activeAll) := by decide

theorem bPair_disjoint : ∀ e ∈ edgePairs,
    Disjoint (spinSupport (bBase e.1 e.2)) (spinSupport activeAll) := by decide

lemma incident_subset (i : Fin 5) : incidentPairs i ⊆ edgePairs := by
  intro e he
  exact (Finset.mem_filter.mp he).1

lemma nonincident_subset (i : Fin 5) : nonincidentPairs i ⊆ edgePairs := by
  intro e he
  exact (Finset.mem_filter.mp he).1

lemma nonincidentBoth_subset (e : Fin 5 × Fin 5) :
    nonincidentBoth e ⊆ edgePairs := by
  intro f hf
  exact (Finset.mem_filter.mp hf).1

lemma nonincident_sum (c : SS.State 6 ℂ) (i : Fin 5) :
    (∑ e ∈ nonincidentPairs i, aMass c e.1 e.2) = totalA c - degreeA c i := by
  let pred : Fin 5 × Fin 5 -> Prop := fun e => e.1 = i ∨ e.2 = i
  have hpart := Finset.sum_filter_add_sum_filter_not edgePairs pred
    (fun e => aMass c e.1 e.2)
  have hnot : edgePairs.filter (fun e => ¬ pred e) = nonincidentPairs i := by
    ext e
    simp [pred, nonincidentPairs]
  rw [hnot] at hpart
  change degreeA c i + (∑ e ∈ nonincidentPairs i, aMass c e.1 e.2) = totalA c at hpart
  linarith

lemma nonincidentBoth_sum (c : SS.State 6 ℂ) (e : Fin 5 × Fin 5)
    (he : e ∈ edgePairs) :
    (∑ f ∈ nonincidentBoth e, aMass c f.1 f.2) =
      totalA c - degreeA c e.1 - degreeA c e.2 + aMass c e.1 e.2 := by
  have hni := nonincident_sum c e.1
  have hp :
      (∑ f ∈ nonincidentPairs e.1, aMass c f.1 f.2) =
        (∑ f ∈ nonincidentBoth e, aMass c f.1 f.2) +
          ∑ f ∈ otherStar e, aMass c f.1 f.2 := by
    rw [nonincident_partition e he,
      Finset.sum_union (nonincident_partition_disjoint e he)]
  have hd : degreeA c e.2 = aMass c e.1 e.2 +
      ∑ f ∈ otherStar e, aMass c f.1 f.2 := by
    unfold degreeA
    rw [incident_partition e he,
      Finset.sum_union (incident_partition_disjoint e he), Finset.sum_singleton]
  linarith

lemma occ0_formula (c : SS.State 6 ℂ) (i : Fin 5) :
    occOn S0 c i.succ = totalA c - degreeA c i := by
  unfold occOn
  rw [occ0_support, sum_aSupportFor c _ (nonincident_subset i), nonincident_sum]

lemma occ2_formula (d : SS.State 6 ℂ) (i : Fin 5) :
    occOn S2 d i.succ = degreeB d i + vMass d := by
  unfold occOn
  rw [occ2_support, Finset.sum_union (bOcc_disjoint i)]
  rw [sum_bSupportFor d _ (incident_subset i), sum_spinSupport]
  rfl

lemma occ20_formula (c : SS.State 6 ℂ) (e : Fin 5 × Fin 5)
    (he : e ∈ edgePairs) :
    occ2On S0 c e.1.succ e.2.succ =
      totalA c - degreeA c e.1 - degreeA c e.2 + aMass c e.1 e.2 := by
  unfold occ2On
  rw [occ20_support e he, sum_aSupportFor c _ (nonincidentBoth_subset e),
    nonincidentBoth_sum c e he]

lemma occ22_formula (d : SS.State 6 ℂ) (e : Fin 5 × Fin 5)
    (he : e ∈ edgePairs) :
    occ2On S2 d e.1.succ e.2.succ = bMass d e.1 e.2 + vMass d := by
  unfold occ2On
  rw [occ22_support e he, Finset.sum_union (bPair_disjoint e he),
    sum_spinSupport, sum_spinSupport]
  rfl

lemma aMass_symm (c : SS.State 6 ℂ) (i j : Fin 5) :
    aMass c i j = aMass c j i := by
  simp [aMass, aBase, activeEdge, SS.bxor_comm]

lemma bMass_symm (d : SS.State 6 ℂ) (i j : Fin 5) :
    bMass d i j = bMass d j i := by
  simp [bMass, bBase, activeEdge, SS.bxor_comm]

lemma occ2On_comm (S : Finset (SS.BitString 6)) (f : SS.State 6 ℂ)
    (i j : Fin 6) : occ2On S f i j = occ2On S f j i := by
  unfold occ2On
  congr 1
  ext x
  simp [and_comm]

lemma occ20_formula_neq (c : SS.State 6 ℂ) (i j : Fin 5) (hij : i ≠ j) :
    occ2On S0 c i.succ j.succ =
      totalA c - degreeA c i - degreeA c j + aMass c i j := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact occ20_formula c (i,j) (by simpa [edgePairs] using hlt)
  · calc
      occ2On S0 c i.succ j.succ = occ2On S0 c j.succ i.succ :=
        occ2On_comm S0 c i.succ j.succ
      _ = totalA c - degreeA c j - degreeA c i + aMass c j i :=
        occ20_formula c (j,i) (by simpa [edgePairs] using hgt)
      _ = totalA c - degreeA c i - degreeA c j + aMass c i j := by
        rw [aMass_symm]
        ring

lemma occ22_formula_neq (d : SS.State 6 ℂ) (i j : Fin 5) (hij : i ≠ j) :
    occ2On S2 d i.succ j.succ = bMass d i j + vMass d := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact occ22_formula d (i,j) (by simpa [edgePairs] using hlt)
  · calc
      occ2On S2 d i.succ j.succ = occ2On S2 d j.succ i.succ :=
        occ2On_comm S2 d i.succ j.succ
      _ = bMass d j i + vMass d :=
        occ22_formula d (j,i) (by simpa [edgePairs] using hgt)
      _ = bMass d i j + vMass d := by rw [bMass_symm]

lemma sum_other_active_indicators (x : SS.BitString 6) (i : Fin 5)
    (a : ℝ) (hi : x i.succ = true) :
    ∑ j ∈ Finset.univ.erase i, (if x j.succ = true then a else 0) =
      ((activeWt x : ℝ) - 1) * a := by
  have h := sum_active_indicators x a
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at h
  simp only [hi, if_true] at h
  linarith

lemma sum_occ2_active_star (S : Finset (SS.BitString 6))
    (f : SS.State 6 ℂ) (i : Fin 5) :
    (∑ j ∈ Finset.univ.erase i, occ2On S f i.succ j.succ) =
      ∑ x ∈ S.filter (fun x => x i.succ = true),
        ((activeWt x : ℝ)-1) * Complex.normSq (f x) := by
  classical
  unfold occ2On
  simp_rw [Finset.sum_filter]
  calc
    (∑ j ∈ Finset.univ.erase i, ∑ x ∈ S,
        if x i.succ = true ∧ x j.succ = true then Complex.normSq (f x) else 0) =
      ∑ x ∈ S, ∑ j ∈ Finset.univ.erase i,
        if x i.succ = true ∧ x j.succ = true then Complex.normSq (f x) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S,
        if x i.succ = true then ((activeWt x : ℝ)-1) * Complex.normSq (f x)
        else 0 := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      by_cases hi : x i.succ = true
      · simp only [hi, true_and, if_true]
        exact sum_other_active_indicators x i (Complex.normSq (f x)) hi
      · simp [hi]

theorem active_true_ne_zero : ∀ x : SS.BitString 6, ∀ i : Fin 5,
    x i.succ = true -> activeWt x ≠ 0 := by decide

theorem shell5_active : ∀ x ∈ S2, activeWt x = 5 -> ∀ i : Fin 5,
    x i.succ = true := by decide

lemma sum_occ20_star (c : SS.State 6 ℂ) (i : Fin 5) :
    (∑ j ∈ Finset.univ.erase i, occ2On S0 c i.succ j.succ) =
      2*(totalA c - degreeA c i) := by
  rw [sum_occ2_active_star]
  have htwo :
      (∑ x ∈ S0.filter (fun x => x i.succ = true),
        ((activeWt x : ℝ)-1) * Complex.normSq (c x)) =
      2 * occOn S0 c i.succ := by
    unfold occOn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxS : x ∈ S0 := (Finset.mem_filter.mp hx).1
    have hxi : x i.succ = true := (Finset.mem_filter.mp hx).2
    rcases S0_shells x hxS with h0 | h3
    · exact absurd h0 (active_true_ne_zero x i hxi)
    · rw [h3]
      norm_num
  rw [htwo, occ0_formula]

lemma sum_occ22_star (d : SS.State 6 ℂ) (i : Fin 5) :
    (∑ j ∈ Finset.univ.erase i, occ2On S2 d i.succ j.succ) =
      degreeB d i + 4*vMass d := by
  rw [sum_occ2_active_star]
  have hweighted :
      (∑ x ∈ S2.filter (fun x => x i.succ = true),
        ((activeWt x : ℝ)-1) * Complex.normSq (d x)) =
      occOn S2 d i.succ + 3*shellMass S2 d 5 := by
    unfold occOn shellMass
    simp_rw [Finset.sum_filter]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rcases S2_shells x hx with h2 | h5
    · by_cases hxi : x i.succ = true
      · simp [hxi, h2]
        norm_num
      · simp [hxi, h2]
    · have hxi := shell5_active x hx h5 i
      simp [hxi, h5]
      ring
  have hv : shellMass S2 d 5 = vMass d := by
    unfold shellMass vMass
    rw [shell5_support]
    exact sum_spinSupport d activeAll
  rw [hweighted, occ2_formula, hv]
  ring

lemma shellMass0_eq_uMass (c : SS.State 6 ℂ) :
    shellMass S0 c 0 = uMass c := by
  unfold shellMass uMass
  rw [shell0_support]
  exact sum_spinSupport c zero

lemma shellMass3_eq_edges (c : SS.State 6 ℂ) :
    shellMass S0 c 3 = ∑ e ∈ edgePairs, aMass c e.1 e.2 := by
  unfold shellMass
  rw [shell3_support]
  unfold aShellSupport
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact aShell_disjoint e he f hf hef)]
  unfold aMass
  exact Finset.sum_congr rfl (fun e he => sum_spinSupport c (aBase e.1 e.2))

lemma shellMass2_eq_edges (d : SS.State 6 ℂ) :
    shellMass S2 d 2 = ∑ e ∈ edgePairs, bMass d e.1 e.2 := by
  unfold shellMass
  rw [shell2_support]
  unfold bShellSupport
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e he f hf hef)]
  unfold bMass
  exact Finset.sum_congr rfl (fun e he => sum_spinSupport d (bBase e.1 e.2))

lemma shellMass5_eq_vMass (d : SS.State 6 ℂ) :
    shellMass S2 d 5 = vMass d := by
  unfold shellMass vMass
  rw [shell5_support]
  exact sum_spinSupport d activeAll

/-- The extreme spinors and the two total edge masses. -/
theorem scalar_totals (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    uMass c = 1/6 ∧ vMass d = 1/6 ∧
      (∑ e ∈ edgePairs, aMass c e.1 e.2) = 5/6 ∧
      (∑ e ∈ edgePairs, bMass d e.1 e.2) = 5/6 := by
  rcases rigid_shells c d hc hd hnc hnd hcode with ⟨h0,h3,h2,h5⟩
  rw [shellMass0_eq_uMass] at h0
  rw [shellMass3_eq_edges] at h3
  rw [shellMass2_eq_edges] at h2
  rw [shellMass5_eq_vMass] at h5
  exact ⟨h0,h5,h3,h2⟩

/-- Complete scalar moment normal form of the manuscript: both extreme
spinors have norm squared `1/6`, the two edge arrays have total mass `5/6`,
every vertex degree is `1/3`, and corresponding edge spinors have equal
norm.  All conclusions are derived from genuine KL occupation rows. -/
theorem scalar_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    uMass c = 1/6 ∧ vMass d = 1/6 ∧ totalA c = 5/6 ∧ totalB d = 5/6 ∧
      (∀ i : Fin 5, degreeA c i = 1/3 ∧ degreeB d i = 1/3) ∧
      (∀ e ∈ edgePairs, aMass c e.1 e.2 = bMass d e.1 e.2) := by
  rcases scalar_totals c d hc hd hnc hnd hcode with ⟨hu,hv,hAt,hBt⟩
  change totalA c = 5/6 at hAt
  change totalB d = 5/6 at hBt
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  have hocc : ∀ i, occOn S0 c i = occOn S2 d i :=
    occOn_eq_of_hasDistance S0 S2 c d hcS hdS hnc hnd hcode
  have hocc2 : ∀ i j, occ2On S0 c i j = occ2On S2 d i j :=
    occ2On_eq_of_hasDistance S0 S2 c d hcS hdS hnc hnd hcode
  have hdeg : ∀ i : Fin 5, degreeA c i = 1/3 ∧ degreeB d i = 1/3 := by
    intro i
    have h1 := hocc i.succ
    rw [occ0_formula, occ2_formula, hAt, hv] at h1
    have h2 :
        (∑ j ∈ Finset.univ.erase i, occ2On S0 c i.succ j.succ) =
          ∑ j ∈ Finset.univ.erase i, occ2On S2 d i.succ j.succ :=
      Finset.sum_congr rfl (fun j hj => hocc2 i.succ j.succ)
    rw [sum_occ20_star, sum_occ22_star, hAt, hv] at h2
    constructor <;> linarith
  have hedge : ∀ e ∈ edgePairs, aMass c e.1 e.2 = bMass d e.1 e.2 := by
    intro e he
    have hp := hocc2 e.1.succ e.2.succ
    rw [occ20_formula c e he, occ22_formula d e he,
      hAt, hv, (hdeg e.1).1, (hdeg e.2).1] at hp
    linarith
  exact ⟨hu,hv,hAt,hBt,hdeg,hedge⟩

end

end SixQubit.Orbit7Universal
