import MainTheory.Orbit31CrossRows
import MainTheory.Orbit31PhaseRatios
import MainTheory.Orbit31SignedSupport

/-! Canonical cross-KL equations in the actual A/B table coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit31CrossConsequences
open MainTheory.Generated.Orbit31CrossRows
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31SignedSupport (A B)
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

theorem pair0 (t : Fin 8 → ℂ) (h : Flip1.W.mulVec t = 0) (e : Fin 4) :
    t ⟨2*e.val,by omega⟩ = t ⟨2*e.val+1,by omega⟩ := by
  rw [(Flip1.kernel_iff t).mp h]
  fin_cases e <;> norm_num [Flip1.pattern]

theorem sum0 (t : Fin 8 → ℂ) (h : Flip1.W.mulVec t = 0) :
    (∑ e : Fin 4, t ⟨2*e.val,by omega⟩) = 0 := by
  rw [(Flip1.kernel_iff t).mp h]
  norm_num [Flip1.pattern,Fin.sum_univ_succ,Fin.succ]
  ring

theorem pair1 (t : Fin 8 → ℂ) (h : Flip2.W.mulVec t = 0) (e : Fin 4) :
    t ⟨2*e.val,by omega⟩ = t ⟨2*e.val+1,by omega⟩ := by
  rw [(Flip2.kernel_iff t).mp h]
  fin_cases e <;> norm_num [Flip2.pattern]

theorem sum1 (t : Fin 8 → ℂ) (h : Flip2.W.mulVec t = 0) :
    (∑ e : Fin 4, t ⟨2*e.val,by omega⟩) = 0 := by
  rw [(Flip2.kernel_iff t).mp h]
  norm_num [Flip2.pattern,Fin.sum_univ_succ,Fin.succ]
  ring

theorem pair2 (t : Fin 8 → ℂ) (h : Flip3.W.mulVec t = 0) (e : Fin 4) :
    t ⟨2*e.val,by omega⟩ = t ⟨2*e.val+1,by omega⟩ := by
  rw [(Flip3.kernel_iff t).mp h]
  fin_cases e <;> norm_num [Flip3.pattern]

theorem sum2 (t : Fin 8 → ℂ) (h : Flip3.W.mulVec t = 0) :
    (∑ e : Fin 4, t ⟨2*e.val,by omega⟩) = 0 := by
  rw [(Flip3.kernel_iff t).mp h]
  norm_num [Flip3.pattern,Fin.sum_univ_succ,Fin.succ]
  ring

theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∀ i : Fin 3, ∀ e : Fin 4,
      star (C c (A e)) * D d (B i e) = star (C c (B i e)) * D d (A e) := by
  intro i e
  fin_cases i
  · have h := pair0 (Flip1.products c d) (Flip1.physical c d hc hd hkl) e
    fin_cases e <;> simpa [Flip1.products,Flip1.src,Flip1.dst,C,D,top,A,B,Fin.succ] using h
  · have h := pair1 (Flip2.products c d) (Flip2.physical c d hc hd hkl) e
    fin_cases e <;> simpa [Flip2.products,Flip2.src,Flip2.dst,C,D,top,A,B,Fin.succ] using h
  · have h := pair2 (Flip3.products c d) (Flip3.physical c d hc hd hkl) e
    fin_cases e <;> simpa [Flip3.products,Flip3.src,Flip3.dst,C,D,top,A,B,Fin.succ] using h

theorem physical_weight_one_sum (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∀ i : Fin 3, (∑ e : Fin 4, star (C c (A e)) * D d (B i e)) = 0 := by
  intro i
  fin_cases i
  · simpa [Flip1.products,Flip1.src,Flip1.dst,C,D,top,A,B,
      Fin.sum_univ_succ,Fin.succ] using
      sum0 (Flip1.products c d) (Flip1.physical c d hc hd hkl)
  · simpa [Flip2.products,Flip2.src,Flip2.dst,C,D,top,A,B,
      Fin.sum_univ_succ,Fin.succ] using
      sum1 (Flip2.products c d) (Flip2.physical c d hc hd hkl)
  · simpa [Flip3.products,Flip3.src,Flip3.dst,C,D,top,A,B,
      Fin.sum_univ_succ,Fin.succ] using
      sum2 (Flip3.products c d) (Flip3.physical c d hc hd hkl)

theorem rectangle_01_01 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨4,by decide⟩) * D d ⟨9,by decide⟩ + star (C c ⟨9,by decide⟩) * D d ⟨4,by decide⟩ + star (C c ⟨5,by decide⟩) * D d ⟨8,by decide⟩ + star (C c ⟨8,by decide⟩) * D d ⟨5,by decide⟩ = 0 := by
  have ht := (Flip34.kernel_iff _).mp (Flip34.physical c d hc hd hkl)
  have h : Flip34.products c d ⟨0,by decide⟩ + Flip34.products c d ⟨1,by decide⟩ + Flip34.products c d ⟨2,by decide⟩ + Flip34.products c d ⟨3,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip34.pattern,Flip34.freeIndices]
    ring
  simpa [Flip34.products,Flip34.src,Flip34.dst,C,D,top] using h

theorem rectangle_01_02 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨4,by decide⟩) * D d ⟨10,by decide⟩ + star (C c ⟨10,by decide⟩) * D d ⟨4,by decide⟩ + star (C c ⟨6,by decide⟩) * D d ⟨8,by decide⟩ + star (C c ⟨8,by decide⟩) * D d ⟨6,by decide⟩ = 0 := by
  have ht := (Flip35.kernel_iff _).mp (Flip35.physical c d hc hd hkl)
  have h : Flip35.products c d ⟨0,by decide⟩ + Flip35.products c d ⟨1,by decide⟩ + Flip35.products c d ⟨4,by decide⟩ + Flip35.products c d ⟨5,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip35.pattern,Flip35.freeIndices]
    ring
  simpa [Flip35.products,Flip35.src,Flip35.dst,C,D,top] using h

theorem rectangle_01_03 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨4,by decide⟩) * D d ⟨11,by decide⟩ + star (C c ⟨11,by decide⟩) * D d ⟨4,by decide⟩ + star (C c ⟨7,by decide⟩) * D d ⟨8,by decide⟩ + star (C c ⟨8,by decide⟩) * D d ⟨7,by decide⟩ = 0 := by
  have ht := (Flip36.kernel_iff _).mp (Flip36.physical c d hc hd hkl)
  have h : Flip36.products c d ⟨0,by decide⟩ + Flip36.products c d ⟨1,by decide⟩ + Flip36.products c d ⟨6,by decide⟩ + Flip36.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip36.pattern,Flip36.freeIndices]
    ring
  simpa [Flip36.products,Flip36.src,Flip36.dst,C,D,top] using h

theorem rectangle_01_12 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨5,by decide⟩) * D d ⟨10,by decide⟩ + star (C c ⟨10,by decide⟩) * D d ⟨5,by decide⟩ + star (C c ⟨6,by decide⟩) * D d ⟨9,by decide⟩ + star (C c ⟨9,by decide⟩) * D d ⟨6,by decide⟩ = 0 := by
  have ht := (Flip36.kernel_iff _).mp (Flip36.physical c d hc hd hkl)
  have h : Flip36.products c d ⟨2,by decide⟩ + Flip36.products c d ⟨3,by decide⟩ + Flip36.products c d ⟨4,by decide⟩ + Flip36.products c d ⟨5,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip36.pattern,Flip36.freeIndices]
    ring
  simpa [Flip36.products,Flip36.src,Flip36.dst,C,D,top] using h

theorem rectangle_01_13 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨5,by decide⟩) * D d ⟨11,by decide⟩ + star (C c ⟨11,by decide⟩) * D d ⟨5,by decide⟩ + star (C c ⟨7,by decide⟩) * D d ⟨9,by decide⟩ + star (C c ⟨9,by decide⟩) * D d ⟨7,by decide⟩ = 0 := by
  have ht := (Flip35.kernel_iff _).mp (Flip35.physical c d hc hd hkl)
  have h : Flip35.products c d ⟨2,by decide⟩ + Flip35.products c d ⟨3,by decide⟩ + Flip35.products c d ⟨6,by decide⟩ + Flip35.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip35.pattern,Flip35.freeIndices]
    ring
  simpa [Flip35.products,Flip35.src,Flip35.dst,C,D,top] using h

theorem rectangle_01_23 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨6,by decide⟩) * D d ⟨11,by decide⟩ + star (C c ⟨11,by decide⟩) * D d ⟨6,by decide⟩ + star (C c ⟨7,by decide⟩) * D d ⟨10,by decide⟩ + star (C c ⟨10,by decide⟩) * D d ⟨7,by decide⟩ = 0 := by
  have ht := (Flip34.kernel_iff _).mp (Flip34.physical c d hc hd hkl)
  have h : Flip34.products c d ⟨4,by decide⟩ + Flip34.products c d ⟨5,by decide⟩ + Flip34.products c d ⟨6,by decide⟩ + Flip34.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip34.pattern,Flip34.freeIndices]
    ring
  simpa [Flip34.products,Flip34.src,Flip34.dst,C,D,top] using h

theorem rectangle_02_01 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨4,by decide⟩) * D d ⟨13,by decide⟩ + star (C c ⟨13,by decide⟩) * D d ⟨4,by decide⟩ + star (C c ⟨5,by decide⟩) * D d ⟨12,by decide⟩ + star (C c ⟨12,by decide⟩) * D d ⟨5,by decide⟩ = 0 := by
  have ht := (Flip24.kernel_iff _).mp (Flip24.physical c d hc hd hkl)
  have h : Flip24.products c d ⟨0,by decide⟩ + Flip24.products c d ⟨1,by decide⟩ + Flip24.products c d ⟨2,by decide⟩ + Flip24.products c d ⟨3,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip24.pattern,Flip24.freeIndices]
    ring
  simpa [Flip24.products,Flip24.src,Flip24.dst,C,D,top] using h

theorem rectangle_02_02 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨4,by decide⟩) * D d ⟨14,by decide⟩ + star (C c ⟨14,by decide⟩) * D d ⟨4,by decide⟩ + star (C c ⟨6,by decide⟩) * D d ⟨12,by decide⟩ + star (C c ⟨12,by decide⟩) * D d ⟨6,by decide⟩ = 0 := by
  have ht := (Flip25.kernel_iff _).mp (Flip25.physical c d hc hd hkl)
  have h : Flip25.products c d ⟨0,by decide⟩ + Flip25.products c d ⟨1,by decide⟩ + Flip25.products c d ⟨4,by decide⟩ + Flip25.products c d ⟨5,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip25.pattern,Flip25.freeIndices]
    ring
  simpa [Flip25.products,Flip25.src,Flip25.dst,C,D,top] using h

theorem rectangle_02_03 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨4,by decide⟩) * D d ⟨15,by decide⟩ + star (C c ⟨15,by decide⟩) * D d ⟨4,by decide⟩ + star (C c ⟨7,by decide⟩) * D d ⟨12,by decide⟩ + star (C c ⟨12,by decide⟩) * D d ⟨7,by decide⟩ = 0 := by
  have ht := (Flip26.kernel_iff _).mp (Flip26.physical c d hc hd hkl)
  have h : Flip26.products c d ⟨0,by decide⟩ + Flip26.products c d ⟨1,by decide⟩ + Flip26.products c d ⟨6,by decide⟩ + Flip26.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip26.pattern,Flip26.freeIndices]
    ring
  simpa [Flip26.products,Flip26.src,Flip26.dst,C,D,top] using h

theorem rectangle_02_12 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨5,by decide⟩) * D d ⟨14,by decide⟩ + star (C c ⟨14,by decide⟩) * D d ⟨5,by decide⟩ + star (C c ⟨6,by decide⟩) * D d ⟨13,by decide⟩ + star (C c ⟨13,by decide⟩) * D d ⟨6,by decide⟩ = 0 := by
  have ht := (Flip26.kernel_iff _).mp (Flip26.physical c d hc hd hkl)
  have h : Flip26.products c d ⟨2,by decide⟩ + Flip26.products c d ⟨3,by decide⟩ + Flip26.products c d ⟨4,by decide⟩ + Flip26.products c d ⟨5,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip26.pattern,Flip26.freeIndices]
    ring
  simpa [Flip26.products,Flip26.src,Flip26.dst,C,D,top] using h

theorem rectangle_02_13 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨5,by decide⟩) * D d ⟨15,by decide⟩ + star (C c ⟨15,by decide⟩) * D d ⟨5,by decide⟩ + star (C c ⟨7,by decide⟩) * D d ⟨13,by decide⟩ + star (C c ⟨13,by decide⟩) * D d ⟨7,by decide⟩ = 0 := by
  have ht := (Flip25.kernel_iff _).mp (Flip25.physical c d hc hd hkl)
  have h : Flip25.products c d ⟨2,by decide⟩ + Flip25.products c d ⟨3,by decide⟩ + Flip25.products c d ⟨6,by decide⟩ + Flip25.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip25.pattern,Flip25.freeIndices]
    ring
  simpa [Flip25.products,Flip25.src,Flip25.dst,C,D,top] using h

theorem rectangle_02_23 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨6,by decide⟩) * D d ⟨15,by decide⟩ + star (C c ⟨15,by decide⟩) * D d ⟨6,by decide⟩ + star (C c ⟨7,by decide⟩) * D d ⟨14,by decide⟩ + star (C c ⟨14,by decide⟩) * D d ⟨7,by decide⟩ = 0 := by
  have ht := (Flip24.kernel_iff _).mp (Flip24.physical c d hc hd hkl)
  have h : Flip24.products c d ⟨4,by decide⟩ + Flip24.products c d ⟨5,by decide⟩ + Flip24.products c d ⟨6,by decide⟩ + Flip24.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip24.pattern,Flip24.freeIndices]
    ring
  simpa [Flip24.products,Flip24.src,Flip24.dst,C,D,top] using h

theorem rectangle_12_01 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨8,by decide⟩) * D d ⟨13,by decide⟩ + star (C c ⟨13,by decide⟩) * D d ⟨8,by decide⟩ + star (C c ⟨9,by decide⟩) * D d ⟨12,by decide⟩ + star (C c ⟨12,by decide⟩) * D d ⟨9,by decide⟩ = 0 := by
  have ht := (Flip14.kernel_iff _).mp (Flip14.physical c d hc hd hkl)
  have h : Flip14.products c d ⟨0,by decide⟩ + Flip14.products c d ⟨1,by decide⟩ + Flip14.products c d ⟨2,by decide⟩ + Flip14.products c d ⟨3,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip14.pattern,Flip14.freeIndices]
    ring
  simpa [Flip14.products,Flip14.src,Flip14.dst,C,D,top] using h

theorem rectangle_12_02 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨8,by decide⟩) * D d ⟨14,by decide⟩ + star (C c ⟨14,by decide⟩) * D d ⟨8,by decide⟩ + star (C c ⟨10,by decide⟩) * D d ⟨12,by decide⟩ + star (C c ⟨12,by decide⟩) * D d ⟨10,by decide⟩ = 0 := by
  have ht := (Flip15.kernel_iff _).mp (Flip15.physical c d hc hd hkl)
  have h : Flip15.products c d ⟨0,by decide⟩ + Flip15.products c d ⟨1,by decide⟩ + Flip15.products c d ⟨4,by decide⟩ + Flip15.products c d ⟨5,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip15.pattern,Flip15.freeIndices]
    ring
  simpa [Flip15.products,Flip15.src,Flip15.dst,C,D,top] using h

theorem rectangle_12_03 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨8,by decide⟩) * D d ⟨15,by decide⟩ + star (C c ⟨15,by decide⟩) * D d ⟨8,by decide⟩ + star (C c ⟨11,by decide⟩) * D d ⟨12,by decide⟩ + star (C c ⟨12,by decide⟩) * D d ⟨11,by decide⟩ = 0 := by
  have ht := (Flip16.kernel_iff _).mp (Flip16.physical c d hc hd hkl)
  have h : Flip16.products c d ⟨0,by decide⟩ + Flip16.products c d ⟨1,by decide⟩ + Flip16.products c d ⟨6,by decide⟩ + Flip16.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip16.pattern,Flip16.freeIndices]
    ring
  simpa [Flip16.products,Flip16.src,Flip16.dst,C,D,top] using h

theorem rectangle_12_12 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨9,by decide⟩) * D d ⟨14,by decide⟩ + star (C c ⟨14,by decide⟩) * D d ⟨9,by decide⟩ + star (C c ⟨10,by decide⟩) * D d ⟨13,by decide⟩ + star (C c ⟨13,by decide⟩) * D d ⟨10,by decide⟩ = 0 := by
  have ht := (Flip16.kernel_iff _).mp (Flip16.physical c d hc hd hkl)
  have h : Flip16.products c d ⟨2,by decide⟩ + Flip16.products c d ⟨3,by decide⟩ + Flip16.products c d ⟨4,by decide⟩ + Flip16.products c d ⟨5,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip16.pattern,Flip16.freeIndices]
    ring
  simpa [Flip16.products,Flip16.src,Flip16.dst,C,D,top] using h

theorem rectangle_12_13 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨9,by decide⟩) * D d ⟨15,by decide⟩ + star (C c ⟨15,by decide⟩) * D d ⟨9,by decide⟩ + star (C c ⟨11,by decide⟩) * D d ⟨13,by decide⟩ + star (C c ⟨13,by decide⟩) * D d ⟨11,by decide⟩ = 0 := by
  have ht := (Flip15.kernel_iff _).mp (Flip15.physical c d hc hd hkl)
  have h : Flip15.products c d ⟨2,by decide⟩ + Flip15.products c d ⟨3,by decide⟩ + Flip15.products c d ⟨6,by decide⟩ + Flip15.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip15.pattern,Flip15.freeIndices]
    ring
  simpa [Flip15.products,Flip15.src,Flip15.dst,C,D,top] using h

theorem rectangle_12_23 (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c ⟨10,by decide⟩) * D d ⟨15,by decide⟩ + star (C c ⟨15,by decide⟩) * D d ⟨10,by decide⟩ + star (C c ⟨11,by decide⟩) * D d ⟨14,by decide⟩ + star (C c ⟨14,by decide⟩) * D d ⟨11,by decide⟩ = 0 := by
  have ht := (Flip14.kernel_iff _).mp (Flip14.physical c d hc hd hkl)
  have h : Flip14.products c d ⟨4,by decide⟩ + Flip14.products c d ⟨5,by decide⟩ + Flip14.products c d ⟨6,by decide⟩ + Flip14.products c d ⟨7,by decide⟩ = 0 := by
    rw [ht]
    norm_num [Flip14.pattern,Flip14.freeIndices]
    ring
  simpa [Flip14.products,Flip14.src,Flip14.dst,C,D,top] using h

theorem physical_rectangles (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∀ r : Fin 3, ∀ k : Fin 6,
      let i := (MainTheory.Orbit31SignedSupport.rowPairs r).1
      let j := (MainTheory.Orbit31SignedSupport.rowPairs r).2
      let e := (MainTheory.Orbit31SignedSupport.colPairs k).1
      let f := (MainTheory.Orbit31SignedSupport.colPairs k).2
      star (C c (B i e)) * D d (B j f) + star (C c (B j f)) * D d (B i e) +
        star (C c (B i f)) * D d (B j e) + star (C c (B j e)) * D d (B i f) = 0 := by
  intro r k
  fin_cases r <;> fin_cases k
  · exact rectangle_01_01 c d hc hd hkl
  · exact rectangle_01_02 c d hc hd hkl
  · exact rectangle_01_03 c d hc hd hkl
  · exact rectangle_01_12 c d hc hd hkl
  · exact rectangle_01_13 c d hc hd hkl
  · exact rectangle_01_23 c d hc hd hkl
  · exact rectangle_02_01 c d hc hd hkl
  · exact rectangle_02_02 c d hc hd hkl
  · exact rectangle_02_03 c d hc hd hkl
  · exact rectangle_02_12 c d hc hd hkl
  · exact rectangle_02_13 c d hc hd hkl
  · exact rectangle_02_23 c d hc hd hkl
  · exact rectangle_12_01 c d hc hd hkl
  · exact rectangle_12_02 c d hc hd hkl
  · exact rectangle_12_03 c d hc hd hkl
  · exact rectangle_12_12 c d hc hd hkl
  · exact rectangle_12_13 c d hc hd hkl
  · exact rectangle_12_23 c d hc hd hkl

end
end MainTheory.Orbit31CrossConsequences
