import SixQubit.Orbit9Pair

/-!
# Orbit 9: finite label bridge for all pair rows

The KL calculation stores one row for each four-element subset of the six
coordinates.  This file proves, by small kernel-checked finite cases, that
those fifteen rows cover every ordering of four pairwise distinct labels.
-/

namespace SixQubit.Orbit9Universal

noncomputable section

lemma pr_swap01 (c d : SS.State 6 ℂ) (i j k l : Fin 6) :
    pairRow c d i j k l = pairRow c d j i k l := by
  unfold pairRow
  rw [damp_symm c j i, camp_symm d j i]
  ring

lemma pr_swap12 (c d : SS.State 6 ℂ) (i j k l : Fin 6) :
    pairRow c d i j k l = pairRow c d i k j l := by
  unfold pairRow
  rw [damp_symm c k j, camp_symm d k j]
  ring

lemma pr_swap23 (c d : SS.State 6 ℂ) (i j k l : Fin 6) :
    pairRow c d i j k l = pairRow c d i j l k := by
  unfold pairRow
  rw [damp_symm c l k, camp_symm d l k]
  ring

lemma pairRow_all_i0_j1 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (0 : Fin 6) ≠ k) (hil : (0 : Fin 6) ≠ l)
    (hjk : (1 : Fin 6) ≠ k) (hjl : (1 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 0 1 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · exact h.h0123
  · exact h.h0124
  · exact h.h0125
  · calc
      pairRow c d 0 1 3 2 = pairRow c d 0 1 2 3 := pr_swap23 c d 0 1 3 2
      _ = 0 := h.h0123
  · exact h.h0134
  · exact h.h0135
  · calc
      pairRow c d 0 1 4 2 = pairRow c d 0 1 2 4 := pr_swap23 c d 0 1 4 2
      _ = 0 := h.h0124
  · calc
      pairRow c d 0 1 4 3 = pairRow c d 0 1 3 4 := pr_swap23 c d 0 1 4 3
      _ = 0 := h.h0134
  · exact h.h0145
  · calc
      pairRow c d 0 1 5 2 = pairRow c d 0 1 2 5 := pr_swap23 c d 0 1 5 2
      _ = 0 := h.h0125
  · calc
      pairRow c d 0 1 5 3 = pairRow c d 0 1 3 5 := pr_swap23 c d 0 1 5 3
      _ = 0 := h.h0135
  · calc
      pairRow c d 0 1 5 4 = pairRow c d 0 1 4 5 := pr_swap23 c d 0 1 5 4
      _ = 0 := h.h0145

lemma pairRow_all_i0_j2 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (0 : Fin 6) ≠ k) (hil : (0 : Fin 6) ≠ l)
    (hjk : (2 : Fin 6) ≠ k) (hjl : (2 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 0 2 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 0 2 1 3 = pairRow c d 0 1 2 3 := pr_swap12 c d 0 2 1 3
      _ = 0 := h.h0123
  · calc
      pairRow c d 0 2 1 4 = pairRow c d 0 1 2 4 := pr_swap12 c d 0 2 1 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 0 2 1 5 = pairRow c d 0 1 2 5 := pr_swap12 c d 0 2 1 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 0 2 3 1 = pairRow c d 0 2 1 3 := pr_swap23 c d 0 2 3 1
      _ = pairRow c d 0 1 2 3 := pr_swap12 c d 0 2 1 3
      _ = 0 := h.h0123
  · exact h.h0234
  · exact h.h0235
  · calc
      pairRow c d 0 2 4 1 = pairRow c d 0 2 1 4 := pr_swap23 c d 0 2 4 1
      _ = pairRow c d 0 1 2 4 := pr_swap12 c d 0 2 1 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 0 2 4 3 = pairRow c d 0 2 3 4 := pr_swap23 c d 0 2 4 3
      _ = 0 := h.h0234
  · exact h.h0245
  · calc
      pairRow c d 0 2 5 1 = pairRow c d 0 2 1 5 := pr_swap23 c d 0 2 5 1
      _ = pairRow c d 0 1 2 5 := pr_swap12 c d 0 2 1 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 0 2 5 3 = pairRow c d 0 2 3 5 := pr_swap23 c d 0 2 5 3
      _ = 0 := h.h0235
  · calc
      pairRow c d 0 2 5 4 = pairRow c d 0 2 4 5 := pr_swap23 c d 0 2 5 4
      _ = 0 := h.h0245

lemma pairRow_all_i0_j3 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (0 : Fin 6) ≠ k) (hil : (0 : Fin 6) ≠ l)
    (hjk : (3 : Fin 6) ≠ k) (hjl : (3 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 0 3 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 0 3 1 2 = pairRow c d 0 1 3 2 := pr_swap12 c d 0 3 1 2
      _ = pairRow c d 0 1 2 3 := pr_swap23 c d 0 1 3 2
      _ = 0 := h.h0123
  · calc
      pairRow c d 0 3 1 4 = pairRow c d 0 1 3 4 := pr_swap12 c d 0 3 1 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 0 3 1 5 = pairRow c d 0 1 3 5 := pr_swap12 c d 0 3 1 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 0 3 2 1 = pairRow c d 0 2 3 1 := pr_swap12 c d 0 3 2 1
      _ = pairRow c d 0 2 1 3 := pr_swap23 c d 0 2 3 1
      _ = pairRow c d 0 1 2 3 := pr_swap12 c d 0 2 1 3
      _ = 0 := h.h0123
  · calc
      pairRow c d 0 3 2 4 = pairRow c d 0 2 3 4 := pr_swap12 c d 0 3 2 4
      _ = 0 := h.h0234
  · calc
      pairRow c d 0 3 2 5 = pairRow c d 0 2 3 5 := pr_swap12 c d 0 3 2 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 0 3 4 1 = pairRow c d 0 3 1 4 := pr_swap23 c d 0 3 4 1
      _ = pairRow c d 0 1 3 4 := pr_swap12 c d 0 3 1 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 0 3 4 2 = pairRow c d 0 3 2 4 := pr_swap23 c d 0 3 4 2
      _ = pairRow c d 0 2 3 4 := pr_swap12 c d 0 3 2 4
      _ = 0 := h.h0234
  · exact h.h0345
  · calc
      pairRow c d 0 3 5 1 = pairRow c d 0 3 1 5 := pr_swap23 c d 0 3 5 1
      _ = pairRow c d 0 1 3 5 := pr_swap12 c d 0 3 1 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 0 3 5 2 = pairRow c d 0 3 2 5 := pr_swap23 c d 0 3 5 2
      _ = pairRow c d 0 2 3 5 := pr_swap12 c d 0 3 2 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 0 3 5 4 = pairRow c d 0 3 4 5 := pr_swap23 c d 0 3 5 4
      _ = 0 := h.h0345

lemma pairRow_all_i0_j4 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (0 : Fin 6) ≠ k) (hil : (0 : Fin 6) ≠ l)
    (hjk : (4 : Fin 6) ≠ k) (hjl : (4 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 0 4 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 0 4 1 2 = pairRow c d 0 1 4 2 := pr_swap12 c d 0 4 1 2
      _ = pairRow c d 0 1 2 4 := pr_swap23 c d 0 1 4 2
      _ = 0 := h.h0124
  · calc
      pairRow c d 0 4 1 3 = pairRow c d 0 1 4 3 := pr_swap12 c d 0 4 1 3
      _ = pairRow c d 0 1 3 4 := pr_swap23 c d 0 1 4 3
      _ = 0 := h.h0134
  · calc
      pairRow c d 0 4 1 5 = pairRow c d 0 1 4 5 := pr_swap12 c d 0 4 1 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 0 4 2 1 = pairRow c d 0 2 4 1 := pr_swap12 c d 0 4 2 1
      _ = pairRow c d 0 2 1 4 := pr_swap23 c d 0 2 4 1
      _ = pairRow c d 0 1 2 4 := pr_swap12 c d 0 2 1 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 0 4 2 3 = pairRow c d 0 2 4 3 := pr_swap12 c d 0 4 2 3
      _ = pairRow c d 0 2 3 4 := pr_swap23 c d 0 2 4 3
      _ = 0 := h.h0234
  · calc
      pairRow c d 0 4 2 5 = pairRow c d 0 2 4 5 := pr_swap12 c d 0 4 2 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 0 4 3 1 = pairRow c d 0 3 4 1 := pr_swap12 c d 0 4 3 1
      _ = pairRow c d 0 3 1 4 := pr_swap23 c d 0 3 4 1
      _ = pairRow c d 0 1 3 4 := pr_swap12 c d 0 3 1 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 0 4 3 2 = pairRow c d 0 3 4 2 := pr_swap12 c d 0 4 3 2
      _ = pairRow c d 0 3 2 4 := pr_swap23 c d 0 3 4 2
      _ = pairRow c d 0 2 3 4 := pr_swap12 c d 0 3 2 4
      _ = 0 := h.h0234
  · calc
      pairRow c d 0 4 3 5 = pairRow c d 0 3 4 5 := pr_swap12 c d 0 4 3 5
      _ = 0 := h.h0345
  · calc
      pairRow c d 0 4 5 1 = pairRow c d 0 4 1 5 := pr_swap23 c d 0 4 5 1
      _ = pairRow c d 0 1 4 5 := pr_swap12 c d 0 4 1 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 0 4 5 2 = pairRow c d 0 4 2 5 := pr_swap23 c d 0 4 5 2
      _ = pairRow c d 0 2 4 5 := pr_swap12 c d 0 4 2 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 0 4 5 3 = pairRow c d 0 4 3 5 := pr_swap23 c d 0 4 5 3
      _ = pairRow c d 0 3 4 5 := pr_swap12 c d 0 4 3 5
      _ = 0 := h.h0345

lemma pairRow_all_i0_j5 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (0 : Fin 6) ≠ k) (hil : (0 : Fin 6) ≠ l)
    (hjk : (5 : Fin 6) ≠ k) (hjl : (5 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 0 5 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 0 5 1 2 = pairRow c d 0 1 5 2 := pr_swap12 c d 0 5 1 2
      _ = pairRow c d 0 1 2 5 := pr_swap23 c d 0 1 5 2
      _ = 0 := h.h0125
  · calc
      pairRow c d 0 5 1 3 = pairRow c d 0 1 5 3 := pr_swap12 c d 0 5 1 3
      _ = pairRow c d 0 1 3 5 := pr_swap23 c d 0 1 5 3
      _ = 0 := h.h0135
  · calc
      pairRow c d 0 5 1 4 = pairRow c d 0 1 5 4 := pr_swap12 c d 0 5 1 4
      _ = pairRow c d 0 1 4 5 := pr_swap23 c d 0 1 5 4
      _ = 0 := h.h0145
  · calc
      pairRow c d 0 5 2 1 = pairRow c d 0 2 5 1 := pr_swap12 c d 0 5 2 1
      _ = pairRow c d 0 2 1 5 := pr_swap23 c d 0 2 5 1
      _ = pairRow c d 0 1 2 5 := pr_swap12 c d 0 2 1 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 0 5 2 3 = pairRow c d 0 2 5 3 := pr_swap12 c d 0 5 2 3
      _ = pairRow c d 0 2 3 5 := pr_swap23 c d 0 2 5 3
      _ = 0 := h.h0235
  · calc
      pairRow c d 0 5 2 4 = pairRow c d 0 2 5 4 := pr_swap12 c d 0 5 2 4
      _ = pairRow c d 0 2 4 5 := pr_swap23 c d 0 2 5 4
      _ = 0 := h.h0245
  · calc
      pairRow c d 0 5 3 1 = pairRow c d 0 3 5 1 := pr_swap12 c d 0 5 3 1
      _ = pairRow c d 0 3 1 5 := pr_swap23 c d 0 3 5 1
      _ = pairRow c d 0 1 3 5 := pr_swap12 c d 0 3 1 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 0 5 3 2 = pairRow c d 0 3 5 2 := pr_swap12 c d 0 5 3 2
      _ = pairRow c d 0 3 2 5 := pr_swap23 c d 0 3 5 2
      _ = pairRow c d 0 2 3 5 := pr_swap12 c d 0 3 2 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 0 5 3 4 = pairRow c d 0 3 5 4 := pr_swap12 c d 0 5 3 4
      _ = pairRow c d 0 3 4 5 := pr_swap23 c d 0 3 5 4
      _ = 0 := h.h0345
  · calc
      pairRow c d 0 5 4 1 = pairRow c d 0 4 5 1 := pr_swap12 c d 0 5 4 1
      _ = pairRow c d 0 4 1 5 := pr_swap23 c d 0 4 5 1
      _ = pairRow c d 0 1 4 5 := pr_swap12 c d 0 4 1 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 0 5 4 2 = pairRow c d 0 4 5 2 := pr_swap12 c d 0 5 4 2
      _ = pairRow c d 0 4 2 5 := pr_swap23 c d 0 4 5 2
      _ = pairRow c d 0 2 4 5 := pr_swap12 c d 0 4 2 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 0 5 4 3 = pairRow c d 0 4 5 3 := pr_swap12 c d 0 5 4 3
      _ = pairRow c d 0 4 3 5 := pr_swap23 c d 0 4 5 3
      _ = pairRow c d 0 3 4 5 := pr_swap12 c d 0 4 3 5
      _ = 0 := h.h0345

lemma pairRow_all_i1_j2 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (1 : Fin 6) ≠ k) (hil : (1 : Fin 6) ≠ l)
    (hjk : (2 : Fin 6) ≠ k) (hjl : (2 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 1 2 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 1 2 0 3 = pairRow c d 1 0 2 3 := pr_swap12 c d 1 2 0 3
      _ = pairRow c d 0 1 2 3 := pr_swap01 c d 1 0 2 3
      _ = 0 := h.h0123
  · calc
      pairRow c d 1 2 0 4 = pairRow c d 1 0 2 4 := pr_swap12 c d 1 2 0 4
      _ = pairRow c d 0 1 2 4 := pr_swap01 c d 1 0 2 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 1 2 0 5 = pairRow c d 1 0 2 5 := pr_swap12 c d 1 2 0 5
      _ = pairRow c d 0 1 2 5 := pr_swap01 c d 1 0 2 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 1 2 3 0 = pairRow c d 1 2 0 3 := pr_swap23 c d 1 2 3 0
      _ = pairRow c d 1 0 2 3 := pr_swap12 c d 1 2 0 3
      _ = pairRow c d 0 1 2 3 := pr_swap01 c d 1 0 2 3
      _ = 0 := h.h0123
  · exact h.h1234
  · exact h.h1235
  · calc
      pairRow c d 1 2 4 0 = pairRow c d 1 2 0 4 := pr_swap23 c d 1 2 4 0
      _ = pairRow c d 1 0 2 4 := pr_swap12 c d 1 2 0 4
      _ = pairRow c d 0 1 2 4 := pr_swap01 c d 1 0 2 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 1 2 4 3 = pairRow c d 1 2 3 4 := pr_swap23 c d 1 2 4 3
      _ = 0 := h.h1234
  · exact h.h1245
  · calc
      pairRow c d 1 2 5 0 = pairRow c d 1 2 0 5 := pr_swap23 c d 1 2 5 0
      _ = pairRow c d 1 0 2 5 := pr_swap12 c d 1 2 0 5
      _ = pairRow c d 0 1 2 5 := pr_swap01 c d 1 0 2 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 1 2 5 3 = pairRow c d 1 2 3 5 := pr_swap23 c d 1 2 5 3
      _ = 0 := h.h1235
  · calc
      pairRow c d 1 2 5 4 = pairRow c d 1 2 4 5 := pr_swap23 c d 1 2 5 4
      _ = 0 := h.h1245

lemma pairRow_all_i1_j3 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (1 : Fin 6) ≠ k) (hil : (1 : Fin 6) ≠ l)
    (hjk : (3 : Fin 6) ≠ k) (hjl : (3 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 1 3 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 1 3 0 2 = pairRow c d 1 0 3 2 := pr_swap12 c d 1 3 0 2
      _ = pairRow c d 0 1 3 2 := pr_swap01 c d 1 0 3 2
      _ = pairRow c d 0 1 2 3 := pr_swap23 c d 0 1 3 2
      _ = 0 := h.h0123
  · calc
      pairRow c d 1 3 0 4 = pairRow c d 1 0 3 4 := pr_swap12 c d 1 3 0 4
      _ = pairRow c d 0 1 3 4 := pr_swap01 c d 1 0 3 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 1 3 0 5 = pairRow c d 1 0 3 5 := pr_swap12 c d 1 3 0 5
      _ = pairRow c d 0 1 3 5 := pr_swap01 c d 1 0 3 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 1 3 2 0 = pairRow c d 1 2 3 0 := pr_swap12 c d 1 3 2 0
      _ = pairRow c d 1 2 0 3 := pr_swap23 c d 1 2 3 0
      _ = pairRow c d 1 0 2 3 := pr_swap12 c d 1 2 0 3
      _ = pairRow c d 0 1 2 3 := pr_swap01 c d 1 0 2 3
      _ = 0 := h.h0123
  · calc
      pairRow c d 1 3 2 4 = pairRow c d 1 2 3 4 := pr_swap12 c d 1 3 2 4
      _ = 0 := h.h1234
  · calc
      pairRow c d 1 3 2 5 = pairRow c d 1 2 3 5 := pr_swap12 c d 1 3 2 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 1 3 4 0 = pairRow c d 1 3 0 4 := pr_swap23 c d 1 3 4 0
      _ = pairRow c d 1 0 3 4 := pr_swap12 c d 1 3 0 4
      _ = pairRow c d 0 1 3 4 := pr_swap01 c d 1 0 3 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 1 3 4 2 = pairRow c d 1 3 2 4 := pr_swap23 c d 1 3 4 2
      _ = pairRow c d 1 2 3 4 := pr_swap12 c d 1 3 2 4
      _ = 0 := h.h1234
  · exact h.h1345
  · calc
      pairRow c d 1 3 5 0 = pairRow c d 1 3 0 5 := pr_swap23 c d 1 3 5 0
      _ = pairRow c d 1 0 3 5 := pr_swap12 c d 1 3 0 5
      _ = pairRow c d 0 1 3 5 := pr_swap01 c d 1 0 3 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 1 3 5 2 = pairRow c d 1 3 2 5 := pr_swap23 c d 1 3 5 2
      _ = pairRow c d 1 2 3 5 := pr_swap12 c d 1 3 2 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 1 3 5 4 = pairRow c d 1 3 4 5 := pr_swap23 c d 1 3 5 4
      _ = 0 := h.h1345

lemma pairRow_all_i1_j4 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (1 : Fin 6) ≠ k) (hil : (1 : Fin 6) ≠ l)
    (hjk : (4 : Fin 6) ≠ k) (hjl : (4 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 1 4 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 1 4 0 2 = pairRow c d 1 0 4 2 := pr_swap12 c d 1 4 0 2
      _ = pairRow c d 0 1 4 2 := pr_swap01 c d 1 0 4 2
      _ = pairRow c d 0 1 2 4 := pr_swap23 c d 0 1 4 2
      _ = 0 := h.h0124
  · calc
      pairRow c d 1 4 0 3 = pairRow c d 1 0 4 3 := pr_swap12 c d 1 4 0 3
      _ = pairRow c d 0 1 4 3 := pr_swap01 c d 1 0 4 3
      _ = pairRow c d 0 1 3 4 := pr_swap23 c d 0 1 4 3
      _ = 0 := h.h0134
  · calc
      pairRow c d 1 4 0 5 = pairRow c d 1 0 4 5 := pr_swap12 c d 1 4 0 5
      _ = pairRow c d 0 1 4 5 := pr_swap01 c d 1 0 4 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 1 4 2 0 = pairRow c d 1 2 4 0 := pr_swap12 c d 1 4 2 0
      _ = pairRow c d 1 2 0 4 := pr_swap23 c d 1 2 4 0
      _ = pairRow c d 1 0 2 4 := pr_swap12 c d 1 2 0 4
      _ = pairRow c d 0 1 2 4 := pr_swap01 c d 1 0 2 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 1 4 2 3 = pairRow c d 1 2 4 3 := pr_swap12 c d 1 4 2 3
      _ = pairRow c d 1 2 3 4 := pr_swap23 c d 1 2 4 3
      _ = 0 := h.h1234
  · calc
      pairRow c d 1 4 2 5 = pairRow c d 1 2 4 5 := pr_swap12 c d 1 4 2 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 1 4 3 0 = pairRow c d 1 3 4 0 := pr_swap12 c d 1 4 3 0
      _ = pairRow c d 1 3 0 4 := pr_swap23 c d 1 3 4 0
      _ = pairRow c d 1 0 3 4 := pr_swap12 c d 1 3 0 4
      _ = pairRow c d 0 1 3 4 := pr_swap01 c d 1 0 3 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 1 4 3 2 = pairRow c d 1 3 4 2 := pr_swap12 c d 1 4 3 2
      _ = pairRow c d 1 3 2 4 := pr_swap23 c d 1 3 4 2
      _ = pairRow c d 1 2 3 4 := pr_swap12 c d 1 3 2 4
      _ = 0 := h.h1234
  · calc
      pairRow c d 1 4 3 5 = pairRow c d 1 3 4 5 := pr_swap12 c d 1 4 3 5
      _ = 0 := h.h1345
  · calc
      pairRow c d 1 4 5 0 = pairRow c d 1 4 0 5 := pr_swap23 c d 1 4 5 0
      _ = pairRow c d 1 0 4 5 := pr_swap12 c d 1 4 0 5
      _ = pairRow c d 0 1 4 5 := pr_swap01 c d 1 0 4 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 1 4 5 2 = pairRow c d 1 4 2 5 := pr_swap23 c d 1 4 5 2
      _ = pairRow c d 1 2 4 5 := pr_swap12 c d 1 4 2 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 1 4 5 3 = pairRow c d 1 4 3 5 := pr_swap23 c d 1 4 5 3
      _ = pairRow c d 1 3 4 5 := pr_swap12 c d 1 4 3 5
      _ = 0 := h.h1345

lemma pairRow_all_i1_j5 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (1 : Fin 6) ≠ k) (hil : (1 : Fin 6) ≠ l)
    (hjk : (5 : Fin 6) ≠ k) (hjl : (5 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 1 5 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 1 5 0 2 = pairRow c d 1 0 5 2 := pr_swap12 c d 1 5 0 2
      _ = pairRow c d 0 1 5 2 := pr_swap01 c d 1 0 5 2
      _ = pairRow c d 0 1 2 5 := pr_swap23 c d 0 1 5 2
      _ = 0 := h.h0125
  · calc
      pairRow c d 1 5 0 3 = pairRow c d 1 0 5 3 := pr_swap12 c d 1 5 0 3
      _ = pairRow c d 0 1 5 3 := pr_swap01 c d 1 0 5 3
      _ = pairRow c d 0 1 3 5 := pr_swap23 c d 0 1 5 3
      _ = 0 := h.h0135
  · calc
      pairRow c d 1 5 0 4 = pairRow c d 1 0 5 4 := pr_swap12 c d 1 5 0 4
      _ = pairRow c d 0 1 5 4 := pr_swap01 c d 1 0 5 4
      _ = pairRow c d 0 1 4 5 := pr_swap23 c d 0 1 5 4
      _ = 0 := h.h0145
  · calc
      pairRow c d 1 5 2 0 = pairRow c d 1 2 5 0 := pr_swap12 c d 1 5 2 0
      _ = pairRow c d 1 2 0 5 := pr_swap23 c d 1 2 5 0
      _ = pairRow c d 1 0 2 5 := pr_swap12 c d 1 2 0 5
      _ = pairRow c d 0 1 2 5 := pr_swap01 c d 1 0 2 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 1 5 2 3 = pairRow c d 1 2 5 3 := pr_swap12 c d 1 5 2 3
      _ = pairRow c d 1 2 3 5 := pr_swap23 c d 1 2 5 3
      _ = 0 := h.h1235
  · calc
      pairRow c d 1 5 2 4 = pairRow c d 1 2 5 4 := pr_swap12 c d 1 5 2 4
      _ = pairRow c d 1 2 4 5 := pr_swap23 c d 1 2 5 4
      _ = 0 := h.h1245
  · calc
      pairRow c d 1 5 3 0 = pairRow c d 1 3 5 0 := pr_swap12 c d 1 5 3 0
      _ = pairRow c d 1 3 0 5 := pr_swap23 c d 1 3 5 0
      _ = pairRow c d 1 0 3 5 := pr_swap12 c d 1 3 0 5
      _ = pairRow c d 0 1 3 5 := pr_swap01 c d 1 0 3 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 1 5 3 2 = pairRow c d 1 3 5 2 := pr_swap12 c d 1 5 3 2
      _ = pairRow c d 1 3 2 5 := pr_swap23 c d 1 3 5 2
      _ = pairRow c d 1 2 3 5 := pr_swap12 c d 1 3 2 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 1 5 3 4 = pairRow c d 1 3 5 4 := pr_swap12 c d 1 5 3 4
      _ = pairRow c d 1 3 4 5 := pr_swap23 c d 1 3 5 4
      _ = 0 := h.h1345
  · calc
      pairRow c d 1 5 4 0 = pairRow c d 1 4 5 0 := pr_swap12 c d 1 5 4 0
      _ = pairRow c d 1 4 0 5 := pr_swap23 c d 1 4 5 0
      _ = pairRow c d 1 0 4 5 := pr_swap12 c d 1 4 0 5
      _ = pairRow c d 0 1 4 5 := pr_swap01 c d 1 0 4 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 1 5 4 2 = pairRow c d 1 4 5 2 := pr_swap12 c d 1 5 4 2
      _ = pairRow c d 1 4 2 5 := pr_swap23 c d 1 4 5 2
      _ = pairRow c d 1 2 4 5 := pr_swap12 c d 1 4 2 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 1 5 4 3 = pairRow c d 1 4 5 3 := pr_swap12 c d 1 5 4 3
      _ = pairRow c d 1 4 3 5 := pr_swap23 c d 1 4 5 3
      _ = pairRow c d 1 3 4 5 := pr_swap12 c d 1 4 3 5
      _ = 0 := h.h1345

lemma pairRow_all_i2_j3 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (2 : Fin 6) ≠ k) (hil : (2 : Fin 6) ≠ l)
    (hjk : (3 : Fin 6) ≠ k) (hjl : (3 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 2 3 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 2 3 0 1 = pairRow c d 2 0 3 1 := pr_swap12 c d 2 3 0 1
      _ = pairRow c d 0 2 3 1 := pr_swap01 c d 2 0 3 1
      _ = pairRow c d 0 2 1 3 := pr_swap23 c d 0 2 3 1
      _ = pairRow c d 0 1 2 3 := pr_swap12 c d 0 2 1 3
      _ = 0 := h.h0123
  · calc
      pairRow c d 2 3 0 4 = pairRow c d 2 0 3 4 := pr_swap12 c d 2 3 0 4
      _ = pairRow c d 0 2 3 4 := pr_swap01 c d 2 0 3 4
      _ = 0 := h.h0234
  · calc
      pairRow c d 2 3 0 5 = pairRow c d 2 0 3 5 := pr_swap12 c d 2 3 0 5
      _ = pairRow c d 0 2 3 5 := pr_swap01 c d 2 0 3 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 2 3 1 0 = pairRow c d 2 1 3 0 := pr_swap12 c d 2 3 1 0
      _ = pairRow c d 1 2 3 0 := pr_swap01 c d 2 1 3 0
      _ = pairRow c d 1 2 0 3 := pr_swap23 c d 1 2 3 0
      _ = pairRow c d 1 0 2 3 := pr_swap12 c d 1 2 0 3
      _ = pairRow c d 0 1 2 3 := pr_swap01 c d 1 0 2 3
      _ = 0 := h.h0123
  · calc
      pairRow c d 2 3 1 4 = pairRow c d 2 1 3 4 := pr_swap12 c d 2 3 1 4
      _ = pairRow c d 1 2 3 4 := pr_swap01 c d 2 1 3 4
      _ = 0 := h.h1234
  · calc
      pairRow c d 2 3 1 5 = pairRow c d 2 1 3 5 := pr_swap12 c d 2 3 1 5
      _ = pairRow c d 1 2 3 5 := pr_swap01 c d 2 1 3 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 2 3 4 0 = pairRow c d 2 3 0 4 := pr_swap23 c d 2 3 4 0
      _ = pairRow c d 2 0 3 4 := pr_swap12 c d 2 3 0 4
      _ = pairRow c d 0 2 3 4 := pr_swap01 c d 2 0 3 4
      _ = 0 := h.h0234
  · calc
      pairRow c d 2 3 4 1 = pairRow c d 2 3 1 4 := pr_swap23 c d 2 3 4 1
      _ = pairRow c d 2 1 3 4 := pr_swap12 c d 2 3 1 4
      _ = pairRow c d 1 2 3 4 := pr_swap01 c d 2 1 3 4
      _ = 0 := h.h1234
  · exact h.h2345
  · calc
      pairRow c d 2 3 5 0 = pairRow c d 2 3 0 5 := pr_swap23 c d 2 3 5 0
      _ = pairRow c d 2 0 3 5 := pr_swap12 c d 2 3 0 5
      _ = pairRow c d 0 2 3 5 := pr_swap01 c d 2 0 3 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 2 3 5 1 = pairRow c d 2 3 1 5 := pr_swap23 c d 2 3 5 1
      _ = pairRow c d 2 1 3 5 := pr_swap12 c d 2 3 1 5
      _ = pairRow c d 1 2 3 5 := pr_swap01 c d 2 1 3 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 2 3 5 4 = pairRow c d 2 3 4 5 := pr_swap23 c d 2 3 5 4
      _ = 0 := h.h2345

lemma pairRow_all_i2_j4 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (2 : Fin 6) ≠ k) (hil : (2 : Fin 6) ≠ l)
    (hjk : (4 : Fin 6) ≠ k) (hjl : (4 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 2 4 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 2 4 0 1 = pairRow c d 2 0 4 1 := pr_swap12 c d 2 4 0 1
      _ = pairRow c d 0 2 4 1 := pr_swap01 c d 2 0 4 1
      _ = pairRow c d 0 2 1 4 := pr_swap23 c d 0 2 4 1
      _ = pairRow c d 0 1 2 4 := pr_swap12 c d 0 2 1 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 2 4 0 3 = pairRow c d 2 0 4 3 := pr_swap12 c d 2 4 0 3
      _ = pairRow c d 0 2 4 3 := pr_swap01 c d 2 0 4 3
      _ = pairRow c d 0 2 3 4 := pr_swap23 c d 0 2 4 3
      _ = 0 := h.h0234
  · calc
      pairRow c d 2 4 0 5 = pairRow c d 2 0 4 5 := pr_swap12 c d 2 4 0 5
      _ = pairRow c d 0 2 4 5 := pr_swap01 c d 2 0 4 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 2 4 1 0 = pairRow c d 2 1 4 0 := pr_swap12 c d 2 4 1 0
      _ = pairRow c d 1 2 4 0 := pr_swap01 c d 2 1 4 0
      _ = pairRow c d 1 2 0 4 := pr_swap23 c d 1 2 4 0
      _ = pairRow c d 1 0 2 4 := pr_swap12 c d 1 2 0 4
      _ = pairRow c d 0 1 2 4 := pr_swap01 c d 1 0 2 4
      _ = 0 := h.h0124
  · calc
      pairRow c d 2 4 1 3 = pairRow c d 2 1 4 3 := pr_swap12 c d 2 4 1 3
      _ = pairRow c d 1 2 4 3 := pr_swap01 c d 2 1 4 3
      _ = pairRow c d 1 2 3 4 := pr_swap23 c d 1 2 4 3
      _ = 0 := h.h1234
  · calc
      pairRow c d 2 4 1 5 = pairRow c d 2 1 4 5 := pr_swap12 c d 2 4 1 5
      _ = pairRow c d 1 2 4 5 := pr_swap01 c d 2 1 4 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 2 4 3 0 = pairRow c d 2 3 4 0 := pr_swap12 c d 2 4 3 0
      _ = pairRow c d 2 3 0 4 := pr_swap23 c d 2 3 4 0
      _ = pairRow c d 2 0 3 4 := pr_swap12 c d 2 3 0 4
      _ = pairRow c d 0 2 3 4 := pr_swap01 c d 2 0 3 4
      _ = 0 := h.h0234
  · calc
      pairRow c d 2 4 3 1 = pairRow c d 2 3 4 1 := pr_swap12 c d 2 4 3 1
      _ = pairRow c d 2 3 1 4 := pr_swap23 c d 2 3 4 1
      _ = pairRow c d 2 1 3 4 := pr_swap12 c d 2 3 1 4
      _ = pairRow c d 1 2 3 4 := pr_swap01 c d 2 1 3 4
      _ = 0 := h.h1234
  · calc
      pairRow c d 2 4 3 5 = pairRow c d 2 3 4 5 := pr_swap12 c d 2 4 3 5
      _ = 0 := h.h2345
  · calc
      pairRow c d 2 4 5 0 = pairRow c d 2 4 0 5 := pr_swap23 c d 2 4 5 0
      _ = pairRow c d 2 0 4 5 := pr_swap12 c d 2 4 0 5
      _ = pairRow c d 0 2 4 5 := pr_swap01 c d 2 0 4 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 2 4 5 1 = pairRow c d 2 4 1 5 := pr_swap23 c d 2 4 5 1
      _ = pairRow c d 2 1 4 5 := pr_swap12 c d 2 4 1 5
      _ = pairRow c d 1 2 4 5 := pr_swap01 c d 2 1 4 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 2 4 5 3 = pairRow c d 2 4 3 5 := pr_swap23 c d 2 4 5 3
      _ = pairRow c d 2 3 4 5 := pr_swap12 c d 2 4 3 5
      _ = 0 := h.h2345

lemma pairRow_all_i2_j5 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (2 : Fin 6) ≠ k) (hil : (2 : Fin 6) ≠ l)
    (hjk : (5 : Fin 6) ≠ k) (hjl : (5 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 2 5 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 2 5 0 1 = pairRow c d 2 0 5 1 := pr_swap12 c d 2 5 0 1
      _ = pairRow c d 0 2 5 1 := pr_swap01 c d 2 0 5 1
      _ = pairRow c d 0 2 1 5 := pr_swap23 c d 0 2 5 1
      _ = pairRow c d 0 1 2 5 := pr_swap12 c d 0 2 1 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 2 5 0 3 = pairRow c d 2 0 5 3 := pr_swap12 c d 2 5 0 3
      _ = pairRow c d 0 2 5 3 := pr_swap01 c d 2 0 5 3
      _ = pairRow c d 0 2 3 5 := pr_swap23 c d 0 2 5 3
      _ = 0 := h.h0235
  · calc
      pairRow c d 2 5 0 4 = pairRow c d 2 0 5 4 := pr_swap12 c d 2 5 0 4
      _ = pairRow c d 0 2 5 4 := pr_swap01 c d 2 0 5 4
      _ = pairRow c d 0 2 4 5 := pr_swap23 c d 0 2 5 4
      _ = 0 := h.h0245
  · calc
      pairRow c d 2 5 1 0 = pairRow c d 2 1 5 0 := pr_swap12 c d 2 5 1 0
      _ = pairRow c d 1 2 5 0 := pr_swap01 c d 2 1 5 0
      _ = pairRow c d 1 2 0 5 := pr_swap23 c d 1 2 5 0
      _ = pairRow c d 1 0 2 5 := pr_swap12 c d 1 2 0 5
      _ = pairRow c d 0 1 2 5 := pr_swap01 c d 1 0 2 5
      _ = 0 := h.h0125
  · calc
      pairRow c d 2 5 1 3 = pairRow c d 2 1 5 3 := pr_swap12 c d 2 5 1 3
      _ = pairRow c d 1 2 5 3 := pr_swap01 c d 2 1 5 3
      _ = pairRow c d 1 2 3 5 := pr_swap23 c d 1 2 5 3
      _ = 0 := h.h1235
  · calc
      pairRow c d 2 5 1 4 = pairRow c d 2 1 5 4 := pr_swap12 c d 2 5 1 4
      _ = pairRow c d 1 2 5 4 := pr_swap01 c d 2 1 5 4
      _ = pairRow c d 1 2 4 5 := pr_swap23 c d 1 2 5 4
      _ = 0 := h.h1245
  · calc
      pairRow c d 2 5 3 0 = pairRow c d 2 3 5 0 := pr_swap12 c d 2 5 3 0
      _ = pairRow c d 2 3 0 5 := pr_swap23 c d 2 3 5 0
      _ = pairRow c d 2 0 3 5 := pr_swap12 c d 2 3 0 5
      _ = pairRow c d 0 2 3 5 := pr_swap01 c d 2 0 3 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 2 5 3 1 = pairRow c d 2 3 5 1 := pr_swap12 c d 2 5 3 1
      _ = pairRow c d 2 3 1 5 := pr_swap23 c d 2 3 5 1
      _ = pairRow c d 2 1 3 5 := pr_swap12 c d 2 3 1 5
      _ = pairRow c d 1 2 3 5 := pr_swap01 c d 2 1 3 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 2 5 3 4 = pairRow c d 2 3 5 4 := pr_swap12 c d 2 5 3 4
      _ = pairRow c d 2 3 4 5 := pr_swap23 c d 2 3 5 4
      _ = 0 := h.h2345
  · calc
      pairRow c d 2 5 4 0 = pairRow c d 2 4 5 0 := pr_swap12 c d 2 5 4 0
      _ = pairRow c d 2 4 0 5 := pr_swap23 c d 2 4 5 0
      _ = pairRow c d 2 0 4 5 := pr_swap12 c d 2 4 0 5
      _ = pairRow c d 0 2 4 5 := pr_swap01 c d 2 0 4 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 2 5 4 1 = pairRow c d 2 4 5 1 := pr_swap12 c d 2 5 4 1
      _ = pairRow c d 2 4 1 5 := pr_swap23 c d 2 4 5 1
      _ = pairRow c d 2 1 4 5 := pr_swap12 c d 2 4 1 5
      _ = pairRow c d 1 2 4 5 := pr_swap01 c d 2 1 4 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 2 5 4 3 = pairRow c d 2 4 5 3 := pr_swap12 c d 2 5 4 3
      _ = pairRow c d 2 4 3 5 := pr_swap23 c d 2 4 5 3
      _ = pairRow c d 2 3 4 5 := pr_swap12 c d 2 4 3 5
      _ = 0 := h.h2345

lemma pairRow_all_i3_j4 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (3 : Fin 6) ≠ k) (hil : (3 : Fin 6) ≠ l)
    (hjk : (4 : Fin 6) ≠ k) (hjl : (4 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 3 4 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 3 4 0 1 = pairRow c d 3 0 4 1 := pr_swap12 c d 3 4 0 1
      _ = pairRow c d 0 3 4 1 := pr_swap01 c d 3 0 4 1
      _ = pairRow c d 0 3 1 4 := pr_swap23 c d 0 3 4 1
      _ = pairRow c d 0 1 3 4 := pr_swap12 c d 0 3 1 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 3 4 0 2 = pairRow c d 3 0 4 2 := pr_swap12 c d 3 4 0 2
      _ = pairRow c d 0 3 4 2 := pr_swap01 c d 3 0 4 2
      _ = pairRow c d 0 3 2 4 := pr_swap23 c d 0 3 4 2
      _ = pairRow c d 0 2 3 4 := pr_swap12 c d 0 3 2 4
      _ = 0 := h.h0234
  · calc
      pairRow c d 3 4 0 5 = pairRow c d 3 0 4 5 := pr_swap12 c d 3 4 0 5
      _ = pairRow c d 0 3 4 5 := pr_swap01 c d 3 0 4 5
      _ = 0 := h.h0345
  · calc
      pairRow c d 3 4 1 0 = pairRow c d 3 1 4 0 := pr_swap12 c d 3 4 1 0
      _ = pairRow c d 1 3 4 0 := pr_swap01 c d 3 1 4 0
      _ = pairRow c d 1 3 0 4 := pr_swap23 c d 1 3 4 0
      _ = pairRow c d 1 0 3 4 := pr_swap12 c d 1 3 0 4
      _ = pairRow c d 0 1 3 4 := pr_swap01 c d 1 0 3 4
      _ = 0 := h.h0134
  · calc
      pairRow c d 3 4 1 2 = pairRow c d 3 1 4 2 := pr_swap12 c d 3 4 1 2
      _ = pairRow c d 1 3 4 2 := pr_swap01 c d 3 1 4 2
      _ = pairRow c d 1 3 2 4 := pr_swap23 c d 1 3 4 2
      _ = pairRow c d 1 2 3 4 := pr_swap12 c d 1 3 2 4
      _ = 0 := h.h1234
  · calc
      pairRow c d 3 4 1 5 = pairRow c d 3 1 4 5 := pr_swap12 c d 3 4 1 5
      _ = pairRow c d 1 3 4 5 := pr_swap01 c d 3 1 4 5
      _ = 0 := h.h1345
  · calc
      pairRow c d 3 4 2 0 = pairRow c d 3 2 4 0 := pr_swap12 c d 3 4 2 0
      _ = pairRow c d 2 3 4 0 := pr_swap01 c d 3 2 4 0
      _ = pairRow c d 2 3 0 4 := pr_swap23 c d 2 3 4 0
      _ = pairRow c d 2 0 3 4 := pr_swap12 c d 2 3 0 4
      _ = pairRow c d 0 2 3 4 := pr_swap01 c d 2 0 3 4
      _ = 0 := h.h0234
  · calc
      pairRow c d 3 4 2 1 = pairRow c d 3 2 4 1 := pr_swap12 c d 3 4 2 1
      _ = pairRow c d 2 3 4 1 := pr_swap01 c d 3 2 4 1
      _ = pairRow c d 2 3 1 4 := pr_swap23 c d 2 3 4 1
      _ = pairRow c d 2 1 3 4 := pr_swap12 c d 2 3 1 4
      _ = pairRow c d 1 2 3 4 := pr_swap01 c d 2 1 3 4
      _ = 0 := h.h1234
  · calc
      pairRow c d 3 4 2 5 = pairRow c d 3 2 4 5 := pr_swap12 c d 3 4 2 5
      _ = pairRow c d 2 3 4 5 := pr_swap01 c d 3 2 4 5
      _ = 0 := h.h2345
  · calc
      pairRow c d 3 4 5 0 = pairRow c d 3 4 0 5 := pr_swap23 c d 3 4 5 0
      _ = pairRow c d 3 0 4 5 := pr_swap12 c d 3 4 0 5
      _ = pairRow c d 0 3 4 5 := pr_swap01 c d 3 0 4 5
      _ = 0 := h.h0345
  · calc
      pairRow c d 3 4 5 1 = pairRow c d 3 4 1 5 := pr_swap23 c d 3 4 5 1
      _ = pairRow c d 3 1 4 5 := pr_swap12 c d 3 4 1 5
      _ = pairRow c d 1 3 4 5 := pr_swap01 c d 3 1 4 5
      _ = 0 := h.h1345
  · calc
      pairRow c d 3 4 5 2 = pairRow c d 3 4 2 5 := pr_swap23 c d 3 4 5 2
      _ = pairRow c d 3 2 4 5 := pr_swap12 c d 3 4 2 5
      _ = pairRow c d 2 3 4 5 := pr_swap01 c d 3 2 4 5
      _ = 0 := h.h2345

lemma pairRow_all_i3_j5 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (3 : Fin 6) ≠ k) (hil : (3 : Fin 6) ≠ l)
    (hjk : (5 : Fin 6) ≠ k) (hjl : (5 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 3 5 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 3 5 0 1 = pairRow c d 3 0 5 1 := pr_swap12 c d 3 5 0 1
      _ = pairRow c d 0 3 5 1 := pr_swap01 c d 3 0 5 1
      _ = pairRow c d 0 3 1 5 := pr_swap23 c d 0 3 5 1
      _ = pairRow c d 0 1 3 5 := pr_swap12 c d 0 3 1 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 3 5 0 2 = pairRow c d 3 0 5 2 := pr_swap12 c d 3 5 0 2
      _ = pairRow c d 0 3 5 2 := pr_swap01 c d 3 0 5 2
      _ = pairRow c d 0 3 2 5 := pr_swap23 c d 0 3 5 2
      _ = pairRow c d 0 2 3 5 := pr_swap12 c d 0 3 2 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 3 5 0 4 = pairRow c d 3 0 5 4 := pr_swap12 c d 3 5 0 4
      _ = pairRow c d 0 3 5 4 := pr_swap01 c d 3 0 5 4
      _ = pairRow c d 0 3 4 5 := pr_swap23 c d 0 3 5 4
      _ = 0 := h.h0345
  · calc
      pairRow c d 3 5 1 0 = pairRow c d 3 1 5 0 := pr_swap12 c d 3 5 1 0
      _ = pairRow c d 1 3 5 0 := pr_swap01 c d 3 1 5 0
      _ = pairRow c d 1 3 0 5 := pr_swap23 c d 1 3 5 0
      _ = pairRow c d 1 0 3 5 := pr_swap12 c d 1 3 0 5
      _ = pairRow c d 0 1 3 5 := pr_swap01 c d 1 0 3 5
      _ = 0 := h.h0135
  · calc
      pairRow c d 3 5 1 2 = pairRow c d 3 1 5 2 := pr_swap12 c d 3 5 1 2
      _ = pairRow c d 1 3 5 2 := pr_swap01 c d 3 1 5 2
      _ = pairRow c d 1 3 2 5 := pr_swap23 c d 1 3 5 2
      _ = pairRow c d 1 2 3 5 := pr_swap12 c d 1 3 2 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 3 5 1 4 = pairRow c d 3 1 5 4 := pr_swap12 c d 3 5 1 4
      _ = pairRow c d 1 3 5 4 := pr_swap01 c d 3 1 5 4
      _ = pairRow c d 1 3 4 5 := pr_swap23 c d 1 3 5 4
      _ = 0 := h.h1345
  · calc
      pairRow c d 3 5 2 0 = pairRow c d 3 2 5 0 := pr_swap12 c d 3 5 2 0
      _ = pairRow c d 2 3 5 0 := pr_swap01 c d 3 2 5 0
      _ = pairRow c d 2 3 0 5 := pr_swap23 c d 2 3 5 0
      _ = pairRow c d 2 0 3 5 := pr_swap12 c d 2 3 0 5
      _ = pairRow c d 0 2 3 5 := pr_swap01 c d 2 0 3 5
      _ = 0 := h.h0235
  · calc
      pairRow c d 3 5 2 1 = pairRow c d 3 2 5 1 := pr_swap12 c d 3 5 2 1
      _ = pairRow c d 2 3 5 1 := pr_swap01 c d 3 2 5 1
      _ = pairRow c d 2 3 1 5 := pr_swap23 c d 2 3 5 1
      _ = pairRow c d 2 1 3 5 := pr_swap12 c d 2 3 1 5
      _ = pairRow c d 1 2 3 5 := pr_swap01 c d 2 1 3 5
      _ = 0 := h.h1235
  · calc
      pairRow c d 3 5 2 4 = pairRow c d 3 2 5 4 := pr_swap12 c d 3 5 2 4
      _ = pairRow c d 2 3 5 4 := pr_swap01 c d 3 2 5 4
      _ = pairRow c d 2 3 4 5 := pr_swap23 c d 2 3 5 4
      _ = 0 := h.h2345
  · calc
      pairRow c d 3 5 4 0 = pairRow c d 3 4 5 0 := pr_swap12 c d 3 5 4 0
      _ = pairRow c d 3 4 0 5 := pr_swap23 c d 3 4 5 0
      _ = pairRow c d 3 0 4 5 := pr_swap12 c d 3 4 0 5
      _ = pairRow c d 0 3 4 5 := pr_swap01 c d 3 0 4 5
      _ = 0 := h.h0345
  · calc
      pairRow c d 3 5 4 1 = pairRow c d 3 4 5 1 := pr_swap12 c d 3 5 4 1
      _ = pairRow c d 3 4 1 5 := pr_swap23 c d 3 4 5 1
      _ = pairRow c d 3 1 4 5 := pr_swap12 c d 3 4 1 5
      _ = pairRow c d 1 3 4 5 := pr_swap01 c d 3 1 4 5
      _ = 0 := h.h1345
  · calc
      pairRow c d 3 5 4 2 = pairRow c d 3 4 5 2 := pr_swap12 c d 3 5 4 2
      _ = pairRow c d 3 4 2 5 := pr_swap23 c d 3 4 5 2
      _ = pairRow c d 3 2 4 5 := pr_swap12 c d 3 4 2 5
      _ = pairRow c d 2 3 4 5 := pr_swap01 c d 3 2 4 5
      _ = 0 := h.h2345

lemma pairRow_all_i4_j5 (c d : SS.State 6 ℂ) (h : PairRows c d)
    (k l : Fin 6) (hik : (4 : Fin 6) ≠ k) (hil : (4 : Fin 6) ≠ l)
    (hjk : (5 : Fin 6) ≠ k) (hjl : (5 : Fin 6) ≠ l) (hkl : k ≠ l) :
    pairRow c d 4 5 k l = 0 := by
  fin_cases k
  all_goals simp at hik hjk
  all_goals fin_cases l
  all_goals simp at hil hjl hkl
  · calc
      pairRow c d 4 5 0 1 = pairRow c d 4 0 5 1 := pr_swap12 c d 4 5 0 1
      _ = pairRow c d 0 4 5 1 := pr_swap01 c d 4 0 5 1
      _ = pairRow c d 0 4 1 5 := pr_swap23 c d 0 4 5 1
      _ = pairRow c d 0 1 4 5 := pr_swap12 c d 0 4 1 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 4 5 0 2 = pairRow c d 4 0 5 2 := pr_swap12 c d 4 5 0 2
      _ = pairRow c d 0 4 5 2 := pr_swap01 c d 4 0 5 2
      _ = pairRow c d 0 4 2 5 := pr_swap23 c d 0 4 5 2
      _ = pairRow c d 0 2 4 5 := pr_swap12 c d 0 4 2 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 4 5 0 3 = pairRow c d 4 0 5 3 := pr_swap12 c d 4 5 0 3
      _ = pairRow c d 0 4 5 3 := pr_swap01 c d 4 0 5 3
      _ = pairRow c d 0 4 3 5 := pr_swap23 c d 0 4 5 3
      _ = pairRow c d 0 3 4 5 := pr_swap12 c d 0 4 3 5
      _ = 0 := h.h0345
  · calc
      pairRow c d 4 5 1 0 = pairRow c d 4 1 5 0 := pr_swap12 c d 4 5 1 0
      _ = pairRow c d 1 4 5 0 := pr_swap01 c d 4 1 5 0
      _ = pairRow c d 1 4 0 5 := pr_swap23 c d 1 4 5 0
      _ = pairRow c d 1 0 4 5 := pr_swap12 c d 1 4 0 5
      _ = pairRow c d 0 1 4 5 := pr_swap01 c d 1 0 4 5
      _ = 0 := h.h0145
  · calc
      pairRow c d 4 5 1 2 = pairRow c d 4 1 5 2 := pr_swap12 c d 4 5 1 2
      _ = pairRow c d 1 4 5 2 := pr_swap01 c d 4 1 5 2
      _ = pairRow c d 1 4 2 5 := pr_swap23 c d 1 4 5 2
      _ = pairRow c d 1 2 4 5 := pr_swap12 c d 1 4 2 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 4 5 1 3 = pairRow c d 4 1 5 3 := pr_swap12 c d 4 5 1 3
      _ = pairRow c d 1 4 5 3 := pr_swap01 c d 4 1 5 3
      _ = pairRow c d 1 4 3 5 := pr_swap23 c d 1 4 5 3
      _ = pairRow c d 1 3 4 5 := pr_swap12 c d 1 4 3 5
      _ = 0 := h.h1345
  · calc
      pairRow c d 4 5 2 0 = pairRow c d 4 2 5 0 := pr_swap12 c d 4 5 2 0
      _ = pairRow c d 2 4 5 0 := pr_swap01 c d 4 2 5 0
      _ = pairRow c d 2 4 0 5 := pr_swap23 c d 2 4 5 0
      _ = pairRow c d 2 0 4 5 := pr_swap12 c d 2 4 0 5
      _ = pairRow c d 0 2 4 5 := pr_swap01 c d 2 0 4 5
      _ = 0 := h.h0245
  · calc
      pairRow c d 4 5 2 1 = pairRow c d 4 2 5 1 := pr_swap12 c d 4 5 2 1
      _ = pairRow c d 2 4 5 1 := pr_swap01 c d 4 2 5 1
      _ = pairRow c d 2 4 1 5 := pr_swap23 c d 2 4 5 1
      _ = pairRow c d 2 1 4 5 := pr_swap12 c d 2 4 1 5
      _ = pairRow c d 1 2 4 5 := pr_swap01 c d 2 1 4 5
      _ = 0 := h.h1245
  · calc
      pairRow c d 4 5 2 3 = pairRow c d 4 2 5 3 := pr_swap12 c d 4 5 2 3
      _ = pairRow c d 2 4 5 3 := pr_swap01 c d 4 2 5 3
      _ = pairRow c d 2 4 3 5 := pr_swap23 c d 2 4 5 3
      _ = pairRow c d 2 3 4 5 := pr_swap12 c d 2 4 3 5
      _ = 0 := h.h2345
  · calc
      pairRow c d 4 5 3 0 = pairRow c d 4 3 5 0 := pr_swap12 c d 4 5 3 0
      _ = pairRow c d 3 4 5 0 := pr_swap01 c d 4 3 5 0
      _ = pairRow c d 3 4 0 5 := pr_swap23 c d 3 4 5 0
      _ = pairRow c d 3 0 4 5 := pr_swap12 c d 3 4 0 5
      _ = pairRow c d 0 3 4 5 := pr_swap01 c d 3 0 4 5
      _ = 0 := h.h0345
  · calc
      pairRow c d 4 5 3 1 = pairRow c d 4 3 5 1 := pr_swap12 c d 4 5 3 1
      _ = pairRow c d 3 4 5 1 := pr_swap01 c d 4 3 5 1
      _ = pairRow c d 3 4 1 5 := pr_swap23 c d 3 4 5 1
      _ = pairRow c d 3 1 4 5 := pr_swap12 c d 3 4 1 5
      _ = pairRow c d 1 3 4 5 := pr_swap01 c d 3 1 4 5
      _ = 0 := h.h1345
  · calc
      pairRow c d 4 5 3 2 = pairRow c d 4 3 5 2 := pr_swap12 c d 4 5 3 2
      _ = pairRow c d 3 4 5 2 := pr_swap01 c d 4 3 5 2
      _ = pairRow c d 3 4 2 5 := pr_swap23 c d 3 4 5 2
      _ = pairRow c d 3 2 4 5 := pr_swap12 c d 3 4 2 5
      _ = pairRow c d 2 3 4 5 := pr_swap01 c d 3 2 4 5
      _ = 0 := h.h2345


/-- The fifteen KL-derived canonical rows cover every ordered four-tuple of
pairwise distinct vertices. -/
theorem pairRow_all (c d : SS.State 6 ℂ) (h : PairRows c d)
    (i j k l : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    pairRow c d i j k l = 0 := by
  fin_cases i <;> fin_cases j
  all_goals simp at hij
  · exact pairRow_all_i0_j1 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i0_j2 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i0_j3 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i0_j4 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i0_j5 c d h k l hik hil hjk hjl hkl
  · calc
      pairRow c d 1 0 k l = pairRow c d 0 1 k l := pr_swap01 c d 1 0 k l
      _ = 0 := pairRow_all_i0_j1 c d h k l hjk hjl hik hil hkl
  · exact pairRow_all_i1_j2 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i1_j3 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i1_j4 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i1_j5 c d h k l hik hil hjk hjl hkl
  · calc
      pairRow c d 2 0 k l = pairRow c d 0 2 k l := pr_swap01 c d 2 0 k l
      _ = 0 := pairRow_all_i0_j2 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 2 1 k l = pairRow c d 1 2 k l := pr_swap01 c d 2 1 k l
      _ = 0 := pairRow_all_i1_j2 c d h k l hjk hjl hik hil hkl
  · exact pairRow_all_i2_j3 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i2_j4 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i2_j5 c d h k l hik hil hjk hjl hkl
  · calc
      pairRow c d 3 0 k l = pairRow c d 0 3 k l := pr_swap01 c d 3 0 k l
      _ = 0 := pairRow_all_i0_j3 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 3 1 k l = pairRow c d 1 3 k l := pr_swap01 c d 3 1 k l
      _ = 0 := pairRow_all_i1_j3 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 3 2 k l = pairRow c d 2 3 k l := pr_swap01 c d 3 2 k l
      _ = 0 := pairRow_all_i2_j3 c d h k l hjk hjl hik hil hkl
  · exact pairRow_all_i3_j4 c d h k l hik hil hjk hjl hkl
  · exact pairRow_all_i3_j5 c d h k l hik hil hjk hjl hkl
  · calc
      pairRow c d 4 0 k l = pairRow c d 0 4 k l := pr_swap01 c d 4 0 k l
      _ = 0 := pairRow_all_i0_j4 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 4 1 k l = pairRow c d 1 4 k l := pr_swap01 c d 4 1 k l
      _ = 0 := pairRow_all_i1_j4 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 4 2 k l = pairRow c d 2 4 k l := pr_swap01 c d 4 2 k l
      _ = 0 := pairRow_all_i2_j4 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 4 3 k l = pairRow c d 3 4 k l := pr_swap01 c d 4 3 k l
      _ = 0 := pairRow_all_i3_j4 c d h k l hjk hjl hik hil hkl
  · exact pairRow_all_i4_j5 c d h k l hik hil hjk hjl hkl
  · calc
      pairRow c d 5 0 k l = pairRow c d 0 5 k l := pr_swap01 c d 5 0 k l
      _ = 0 := pairRow_all_i0_j5 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 5 1 k l = pairRow c d 1 5 k l := pr_swap01 c d 5 1 k l
      _ = 0 := pairRow_all_i1_j5 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 5 2 k l = pairRow c d 2 5 k l := pr_swap01 c d 5 2 k l
      _ = 0 := pairRow_all_i2_j5 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 5 3 k l = pairRow c d 3 5 k l := pr_swap01 c d 5 3 k l
      _ = 0 := pairRow_all_i3_j5 c d h k l hjk hjl hik hil hkl
  · calc
      pairRow c d 5 4 k l = pairRow c d 4 5 k l := pr_swap01 c d 5 4 k l
      _ = 0 := pairRow_all_i4_j5 c d h k l hjk hjl hik hil hkl

end

end SixQubit.Orbit9Universal
