-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard037

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard006

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0_1_4_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032.canonicalBound_0523

theorem cover_p_0_1_4_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032.canonicalBound_0524

theorem cover_p_0_1_5_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032.canonicalBound_0525
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032.canonicalBound_0526
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032.canonicalBound_0527

theorem cover_p_0_1_5_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0528
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0529

theorem cover_p_0_1_5_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0530

theorem cover_p_0_1_5_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0531
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0532

theorem cover_p_0_1_5_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0533

theorem cover_p_0_1_5_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0534

theorem cover_p_0_1_6_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 6 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0535
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0536

theorem cover_p_0_1_6_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 6 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0537

theorem cover_p_0_1_6_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 6 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0538

theorem cover_p_0_1_7_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 7 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0539

theorem cover_p_0_2_2_2_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0540
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0541
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0542
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0543
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0544
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0545

theorem cover_p_0_2_2_2_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0546
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0547
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0548
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0549
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0550

theorem cover_p_0_2_2_2_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0551
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0552
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0553
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0554

theorem cover_p_0_2_2_2_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0555
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0556
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0557

theorem cover_p_0_2_2_2_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0558
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0559

theorem cover_p_0_2_2_2_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0560

theorem cover_p_0_2_2_3_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0561
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0562
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0563
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0564
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0565

theorem cover_p_0_2_2_3_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0566
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0567
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0568
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0569

theorem cover_p_0_2_2_3_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0570
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0571
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0572

theorem cover_p_0_2_2_3_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0573
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0574

theorem cover_p_0_2_2_3_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0575

theorem cover_p_0_2_2_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0576
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0577
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0578
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0579

theorem cover_p_0_2_2_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0580
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0581
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0582

theorem cover_p_0_2_2_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0583
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0584

theorem cover_p_0_2_2_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0585

theorem cover_p_0_2_2_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0586
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0587
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0588

theorem cover_p_0_2_2_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0589
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0590

theorem cover_p_0_2_2_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036.canonicalBound_0591

theorem cover_p_0_2_2_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard037.canonicalBound_0592
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard037.canonicalBound_0593

theorem cover_p_0_2_2_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard037.canonicalBound_0594

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard006
