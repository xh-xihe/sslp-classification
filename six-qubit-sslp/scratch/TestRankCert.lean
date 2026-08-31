import MainTheory.AffineRankCertificate

namespace MainTheory.Generated.TestRankCert

open MainTheory.FinitePipeline
open MainTheory.AffineRankCertificate

def d : Data where
  rank := 6
  base := 0
  lowerPoints := [1, 2, 4, 24, 40, 48]
  lowerCoords := [0, 1, 2, 3, 4, 5]
  normals := []
  normalCoords := []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
example : d.Valid 72056498804490495 := by
  apply Data.valid_of_inverse_witnesses
  · refine
      { inverseRows := [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0],
          [0, 0, 1, 0, 0, 0], [0, 0, 0, (1 / 2), (1 / 2), (-1 / 2)],
          [0, 0, 0, (1 / 2), (-1 / 2), (1 / 2)],
          [0, 0, 0, (-1 / 2), (1 / 2), (1 / 2)]]
        rank_le := by norm_num [d]
        base_lt := by norm_num [d]
        base_mem := by
          norm_num [d, Data.baseWord, AffineRankCertificate.wordOfNat, InMask,
            Nat.testBit, Nat.shiftRight_eq_div_pow]
        lower_length := by norm_num [d]
        coord_length := by norm_num [d]
        lower_lt := by intro i; fin_cases i <;> norm_num [d]
        lower_mem := by
          intro i
          fin_cases i <;>
            norm_num [d, Data.lowerWord, AffineRankCertificate.wordOfNat, InMask,
              Nat.testBit, Nat.shiftRight_eq_div_pow]
        coord_lt := by
          intro j
          fin_cases j <;> norm_num [d, Data.lowerCoord, coordOfNat]
        right_inverse := by decide }
  · refine
      { inverseRows := []
        rank_le := by norm_num [d]
        normals_length := by norm_num [d]
        normal_width := by intro i; exact Fin.elim0 i
        coord_length := by norm_num [d]
        coord_lt := by intro j; exact Fin.elim0 j
        right_inverse := by ext i; exact Fin.elim0 i
        annihilates := by intro x hx i; exact Fin.elim0 i }

end MainTheory.Generated.TestRankCert
