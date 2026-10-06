import MainTheory.Generated.Orbit31VertexReconstructions.Shard000
import MainTheory.Generated.Orbit31VertexReconstructions.Shard001
import MainTheory.Generated.Orbit31VertexReconstructions.Shard002
import MainTheory.Generated.Orbit31VertexReconstructions.Shard003
import MainTheory.Generated.Orbit31VertexReconstructions.Shard004
import MainTheory.Generated.Orbit31VertexReconstructions.Shard005
import MainTheory.Generated.Orbit31VertexReconstructions.Shard006
import MainTheory.Generated.Orbit31VertexReconstructions.Shard007
import MainTheory.Generated.Orbit31VertexReconstructions.Shard008
import MainTheory.Generated.Orbit31VertexReconstructions.Shard009
import MainTheory.Generated.Orbit31VertexReconstructions.Shard010
import MainTheory.Generated.Orbit31VertexReconstructions.Shard011
import MainTheory.Generated.Orbit31VertexReconstructions.Shard012

/-! Each of the 204 real candidates is unique on its face and is a vertex. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31VertexReconstructions.Aggregate
open MainTheory.Orbit31VertexCertificateBase
noncomputable section
def candidate (v : Fin 204) : Matrix (Fin 16) (Fin 7) ℤ :=
  if h0 : v.val < 16 then Shard000.candidates ⟨v.val-0,by omega⟩ else
  if h1 : v.val < 32 then Shard001.candidates ⟨v.val-16,by omega⟩ else
  if h2 : v.val < 48 then Shard002.candidates ⟨v.val-32,by omega⟩ else
  if h3 : v.val < 64 then Shard003.candidates ⟨v.val-48,by omega⟩ else
  if h4 : v.val < 80 then Shard004.candidates ⟨v.val-64,by omega⟩ else
  if h5 : v.val < 96 then Shard005.candidates ⟨v.val-80,by omega⟩ else
  if h6 : v.val < 112 then Shard006.candidates ⟨v.val-96,by omega⟩ else
  if h7 : v.val < 128 then Shard007.candidates ⟨v.val-112,by omega⟩ else
  if h8 : v.val < 144 then Shard008.candidates ⟨v.val-128,by omega⟩ else
  if h9 : v.val < 160 then Shard009.candidates ⟨v.val-144,by omega⟩ else
  if h10 : v.val < 176 then Shard010.candidates ⟨v.val-160,by omega⟩ else
  if h11 : v.val < 192 then Shard011.candidates ⟨v.val-176,by omega⟩ else
  Shard012.candidates ⟨v.val-192,by omega⟩

theorem valid (v : Fin 204) : Valid v (candidate v) := by
  unfold candidate
  by_cases h0 : v.val < 16
  · rw [dif_pos h0]
    have hi : (⟨0+(v.val-0),by omega⟩ : Fin 204) = v := by
      apply Fin.ext
      dsimp
      omega
    simpa only [hi] using Shard000.checked ⟨v.val-0,by omega⟩
  · rw [dif_neg h0]
    by_cases h1 : v.val < 32
    · rw [dif_pos h1]
      have hi : (⟨16+(v.val-16),by omega⟩ : Fin 204) = v := by
        apply Fin.ext
        dsimp
        omega
      simpa only [hi] using Shard001.checked ⟨v.val-16,by omega⟩
    · rw [dif_neg h1]
      by_cases h2 : v.val < 48
      · rw [dif_pos h2]
        have hi : (⟨32+(v.val-32),by omega⟩ : Fin 204) = v := by
          apply Fin.ext
          dsimp
          omega
        simpa only [hi] using Shard002.checked ⟨v.val-32,by omega⟩
      · rw [dif_neg h2]
        by_cases h3 : v.val < 64
        · rw [dif_pos h3]
          have hi : (⟨48+(v.val-48),by omega⟩ : Fin 204) = v := by
            apply Fin.ext
            dsimp
            omega
          simpa only [hi] using Shard003.checked ⟨v.val-48,by omega⟩
        · rw [dif_neg h3]
          by_cases h4 : v.val < 80
          · rw [dif_pos h4]
            have hi : (⟨64+(v.val-64),by omega⟩ : Fin 204) = v := by
              apply Fin.ext
              dsimp
              omega
            simpa only [hi] using Shard004.checked ⟨v.val-64,by omega⟩
          · rw [dif_neg h4]
            by_cases h5 : v.val < 96
            · rw [dif_pos h5]
              have hi : (⟨80+(v.val-80),by omega⟩ : Fin 204) = v := by
                apply Fin.ext
                dsimp
                omega
              simpa only [hi] using Shard005.checked ⟨v.val-80,by omega⟩
            · rw [dif_neg h5]
              by_cases h6 : v.val < 112
              · rw [dif_pos h6]
                have hi : (⟨96+(v.val-96),by omega⟩ : Fin 204) = v := by
                  apply Fin.ext
                  dsimp
                  omega
                simpa only [hi] using Shard006.checked ⟨v.val-96,by omega⟩
              · rw [dif_neg h6]
                by_cases h7 : v.val < 128
                · rw [dif_pos h7]
                  have hi : (⟨112+(v.val-112),by omega⟩ : Fin 204) = v := by
                    apply Fin.ext
                    dsimp
                    omega
                  simpa only [hi] using Shard007.checked ⟨v.val-112,by omega⟩
                · rw [dif_neg h7]
                  by_cases h8 : v.val < 144
                  · rw [dif_pos h8]
                    have hi : (⟨128+(v.val-128),by omega⟩ : Fin 204) = v := by
                      apply Fin.ext
                      dsimp
                      omega
                    simpa only [hi] using Shard008.checked ⟨v.val-128,by omega⟩
                  · rw [dif_neg h8]
                    by_cases h9 : v.val < 160
                    · rw [dif_pos h9]
                      have hi : (⟨144+(v.val-144),by omega⟩ : Fin 204) = v := by
                        apply Fin.ext
                        dsimp
                        omega
                      simpa only [hi] using Shard009.checked ⟨v.val-144,by omega⟩
                    · rw [dif_neg h9]
                      by_cases h10 : v.val < 176
                      · rw [dif_pos h10]
                        have hi : (⟨160+(v.val-160),by omega⟩ : Fin 204) = v := by
                          apply Fin.ext
                          dsimp
                          omega
                        simpa only [hi] using Shard010.checked ⟨v.val-160,by omega⟩
                      · rw [dif_neg h10]
                        by_cases h11 : v.val < 192
                        · rw [dif_pos h11]
                          have hi : (⟨176+(v.val-176),by omega⟩ : Fin 204) = v := by
                            apply Fin.ext
                            dsimp
                            omega
                          simpa only [hi] using Shard011.checked ⟨v.val-176,by omega⟩
                        · rw [dif_neg h11]
                          have hi : (⟨192+(v.val-192),by omega⟩ : Fin 204) = v := by
                            apply Fin.ext
                            dsimp
                            omega
                          simpa only [hi] using Shard012.checked ⟨v.val-192,by omega⟩

theorem every_candidate_extreme (v : Fin 204) :
    MainTheory.Orbit31SupportSemantics.primal v ∈
    ({p | MainTheory.MatrixPositiveSupportCertificates.Feasible
      MainTheory.Orbit31SupportBase.M MainTheory.Orbit31SupportBase.b p} :
      Set (Fin 16 → ℝ)).extremePoints ℝ := extreme (valid v)
end
end MainTheory.Generated.Orbit31VertexReconstructions.Aggregate
