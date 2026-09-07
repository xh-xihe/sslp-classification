import SixQubit.Generated.OpenMParity.Rows0
import SixQubit.Generated.OpenMParity.Rows1
import SixQubit.Generated.OpenMParity.Rows2
import SixQubit.Generated.OpenMParity.Rows3
import SixQubit.Generated.OpenMParity.Rows4
import SixQubit.Generated.OpenMParity.Rows5
import SixQubit.Generated.OpenMParity.Rows6
import SixQubit.Generated.OpenMParity.Rows7

namespace SixQubit.OpenMParity

open SixQubit.Realize SixQubit.Orbit8Family
open SixQubit.ParityCircleFamily SixQubit.ParityMomentFamily

theorem all_rows (P : SS.PauliString 6) : rowCheck P := by
  have hx := num_lt P.x
  have hz := num_lt P.z
  have he : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
    cases P; simp only [nbit_num]
  rw [← he]
  have hblock : num P.x / 8 < 8 := by omega
  interval_cases hb : num P.x / 8
  · have h := rows0 (num P.x - 0) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega
  · have h := rows1 (num P.x - 8) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega
  · have h := rows2 (num P.x - 16) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega
  · have h := rows3 (num P.x - 24) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega
  · have h := rows4 (num P.x - 32) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega
  · have h := rows5 (num P.x - 40) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega
  · have h := rows6 (num P.x - 48) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega
  · have h := rows7 (num P.x - 56) (by omega) (num P.z) hz
    convert h using 1
    congr 2
    omega

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

def certificate : SixQubit.ParityMomentFamily.Certificate where
  angle := angle
  c0 := c0
  c1 := c1
  L0 := L0
  L1 := L1
  denominator := 32
  denominator_pos := by decide
  L0_nodup := by decide
  L1_nodup := by decide
  vanishes0 := by decide
  vanishes1 := by decide
  fiber0 := by decide
  fiber1 := by decide
  kl := fun P hP => (all_rows P).1 hP
  norm0 := by decide
  norm1 := by decide

end SixQubit.OpenMParity
