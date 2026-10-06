import MainTheory.Orbit19ShellDisplays
set_option autoImplicit false
namespace MainTheory.Orbit19TailIdentity
open MainTheory.Orbit19ShellDisplays
theorem mismatch_square : ∀ x : SS.BitString 6,
    u x=((bit x 4 : ℚ)-(bit x 5 : ℚ))^2 := by decide +kernel
end MainTheory.Orbit19TailIdentity
