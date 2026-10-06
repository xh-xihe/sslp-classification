# Alternative proofs

`Orbit5_brutecoords.lean.txt` is a SECOND, independent proof of orbit 5, produced in
parallel with the one now installed as `SixQubit/Orbit5.lean`.

The installed version discharges the flip-kernel dichotomy by casing on the scalar
invariant `dsc u = (u†u)² − 4·conj(det U)·det U` (see `SixQubit/Flip5.lean`).
This one instead expands everything into coordinates and cases on an explicit
branch polynomial (see `SixQubit/Kernel5.lean`, which IS installed and compiles).

Both were verified to compile cleanly and to have the axiom footprint
`[propext, Classical.choice, Quot.sound]`. Only one can occupy `SixQubit/Orbit5.lean`,
so the other is parked here as `.txt` (lake ignores it). To swap:

```sh
cp alternatives/Orbit5_brutecoords.lean.txt SixQubit/Orbit5.lean
lake build SixQubit.Orbit5
```

Having two independent proofs of the same statement, each kernel-checked, is a
stronger position than having one; that is why this is kept rather than deleted.
