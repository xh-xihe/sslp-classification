"""ADVERSARIAL from-scratch re-verification of bd12_type_II (arXiv:2504.20847, App D Type II).

No import of dyadic_lift's distance checker. We build:
  - the codeword |0_L>, |1_L> directly from the LaTeX (independent transcription)
  - every weight<=2 Pauli as explicit np.kron of single-qubit I/X/Y/Z
  - the 2x2 compressed matrix and require scalar*I.
We also independently recompute H1/H2/H3/H4 arithmetic, and re-run the lift chain
(using lift_once_dense for the LIFT only, but re-checking each rung with our own
from-scratch Pauli checker).
"""
import itertools
import numpy as np

I2 = np.array([[1, 0], [0, 1]], dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
PAULIS = {"I": I2, "X": X, "Y": Y, "Z": Z}


def bits_to_index(bs):
    """bitstring 'b0 b1 ... b_{n-1}' with b0 = MSB (qubit 0 is leftmost)."""
    idx = 0
    for ch in bs:
        idx = (idx << 1) | (1 if ch == "1" else 0)
    return idx


def build_typeII(theta, s1, s2):
    """Independent transcription of the LaTeX Type II |0_L>. n=7."""
    n = 7
    coef_a = theta / np.sqrt(8.0)
    coef_b = np.sqrt(1.0 / 12.0 - theta * theta / 8.0)
    coef_c = theta / 2.0
    coef_d = 0.5 * np.sqrt(2.0 / 3.0 - theta * theta)
    terms = []
    # line 1: theta/sqrt(8) * ( +0000000 +1100101 +1101001 +1110001
    #                           -0000011 -1100110 -1101010 -1110010 )
    for s in ["0000000", "1100101", "1101001", "1110001"]:
        terms.append((s, coef_a))
    for s in ["0000011", "1100110", "1101010", "1110010"]:
        terms.append((s, -coef_a))
    # line 2: i s1 sqrt(1/12 - theta^2/8) * (8 strings)
    for s in ["0100101", "0100110", "0110001", "0101001",
              "0101010", "0110010", "1000000", "1000011"]:
        terms.append((s, 1j * s1 * coef_b))
    # line 3a: i s2 theta/2 * ( 0011100 + 0011111 )
    for s in ["0011100", "0011111"]:
        terms.append((s, 1j * s2 * coef_c))
    # line 3b: s1 s2 (1/2) sqrt(2/3 - theta^2) * ( +1011100 - 1011111 )
    terms.append(("1011100", s1 * s2 * coef_d))
    terms.append(("1011111", -s1 * s2 * coef_d))

    d = 1 << n
    zero = np.zeros(d, dtype=complex)
    for s, c in terms:
        zero[bits_to_index(s)] += c
    # |1_L> = X^{⊗7} |0_L>
    Xall = X
    for _ in range(n - 1):
        Xall = np.kron(Xall, X)
    one = Xall @ zero
    return n, zero, one


def pauli_op(letters):
    op = PAULIS[letters[0]]
    for ch in letters[1:]:
        op = np.kron(op, PAULIS[ch])
    return op


def apply_single_pauli(vec, n, pos, L):
    """Apply single-qubit Pauli L at qubit `pos` (0=MSB) to statevector `vec`
    of length 2^n, WITHOUT forming a dense matrix.  Returns new vector.
    Index convention: qubit pos contributes bit (idx >> (n-1-pos)) & 1.
    Verified against np.kron for n=7."""
    if L == "I":
        return vec.copy()
    shift = n - 1 - pos
    bit = (np.arange(vec.size) >> shift) & 1  # bit value at qubit pos
    flip = vec.size  # placeholder
    out = np.empty_like(vec)
    # partner index = toggle that bit
    partner = np.arange(vec.size) ^ (1 << shift)
    if L == "X":
        out = vec[partner]
    elif L == "Z":
        out = np.where(bit == 1, -vec, vec)
    elif L == "Y":
        # Y = i X Z ; Y|0>=i|1>, Y|1>=-i|0>
        # (Y v)_idx = sum_j Y[bit_idx, bit_j] v at partner.
        # If bit==0 (target |0> component sits where pos-bit=0): result picks
        # amplitude from partner (bit=1) times Y[0,1] = -i.
        # If bit==1: from partner (bit=0) times Y[1,0]=+i.
        coeff = np.where(bit == 0, -1j, 1j)
        out = coeff * vec[partner]
    return out


def apply_pauli_string(vec, n, letters):
    out = vec
    for pos, L in enumerate(letters):
        if L != "I":
            out = apply_single_pauli(out, n, pos, L)
    return out


def compressed_2x2_sv(letters, n, zero, one):
    """Compute 2x2 [[<0|P|0>,<0|P|1>],[<1|P|0>,<1|P|1>]] via statevector action."""
    Pz = apply_pauli_string(zero, n, letters)
    Po = apply_pauli_string(one, n, letters)
    m00 = np.vdot(zero, Pz)
    m01 = np.vdot(zero, Po)
    m10 = np.vdot(one, Pz)
    m11 = np.vdot(one, Po)
    return np.array([[m00, m01], [m10, m11]], dtype=complex)


def compressed_2x2(P, zero, one):
    m00 = np.vdot(zero, P @ zero)
    m01 = np.vdot(zero, P @ one)
    m10 = np.vdot(one, P @ zero)
    m11 = np.vdot(one, P @ one)
    return np.array([[m00, m01], [m10, m11]], dtype=complex)


def worst_violation_distance3(zero, one, n, tol=1e-8, report=False):
    """KL condition: for every weight<=2 Pauli, 2x2 must be scalar*I.
    violation = max(|m01|, |m10|, |m00-m11|). Return (worst, offending)."""
    worst = 0.0
    offending = None
    # all weight 0,1,2 Paulis
    positions = range(n)
    # weight 0
    cand = [("I" * n, ())]
    # weight 1
    for p in positions:
        for L in "XYZ":
            letters = ["I"] * n
            letters[p] = L
            cand.append(("".join(letters), (p, L)))
    # weight 2
    for p, q in itertools.combinations(positions, 2):
        for Lp in "XYZ":
            for Lq in "XYZ":
                letters = ["I"] * n
                letters[p] = Lp
                letters[q] = Lq
                cand.append(("".join(letters), (p, Lp, q, Lq)))

    for letters, tag in cand:
        M = compressed_2x2_sv(letters, n, zero, one)
        v = max(abs(M[0, 1]), abs(M[1, 0]), abs(M[0, 0] - M[1, 1]))
        if v > worst:
            worst = v
            offending = (letters, tag, M)
    if report:
        return worst, offending
    return worst


def lift_once_dense(n, m, a, zero, one, b_list):
    """Reproduced verbatim from dyadic_lift.lift_once_dense (LIFT op only)."""
    new_m = 2 * m
    new_n = n + 2
    new_a = tuple(a) + (m, m)
    new_b = (b_list[0] + 0 * m, b_list[1] + 1 * m)
    d_old = 1 << n
    d_new = 1 << new_n
    avec = np.array(a, dtype=np.int64)
    arange_old = np.arange(d_old, dtype=np.int64)
    cols = (n - 1 - np.arange(n))
    bits = ((arange_old[:, None] >> cols[None, :]) & 1).astype(np.int64)
    A_x_mod_2m = (bits @ avec) % (2 * m)
    new_zero = np.zeros(d_new, dtype=complex)
    new_one = np.zeros(d_new, dtype=complex)
    inv_sqrt2 = 1.0 / np.sqrt(2.0)
    for k, codeword, out in [(0, zero, new_zero), (1, one, new_one)]:
        b_k = int(b_list[k])
        for x in range(d_old):
            coeff = codeword[x]
            if coeff == 0:
                continue
            r = int(A_x_mod_2m[x])
            if r == b_k:
                h = 0
            elif r == b_k + m:
                h = 1
            else:
                raise ValueError(
                    f"lift_once_dense: x={x:0{n}b} A_a mod 2m={r} expected {b_k} or {b_k+m} (k={k})"
                )
            parity = h ^ k
            tags = (0b00, 0b11) if parity == 0 else (0b01, 0b10)
            scaled = coeff * inv_sqrt2
            base = x << 2
            for tag in tags:
                out[base | tag] += scaled
    return new_n, new_m, new_a, new_zero, new_one, new_b


def diag_subset_sums(zero, one, n, a, m):
    """Report subset-sum (mod 2m) values present in supports of |0_L>,|1_L>."""
    avec = np.array(a, dtype=np.int64)
    d = 1 << n
    cols = (n - 1 - np.arange(n))
    arange = np.arange(d, dtype=np.int64)
    bits = ((arange[:, None] >> cols[None, :]) & 1).astype(np.int64)
    A = bits @ avec
    supp0 = np.where(np.abs(zero) > 1e-12)[0]
    supp1 = np.where(np.abs(one) > 1e-12)[0]
    ss0_mod = sorted(set(int(A[x]) % (2 * m) for x in supp0))
    ss1_mod = sorted(set(int(A[x]) % (2 * m) for x in supp1))
    ss0_int = sorted(set(int(A[x]) for x in supp0))
    ss1_int = sorted(set(int(A[x]) for x in supp1))
    return supp0, supp1, ss0_mod, ss1_mod, ss0_int, ss1_int, A


def fmt_bits(x, n):
    return format(x, f"0{n}b")


def main():
    np.set_printoptions(precision=4, suppress=True, linewidth=160)

    # ---- SELF-CHECK: statevector Pauli action == dense np.kron (n=4) ----
    rng = np.random.default_rng(0)
    nt = 4
    v = rng.standard_normal(1 << nt) + 1j * rng.standard_normal(1 << nt)
    maxerr = 0.0
    for letters in itertools.product("IXYZ", repeat=nt):
        L = "".join(letters)
        dense = pauli_op(L) @ v
        sv = apply_pauli_string(v, nt, L)
        maxerr = max(maxerr, np.max(np.abs(dense - sv)))
    print(f"[self-check] statevector-Pauli vs dense-kron max err over all {4**nt} "
          f"weight-* Paulis (n={nt}): {maxerr:.2e}  "
          f"{'OK' if maxerr < 1e-10 else 'MISMATCH!!'}", flush=True)

    a = (0, 1, 2, 2, 2, 3, 3)
    m = 6
    n = 7

    print("=" * 70)
    print("ARITHMETIC (independent recompute)")
    print("=" * 70)
    sa = sum(a)
    print(f"a = {a}")
    print(f"sum(a) = {sa}  ; 2m-1 = {2*m-1}  -> H1 strong sum: {sa == 2*m-1}")
    print(f"max(a) = {max(a)} ; m-2 = {m-2} -> H2 bounded: {max(a) <= m-2}")
    print(f"sum(a) mod m = {sa % m} ; m-1 = {m-1}  (b_1 residue)")
    print(f"sum(a) mod 2m = {sa % (2*m)}")

    print("\n" + "=" * 70)
    print("TRANSCRIPTION / NORM / ORTHO at theta=0.5*sqrt(2/3), s1=s2=+1")
    print("=" * 70)
    theta = 0.5 * np.sqrt(2.0 / 3.0)
    n, zero, one = build_typeII(theta, +1, +1)
    nrm0 = np.vdot(zero, zero).real
    nrm1 = np.vdot(one, one).real
    ov = np.vdot(zero, one)
    print(f"theta = {theta}")
    print(f"<0|0> = {nrm0:.15f}")
    print(f"<1|1> = {nrm1:.15f}")
    print(f"<0|1> = {ov}")
    print(f"|<0|1>| = {abs(ov):.3e}")

    # subset-sum / anchor structure
    print("\n" + "=" * 70)
    print("ANCHOR STRUCTURE (subset sums)")
    print("=" * 70)
    supp0, supp1, ss0m, ss1m, ss0i, ss1i, A = diag_subset_sums(zero, one, n, a, m)
    print(f"supp(|0_L>) integer subset sums: {ss0i}")
    print(f"   mod 2m={2*m}: {ss0m}")
    print(f"supp(|1_L>) integer subset sums: {ss1i}")
    print(f"   mod 2m={2*m}: {ss1m}")
    # H3 unique bottom anchor: 0^7 unique support at subset-sum 0 in |0_L>?
    zeros_at_ss0 = [fmt_bits(x, n) for x in supp0 if int(A[x]) == 0]
    print(f"supports of |0_L> with integer subset-sum 0: {zeros_at_ss0}")
    print(f"-> H3 unique bottom anchor (only 0^7): {zeros_at_ss0 == ['0000000']}")
    # H4 unique top anchor: support of |1_L> with integer subset-sum 2m-1=11?
    top_at = [fmt_bits(x, n) for x in supp1 if int(A[x]) == 2*m - 1]
    print(f"supports of |1_L> with integer subset-sum 2m-1={2*m-1}: {top_at}")
    print(f"-> H4 unique top anchor: {len(top_at) == 1}")
    # subset sum of 1^7
    print(f"subset-sum of 1^7 = {int(A[(1<<n)-1])}  (mod 2m = {int(A[(1<<n)-1]) % (2*m)})")

    # SS-LP structure for the lift: are |0_L> diagonal values all in {0,m} mod 2m?
    print(f"\nSS-LP check: |0_L> subset sums mod 2m all in {{0,m}}={{0,{m}}}? "
          f"{set(ss0m) <= {0, m}}  values={ss0m}")
    print(f"           |1_L> subset sums mod 2m all in {{m,0}}? "
          f"values={ss1m}")

    print("\n" + "=" * 70)
    print("FROM-SCRATCH DISTANCE-3 (KL weight<=2) for SEED, multiple theta")
    print("=" * 70)
    for th in [0.0, 0.2, 0.4, 0.5*np.sqrt(2/3), np.sqrt(2/3)]:
        for (ss1, ss2) in [(+1, +1)]:
            nn, z, o = build_typeII(th, ss1, ss2)
            w, off = worst_violation_distance3(z, o, nn, report=True)
            tag = off[0] if off else None
            print(f"theta={th:.6f} s=({ss1},{ss2}): worst_violation={w:.3e}  "
                  f"({'PASS' if w < 1e-8 else 'FAIL via '+tag})")

    # also try a few sign choices at endpoint theta
    print("\n  sign-variation at theta=0.5*sqrt(2/3):")
    for ss1, ss2 in itertools.product([+1, -1], repeat=2):
        nn, z, o = build_typeII(0.5*np.sqrt(2/3), ss1, ss2)
        w = worst_violation_distance3(z, o, nn)
        print(f"    s1={ss1:+d} s2={ss2:+d}: worst={w:.3e} {'PASS' if w<1e-8 else 'FAIL'}")

    print("\n" + "=" * 70)
    print("LIFT CHAIN (b_list=(0,1)); re-check each rung from-scratch")
    print("=" * 70)
    theta = 0.5 * np.sqrt(2.0 / 3.0)
    nn, z, o = build_typeII(theta, +1, +1)
    b_list = (0, 1)
    # seed rung r0
    w0 = worst_violation_distance3(z, o, nn)
    print(f"r0: n={nn} worst={w0:.3e} {'PASS' if w0<1e-8 else 'FAIL'}")
    cur_n, cur_m, cur_a = nn, m, a
    cz, co = z, o
    bl = b_list
    for r in range(1, 6):
        try:
            cur_n, cur_m, cur_a, cz, co, bl = lift_once_dense(
                cur_n, cur_m, cur_a, cz, co, bl)
        except ValueError as e:
            print(f"r{r}: LIFT RAISED: {e}")
            break
        # renormalize defensively
        nz = np.vdot(cz, cz).real
        no = np.vdot(co, co).real
        # check norm preserved
        w, off = worst_violation_distance3(cz, co, cur_n, report=True)
        tag = off[0] if off else None
        print(f"r{r}: n={cur_n} m={cur_m} b={bl} |0|^2={nz:.6f} |1|^2={no:.6f} "
              f"worst={w:.6f} {'PASS' if w<1e-8 else 'FAIL via '+str(tag)}")


if __name__ == "__main__":
    main()
