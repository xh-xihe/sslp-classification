"""Find the gauge in which the paper's orbit-9 witness lists lie in single
residue classes: try every cube translation, every coordinate permutation,
and both bit orders."""
import sys
from itertools import permutations

sys.path.insert(0, 'tools/core')

L0 = ['000000', '000111', '001110', '010110', '011001', '100001',
      '101000', '101111', '110000', '110111', '111110']
L1 = ['000001', '001000', '001111', '010000', '010111', '011110',
      '100110', '101001', '110001', '111000', '111111']
A, Q = [1, 1, 1, 1, 1, 2], 3

xor = lambda s, t: ''.join('01'[(int(u) + int(v)) % 2] for u, v in zip(s, t))
res = lambda s, a: sum(a[i] * int(s[i]) for i in range(6)) % Q


def classes(lst, a, t):
    return {res(xor(s, t), a) for s in lst}


hits = []
for perm in permutations(range(6)):
    a = [A[perm[i]] for i in range(6)]
    if sorted(a) != sorted(A):
        continue
    for tm in range(64):
        t = format(tm, '06b')
        r0, r1 = classes(L0, a, t), classes(L1, a, t)
        if len(r0) == 1 and len(r1) == 1 and r0 != r1:
            hits.append((perm, t, r0.pop(), r1.pop()))

print('gauges in which BOTH lists are single, distinct residue classes: %d'
      % len(hits))
seen = set()
for perm, t, r0, r1 in hits:
    key = (t, r0, r1)
    if key in seen:
        continue
    seen.add(key)
    print('   permutation %s  translation %s  ->  L0 in class %d, L1 in class %d'
          % (perm, t, r0, r1))
    if len(seen) >= 8:
        break

# also try reversed strings
print()
rev = lambda s: s[::-1]
for tm in range(64):
    t = format(tm, '06b')
    r0 = {res(xor(rev(s), t), A) for s in L0}
    r1 = {res(xor(rev(s), t), A) for s in L1}
    if len(r0) == 1 and len(r1) == 1 and r0 != r1:
        print('reversed bit order, translation %s: L0 class %d, L1 class %d'
              % (t, r0.pop(), r1.pop()))

print()
print('residues of L0 under the plain record %s:' % A,
      sorted({res(s, A) for s in L0}))
print('residues of L1 under the plain record %s:' % A,
      sorted({res(s, A) for s in L1}))
print('weight distribution of L0:', sorted(s.count('1') for s in L0))
print('weight distribution of L1:', sorted(s.count('1') for s in L1))
