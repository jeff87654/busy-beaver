"""Independent gate computation for P12 (bb12-p2 agent, 2026-11-15).  Written from scratch; does not import msim/follower.

High-level rules (derived by hand, checked literally by rules_check.py):
  Y p u w  = [1]^u [0;1]^p 0^inf  I>  w        (P12 naming)
  big round k starts at  X 7 (W 4 1 + 2) ([1;0]^(D_k - 2) 0^inf),  D_0 = 9 + W(4,1)/2
  one round (u even, d >= 2):  X p u ([1;0]^d S) -> X (p - 1 + m*c) ... with m = (W p u + 1)/2 class-2 passes
  D_{k+1} = q_m + U/2 + 1   (blank conversion), halt iff D_k odd.

2-adic facts: for j >= 4 (and the argument giving a huge tower height) W j b = T_h, T_0 = 2, T_{h+1} = W2(T_h),
W2(y) = (3^(y+3)-5)/2, h = b+1 mod 2; T_h mod 2^N depends only on h mod 2 once h >= N.
   c_E = lim T_(even h),  c_O = lim T_(odd h).
"""
import sys

N = 200  # working precision: residues mod 2^N


def W2_mod(y, k):
    """W2(y) mod 2^k, given y mod 2^(k-1) (k>=2) or y mod 2 (k=1)."""
    if k == 1:
        return (y + 1) % 2
    M = 1 << (k + 1)
    t = pow(3, (y % (1 << (k - 1))) + 3, M)
    v = (t - 5) % M
    assert v % 2 == 0
    return (v // 2) % (1 << k)


def T_limit(parity, N):
    """T_h mod 2^N for h >= N with h = parity mod 2."""
    # T_(h-N+1) mod 2 = (h-N+1) mod 2
    x = (parity - N + 1) % 2
    for k in range(2, N + 1):
        x = W2_mod(x, k)
    return x


def check_T():
    # exact T_0..T_2 versus the limit recursion at small precision, and stability
    T = [2]
    T.append((3 ** (T[0] + 3) - 5) // 2)
    T.append((3 ** (T[1] + 3) - 5) // 2)
    assert T[1] == 119
    # T_2 mod 2^k must equal recursion with h=2: valid for k <= 2 only by the theorem, check the recursion itself:
    for k in range(1, 40):
        x = T[1] % (1 << max(k - 1, 1))
        assert W2_mod(T[1], k) == T[2] % (1 << k), k
    for N2 in (10, 20, 50):
        for par in (0, 1):
            a = T_limit(par, N2)
            b = T_limit(par, N2 + 7) % (1 << N2)
            assert a == b, (N2, par)
    print('T checks ok')


def main():
    check_T()
    cE = T_limit(0, N)
    cO = T_limit(1, N)
    print('c_E mod 2^16 =', cE % (1 << 16), ' c_E mod 4 =', cE % 4)
    print('c_O mod 2^16 =', cO % (1 << 16), ' c_O mod 4 =', cO % 4)
    # residues usable mod 2^(N-1) after halving
    M = 1 << (N - 2)
    half_cE = (cE // 2)            # cE even
    m = (cO + 1) // 2              # cO odd
    A = (9 + half_cE) % M
    delta = (m * half_cE - 1) % M
    print('A mod 64 =', A % 64, ' delta mod 64 =', delta % 64)
    D = A
    prec = N - 2
    k = 0
    out = []
    while prec > 2 and k < 60:
        par = D % 2
        out.append(par)
        print('D_%d mod 2^%d = %d   parity %d' % (k, min(prec, 16), D % (1 << min(prec, 16)), par))
        if par == 1:
            print('HALT in big round', k, '(class-3 loop number', k + 1, ')')
            break
        D = (A + delta * ((D - 2) // 2)) % (1 << (prec - 1))
        prec -= 1
        k += 1
    print('gate parities (D_1..):', out[1:])


if __name__ == '__main__':
    main()
