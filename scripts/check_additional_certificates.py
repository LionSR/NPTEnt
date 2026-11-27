#!/usr/bin/env python3
"""Exact, full-basis certificate checks for new candidate NPT examples.

Run from any directory: python3 -B scripts/check_additional_certificates.py
Uses Python standard library only (int and fractions.Fraction).
No floating-point arithmetic, random sampling, or external solver is used.

IMPORTANT: This script performs exact computational finite-certificate checks.
It is NOT a Lean proof. The general certificate-to-overlap and finite-round
zero-rate mechanisms are proved in QICLean; these additional concrete witnesses
still require their own kernel-checked replay and instantiation.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations, product
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(a, row, col, value):
    if not value:
        return
    key = (row, col)
    value += a.get(key, 0)
    if value:
        a[key] = value
    else:
        a.pop(key, None)


def make_basis(d):
    basis = list(product(range(d), repeat=4))
    index = {x: i for i, x in enumerate(basis)}
    return basis, index


def pt(a, factors, basis, index):
    result = {}
    for (r, c), value in a.items():
        row, col = list(basis[r]), list(basis[c])
        for f in factors:
            row[f], col[f] = col[f], row[f]
        key = (index[tuple(row)], index[tuple(col)])
        require(key not in result, 'Partial transpose must be bijective')
        result[key] = value
    return result


def check_hermitian(a, name):
    require(all(a.get((c, r), 0) == v for (r, c), v in a.items()),
            f'{name}: not Hermitian')


def phase(x, positive, d):
    weights = [0] * d
    for f, label in enumerate(x):
        weights[label] += 1 if f == positive else -1
    return tuple(weights)


def components(a, n):
    adjacency = [set() for _ in range(n)]
    for (r, c) in a:
        if r != c:
            adjacency[r].add(c)
            adjacency[c].add(r)
    unseen = set(range(n))
    result = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        stack, block = [root], []
        while stack:
            r = stack.pop()
            block.append(r)
            for c in adjacency[r]:
                if c in unseen:
                    unseen.remove(c)
                    stack.append(c)
        result.append(sorted(block))
    return result


def exact_ldl(a):
    """Exact rational A = L diag(d) L^T with full entrywise reconstruction.

    Returns the rank (number of strictly positive pivots). Raises ValueError
    if any pivot is negative or if a zero pivot has a nonzero residual column.
    """
    n = len(a)
    s = [[Fraction(v) for v in row] for row in a]
    l = [[Fraction(i == j) for j in range(n)] for i in range(n)]
    d = []
    for k in range(n):
        pivot = s[k][k]
        require(pivot >= 0, f'negative LDL pivot {k}: {pivot}')
        d.append(pivot)
        if not pivot:
            require(all(s[i][k] == 0 for i in range(k + 1, n)),
                    f'zero LDL pivot {k} with nonzero residual column')
            continue
        for i in range(k + 1, n):
            l[i][k] = s[i][k] / pivot
        for i in range(k + 1, n):
            for j in range(k + 1, i + 1):
                s[i][j] -= l[i][k] * pivot * l[j][k]
                s[j][i] = s[i][j]
    for i in range(n):
        for j in range(n):
            require(sum(l[i][k] * d[k] * l[j][k]
                        for k in range(min(i, j) + 1)) == a[i][j],
                    'LDL reconstruction failed')
    return sum(v > 0 for v in d)


def check_psd(a, name, positive, d, basis):
    n = len(basis)
    groups = defaultdict(list)
    for i, x in enumerate(basis):
        groups[phase(x, positive, d)].append(i)
    require(sum(map(len, groups.values())) == n, 'phase coverage')
    for r, c in a:
        require(phase(basis[r], positive, d) == phase(basis[c], positive, d),
                f'{name}: entry outside phase block: {r}, {c}')
    blocks = components(a, n)
    flattened = [i for block in blocks for i in block]
    require(len(flattened) == n and set(flattened) == set(range(n)),
            'component coverage/uniqueness')
    owner = {i: b for b, block in enumerate(blocks) for i in block}
    require(all(owner[r] == owner[c] for r, c in a), 'off-component entry')
    require(all(len({phase(basis[i], positive, d) for i in block}) == 1
                for block in blocks), 'component crosses phases')
    cache = {}
    rank = 0
    for block in blocks:
        matrix = tuple(tuple(a.get((r, c), 0) for c in block) for r in block)
        if matrix not in cache:
            cache[matrix] = exact_ldl(matrix)
        rank += cache[matrix]
    print(f'  {name}: nnz={len(a)}; blocks={len(blocks)}; '
          f'unique={len(cache)}; rank={rank}; nullity={n - rank}; PSD PASS',
          flush=True)
    return rank


def check_kernel(minus, d, basis):
    n = len(basis)
    residual = [[0] * (d * d) for _ in range(n)]
    for (r, c), v in minus.items():
        i, j, k, l = basis[c]
        if i == j:
            residual[r][d * k + l] += v
    bad = [(r, c, v) for r, row in enumerate(residual)
           for c, v in enumerate(row) if v]
    require(not bad, f'kernel equation failed: {bad[:5]}')
    print(f'  kernel: all {n * d * d} entries of (J-Q)(u tensor I) zero; PASS',
          flush=True)


def build_werner_J(d, a, b, c, e, scale, basis, index):
    """Build scale * J for L(X)=a Tr(X)I - b X^T, M(X)=c Tr(X)I + e X."""
    jmat = {}
    ac, bc, ae, be = scale * a * c, scale * b * c, scale * a * e, scale * b * e
    for ci, (i, j, k, l) in enumerate(basis):
        add(jmat, ci, ci, ac)
        add(jmat, index[k, j, i, l], ci, -bc)
        if j == l:
            for m in range(d):
                add(jmat, index[i, m, k, m], ci, ae)
                add(jmat, index[k, m, i, m], ci, -be)
    return jmat


def build_werner_Q(d, coeffs, basis, index):
    """Build sum_pi coeffs[pi] B_pi where B_pi = U_pi^{Gamma_2}."""
    q = {}
    for perm, m in zip(permutations(range(4)), coeffs, strict=True):
        if m == 0:
            continue
        u = {(index[tuple(c[p] for p in perm)], ci): m
             for ci, c in enumerate(basis)}
        b = pt(u, (1,), basis, index)
        require(pt(b, (1,), basis, index) == u, 'PT factor 2 involution')
        for (r, c), v in b.items():
            add(q, r, c, v)
    return q


def extract_output_state(jmat, d, basis):
    """Compute unnormalized R = C(|u><u|) directly from Choi matrix J:
    R_{(k,l),(k',l')} = sum_{i,j} J_{(i,i,k,l),(j,j,k',l')}.
    """
    m = d * d
    R = [[0] * m for _ in range(m)]
    for (r, c), v in jmat.items():
        i, j, k, l = basis[r]
        ip, jp, kp, lp = basis[c]
        if i == j and ip == jp:
            R[d * k + l][d * kp + lp] += v
    return R


def verify_werner_example(title, d, a, b, c, e, scale, coeffs):
    t0 = time.monotonic()
    print(f'=== {title} ===', flush=True)
    # 1. Check L and M are CP
    require(a >= abs(b) and b > 0, 'L not CP with b > 0')
    require(c >= 0 and e > 0 and c + d * e >= 0, 'M not CP with e > 0')
    # 2. Compute exact Werner state rho = (A I - B SWAP) / tr
    A = d * a * c + a * e - b * c
    B = b * e
    alpha = Fraction(-B, A)
    tr_unnorm = A * d * d - B * d
    # Check PSD of rho and NPT witness <u|rho^Gamma|u>
    require(A - B > 0 and A + B > 0, 'rho not PSD')
    npt_eig = Fraction(A - d * B, tr_unnorm)
    require(npt_eig < 0, f'rho is NOT NPT: eig={npt_eig}')
    negativity = -npt_eig
    paper_neg = Fraction(1, 1448)
    print(f'  d={d}; L={a}TrI-{b}T; M={c}TrI+{e}id; '
          f'alpha={alpha} ({float(alpha):.6f}); d*alpha={float(d*alpha):.6f}',
          flush=True)
    print(f'  rho^Gamma|u> = ({npt_eig})|u> < 0 (NPT PASS); '
          f'negativity={negativity} ({float(negativity/paper_neg):.3f}x paper)',
          flush=True)
    # 3. Full-basis certificate check
    basis, index = make_basis(d)
    jmat = build_werner_J(d, a, b, c, e, scale, basis, index)
    # Directly verify C(|u><u|) = A I - B SWAP from the Choi matrix jmat
    R = extract_output_state(jmat, d, basis)
    for k in range(d):
        for l in range(d):
            for kp in range(d):
                for lp in range(d):
                    expected = scale * (A * int(k == kp and l == lp)
                                        - B * int(k == lp and l == kp))
                    require(R[d * k + l][d * kp + lp] == expected,
                            'Choi output R != A I - B SWAP')
    qmat = build_werner_Q(d, coeffs, basis, index)
    gamma = pt(qmat, (0, 1), basis, index)
    require(pt(gamma, (0, 1), basis, index) == qmat, 'input PT involution')
    plus, minus = dict(jmat), dict(jmat)
    for (r, c), v in qmat.items():
        add(plus, r, c, v)
        add(minus, r, c, -v)
    for name, mat in [('J', jmat), ('Q', qmat), ('J+Q', plus),
                      ('J-Q', minus), ('Q^Gamma_in', gamma)]:
        check_hermitian(mat, name)
    check_kernel(minus, d, basis)
    r_plus = check_psd(plus, f'{scale}(J+Q)', 1, d, basis)
    r_minus = check_psd(minus, f'{scale}(J-Q)', 1, d, basis)
    r_gamma = check_psd(gamma, f'{scale}Q^Gamma_in', 0, d, basis)
    n = d ** 4
    require(r_plus == n and r_gamma == n and r_minus == n - d * d,
            'unexpected rank profile')
    print(f'  DONE in {time.monotonic() - t0:.2f}s (ALL CHECKS PASS)\n',
          flush=True)


def mul_Pi_left(mat, d, basis, index):
    """Return d * Pi * mat where Pi = (1/d) |u><u|_12 tensor I_34."""
    col_sums = defaultdict(int)
    for (r, c), v in mat.items():
        i, j, k, l = basis[r]
        if i == j:
            col_sums[(k, l, c)] += v
    out = {}
    for (k, l, c), s in col_sums.items():
        if s:
            for a in range(d):
                add(out, index[a, a, k, l], c, s)
    return out


def verify_nonwerner_example():
    """Example 3: d=8 non-Werner NPT state via explicit projector perturbation.

    L(X) = 5 Tr(X) I - 3 X^T
    M'(X) = 18 Tr(X) I + 37 X - (1/8) <0|X|0> |0><0|
    Q' = Q_paper - (1/8) (Pi dJ + dJ Pi - Pi dJ Pi)
    where dJ = (5 I_13 - 3 F_13) tensor |0,0><0,0|_24.
    """
    t0 = time.monotonic()
    print('=== Example 3: d=8 non-Werner NPT state (eps = -1/8 perturbation) ===',
          flush=True)
    d = 8
    basis, index = make_basis(d)
    # 1. Verify M' is CP: J_M' = 18 I + 37 |u><u| - (1/8) |0,0><0,0| >= (18 - 1/8) I > 0.
    require(Fraction(18) - Fraction(1, 8) > 0, 'M_prime not CP')
    # 2. Verify non-Werner marginal and strict NPT witness of R' = (L tensor M')(|u><u|)
    # R' = 37(23 I - 3 SWAP) - (1/8)(5 I - 3 |0><0|) tensor |0><0|
    tr_R = Fraction(37 * 1448) - Fraction(37, 8)
    # Bob marginal: Tr_A(R') = 37*181 I - (37/8) |0><0|
    bob_marg_0 = (Fraction(37 * 181) - Fraction(37, 8)) / tr_R
    bob_marg_1 = Fraction(37 * 181) / tr_R
    require(bob_marg_0 != bob_marg_1, 'marginal unexpectedly maximally mixed')
    # Exact NPT witness <u|rho'^Gamma|u> / <u|u>
    u_val = (Fraction(37 * (-8)) - Fraction(2, 8)) / tr_R
    paper_u_val = Fraction(-8, 1448)
    require(u_val < paper_u_val < 0, 'NPT witness not strictly stronger than paper')
    # Note: since <u/sqrt(8)|rho'^Gamma|u/sqrt(8)> = u_val / 8 < -1/1448,
    # by variational principle the negativity N(rho') >= -u_val / 8 > 1/1448 = N(rho_paper)!
    neg_lower_bound = -u_val / d
    paper_neg = Fraction(1, 1448)
    require(neg_lower_bound > paper_neg, 'negativity lower bound not strictly larger')
    print(f'  Bob marginal eigenvalues: {bob_marg_0} (mult 1), {bob_marg_1} (mult 7) '
          f'-> NOT LU-equivalent to any Werner state', flush=True)
    print(f'  <u|rho_3^Gamma|u>/8 = {u_val / d} < {-paper_neg} '
          f'-> N(rho_3) >= {neg_lower_bound} > {paper_neg} = N(rho_paper)',
          flush=True)

    # 3. Build integer-scaled 40*512 J' and 40*512 Q'
    # Scale = 40 * 8 * 64 = 20480? Wait: eps = -1/8, dQ = (1/64)*dq64, so
    # 40*512 * J' = 512*(40 J) - 40*64 * dJ
    # 40*512 * Q' = 512*(40 Q) - 40 * dq64
    M_paper = (88, 77, 16, 24, 24, 16, 380, 40, -288, 128, -525, 760,
               -288, -525, 884, -876, 612, -756, 128, 760, -876, 2060, -756, -172)
    j40 = build_werner_J(d, 5, 3, 18, 37, 40, basis, index)
    q40 = build_werner_Q(d, M_paper, basis, index)

    dj = {}
    for i in range(d):
        for k in range(d):
            col = index[i, 0, k, 0]
            add(dj, col, col, 5)
            add(dj, index[k, 0, i, 0], col, -3)

    pi_dj = mul_Pi_left(dj, d, basis, index)          # 8 Pi dJ
    dj_pi = {(c, r): v for (r, c), v in pi_dj.items()}  # 8 dJ Pi
    pi_dj_pi = mul_Pi_left(dj_pi, d, basis, index)    # 64 Pi dJ Pi
    dq64 = {}
    for (r, c), v in pi_dj.items():
        add(dq64, r, c, 8 * v)
    for (r, c), v in dj_pi.items():
        add(dq64, r, c, 8 * v)
    for (r, c), v in pi_dj_pi.items():
        add(dq64, r, c, -v)

    j_tot, q_tot = {}, {}
    for (r, c), v in j40.items():
        add(j_tot, r, c, 512 * v)
    for (r, c), v in dj.items():
        add(j_tot, r, c, -40 * 64 * v)
    for (r, c), v in q40.items():
        add(q_tot, r, c, 512 * v)
    for (r, c), v in dq64.items():
        add(q_tot, r, c, -40 * v)

    # Directly verify R3 = C'(|u><u|) from j_tot: PSD, trace, Bob marginal, <u|R3^Gamma|u>
    R3 = extract_output_state(j_tot, d, basis)
    scale3 = 40 * 512
    require(exact_ldl(R3) == d * d, 'R3 not positive definite')
    tr_R3 = sum(R3[i][i] for i in range(d * d))
    require(Fraction(tr_R3, scale3) == tr_R, 'Tr(R3) mismatch')
    # Bob marginal: (Tr_A R3)_{l, lp} = sum_k R3_{(k,l),(k,lp)}
    bob_m = [[sum(R3[d * k + l][d * k + lp] for k in range(d))
              for lp in range(d)] for l in range(d)]
    require(all(bob_m[l][lp] == 0 for l in range(d) for lp in range(d) if l != lp),
            'Bob marginal not diagonal')
    require(Fraction(bob_m[0][0], tr_R3) == bob_marg_0, 'Bob marginal [0,0] mismatch')
    require(all(Fraction(bob_m[l][l], tr_R3) == bob_marg_1 for l in range(1, d)),
            'Bob marginal [l,l] mismatch')
    # <u|R3^Gamma|u> = sum_{a,b} (R3^Gamma)_{(a,a),(b,b)} = sum_{a,b} R3_{(a,b),(b,a)}
    u_pt_u = sum(R3[d * a + b][d * b + a] for a in range(d) for b in range(d))
    require(Fraction(u_pt_u, tr_R3) == u_val, '<u|rho_3^Gamma|u> mismatch')
    gamma = pt(q_tot, (0, 1), basis, index)
    require(pt(gamma, (0, 1), basis, index) == q_tot, 'input PT involution')
    plus, minus = dict(j_tot), dict(j_tot)
    for (r, c), v in q_tot.items():
        add(plus, r, c, v)
        add(minus, r, c, -v)
    for name, mat in [('J3', j_tot), ('Q3', q_tot), ('J3+Q3', plus),
                      ('J3-Q3', minus), ('Q3^Gamma_in', gamma)]:
        check_hermitian(mat, name)
    check_kernel(minus, d, basis)
    r_plus = check_psd(plus, '20480(J3+Q3)', 1, d, basis)
    r_minus = check_psd(minus, '20480(J3-Q3)', 1, d, basis)
    r_gamma = check_psd(gamma, '20480Q3^Gamma_in', 0, d, basis)
    n = d ** 4
    require(r_plus == n and r_gamma == n and r_minus == n - d * d,
            'unexpected rank profile')
    print(f'  DONE in {time.monotonic() - t0:.2f}s (ALL CHECKS PASS)\n',
          flush=True)


def main():
    # Example 1: d=8, strictly stronger NPT Werner state than paper's rho(8, -3/23)
    M_ex1 = (52, -1, -4, -4, -4, 0, 2064, 268, -1516, 673, -2816, 4152,
             -1516, -2816, 5116, -4404, 2936, -4504, 673, 4152, -4404, 11288, -4504, -976)
    verify_werner_example(
        'Example 1: d=8 stronger NPT Werner state rho(8, -75/569)',
        d=8, a=5, b=3, c=12, e=25, scale=320, coeffs=M_ex1
    )

    # Example 2: d=9, higher-dimension NPT Werner state with scale=40
    M_ex2 = (23, 0, 0, 0, 0, 0, 373, 46, -285, 115, -529, 745,
             -285, -529, 976, -842, 603, -811, 115, 745, -842, 2106, -811, -193)
    verify_werner_example(
        'Example 2: d=9 higher-dimension NPT Werner state rho(9, -125/1004)',
        d=9, a=8, b=5, c=12, e=25, scale=40, coeffs=M_ex2
    )

    # Example 3: d=8, genuinely non-Werner NPT state via explicit projector perturbation
    verify_nonwerner_example()

    print('ALL 3 NEW EXAMPLES PASS FULL-BASIS EXACT RATIONAL CHECKS '
          '(computational certificate check only; not a Lean proof)', flush=True)


if __name__ == '__main__':
    main()
