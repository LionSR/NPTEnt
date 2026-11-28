"""Certificate search for local maps invariant under the monomial group (diagonal unitaries and
label permutations), which contains the U(d)-covariant family of arXiv:2611.34921 as g = h = 0.

  L(X) = a Tr(X) I - b X^T + h diag(X)        (Alice, factors 1 -> 3)
  M(X) = c Tr(X) I + e X   + g diag(X)        (Bob,   factors 2 -> 4)
  C = L (x) M,  u = sum_i |ii>,  J = Choi(C) on (C^d)^{(x)4} ordered (A_in, B_in, A_out, B_out).

Certificate: real symmetric Q with J + Q >= 0, J - Q >= 0, Q^{Gamma_in} >= 0, (J - Q)(u (x) I) = 0.
Output state: C(|u><u|) = A I - b e F + kappa Delta, Delta = sum_i |ii><ii|, and its U(x)U twirl is
an NPT Werner state iff the margin  mu = d b e - A - kappa  is positive.

All matrices commute with the diagonal torus, so every LMI splits into weight blocks, and label
permutations identify blocks of the same type. Q is parametrised by one real variable per
equality pattern of the eight labels of an entry.
"""
import itertools
import numpy as np
import cvxpy as cp
import scipy.sparse as sp


def canon(labels):
    seen, out = {}, []
    for t in labels:
        if t not in seen:
            seen[t] = len(seen)
        out.append(seen[t])
    return tuple(out)


class Reduced:
    """Symmetry-reduced structure for dimension d; independent of the map parameters."""

    def __init__(self, d):
        self.d = d
        self.var = {}
        states = list(itertools.product(range(d), repeat=4))

        def weight(r, plus):
            w = [0] * d
            for pos, t in enumerate(r):
                w[t] += 1 if pos == plus else -1
            return tuple(w)

        def representative_blocks(plus):
            by_weight = {}
            for r in states:
                by_weight.setdefault(weight(r, plus), []).append(r)
            reps = {}
            for w, rows in by_weight.items():
                reps.setdefault(tuple(sorted(w)), rows)
            return list(reps.values())

        self.j_blocks = representative_blocks(plus=1)      # weight e_j - e_i - e_k - e_l
        self.g_blocks = representative_blocks(plus=0)      # weight e_i - e_j - e_k - e_l
        self.j_index = [self._index(rows, transpose_in=False) for rows in self.j_blocks]
        self.g_index = [self._index(rows, transpose_in=True) for rows in self.g_blocks]

        # Kernel equations: sum_m (J - Q)[r, (m, m, k', l')] = 0 for representative (k', l').
        self.kernel = []
        targets = [(0, 0)] + ([(0, 1)] if d >= 2 else [])
        for kp, lp in targets:
            cols = [(m, m, kp, lp) for m in range(d)]
            w = weight(cols[0], 1)
            for r in states:
                if weight(r, 1) == w:
                    self.kernel.append((r, cols, [self._v(r, c) for c in cols]))
        self.nvar = len(self.var)

    def _v(self, r, rp):
        key = min(canon(r + rp), canon(rp + r))
        if key not in self.var:
            self.var[key] = len(self.var)
        return self.var[key]

    def _index(self, rows, transpose_in):
        n = len(rows)
        idx = np.zeros((n, n), dtype=int)
        for p, r in enumerate(rows):
            for q, rp in enumerate(rows):
                if transpose_in:   # (Q^Gamma)[r, r'] = Q[(i', j', k, l), (i, j, k', l')]
                    idx[p, q] = self._v((rp[0], rp[1], r[2], r[3]), (r[0], r[1], rp[2], rp[3]))
                else:
                    idx[p, q] = self._v(r, rp)
        return idx


def jl_entry(a, b, h, i, k, ip, kp):
    return a * (i == ip and k == kp) - b * (i == kp and k == ip) + h * (i == ip and k == kp and i == k)


def jm_parts(j, l, jp, lp):
    """Coefficients of (c, e, g) in J_M[(j, l), (j', l')]."""
    return (float(j == jp and l == lp), float(j == l and jp == lp), float(j == jp and l == lp and j == l))


def j_parts(a, b, h, r, rp):
    jl = jl_entry(a, b, h, r[0], r[2], rp[0], rp[2])
    pc, pe, pg = jm_parts(r[1], r[3], rp[1], rp[3])
    return jl * pc, jl * pe, jl * pg


def margin_coeffs(d, a, b, h):
    """mu = m0 * e + mc * c + mg * g."""
    return d * b - a - h, -(d * a + h - b), -(a + h - b)


def solve(red, a, h, b=1.0, allow_g=True, solver="CLARABEL", return_solution=False):
    d = red.d
    assert a >= b > 0 and h >= b - a - 1e-12, "L must be completely positive"
    x = cp.Variable(red.nvar)
    c = cp.Variable(nonneg=True)
    g = cp.Variable()
    e = 1.0
    cons = [c + g >= 0]
    if not allow_g:
        cons.append(g == 0)

    def selector(idx):
        n = idx.shape[0]
        return sp.csr_matrix((np.ones(n * n), (np.arange(n * n), idx.ravel())), shape=(n * n, red.nvar))

    for rows, idx in zip(red.j_blocks, red.j_index):
        n = len(rows)
        parts = np.array([[j_parts(a, b, h, r, rp) for rp in rows] for r in rows])
        jblk = c * parts[:, :, 0] + e * parts[:, :, 1] + g * parts[:, :, 2]
        qblk = cp.reshape(selector(idx) @ x, (n, n), order="C")
        cons += [jblk + qblk >> 0, jblk - qblk >> 0]
    for rows, idx in zip(red.g_blocks, red.g_index):
        n = len(rows)
        cons.append(cp.reshape(selector(idx) @ x, (n, n), order="C") >> 0)

    rows_k, const_k = [], []
    seen = set()
    for r, cols, vs in red.kernel:
        parts = np.sum([j_parts(a, b, h, r, cc) for cc in cols], axis=0)
        key = (tuple(np.round(parts, 12)), tuple(sorted(vs)))
        if key in seen:
            continue
        seen.add(key)
        coeff = np.zeros(red.nvar)
        for v in vs:
            coeff[v] += 1
        cons.append(c * parts[0] + e * parts[1] + g * parts[2] - coeff @ x == 0)

    m0, mc, mg = margin_coeffs(d, a, b, h)
    mu = m0 * e + mc * c + mg * g
    prob = cp.Problem(cp.Maximize(mu), cons)
    prob.solve(solver=solver)
    if return_solution:
        return prob.status, prob.value, c.value, g.value, x.value
    return prob.status, prob.value, c.value, g.value


def brute(d, a, h, b=1.0, allow_g=True, solver="CLARABEL"):
    """Unreduced SDP with a general real symmetric Q; a cross-check for small d."""
    states = list(itertools.product(range(d), repeat=4))
    pos = {r: n for n, r in enumerate(states)}
    N = len(states)
    parts = np.zeros((3, N, N))
    for p, r in enumerate(states):
        for q, rp in enumerate(states):
            parts[:, p, q] = j_parts(a, b, h, r, rp)
    Q = cp.Variable((N, N), symmetric=True)
    c = cp.Variable(nonneg=True)
    g = cp.Variable()
    e = 1.0
    J = c * parts[0] + e * parts[1] + g * parts[2]
    rr, cc = [], []
    for p, r in enumerate(states):
        for q, rp in enumerate(states):
            rr.append(p * N + q)
            cc.append(pos[(rp[0], rp[1], r[2], r[3])] * N + pos[(r[0], r[1], rp[2], rp[3])])
    perm = sp.csr_matrix((np.ones(N * N), (rr, cc)), shape=(N * N, N * N))
    QG = cp.reshape(perm @ cp.reshape(Q, (N * N,), order="C"), (N, N), order="C")
    U = np.zeros((N, d * d))
    for m in range(d):
        for k in range(d):
            for l in range(d):
                U[pos[(m, m, k, l)], k * d + l] = 1
    cons = [J + Q >> 0, J - Q >> 0, (QG + QG.T) / 2 >> 0, (J - Q) @ U == 0, c + g >= 0]
    if not allow_g:
        cons.append(g == 0)
    m0, mc, mg = margin_coeffs(d, a, b, h)
    prob = cp.Problem(cp.Maximize(m0 * e + mc * c + mg * g), cons)
    prob.solve(solver=solver)
    return prob.status, prob.value, c.value, g.value


def state_margin_direct(d, a, b, h, c, e, g):
    """Recompute the margin from the output state itself: -<u| C(|u><u|)^Gamma |u> / d."""
    L = lambda X: a * np.trace(X) * np.eye(d) - b * X.T + h * np.diag(np.diag(X))
    M = lambda X: c * np.trace(X) * np.eye(d) + e * X + g * np.diag(np.diag(X))
    rho = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1
            rho += np.kron(L(E), M(E))
    pt = rho.reshape(d, d, d, d).transpose(0, 3, 2, 1).reshape(d * d, d * d)
    u = np.eye(d).reshape(-1)
    return -(u @ pt @ u) / d, np.linalg.eigvalsh(rho).min(), np.linalg.eigvalsh(pt).min()
