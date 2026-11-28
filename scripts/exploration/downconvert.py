"""Can n copies of the certified d = 8 Werner state be locally projected to an NPT r x r state, r < 8?

rho^Gamma is proportional to W = I - c' P with P the maximally entangled projector and c' = 8 x.
A vector psi of Schmidt rank <= r across A^n : B^n corresponds to a matrix Psi of rank <= r, and
    <psi| W^{(x)n} |psi> = sum_S (-x)^{|S|} || Tr_S Psi ||^2 .
We minimise the Rayleigh quotient over Psi = A B^T with A, B of shape (8^n, r).
"""
import sys, time, numpy as np
from scipy.optimize import minimize
d = 8
def apply_W(Psi, n, x):
    T = Psi.reshape([d] * (2 * n))                      # (a_1..a_n, b_1..b_n)
    for s in range(n):
        tr = np.trace(T, axis1=s, axis2=n + s)           # partial trace over site s
        eye = np.eye(d)
        corr = np.multiply.outer(tr, eye)                # axes: remaining (2n-2), then (a_s, b_s)
        order = list(range(2 * n - 2))
        order.insert(s, 2 * n - 2)                       # put a_s back at position s
        order.insert(n + s, 2 * n - 1)                   # put b_s back at position n+s
        T = T - x * corr.transpose(order)
    return T.reshape(d ** n, d ** n)
def run(n, r, x, restarts, seed=0, product_start=False):
    N = d ** n
    rng = np.random.default_rng(seed)
    def fg(p):
        A, B = p[:N * r].reshape(N, r), p[N * r:].reshape(N, r)
        Psi = A @ B.T
        WP = apply_W(Psi, n, x)
        nn = np.vdot(Psi, Psi); f = np.vdot(Psi, WP) / nn
        G = 2 * (WP - f * Psi) / nn
        return f, np.concatenate([(G @ B).ravel(), (G.T @ A).ravel()])
    best = np.inf
    for t in range(restarts):
        if product_start and t == 0:                     # rank-r maximally entangled on copy 1, product elsewhere
            A = np.zeros((N, r)); B = np.zeros((N, r))
            for k in range(r):
                A[k * d ** (n - 1), k] = 1; B[k * d ** (n - 1), k] = 1
            p0 = np.concatenate([A.ravel(), B.ravel()]) + 0.05 * rng.normal(size=2 * N * r)
        else:
            p0 = rng.normal(size=2 * N * r)
        res = minimize(fg, p0, jac=True, method="L-BFGS-B", options={"maxiter": 4000, "maxfun": 6000, "ftol": 1e-15, "gtol": 1e-10})
        best = min(best, res.fun)
    return best
# self-test of apply_W against the explicit formula for n = 1
rng = np.random.default_rng(5); X = rng.normal(size=(8, 8))
assert np.allclose(apply_W(X, 1, 0.3), X - 0.3 * np.trace(X) * np.eye(8))
for label, x in [("x = 3/23 (Lean-verified state)", 3 / 23), ("x = 75/569 (exact-checked candidate)", 75 / 569)]:
    print(label)
    for n in (1, 2, 3):
        row = []
        for r in (7, 6, 5, 4, 3, 2):
            t = time.time()
            v = run(n, r, x, restarts=(6 if n < 3 else 3), product_start=True)
            prod = (1 - r * x) * (1 - x) ** (n - 1)
            row.append(f"r={r}: {v:+.5f} (product {prod:+.5f})")
        print(f"  n={n}: " + " | ".join(row), flush=True)
