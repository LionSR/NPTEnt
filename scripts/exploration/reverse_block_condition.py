"""S-free necessary condition for a certificate (the one used in docs/qutrit-werner-endpoint.md):
for every z the block matrix [[C(uu), C(zu)], [C(uz), C(zz)]] is PSD.  With rho~ = C(uu) > 0 this is
positivity of the map  C - Xi,  Xi(|z><z|) = C(|u><z|) rho~^{-1} C(|z><u|),  i.e. block-positivity
of its Choi matrix on product vectors z (x) w.  We minimise that biquadratic form numerically.
"""
import sys, numpy as np
def choi_maps(d, x, y):
    """L(X) = Tr(X) I - x X^T, M(X) = y Tr(X) I + X, as 4-index arrays T[a,b,p,q] = <p| Map(E_ab) |q>."""
    I = np.eye(d)
    Lt = np.einsum("ab,pq->abpq", I, I) - x * np.einsum("aq,bp->abpq", I, I)
    Mt = y * np.einsum("ab,pq->abpq", I, I) + np.einsum("ap,bq->abpq", I, I)
    return Lt, Mt
def rmin(d, x, y, restarts=40, iters=300, seed=0):
    Lt, Mt = choi_maps(d, x, y)
    D = d * d
    # C[a1 a2, b1 b2, p1 p2, q1 q2] = L[a1,b1,p1,q1] M[a2,b2,p2,q2]
    Ct = np.einsum("abpq,cdrs->acbdprqs", Lt, Mt).reshape(D, D, D, D)
    u = np.eye(d).reshape(D)
    rho = np.einsum("a,b,abpq->pq", u, u, Ct)
    K = np.einsum("b,abpq->apq", u, Ct)                     # K[a] = C(E_{a,u})
    rinv = np.linalg.inv(rho)
    Xi = np.einsum("brp,rs,asq->abpq", K, rinv, K)          # reverse block: C(E_uz) rho^-1 C(E_zu), real case
    G = Ct - Xi                                              # G[a,b,p,q] = <p|(C - Xi)(E_ab)|q>
    rng = np.random.default_rng(seed)
    Q, _ = np.linalg.qr(np.column_stack([u, rng.normal(size=(D, D - 1))]))
    B = Q[:, 1:]                                             # real orthonormal basis of the complement of u
    best, arg = np.inf, None
    for t in range(restarts):
        w = rng.normal(size=D) + 1j * rng.normal(size=D); w /= np.linalg.norm(w)
        val = np.inf
        for it in range(iters):
            Az = np.einsum("abpq,p,q->ab", G, w.conj(), w)   # form in z: z^dagger Az^T-type
            Az = (Az + Az.conj().T) / 2
            ev, V = np.linalg.eigh(B.T @ Az @ B); z = (B @ V[:, 0]).conj()   # z restricted to z _|_ u   # <w|(C-Xi)(zz*)|w> = sum z_a conj(z_b) Az[a,b]
            Aw = np.einsum("abpq,a,b->pq", G, z, z.conj())
            Aw = (Aw + Aw.conj().T) / 2
            ew, Vw = np.linalg.eigh(Aw); w = Vw[:, 0]
            if abs(ew[0] - val) < 1e-13: break
            val = ew[0]
        if val < best: best, arg = val, (z, w)
    return best / np.trace(rho) * D                          # scale-free
if __name__ == "__main__":
    print("sanity d=3: x=0.9, y=0.4 (NPT side) ->", round(rmin(3, 0.9, 0.4, restarts=20), 4), "| x=0.5, y=2.0 (deep PPT) ->", round(rmin(3, 0.5, 2.0, restarts=20), 4))
    for d in range(3, 8):
        print(f"d={d}: minimum of the form (z orthogonal to u); negative = necessary condition violated")
        for frac, tag in ((1.0, "on the PPT boundary      "), (0.9, "inside NPT (y = 0.9 y_bd) ")):
            row = []
            for x in (0.5, 0.6, 0.7, 0.85):
                y = frac * (d * x - 1) / (d - x)
                row.append(f"x={x}: " + (f"{rmin(d, x, y, restarts=(16 if d < 6 else 5), iters=(300 if d < 6 else 120)):+.4f}" if y > 0 else "n/a"))
            print("   " + tag + " | ".join(row), flush=True)
