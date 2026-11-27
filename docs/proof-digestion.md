# Proof Digestion: General Mechanisms Behind NPT Bound Entanglement

This document digests the proof of Faisal (arXiv:2611.34921v1) into its underlying, reusable mathematical principles, separates those model-independent criteria from the explicit $\mathbb{C}^8 \otimes \mathbb{C}^8$ Werner-state instance and finite certificate data, and records subtle hypotheses, representation conventions, and open generalizations.

The guiding principle follows the architecture of CertifiedGaps: isolate the broadest natural mathematical mechanism, formalize reusable foundations upstream in QICLean, and instantiate them with self-contained, Lean-checked finite data in NPTEnt. Every accepted final theorem must be self-contained over QICLean and Mathlib, with no unformalized cited theorems and no trusted external numerical oracles.

---

## 1. Architecture of the Proof: Four General Layers + One Concrete Application

Faisal's argument for the Werner state $\rho = (23I - 3F)/1448$ on $\mathbb{C}^8 \otimes \mathbb{C}^8$ decomposes cleanly into four dimension-independent mathematical mechanisms followed by a concrete instantiation:

1. **Tensor stability of symmetric order intervals (heterogeneous dimensions, no positivity of $B_k$).**
2. **Map-level reverse-block criterion (with CP rank-one agreement and Choi representation).**
3. **Local factorization $\mathcal{C} = L \otimes M$, spectral splitting, coherence bounds, and the dimension-independent all-copy Bell-overlap obstruction.**
4. **Operational zero-distillation criterion for any explicit protocol class $\mathcal{P} \subseteq \mathrm{SEP}_{\mathrm{TP}}$.**
5. **Application and finite data:** explicit Werner state $\rho$, local CP maps $L, M$, and exact rational certificate $Q$.

Crucially, **Layers 1–4 do not assume that $\rho$ is NPT**, do not depend on local dimension $8$, do not require $\ket{u}$ to be maximally entangled or real, and do not require $L, M$ to be square maps. The NPT property enters *only* in the concrete application to show that $\rho$ is entangled (and specifically NPT) rather than separable or PPT.

---

## 2. Layer 1: Tensor Stability of Symmetric Order Intervals

### Statement
Let $n \ge 0$ and let $(A_k, B_k)_{k=1}^n$ be pairs of Hermitian operators on finite-dimensional Hilbert spaces $\mathcal{H}_k$ (of arbitrary, possibly distinct dimensions) such that
$$
  A_k + B_k \succeq 0 \qquad\text{and}\qquad A_k - B_k \succeq 0
  \qquad (1 \le k \le n),
$$
equivalently $B_k \in [-A_k, A_k]$ in the Loewner order. Then
$$
  \bigotimes_{k=1}^n A_k + \bigotimes_{k=1}^n B_k \succeq 0
  \qquad\text{and}\qquad
  \bigotimes_{k=1}^n A_k - \bigotimes_{k=1}^n B_k \succeq 0,
$$
that is, $\bigotimes_{k=1}^n B_k \in \big[-\bigotimes_{k=1}^n A_k,\, \bigotimes_{k=1}^n A_k\big]$.

### Proof mechanism and hypotheses
- **No positivity of $B_k$ is assumed:** $B_k$ may be indefinite. By contrast, $A_k = \tfrac{1}{2}((A_k+B_k)+(A_k-B_k)) \succeq 0$ and Hermiticity of both $A_k$ and $B_k$ follow automatically from $A_k \pm B_k \succeq 0$.
- **Binary inductive step:** Setting $P_k^{\pm} = \tfrac{1}{2}(A_k \pm B_k) \succeq 0$, the identities
  $$
    A_1 \otimes A_2 + B_1 \otimes B_2
    = \tfrac{1}{2}\big((A_1+B_1)\otimes(A_2+B_2) + (A_1-B_1)\otimes(A_2-B_2)\big),
  $$
  $$
    A_1 \otimes A_2 - B_1 \otimes B_2
    = \tfrac{1}{2}\big((A_1+B_1)\otimes(A_2-B_2) + (A_1-B_1)\otimes(A_2+B_2)\big)
  $$
  preserve both inequalities simultaneously. The base case $n = 0$ is the $1 \times 1$ identity $1 \in [-1, 1]$.
- **Cone generality:** The same algebraic identity holds in any partially ordered cone closed under addition, nonnegative scaling, and tensor products—in particular for completely positive linear maps between matrix algebras.

### Integration status
The general heterogeneous tensor-domination theorems (`Matrix.kronecker_add_sub_posSemidef`, `Matrix.piKronecker_add_sub_posSemidef`, `Matrix.piKronecker_const_add_sub_posSemidef` in `Analysis.Order.FiniteKroneckerOrder`, covering indefinite $B_k$, heterogeneous finite bases, $n = 0$, and empty spaces with only the three standard axioms) are verified in the upstream QICLean worktree. Because NPTEnt's published downstream pin is unchanged, the corresponding blueprint node (`lem:tensor-interval`) remains `\notready` here with no unavailable declaration links until the upstream revision is published and integrated.

---

## 3. Layer 2: Map-Level Reverse-Block Criterion and Choi Representation

### Rank-one agreement implies off-diagonal agreement
Let $\mathcal{D} : \mathcal{L}(\mathcal{H}_{\mathrm{in}}) \to \mathcal{L}(\mathcal{H}_{\mathrm{out}})$ be a completely positive linear map (rectangular dimensions allowed) and let $\ket{u} \in \mathcal{H}_{\mathrm{in}}$ be an arbitrary vector. If $\mathcal{D}(\ketbra{u}{u}) = 0$, then
$$
  \mathcal{D}(\ketbra{z}{u}) = 0 \qquad\text{and}\qquad \mathcal{D}(\ketbra{u}{z}) = 0
  \qquad \forall \ket{z} \in \mathcal{H}_{\mathrm{in}}.
$$
**Proof:** Writing $\mathcal{D}(X) = \sum_\alpha K_\alpha X K_\alpha^{\dagger}$, the condition $\sum_\alpha (K_\alpha \ket{u})(K_\alpha \ket{u})^{\dagger} = 0$ forces $K_\alpha \ket{u} = 0$ for every $\alpha$, whence $\mathcal{D}(\ketbra{z}{u}) = \sum_\alpha (K_\alpha \ket{z})(K_\alpha \ket{u})^{\dagger} = 0$ and $\mathcal{D}(\ketbra{u}{z}) = 0$. (Alternatively, $2$-positivity applied to $\begin{pmatrix}\ketbra{u}{u} & \ketbra{u}{z} \\ \ketbra{z}{u} & \ketbra{z}{z}\end{pmatrix} \succeq 0$ gives a PSD $2\times 2$ block matrix with zero upper-left block, forcing both off-diagonal blocks to vanish.)

**Simplification for tensor products:** When **both** $\mathcal{C}_k + \mathcal{S}_k$ and $\mathcal{C}_k - \mathcal{S}_k$ are CP and $\mathcal{C}_k(\ketbra{u^{(k)}}{u^{(k)}}) = \mathcal{S}_k(\ketbra{u^{(k)}}{u^{(k)}})$ for each $k$, the tensor products $\mathcal{C} = \bigotimes_k \mathcal{C}_k$ and $\mathcal{S} = \bigotimes_k \mathcal{S}_k$ immediately agree on $\ketbra{u}{u}$ for $\ket{u} = \bigotimes_k \ket{u^{(k)}}$. Since $\mathcal{C} - \mathcal{S}$ is CP by Layer 1 (which requires both $\mathcal{C}_k + \mathcal{S}_k$ and $\mathcal{C}_k - \mathcal{S}_k$ to be CP), off-diagonal agreement $\mathcal{C}(\ketbra{z}{u}) = \mathcal{S}(\ketbra{z}{u})$ and $\mathcal{C}(\ketbra{u}{z}) = \mathcal{S}(\ketbra{u}{z})$ follows for all $\ket{z}$ immediately—without needing a product-vector spanning argument. (This simplification is a planned lemma to formalize, not yet Lean-verified.)

### Abstract map-level reverse-block criterion
Let $\mathcal{C}, \mathcal{S} : \mathcal{L}(\mathcal{H}_{\mathrm{in}}) \to \mathcal{L}(\mathcal{H}_{\mathrm{out}})$ be linear maps and $\ket{u} \in \mathcal{H}_{\mathrm{in}}$ an arbitrary vector satisfying:
1. $\mathcal{C} + \mathcal{S}$ and $\mathcal{C} - \mathcal{S}$ are completely positive;
2. $\mathcal{S}$ is completely copositive (i.e., $\mathcal{S} \circ T$ is completely positive, where $T(X) = X^T$ in a fixed basis);
3. $\mathcal{C}(\ketbra{u}{u}) = \mathcal{S}(\ketbra{u}{u})$ (equivalently, under (1), $\mathcal{C}$ and $\mathcal{S}$ agree on $\ketbra{z}{u}$ and $\ketbra{u}{z}$ for all $\ket{z}$).

Then for every $n \ge 1$ and all vectors $\ket{v}, \ket{w} \in \mathcal{H}_{\mathrm{in}}^{\otimes n}$ with $\ket{v} + \ket{w} = \ket{u}^{\otimes n}$,
$$
  \Omega_{v,w} = \begin{pmatrix}
    \mathcal{C}^{\otimes n}(\ketbra{w}{w}) & \mathcal{C}^{\otimes n}(\ketbra{v}{w}) \\
    \mathcal{C}^{\otimes n}(\ketbra{w}{v}) & \mathcal{C}^{\otimes n}(\ketbra{v}{v})
  \end{pmatrix} \succeq 0.
$$
The same conclusion holds for any finite heterogeneous tensor product $\bigotimes_{k=1}^n \mathcal{C}_k$ with $\ket{u} = \bigotimes_{k=1}^n \ket{u^{(k)}}$ whenever each factor $(\mathcal{C}_k, \mathcal{S}_k, \ket{u^{(k)}})$ satisfies (1)–(3).

**Check for complex vectors:** For arbitrary complex $\ket{u_n}, \ket{z}$, the block matrix $\begin{pmatrix}\ketbra{u_n}{u_n} & \ketbra{u_n}{z} \\ \ketbra{z}{u_n} & \ketbra{z}{z}\end{pmatrix}$ is PSD, so its global transpose $\begin{pmatrix}(\ketbra{u_n}{u_n})^T & (\ketbra{z}{u_n})^T \\ (\ketbra{u_n}{z})^T & (\ketbra{z}{z})^T\end{pmatrix}$ is PSD (transposition preserves PSD for complex matrices because $X^T = \overline{X^{\dagger}}$). Applying the CP map $\mathcal{S}_n \circ T$ blockwise, replacing $\mathcal{S}_n$ with $\mathcal{C}_n$ in the first three blocks, adding $(\mathcal{C}_n - \mathcal{S}_n)(\ketbra{z}{z}) \succeq 0$ to the $(2,2)$ block, setting $\ket{z} = \ket{v}$, and conjugating by $E = \begin{pmatrix}I & -I \\ 0 & I\end{pmatrix}$ yields $\Omega_{v,w} \succeq 0$. No reality assumption on $\ket{u}$ is used.

### Choi representation and the complex-conjugate kernel condition (API warning)
For a linear map $\Lambda : \mathcal{L}(\mathbb{C}^{d_{\mathrm{in}}}) \to \mathcal{L}(\mathbb{C}^{d_{\mathrm{out}}})$, the **unnormalized, input-first Choi matrix** is
$$
  J_\Lambda = \sum_{a,b} \ketbra{a}{b} \otimes \Lambda(\ketbra{a}{b})
  \in \mathcal{L}(\mathbb{C}^{d_{\mathrm{in}}} \otimes \mathbb{C}^{d_{\mathrm{out}}}).
$$
Let $\ket{u} = \sum_b u_b \ket{b} \in \mathbb{C}^{d_{\mathrm{in}}}$ be an arbitrary complex vector, and let $\ket{\bar{u}} = \sum_b \overline{u_b}\ket{b}$ be its entrywise complex conjugate in the computational basis. Because $\bra{u} = \sum_b \overline{u_b}\bra{b}$ and $\braket{b}{\bar{u}} = \overline{u_b}$, we have
$$
  J_\Lambda(\ket{\bar{u}} \otimes I_{\mathrm{out}})
  = \sum_{a,b} \ket{a}\braket{b}{\bar{u}} \otimes \Lambda(\ketbra{a}{b})
  = \sum_a \ket{a} \otimes \Lambda\!\left(\sum_b \overline{u_b}\ketbra{a}{b}\right)
  = \sum_a \ket{a} \otimes \Lambda(\ketbra{a}{u}),
$$
and similarly
$$
  (\bra{\bar{u}} \otimes I_{\mathrm{out}})\, J_\Lambda\, (\ket{\bar{u}} \otimes I_{\mathrm{out}})
  = \sum_{a,b} u_a \overline{u_b}\, \Lambda(\ketbra{a}{b})
  = \Lambda(\ketbra{u}{u}).
$$
Multiplying instead by $\ket{u} \otimes I_{\mathrm{out}}$ yields $\sum_a \ket{a} \otimes \Lambda(\ketbra{a}{\bar{u}})$, which agrees with $\Lambda(\ketbra{a}{u})$ only when $\ket{u}$ has real coordinates (as in Faisal's $\ket{u} = \sum_i \ket{i,i}$).

**Important QICLean API distinction (do not conflate):**
- `Matrix.rectangularChoi` (in `RectangularChoi.lean`) is **unnormalized, input-first**: $J_{(i,a),(j,b)} = \Phi(E_{ij})_{ab}$. Its kernel vector is $\ket{\bar{u}} \otimes y$, and $(\bra{\bar{u}} \otimes I)\,J\,(\ket{\bar{u}} \otimes I) = \Phi(\ketbra{u}{u})$.
- `ChoiRectangular.choiMatrix` (in `Rectangular.lean`) is **normalized, output-first**: $\frac{1}{d_{\mathrm{in}}} \mathrm{SWAP}\,J\,\mathrm{SWAP}$ (for $d_{\mathrm{in}} > 0$). Its kernel vector is $y \otimes \ket{\bar{u}}$, and $(I \otimes \bra{\bar{u}})\,J^{\mathrm{out}}\, (I \otimes \ket{\bar{u}}) = \frac{1}{d_{\mathrm{in}}}\Phi(\ketbra{u}{u})$.

For the input-first convention, the map-level conditions (1)–(3) are equivalent to:
$$
  J_{\mathcal{C}} + J_{\mathcal{S}} \succeq 0, \qquad
  J_{\mathcal{C}} - J_{\mathcal{S}} \succeq 0, \qquad
  J_{\mathcal{S}}^{\Gamma_{\mathrm{in}}} \succeq 0, \qquad
  (J_{\mathcal{C}} - J_{\mathcal{S}})(\ket{\bar{u}} \otimes I_{\mathrm{out}}) = 0
$$
(where the fourth condition is equivalent to $(\bra{\bar{u}} \otimes I_{\mathrm{out}})(J_{\mathcal{C}} - J_{\mathcal{S}})(\ket{\bar{u}} \otimes I_{\mathrm{out}}) = 0$ given $J_{\mathcal{C}} - J_{\mathcal{S}} \succeq 0$).

---

## 4. Layer 3: Local Factorization, Spectral Split, Coherence, and All-Copy Overlap Obstruction

### Do arbitrary bipartite $\ket{u}$ and rectangular CP local maps suffice?
**Yes (hand-derived mathematical argument reviewed here; not yet Lean-verified — formalization of the general criterion remains pending).** Let $\mathcal{H}_{A,\mathrm{in}}, \mathcal{H}_{B,\mathrm{in}}, \mathcal{H}_{A,\mathrm{out}}, \mathcal{H}_{B,\mathrm{out}}$ be arbitrary finite-dimensional Hilbert spaces, let
$$
  L : \mathcal{L}(\mathcal{H}_{A,\mathrm{in}}) \to \mathcal{L}(\mathcal{H}_{A,\mathrm{out}}),
  \qquad
  M : \mathcal{L}(\mathcal{H}_{B,\mathrm{in}}) \to \mathcal{L}(\mathcal{H}_{B,\mathrm{out}})
$$
be rectangular completely positive maps, set $\mathcal{C} = L \otimes M$, and let $\ket{u} \in \mathcal{H}_{A,\mathrm{in}} \otimes \mathcal{H}_{B,\mathrm{in}}$ be an arbitrary bipartite vector with $\Tr(\mathcal{C}(\ketbra{u}{u})) > 0$. Define the state $\rho = \mathcal{C}(\ketbra{u}{u}) / \Tr(\mathcal{C}(\ketbra{u}{u}))$.

Suppose there exists a linear map $\mathcal{S} : \mathcal{L}(\mathcal{H}_{A,\mathrm{in}} \otimes \mathcal{H}_{B,\mathrm{in}}) \to \mathcal{L}(\mathcal{H}_{A,\mathrm{out}} \otimes \mathcal{H}_{B,\mathrm{out}})$ satisfying the single-copy certificate conditions of Layer 2. Then:

1. **Adjoints:** The Hilbert--Schmidt adjoints $L_n^{\dagger} = (L^{\dagger})^{\otimes n}$ and $M_n^{\dagger} = (M^{\dagger})^{\otimes n}$ are CP (rectangular Kraus operators simply conjugate-transpose). For any PSD $X_i$ on $\mathcal{H}_{A,\mathrm{out}}^{\otimes n}$ and $Y_j$ on $\mathcal{H}_{B,\mathrm{out}}^{\otimes n}$, setting $E_i = L_n^{\dagger}(X_i) \succeq 0$ and $F_j = M_n^{\dagger}(Y_j) \succeq 0$ gives $\Tr((X_i \otimes Y_j)\mathcal{C}_n(\ketbra{x}{y})) = \bra{y}(E_i \otimes F_j)\ket{x}$.
2. **Spectral split without invertibility:** Let $H = E_0 + E_1 \succeq 0$ and let $\Pi$ be the orthogonal projection onto $\operatorname{supp}(H) = (\ker H)^{\perp}$. Define $N = H^{-1/2}\Pi + (I - \Pi)$, which is always Hermitian and positive definite (invertible even when $H$ is singular or zero). Then $E_i' = N E_i N$ satisfy $E_0' + E_1' = \Pi$ and $\Pi E_i' = E_i' \Pi = E_i'$, so $E_0'$ and $E_1'$ commute. Letting $P$ be the nonnegative spectral projection of $E_0' - E_1'$ and setting
   $$
     \ket{v} = (N P N^{-1} \otimes I)\ket{u_n}, \qquad
     \ket{w} = (N (I-P) N^{-1} \otimes I)\ket{u_n}
   $$
   gives $\ket{v} + \ket{w} = \ket{u_n}$, cross-term vanishing $\Tr(D_{ij} R_{vw}) = \Tr(D_{ij} R_{wv}) = 0$, $p_{ij} = a_{ij} + b_{ij}$, $a_{0j} \ge a_{1j}$, and $b_{0j} \le b_{1j}$. Nothing here uses maximal entanglement of $\ket{u}$, reality of $\ket{u}$, or squareness of $L, M$.
3. **Rank-one coherence bound:** For rank-one $X_i = \ketbra{a_i}{a_i}$ and $Y_j = \ketbra{b_j}{b_j}$, compressing the four $2\times 2$ block matrices to $2\times 2$ scalar PSD matrices avoids operator-norm contractions and Schatten norms completely, yielding the four-term bound $k \le \sqrt{p_{00}p_{01}} + \sqrt{p_{10}p_{11}} + 2\sqrt{p_{01}p_{10}}$. Rescaling $(X_0, X_1) \mapsto (\lambda X_0, \lambda^{-1} X_1)$ and tensor-power amplification on $nt$ copies with $\ket{a_i}^{\otimes t}, \ket{b_j}^{\otimes t}$ (handling zero cases explicitly) yields $k^4 \le p_{00} p_{01} p_{10} p_{11}$ for every $n \ge 1$.
4. **Unnormalized linear Bell-overlap cap:** For a single product Kraus operator $A \otimes B$ with output $\tau_\alpha = (A \otimes B)\rho^{\otimes n}(A \otimes B)^{\dagger}$, setting $s_\alpha = p_{00}^{(\alpha)} + p_{11}^{(\alpha)}$ and $r_\alpha = p_{01}^{(\alpha)} + p_{10}^{(\alpha)}$ gives $k^{(\alpha)} \le \tfrac{1}{2}\sqrt{s_\alpha r_\alpha}$. By AM--GM,
   $$
     (\sqrt{2}-1)s_\alpha + (\sqrt{2}+1)r_\alpha \ge 2\sqrt{s_\alpha r_\alpha},
   $$
   and hence
   $$
     \Tr(\Phi^+ \tau_\alpha)
     \le \tfrac{1}{2}\big(s_\alpha + \sqrt{s_\alpha r_\alpha}\big)
     \le \frac{1+\sqrt{2}}{4}(s_\alpha + r_\alpha)
     = \frac{1+\sqrt{2}}{4}\Tr(\tau_\alpha),
   $$
   valid even when $\tau_\alpha = 0$. By **linearity**, summing over any finite shared-index product-Kraus family immediately yields
   $$
     \Tr\big(\Phi\,\Lambda(\rho^{\otimes n})\big)
     \le \frac{1+\sqrt{2}}{4}\Tr\big(\Lambda(\rho^{\otimes n})\big)
   $$
   for every maximally entangled two-qubit Bell state $\ket{\Phi}$ (by local-unitary closure of product-Kraus operations). Dividing by $\Tr(\Lambda(\rho^{\otimes n})) > 0$ gives the normalized fidelity cap $(1+\sqrt{2})/4$.

### Hypotheses that CANNOT be dropped (and unchecked generalizations)
- **Local factorization $\mathcal{C} = L \otimes M$ is essential:** The spectral split requires $\mathcal{C}_n^{\dagger}(X_i \otimes Y_j)$ to factor as $E_i \otimes F_j$ so that Alice's input space can be spectrally split while $F_j \succeq 0$ remains untouched on Bob's side. Whether a similar criterion holds for non-factorized separable CP maps $\mathcal{C} = \sum_\gamma L_\gamma \otimes M_\gamma$ (without enlarging the input space by a classical register) is **not established** here.
- **Stronger trace-norm coherence bound:** Faisal's Lemma 5 states $\|\sqrt{D_{00}}\rho^{\otimes n}\sqrt{D_{11}}\|_1 \le (p_{00}p_{01}p_{10}p_{11})^{1/4}$ for arbitrary PSD $X_i, Y_j$. This follows from the same spectral split plus the Schatten-norm block inequality and multiplicativity of $\|\cdot\|_1$, and is a useful reusable theorem, though the rank-one specialization already suffices for the two-qubit Bell-overlap cap.
- **Positive-definiteness shortcut for $L_n^{\dagger}$:** For the concrete Werner map $L(X) = 5\Tr(X)I - 3X^T$, $L - 2\Tr(\cdot)I$ is CP, so $L_n^{\dagger}(X_0+X_1)$ is strictly positive definite whenever $X_0+X_1 \neq 0$. However, the general support/kernel construction $N = H^{-1/2}\Pi + (I-\Pi)$ avoids any invertibility hypothesis altogether and should be preferred for reusable theory.

---

## 5. Layer 4: Operational Zero-Distillation Criterion

### General criterion for any protocol class $\mathcal{P} \subseteq \mathrm{SEP}_{\mathrm{TP}}$
Let $\mathcal{P}$ be any explicit class of trace-preserving bipartite linear maps between finite-dimensional bipartite systems such that every $\Lambda \in \mathcal{P}$ is induced by a trace-preserving product-Kraus separable operation. Define the minimal distillation error at rate $r \ge 0$ and copy number $n \ge 1$ in the extended nonnegative reals $[0, +\infty]$ by
$$
  \varepsilon_n^{\mathcal{P}}(r)
  = \inf_{\Lambda \in \mathcal{P}(n,\lfloor rn\rfloor)}
    \big\|\Lambda(\sigma^{\otimes n}) - \Phi^{\otimes \lfloor rn\rfloor}\big\|_1
$$
with the convention $\inf \emptyset = +\infty$ (so that an empty protocol set $\mathcal{P}(n, \lfloor rn\rfloor)$ never makes a rate vacuously achievable), and define the distillable entanglement $E_D^{\mathcal{P}}(\sigma) \in [0, +\infty]$ by $E_D^{\mathcal{P}}(\sigma) = \sup\{r \ge 0 : \lim_{n\to\infty} \varepsilon_n^{\mathcal{P}}(r) = 0\}$ with $\sup \emptyset = 0$.

If there exists $c < 1$ such that $\Tr(\Phi\,\Lambda(\sigma^{\otimes n})) \le c\,\Tr(\Lambda(\sigma^{\otimes n}))$ for every $n \ge 1$ and every product-Kraus separable operation $\Lambda$ to $\mathbb{C}^2 \otimes \mathbb{C}^2$, then $E_D^{\mathcal{P}}(\sigma) = 0$.

**Key observations:**
- **No closure of $\mathcal{P}$ under partial trace is needed:** Discarding $m - 1$ output qubit pairs is itself a trace-preserving product-Kraus separable operation, and $\mathrm{SEP}_{\mathrm{TP}}$ is closed under composition. Thus $\operatorname{Tr}_{\setminus 1} \circ \Lambda \in \mathrm{SEP}_{\mathrm{TP}}$ for any $\Lambda \in \mathcal{P}(n, m)$.
- **Finite-round LOCC inclusion:** Finite-round, finite-outcome adaptive bipartite protocols built from outcome-dependent local instruments with classical feed-forward form a concrete protocol class $\mathrm{LOCC}_{\mathrm{fin}} \subseteq \mathrm{SEP}_{\mathrm{TP}}$.
- **Closure / infinite-round LOCC (unchecked extension):** Because the unnormalized bound $\Tr(\Phi\,\Lambda(\sigma^{\otimes n})) \le c\,\Tr(\Lambda(\sigma^{\otimes n}))$ defines a **closed half-space** of linear maps for each fixed $n$, it passes immediately to norm-limits of maps (e.g., $\overline{\mathrm{LOCC}}$) without any division-by-trace pathology near $\Tr(\Lambda(\sigma^{\otimes n})) = 0$. However, formalizing $\overline{\mathrm{LOCC}}$ or infinite-round LOCC requires explicit topological/operational definitions and continuity proofs, which are not yet formalized and must not be claimed as established.

---

## 6. Layer 5: Concrete Application and Certificate Verification

For the Werner state $\rho = (23I - 3F)/1448$ on $\mathbb{C}^8 \otimes \mathbb{C}^8$:
- **Already Lean-verified (NPTEnt):** $\rho \succeq 0$, $\Tr(\rho) = 1$, $\rho^{\Gamma}\ket{u} = -\ket{u}/1448$, $\rho$ is NPT and nonseparable; basic product-Kraus separable operations and their composition/trace properties.
- **Remaining concrete steps:**
  1. Verify complete positivity of $L(X) = 5\Tr(X)I - 3X^T$ and $M(X) = 18\Tr(X)I + 37X$ and the identity $\mathcal{C}(\ketbra{u}{u}) = 37 \cdot 1448\,\rho$.
  2. Verify the exact rational single-copy certificate $Q = J_{\mathcal{S}}$ on $(\mathbb{C}^8)^{\otimes 4}$ in Lean (no external numerical oracle; exact rational $LDL^T$ / Gram witnesses + full coordinate coverage of all $4096$ basis states + exact kernel check $(J-Q)(\ket{u} \otimes I) = 0$). Independent exact Python arithmetic (`scripts/check_certificate.py`) confirms all four conditions, but serves only as computational evidence prior to Lean verification.
  3. Instantiate the general criteria of Layers 1–4 to conclude the uniform Bell-overlap cap $(1+\sqrt{2})/4$ and $E_D(\rho) = 0$ under finite-round LOCC.
  4. **Not in scope yet:** Superactivation, nonadditivity, and nonconvexity of $E_D$ depend on external activation theorems for PPT states and would require self-contained formalization of those theorems before acceptance.
