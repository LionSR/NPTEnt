# Explicit families from the NPT certificate mechanism

Let $F$ be SWAP on $\mathbb C^8\otimes\mathbb C^8$, let $I$ be the identity there, and set
$$\rho_\star=\frac{23I-3F}{1448},\qquad c_\star=\frac{1+\sqrt2}{4}.$$
Let $\Phi_2$ project onto $(|00\rangle+|11\rangle)/\sqrt2$. Bell overlap of an unnormalized output $\tau$ is $\operatorname{Tr}(\Phi_2\tau)$. The committed baseline theorem gives the homogeneous all-copy Bell-overlap cap $c_\star$ under finite separable operations. This note derives families from that mechanism. The parameterized family statements below are mathematical derivations, not yet additional Lean declarations.

## 1. Closure under successful separable operations

Suppose $\Sigma$ is a finite product-Kraus separable operation and $p=\operatorname{Tr}\Sigma(\rho_\star)>0$. Then
$$\sigma=\frac{\Sigma(\rho_\star)}p$$
inherits the same all-copy cap: for any $n$ and any separable output map $\Lambda$,
$$\Lambda(\sigma^{\otimes n})=p^{-n}(\Lambda\circ\Sigma^{\otimes n})(\rho_\star^{\otimes n}).$$
Tensor products and compositions preserve product-Kraus form, and the cap is homogeneous. This also covers a trace-increasing algebraic presentation of $\Sigma$: scaling a finite Kraus family down gives a physical branch without changing its normalized output. It does not establish convexity of the set of undistillable states.

## 2. An immediate Werner interval

For $0\le s<1$, define
$$\rho_s=\frac{(23+s)I-3F}{1448+64s}.$$
Write $\eta=64s/(1448+64s)$. Since both marginals of $\rho_\star$ are $I_8/8$,
$$\rho_s=(1-\eta)\rho_\star+\eta\frac I{64}
=(\operatorname{id}\otimes\mathcal D_\eta)(\rho_\star),\qquad
\mathcal D_\eta(X)=(1-\eta)X+\eta\operatorname{Tr}(X)I_8/8.$$
Thus this is local depolarization, not an unjustified convex mixture of two entangled resources. Positivity and trace one are immediate; the partial-transpose eigenvalue on $u=\sum_i|i,i\rangle$ is
$$\frac{s-1}{1448+64s}<0.$$
Every member inherits the all-copy obstruction. In Werner notation $\rho(d,\alpha)=(I+\alpha F)/(d^2+d\alpha)$, this covers
$$d=8,\qquad -\frac3{23}\le\alpha<-\frac18.$$
In the Dür–Cirac convention the parameter is $\beta=(1-s)/(23+s)$, so $0<\beta\le1/23$. At $s=1$ the negative eigenvalue vanishes, as required.

## 3. Non-Werner filtering and higher-dimensional families

Let $D_r=\operatorname{diag}(r,1,\ldots,1)$, $r>0$. A normalized local filter gives
$$\sigma_r=\frac{23(D_r^2\otimes I_8)-3(D_r\otimes D_r)F}{181(r^2+7)}.$$
For $\psi_r=(D_r^{-1}\otimes I_8)u$,
$$\langle\psi_r|\sigma_r^{T_A}|\psi_r\rangle=-\frac8{181(r^2+7)}<0.$$
Its Alice marginal is $D_r^2/(r^2+7)$, nonuniform for $r\ne1$. Hence these are non-Werner states and not locally-unitarily equivalent to Werner states. They are nevertheless invertible-local-filter equivalents of the baseline, not new SLOCC resource types. Replace $D_r$ by $D_r/\max(1,r)$ to obtain a contraction; normalization removes this scale.

For every integer $d\ge8$, let $V:\mathbb C^8\to\mathbb C^d$ be the standard coordinate isometry. Then
$$\tau_{d,t}=(1-t)(V\otimes V)\rho_\star(V\otimes V)^\dagger+t\frac{I_{d^2}}{d^2},\qquad
0<t<\frac{d^2}{1448+d^2},$$
is full rank and NPT. Its negative partial-transpose eigenvalue is
$$-\frac{1-t}{1448}+\frac t{d^2}<0.$$
The construction uses local isometries and a shared-randomness choice between keeping the input and preparing a product maximally mixed state. It therefore inherits the cap. For $d>8$ its marginals are nonuniform, excluding local-unitary equivalence to a $d$-dimensional Werner state. This is not a minimum-dimension theorem.

## 4. A nontrivial certificate family from the checked perturbation endpoint

Fix $L(X)=5\operatorname{Tr}(X)I_8-3X^T$ and $P_0=|0\rangle\langle0|$. Consider
$$M_t(X)=18\operatorname{Tr}(X)I_8+37X-\frac t8\langle0|X|0\rangle P_0,\qquad 0\le t\le1.$$
The normalized output is
$$\widetilde\rho_t=
\frac{296(23I-3F)-t(5I_8-3P_0)\otimes P_0}{37(11584-t)}.$$
It is strictly positive: its numerator is at least $(5920-5t)I$. Moreover,
$$\frac{\langle u|\widetilde\rho_t^{T_A}|u\rangle}{8}
=-\frac{1184+t}{148(11584-t)}<0,$$
and its Bob marginal is $(1448I_8-tP_0)/(11584-t)$, nonuniform for $t>0$.

The endpoints are the baseline and candidate 3 of the exact-check report. Both have exact rational certificates. With $J_t=(1-t)J_0+tJ_1$ and $Q_t=(1-t)Q_0+tQ_1$, all three PSD conditions and the common-vector kernel equation persist throughout the interval by convexity and linearity. The common $L$ and input vector are essential; this is not generic convexity of bound entanglement.

The endpoint at $t=1$ was rechecked in full-basis exact rational arithmetic. It still needs its own Lean certificate replay. Once that endpoint and the interpolation lemma are formalized, the entire non-Werner interval follows, rather than a separate numerical check for every $t$.

## 5. Stronger Werner endpoints to formalize next

The same exact checker passes $\rho(8,-75/569)$ and $\rho(9,-125/1004)$. Certifying these endpoints in Lean would immediately extend the depolarization families to
$$-\frac{75}{569}\le\alpha<-\frac18\quad(d=8),\qquad
-\frac{125}{1004}\le\alpha<-\frac19\quad(d=9).$$
At dimension 8 the baseline and stronger endpoint also share $L$. Interpolating their local maps as $M_\lambda(X)=(18-6\lambda)\operatorname{Tr}(X)I_8+(37-12\lambda)X$ gives the explicit certificate family
$$\omega_\lambda=
\frac{(851-282\lambda)I-(111-36\lambda)F}{53576-17760\lambda},\qquad0\le\lambda\le1.$$
The state mixture weights are trace-renormalized; they are not simply $\lambda$.

These are alternatives to the paper example, not a claim of literature priority or optimality. No sharp dimension threshold or large-dimension scaling law follows from these constructions.
