# Search for certified NPT examples below dimension eight

## Epistemic status

Everything here is numerical evidence from floating-point semidefinite programs and local
minimisations run on 2026-11-28 with the scripts in `scripts/exploration/` (NumPy, SciPy and
CVXPY with the Clarabel solver; not part of CI). Nothing in this note is a Lean proof or an exact
rational certificate. A negative value found for the reverse-block condition of Section 4 is a
violation witnessed by explicit vectors, up to floating-point error; a nonnegative value only says
that the local search found no violation.

**Outcome: no certified NPT state of local dimension below eight was found.** The four experiments
below explain why the present construction stops at eight and which directions remain.

## Conventions

Local maps on $d\times d$ matrices, with $u=\sum_i|ii\rangle$ and $C=L\otimes M$:
$$L(X)=a\operatorname{Tr}(X)I-bX^T+h\operatorname{diag}(X),\qquad
M(X)=c\operatorname{Tr}(X)I+eX+g\operatorname{diag}(X).$$
The paper's family is $g=h=0$. The output is $C(|u\rangle\langle u|)=A\,I-be\,F+\kappa\Delta$ with
$\Delta=\sum_i|ii\rangle\langle ii|$, $A=dac+a(e+g)+(h-b)c$ and $\kappa=he+hg-bg$. Its
$U\otimes U$ twirl is an NPT Werner state exactly when the margin
$$\mu=dbe-A-\kappa$$
is positive. We fix $b=e=1$. For $g=h=0$ the Werner parameter satisfies $d\alpha=-d/(d-\mu)$.

A certificate is a real symmetric $Q$ with $J\pm Q\succeq0$, $Q^{\Gamma_{\mathrm{in}}}\succeq0$ and
$(J-Q)(u\otimes I)=0$, where $J$ is the Choi matrix of $C$. All these maps are invariant under
diagonal unitaries and label permutations, so $Q$ may be taken invariant as well. Every matrix
inequality then splits into torus-weight blocks of size at most $6d-6$, and $Q$ has one real
parameter per equality pattern of the eight labels of an entry (82 parameters for $d\ge4$).
`validate_reduction.py` checks the reduction against the unreduced program at $d=3$: the optimal
values agree to six digits in four test cases.

## 1. The covariant family, reproduced

`covariant_table.py` maximises $\mu$ over $c$ and $Q$ for fixed $a$ and then over $a$.

| $d$ | best $a$ | $\mu$ | $d\alpha$ | NPT |
|---:|---:|---:|---:|:---:|
| 3 | 1.837 | $-2.461$ | $-0.5494$ | no |
| 4 | 1.744 | $-1.891$ | $-0.6790$ | no |
| 5 | 1.686 | $-1.311$ | $-0.7922$ | no |
| 6 | 1.652 | $-0.727$ | $-0.8919$ | no |
| 7 | 1.634 | $-0.141$ | $-0.9803$ | no |
| 8 | 1.623 | $+0.458$ | $-1.0608$ | yes |
| 9 | 1.615 | $+1.080$ | $-1.1363$ | yes |
| 10 | 1.608 | $+1.721$ | $-1.2079$ | yes |

This independently reproduces the table in `docs/additional-candidates.md`, which was reported
from an unsaved Wolfram computation. The agreement is to three or four digits; the values here are
slightly better because $a$ is optimised rather than sampled.

## 2. Diagonal terms do not help at dimension seven

`monomial_family.py 7` scans $a\in[1,3]$ and $h\in[0,10]$ with $c$, $g$ and $Q$ optimised. The best
point of the grid is the covariant one ($h=0$, optimal $g=0$, $\mu=-0.141$); a scan in $h$ through
the covariant optimum, including negative $h$, is maximal at $h=0$. At $d=3$ the same family moves
the optimum to $a\approx1.01$, $h\approx1.47$, $g\approx-0.91$ with $\mu\approx-1.36$, better than
the covariant $-2.46$ but still on the PPT side.

The covariant optimum is a critical point for every non-covariant perturbation of the maps, since
the first-order change of the optimal value depends only on the twirl of the perturbation. The
scan shows that in the two diagonal directions it is a local maximum, not a saddle.

## 3. Copies of the dimension-eight state do not project to smaller NPT states

If $n$ copies of a certified state could be projected by local filters onto an NPT state of local
dimension $r<8$, that state would inherit undistillability with no new certificate. This happens
exactly when $W^{\otimes n}$ takes a negative value on a vector of Schmidt rank at most $r$ across
$A^n:B^n$, where $W=I-8xP$ is proportional to $\rho^\Gamma$ and $P$ is the maximally entangled
projector. For a vector with coefficient matrix $\Psi$,
$$\langle\psi|W^{\otimes n}|\psi\rangle=\sum_{S\subseteq[n]}(-x)^{|S|}\,\|\operatorname{Tr}_S\Psi\|_2^2 .$$
`downconvert.py` minimises this over rank-$r$ matrices for $x=3/23$ (the Lean-verified state) and
$x=75/569$, with $n\le3$ and $2\le r\le7$. In every case the minimum found equals the value
$(1-rx)(1-x)^{n-1}>0$ of a rank-$r$ maximally entangled vector on one copy tensored with product
vectors on the others. No entangled-across-copies vector did better.

This suggests that $\rho^{\Gamma\,\otimes n}$ stays positive on Schmidt rank seven for all $n$,
which would be stronger than the Schmidt-rank-two statement proved in `NPTEnt.Main`. It is not
proved here.

## 4. A certificate-free obstruction below dimension eight

A certificate for $(C,u)$ implies that for every $z$ the reverse block matrix
$$\begin{pmatrix}C(E_{uu})&C(E_{zu})\\ C(E_{uz})&C(E_{zz})\end{pmatrix}$$
is positive semidefinite; this is the condition used in `docs/qutrit-werner-endpoint.md`. It does
not mention $Q$, and it is necessary for reverse-block positivity on any number of copies (take
$z\otimes u^{\otimes(n-1)}$). By a Schur complement it says that the map
$X\mapsto C(X)-\Xi(X)$, $\Xi(E_{zz})=C(E_{uz})\,C(E_{uu})^{-1}C(E_{zu})$, is positive.
`reverse_block_condition.py` minimises the corresponding biquadratic form over $z\perp u$ and $w$,
normalised by $\operatorname{Tr}C(E_{uu})/d^2$.

For the covariant family, written as $L(X)=\operatorname{Tr}(X)I-xX^T$, $M(X)=y\operatorname{Tr}(X)I+X$,
the minimum on the PPT boundary $y=(dx-1)/(d-x)$ is

| $d$ | $x=0.5$ | $x=0.6$ | $x=0.7$ | $x=0.85$ |
|---:|---:|---:|---:|---:|
| 3 | $-0.806$ | $-0.601$ | $-0.546$ | $-0.646$ |
| 4 | $-0.307$ | $-0.215$ | $-0.203$ | $-0.279$ |
| 5 | $-0.131$ | $-0.080$ | $-0.082$ | $-0.145$ |
| 6 | $-0.052$ | $-0.022$ | $-0.028$ | $-0.083$ |
| 7 | $-0.017$ | $-0.003$ | $-0.006$ | $-0.050$ |

and it is more negative at $y=0.9\,y_{\mathrm{bd}}$ in every sampled case. A finer scan at $d=7$
($x=0.58,\dots,0.67$) stays between $-0.0028$ and $-0.0043$. At $d=8$, $x=3/5$, $y=18/37$, where the
paper's certificate exists, the search finds no violation (minimum $+0.0019$).

So at the sampled parameters the covariant maps violate a necessary condition throughout the NPT
region for every $d\le7$. No auxiliary map of any kind, and no certificate built on several copies
of the same $C$, can exist there. The qutrit proposition is the $d=3$ instance with the explicit
choice $z=|01\rangle$.

`threshold_comparison.py` compares, for fixed $a$, the smallest $c$ admitting a certificate with
the point where this condition starts to fail. In six of seven tested cases ($d=4,5,6$) the
condition already fails at $0.97\,c^\ast$. The single-copy certificate therefore loses at most a
few percent against the necessary condition, and that is not enough to reach the NPT boundary at
$d=7$.

## What remains open

The obstruction concerns the local maps $C$, not the Werner states. A state has many
factorisations $C(|u\rangle\langle u|)$ with $C=L\otimes M$: a completely positive map can be moved
from Alice's input to Bob's without changing the state. Only the covariant factorisation and its
two diagonal deformations were examined. A search over less symmetric factorisations can use the
reverse-block condition as a screen before any semidefinite program for $Q$ is solved. At
$d=7$ the violation is small ($3\times10^{-3}$ in the normalisation above), which makes that the
natural first target.
