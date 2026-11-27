# Exploration of Other Candidate NPT Examples in the arXiv:2611.34921 Framework

## Epistemic status and assumptions

This note reports an exploratory mathematical and computational study of other
explicit state/map/certificate examples compatible with the framework of
`Papers/2611.34921/source/paper.tex`. We strictly distinguish three levels of
assurance:

1. **Algebraic arguments** (Section 1 and the conditional perturbation proof inspected; general representation claims in Section 2 preliminary, not proved here): general parameter
   relations for $U(d)$-covariant local maps $(L, M)$, twirling reduction to
   the 24-dimensional walled Brauer algebra $B_{3,1}(d)$, and an
   **Open-Neighborhood Perturbation Theorem** showing that the boundary kernel
   condition $(J - Q)(|u\rangle \otimes I) = 0$ does *not* obstruct local
   (including non-Werner) perturbations when $J + Q \succ 0$,
   $Q^{\Gamma_{\mathrm{in}}} \succ 0$, and
   $\ker(J - Q) = \operatorname{im}(|u\rangle \otimes I)$.
2. **Exact finite-certificate computations** (verified in exact rational
   arithmetic by `scripts/check_additional_certificates.py`): full-basis checks
   (no floating-point positivity decisions, no random sampling, no external solver) of
   Hermiticity, complete positivity of $L$ and $M$, exact output state
   $R = (L \otimes M)(|u\rangle\langle u|)$, NPT witness, full entrywise
   $L \operatorname{diag}(d) L^T$ PSD factorizations of $J + Q$, $J - Q$, and
   $Q^{\Gamma_{\mathrm{in}}}$, and all $d^6$ entries of
   $(J - Q)(|u\rangle \otimes I) = 0$ for **three genuinely new candidate NPT
   states**.
3. **Unreproduced exploratory numerical SDP reports** (from Wolfram `SemidefiniteOptimization` on the
   exact 5-block symmetry reduction): a possible sampled transition near $d=8$ within
   the $U(d)$-covariant $(L, M)$ ansatz (reported samples at $d\le7$ miss the NPT
   threshold $d\alpha < -1$), the approximate optimal Werner parameter
   $\alpha_{\min}(d)$ for $d = 8, 9, \dots$, and the large-$d$ scaling
   $\alpha_{\min}(d) \approx -0.43/\sqrt{d}$.

**No bound-entanglement claim is made here.** Computational certificate checks
are *not* Lean proofs, and they do *not* by themselves prove bound entanglement.
In the paper's architecture (see `docs/formalization-roadmap.md`), passing
from a single-copy finite certificate $(L, M, Q)$ to $E_D(\rho) = 0$ requires
both:

- **Track B (still unformalized in Lean):** the single-copy certificate
  conditions imply $J^{\otimes n} - Q^{\otimes n} \succeq 0$, reverse block
  positivity $\Omega_{v,w} \succeq 0$, the coherence bound
  $K \le (p_{00} p_{01} p_{10} p_{11})^{1/4}$, and the all-copy separable-map
  Bell-overlap cap $(1 + \sqrt{2})/4$.
- **Track C (still unformalized in Lean):** the operational inclusion of
  finite-round LOCC in separable operations and the uniform Bell-overlap cap
  criterion for $E_D(\rho) = 0$.

All three are independently checked NPT states with exact finite certificates. Only their proposed bound-entangled status is conditional on all-copy and operational implications.

---

## 1. General parameter relations for the $(L, M)$ Werner ansatz

On $\mathbb{C}^d \otimes \mathbb{C}^d$ with $|u\rangle = \sum_{i=1}^d |i,i\rangle$,
consider $U(d)$-covariant local linear maps of the paper's form:
$$
L(X) = a \operatorname{Tr}(X)\,I - b\,X^T, \qquad
M(X) = c \operatorname{Tr}(X)\,I + e\,X.
$$
Their Choi matrices are $J_L = a I - b\,\mathrm{SWAP}$ and
$J_M = c I + e\,|u\rangle\langle u|$, so complete positivity holds if and only if
$$
a \ge |b|, \qquad c \ge 0, \qquad c + d e \ge 0.
$$
Applying $\mathcal{C} = L \otimes M$ to $|u\rangle\langle u| = \sum_{i,j} |i\rangle\langle j| \otimes |i\rangle\langle j|$ yields
$$
\mathcal{C}(|u\rangle\langle u|) = (d a c + a e - b c)\,I - b e\,\mathrm{SWAP}.
$$
Hence $\mathcal{C}(|u\rangle\langle u|) \propto I + \alpha\,\mathrm{SWAP} \propto \rho(d, \alpha)$ with Werner parameter
$$
\alpha = -\frac{b e}{d a c + a e - b c}.
$$
Since $(I + \alpha\,\mathrm{SWAP})^\Gamma = I + \alpha\,|u\rangle\langle u|$ has
eigenvalues $1$ and $1 + d\alpha$, the state $\rho(d, \alpha)$ is NPT if and
only if $\alpha < -1/d$ (and PSD whenever $|\alpha| \le 1$).

### Sign and map-type classification

1. **Positive sign choice ($b > 0, e > 0$):** Since positive scaling of $L$ or
   $M$ rescales $J$ and $Q$ uniformly, set $x = a/b \ge 1$ and $y = c/e \ge 0$.
   Then
   $$
   \alpha = -\frac{1}{d x y + x - y},
   $$
   and the NPT condition $\alpha < -1/d$ is equivalent to
   $$
   d x y + x - y < d \iff y < \frac{d - x}{d x - 1}.
   $$
   For the paper's choice $(d, x, y) = (8, 5/3, 18/37)$, the PPT boundary is
   $(8 - 5/3)/(40/3 - 1) = 19/37$, so $y = 18/37$ lies just inside the NPT
   region ($\alpha = -3/23 \approx -0.130435$, $8\alpha = -24/23 \approx -1.043478$).
2. **Opposite sign choice ($b < 0, e < 0$):** Setting $x = a/|b| \ge 1$ and
   $y = c/|e| \ge d$ (from $c + de \ge 0$) gives
   $dxy - x + y = y(dx+1) - x \ge d^2 x + d - x > d$ for all $d \ge 2, x \ge 1$,
   so $\alpha = -1/(dxy - x + y) > -1/d$ is **always PPT**.
3. **Both maps using $X$ or both using $X^T$:** Then
   $\mathcal{C}(|u\rangle\langle u|) = (dac + ae + bc)I + be |u\rangle\langle u|$
   is an **isotropic state**. Projecting any NPT isotropic state onto a
   two-dimensional local subspace $\operatorname{span}\{|0\rangle, |1\rangle\}$
   immediately yields an NPT two-qubit state, so every NPT isotropic state is
   1-copy 2-distillable and never bound entangled.
4. **Swapping $L \leftrightarrow M$:** Exchanges Alice and Bob (a local symmetry).

Thus, up to Alice/Bob exchange and positive rescaling, the $(x, y)$ family with
$x \ge 1, y \ge 0$ is the unique $U(d)$-covariant pair producing NPT Werner
states.

---

## 2. Proposed symmetry reduction and exploratory dimension search

**Preliminary and not independently reproduced:** no explicit general five-block matrices, intertwiners, positive inner-product metrics, partial-transpose action, or proofs of the low-dimensional quotients are exhibited here. Dimension counts do not establish the claimed PSD/kernel equivalences. The Python checker constructs full sparse matrices at $d=8,9$ and does not implement or validate this representation reduction.

No Wolfram source, solver logs, tolerances, or primal/dual certificates are saved in the assigned files. The following solver and representation claims are retained as exploratory reports, not independently verified general results.

For any $(d, x, y)$, the Choi matrix
$J = (x I_{13} - F_{13})(y I_{24} + P_{24})$ commutes with
$\bar U \otimes U \otimes \bar U \otimes \bar U$ for all $U \in U(d)$, while
$|u\rangle_{12}$ is invariant under $\bar U \otimes U$. By Haar twirling over
$U(d)$ and real symmetrization, a certificate $Q$ satisfying the four conditions
of Lemma 3 of the paper exists **if and only if** one exists in the
real-symmetric subspace of the 24-dimensional commutant
$\operatorname{span}_{\mathbb{R}}\{B_\pi : \pi \in S_4\}$ (the walled Brauer
algebra $B_{3,1}(d)$, where $B_\pi = U_\pi^{\Gamma_2}$).

- Hermiticity ($B_\pi^\dagger = B_{\pi^{-1}}$) reduces the 24 coefficients to
  17 real parameters (10 involutions + 7 inverse pairs).
- For $d \ge 4$, $B_{3,1}(d)$ decomposes into **five** irreducible blocks of
  sizes $1, 2, 1, 3, 3$ (sum of squares $1 + 4 + 1 + 9 + 9 = 24$): the three
  $S_3$-irreps on $\{1, 3, 4\}$ (independent of $d$) and the two $3 \times 3$
  blocks $S^2$ and $\Lambda^2$ (linear in $d$). For $d = 3$, the sign block
  vanishes; for $d = 2$, both $(2,1)$ and sign blocks vanish and $\Lambda^2$
  drops to size $2 \times 2$.
- The kernel condition $(J - Q)(|u\rangle \otimes I) = 0$ is equivalent to
  vanishing of the first row/column of the $S^2$ and $\Lambda^2$ blocks of
  $J - Q$ (6 linear equations, leaving 11 free parameters for $d \ge 3$).
- For fixed $(d, x)$, $J$ is affine-linear in $y$, and minimizing $\alpha$ is
  equivalent to minimizing $y$. Thus finding the most negative certifiable
  $\alpha(d, x)$ is a tiny 12-variable convex SDP.

### Numerical SDP sweep across dimensions (numerical evidence, not a proof)

Solving this exact 5-block SDP in Wolfram `SemidefiniteOptimization` across
$d = 2, \dots, 20$ (scanning $x \in [1, 4]$) gives:

| $d$ | PPT threshold $-1/d$ | Best numerical $\alpha_{\min}(d)$ | Best $d\,\alpha_{\min}(d)$ | Crosses NPT ($d\alpha < -1$)? |
|---:|---:|---:|---:|:---:|
| 2 | $-0.500000$ | $-0.200000$ | $-0.400000$ | No |
| 3 | $-0.333333$ | $-0.181682$ | $-0.545046$ | No |
| 4 | $-0.250000$ | $-0.169752$ | $-0.679007$ | No |
| 5 | $-0.200000$ | $-0.158390$ | $-0.791950$ | No |
| 6 | $-0.166667$ | $-0.148619$ | $-0.891714$ | No |
| 7 | $-0.142857$ | $-0.140026$ (near $x \approx 1.62$) | $-0.980181$ | **No** (misses $-1$ by $\approx 0.020$) |
| **8** | $-0.125000$ | **$-0.132594$** (near $x \approx 1.62$) | **$-1.060754$** | **Yes** |
| **9** | $-0.111111$ | **$-0.126241$** (near $x \approx 1.60$) | **$-1.136173$** | **Yes** |
| 10 | $-0.100000$ | $-0.120781$ | $-1.207814$ | Yes |
| 12 | $-0.083333$ | $-0.111743$ | $-1.340916$ | Yes |
| 16 | $-0.062500$ | $-0.098559$ | $-1.576943$ | Yes |
| 20 | $-0.050000$ | $-0.089233$ | $-1.784667$ | Yes |

At larger $d$ (evaluated at $x = 8/5$):
- $d = 50$: $\alpha \approx -0.05852$, $\sqrt{d}\,\alpha \approx -0.4138$;
- $d = 100$: $\alpha \approx -0.04210$, $\sqrt{d}\,\alpha \approx -0.4210$;
- $d = 500$: $\alpha \approx -0.01925$, $\sqrt{d}\,\alpha \approx -0.4304$;
- $d = 1000$: $\alpha \approx -0.01371$, $\sqrt{d}\,\alpha \approx -0.4336$.

**Qualified interpretation:**
1. The samples suggest a transition near $d=8$, not a sharp minimum dimension theorem. Scanning $x\in[1,4]$ proves neither infeasibility throughout that interval nor global infeasibility over all $x\ge1$ for $d\le7$.
2. Exact Example 1 independently establishes $\alpha=-75/569$, deeper into NPT than the baseline. The reported optimum near $-0.13259$ is not independently certified.
3. The larger-$d$ samples suggest a possible $d^{-1/2}$ trend but prove no asymptotic law, optimal constant, or existence for every $d\ge8$.

## 3. Conditional perturbation argument

Under strict local Choi positivity, strict positivity of $J+Q,Q^{\Gamma_{\mathrm{in}}}$, exact kernel $\ker(J-Q)=\operatorname{im}(|u\rangle\otimes I)$, and NPT output, set $\Pi=|u\rangle\langle u|_{12}\otimes I_{34}/d$. For a small signed increment $D=J'-J$, take $Q'=Q+\Pi D+D\Pi-\Pi D\Pi$. Then $J'-Q'=(J-Q)+(I-\Pi)D(I-\Pi)$ preserves the kernel. The positive gap on its complement and the other strict inequalities persist by finite-dimensional continuity, as does NPT. This proves existence of a neighborhood, not a radius. A positive rank-one addition to $M$ yields a mixture with a separable operator after normalization; a small negative addition can remain CP and avoid that construction.

## 4. Three exact-checked candidates

All formulas use $\rho(d,\alpha)=(I+\alpha F)/(d^2+d\alpha)$, with $F$ SWAP.

| Candidate | Maps | State and negativity |
|---|---|---|
| 1 ($d=8$) | $L=5\operatorname{Tr}(\cdot)I-3T$, $M=12\operatorname{Tr}(\cdot)I+25\operatorname{id}$ | $\rho(8,-75/569)$; $31/35816$ |
| 2 ($d=9$) | $L=8\operatorname{Tr}(\cdot)I-5T$, $M=12\operatorname{Tr}(\cdot)I+25\operatorname{id}$ | $\rho(9,-125/1004)$; $121/80199$ |
| 3 ($d=8$) | $L=5\operatorname{Tr}(\cdot)I-3T$, $M=18\operatorname{Tr}(\cdot)I+37\operatorname{id}-\langle0|\cdot|0\rangle P_0/8$ | non-Werner; $\mathcal N\ge395/571428$ |

Here $P_0=|0\rangle\langle0|$. All exceed baseline negativity $1/1448$, excluding deterministic one-copy LOCC/TP separable conversion from the baseline, NOT stochastic postselection. Candidate 1 is deeper NPT at the same dimension (the baseline is its depolarization). Candidate 2 has higher dimension. Candidate 3 is
$\rho_3=\frac{296(23I-3F)-(5I-3P_0)\otimes P_0}{37\cdot11583}.$
Its Bob marginal eigenvalues are $1447/11583$ once and $1448/11583$ seven times, excluding LU equivalence to Werner states. The witness is $\langle u|\rho_3^\Gamma|u\rangle/8=-395/571428$.

Certificate coefficients in the ordering of Section 6, for $Q=\sum m_\pi B_\pi/s$:

Candidate 1, $s=320$:

    52, -1, -4, -4, -4, 0, 2064, 268, -1516, 673, -2816, 4152, -1516, -2816, 5116, -4404, 2936, -4504, 673, 4152, -4404, 11288, -4504, -976

Candidate 2, $s=40$:

    23, 0, 0, 0, 0, 0, 373, 46, -285, 115, -529, 745, -285, -529, 976, -842, 603, -811, 115, 745, -842, 2106, -811, -193

Baseline $Q_{\rm paper}$, $s=40$:

    88, 77, 16, 24, 24, 16, 380, 40, -288, 128, -525, 760, -288, -525, 884, -876, 612, -756, 128, 760, -876, 2060, -756, -172

For candidate 3 let $H=(5I_{13}-3F_{13})\otimes|0,0\rangle\langle0,0|_{24}$ and take $Q_3=Q_{\rm paper}-(\Pi H+H\Pi-\Pi H\Pi)/8$. The signed Choi increment is $-H/8$. CP holds since $J_{M'}\succeq(18-1/8)I$. The exact checker verifies the finite size choice separately from continuity. Diagonal phase partitions after input partial transpose move the positive factor from factor 2 to factor 1; they are not literally the same indexed partition. Each candidate-3 matrix has 708 connected components.

## 5. Reproduction

Run: `python3 -B scripts/check_additional_certificates.py` (Python 3.10+ standard library). Expected final line: `ALL 3 NEW EXAMPLES PASS FULL-BASIS EXACT RATIONAL CHECKS (computational certificate check only; not a Lean proof)`.

## 6. Independent review (2026-11-27)

**PASS: all three exact finite certificates.** The unmodified standard-library script exited successfully in 38.5 seconds (10.36, 17.76, 10.32 seconds per candidate). Reproduced ranks of $(J+Q,J-Q,Q^{\Gamma_{\mathrm{in}}})$ are $(4096,4032,4096)$, $(6561,6480,6561)$, and $(4096,4032,4096)$. All 262144, 531441, and 262144 kernel entries respectively vanish. State output extraction, normalization, Werner parameters, Example 3 marginal and negative witnesses agree with the report. Negativities are exactly $31/35816$, $121/80199$, and a lower bound $395/571428$ respectively; the last is not an exact negativity evaluation. Full componentwise rational $LDL^T$ reconstruction and absence of cross-component entries establish PSD, not sampling. CP uses analytic Choi bounds. Floating point is used only for printed decimals/timing. No demonstrated script bug was found; no script changes were made. Python 3.10+ is needed for zip(strict=True).

**Ordering and provenance:** factors 1,2 are Alice/Bob input; 3,4 are Alice/Bob output. Tuples are lexicographic in $\{0,\ldots,d-1\}^4$. Certificate coefficients follow Python itertools.permutations(range(4)) lexicographic order, with $U_\pi|c_0,c_1,c_2,c_3\rangle=|c_{\pi(0)},c_{\pi(1)},c_{\pi(2)},c_{\pi(3)}\rangle$. Here $B_\pi=U_\pi^{\Gamma_2}$ transposes one-based factor 2, and input partial transpose acts on factors 1,2. Both $J,Q$ are scaled by the same positive denominator in the checker. Example 3 uses the explicit baseline coefficient tuple stored in the script, not a solver call. “New” means alternatives to the paper baseline, not verified literature priority.

**Normalization and formulas:** local preparation maps are CP but not asserted to be TP operational channels. Outputs are normalized by their trace; $\rho(d,\alpha)=(I+\alpha F)/(d^2+d\alpha)$. Zero-output parameters are excluded and the sign analysis assumes $d\ge2$. The isotropic formula in Section 1 uses signed coefficients $+b,+e$; if retaining the earlier $-b$ convention, replace $b$ by $-b$ throughout that formula. The classification is within the trace/identity/transpose ansatz, not arbitrary CP map pairs. Negativity means $(\|\rho^\Gamma\|_1-1)/2$. Its deterministic monotonicity holds also across different dimensions, but a successful postselected branch may increase it.

**Perturbation:** the projector-correction proof is valid in fixed finite dimension under its strict Choi/PSD gaps and exact-kernel hypotheses. It supplies some sufficiently small neighborhood, not a quantitative radius or arbitrary finite perturbations. The $-1/8$ choice is justified separately by exact computation, not continuity alone. In Example 3, $\Delta J$ denotes the positive direction matrix, so the actual signed increment is $-\Delta J/8$, unlike Section 3’s notation. Strict negativity increase is checked for this direction and this choice, not asserted for all perturbations. Baseline ranks quoted from another note were not separately rerun here.

**Not independently reproduced:** the general representation reduction and Wolfram sweeps establish no sharp threshold, global infeasibility, certified optimum or asymptotic scaling in this review.

**No bound-entanglement verdict:** no tensor power beyond one, Bell-overlap cap, or operational distillation criterion is checked by the script. Algebraically $J\pm Q\succeq0$ does imply $J^{\otimes n}-Q^{\otimes n}\succeq0$ by expanding products of $J+Q,J-Q$ with an odd number of minus factors. This alone does not supply reverse block positivity, the coherence bound, or the operational implication. Track B/C arguments and their hypotheses need independent validation; “unformalized” does not certify mathematical correctness. The three concrete exact-checked candidates remain useful independently of any bound-entanglement claim.