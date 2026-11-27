# Finite-copy undistillability

For the concrete state $\rho=(23I-3F)/1448$ on $\mathbb C^8\otimes\mathbb C^8$,
`NPTEnt.Main.isFiniteCopyUndistillable_rho` proves the standard
Dür–Cirac–Lewenstein–Bruß finite-copy criterion. Explicitly, for every $N>0$
and every vector $\psi$ of Schmidt rank at most two,
$$
\langle\psi|(\rho^{\otimes N})^{T_A}|\psi\rangle\ge0.
$$
The Alice and Bob versions are
`partialTransposeFst_bipartiteCopies_rho_schmidtRankLE_two_nonneg` and
`partialTransposeBob_bipartiteCopies_rho_schmidtRankLE_two_nonneg`. Copies use
party-major coordinates. For this real Werner state, the two partial transposes
are equal entrywise, as proved by
`partialTransposeBob_bipartiteCopies_rho_eq_fst`. This equality is specific to
the state, not an identification of Alice and Bob transpose for arbitrary matrices.
The combined NPT endpoint is `NPTEnt.Main.npt_finiteCopyUndistillable`.

## Argument

A negative Schmidt-rank-two partial-transpose witness yields a two-qubit NPT
output under local filters. A further explicit local filter produces a
positive-trace output with normalized Bell overlap $f>1/2$. A finite isotropic
twirl then produces a positive multiple of
$$
\rho_f=f\Phi_2+\frac{1-f}{3}(I-\Phi_2).
$$
The twirl is implemented by twelve product Kraus operators; its algebraic
normalization is twelve times the averaged twirl. Bilateral even-parity
filtering followed by twirling gives the recurrence
$$
g(f)=\frac{10f^2-2f+1}{8f^2-4f+5}.
$$
For $1/2<f<1$, the odds $(f-1/2)/(1-f)$ grow by at least $6/5$ at every step.
Consequently finitely many rounds, using $2^n$ copies, exceed any fixed
threshold $c<1$ while retaining strictly positive output trace. Tensoring
the initial filters and explicitly regrouping copies gives a finite
product-Kraus map on copies of the original state.

This contradicts the proved uniform cap $c=(1+\sqrt2)/4<1$. The argument uses
the homogeneous cap for all finite product-Kraus operations; it does not
assume that an unscaled algebraic Kraus sum is trace-nonincreasing. No
equivalence between finite-copy distillability and positive asymptotic
distillation rate is used. The previously established zero finite-round
LOCC rate remains a separate theorem. Infinite-round LOCC and its closure
are not claimed.

## Ownership and verification scope

QICLean supplies the standard finite-copy definitions, Schmidt/filter criterion,
and separable-operation tensor and copy-regrouping laws. The explicit
two-qubit construction, twirl, recurrence and cap bridge are in
`NPTEnt.TwoQubitDistillability`, `NPTEnt.QubitRecurrence` and
`NPTEnt.RecurrenceAmplification`, preserving the completed sources’ attribution.
The concrete instance remains in `NPTEnt.Main`. Python certificate checks
are independent exact cross-checks, not proof assumptions. The Gemini 4-authored
blueprint now records the local-filter criterion, finite recurrence amplification,
and the uniform-cap obstruction as separate dependency
nodes leading to the concrete finite-copy endpoint.
