# The qutrit Werner endpoint and a local-map obstruction

Let $F$ interchange two copies of $\mathbb C^3$, let $u=\sum_{i=0}^2|ii\rangle$, and put $W=2I-|u\rangle\langle u|$. The partial transpose of $\rho=(2I-F)/15$ is $W/15$. The qutrit Werner conjecture of Dür, Cirac, Lewenstein and Bruß reduces to
$$
\langle\psi,W^{\otimes n}\psi\rangle\ge0
\qquad(n\ge1,\quad \operatorname{SR}_{A^n:B^n}(\psi)\le2).
$$
Indeed, mixing $\rho$ with the maximally mixed state by local operations gives every Werner state between this endpoint and the PPT boundary. The following arguments give an obstruction to one proposed proof and a necessary condition on a counterexample. The all-copy inequality remains unresolved here. [Dür et al., §§II, VI](https://arxiv.org/pdf/quant-ph/9910022)

## A necessary inequality for the auxiliary map

For $0<x\le1$ and $y\ge0$ consider the completely positive maps
$$
L(X)=\operatorname{Tr}(X)I-xX^T,\qquad
M(X)=y\operatorname{Tr}(X)I+X,\qquad C=L\otimes M.
$$
These are the local maps in the positive-coefficient Werner construction, up to scalar factors. Write $E_{vw}=|v\rangle\langle w|$ and $T$ for transposition on the full input. The eight-dimensional proof uses an auxiliary map $S$ such that $C\pm S$ and $S\circ T$ are completely positive and $S(E_{uu})=C(E_{uu})$. [Faisal](https://arxiv.org/abs/2611.34921)

**Proposition.** If $C(E_{uu})$ has negative partial transpose, no such $S$ exists in this qutrit family.

**Proof.** Write $C(E_{uu})=A I-xF$, where $A=1+(3-x)y$. Negative partial transpose is equivalent to $A<3x$. Since the completely positive map $C-S$ annihilates $E_{uu}$, each of its Kraus operators kills $u$. Hence $C$ and $S$ agree on $E_{uz}$ and $E_{zu}$ for every $z$.

Take $z=|01\rangle$. Both $u$ and $z$ are real. Applying $S\circ T$ to the entries of the positive Gram block of $(u,z)$ and adding $(C-S)(E_{zz})$ in the lower diagonal block gives
$$
\begin{pmatrix}C(E_{uu})&C(E_{zu})\\ C(E_{uz})&C(E_{zz})\end{pmatrix}\succeq0.
$$
Compress the upper summand to $|11\rangle$ and the lower summand to $(|10\rangle,|01\rangle)$. The resulting matrix must satisfy
$$
H=\begin{pmatrix}
 A-x&1&-x(1+y)\\
 1&y&0\\
 -x(1+y)&0&(1-x)(1+y)
\end{pmatrix}\succeq0.
$$
Indeed, $C(E_{zz})=(I-x|0\rangle\langle0|)\otimes(yI+|1\rangle\langle1|)$ and
$C(E_{uz})|11\rangle=|10\rangle-x(1+y)|01\rangle$.

At the desired endpoint $A=2x$. Its leading minor requires $xy\ge1$, whereas $y=(2x-1)/(3-x)\le1/2$. This already rules out the endpoint.

For the whole NPT interval, $y=0$ is excluded by the same minor. Suppose $y>0$. The inequality $A<3x$ implies $x_0<x\le1$ for $x_0=(1+3y)/(3+y)$. Expanding the determinant gives
$$
\det H=(1+y)p(x,y),\qquad
p(x,y)=(3-4x)y^2+(1-2x)y+x-1.
$$
For fixed $y$, this is affine in $x$. At the two ends,
$$
p(1,y)=-y(1+y)<0,\qquad
(3+y)p(x_0,y)=-9y^3+3y-2\le-4/3.
$$
The last cubic attains its maximum on $[0,\infty)$ at $y=1/3$. Thus $\det H<0$, a contradiction. The obstruction allows arbitrary auxiliary maps $S$ for this fixed form of $C$ and this input $u$. Other local factorizations or input dimensions require a separate argument.

## Removing a copy with local support of dimension two

Suppose $W^{\otimes(n-1)}$ is nonnegative on vectors of Schmidt rank at most two. Then the same holds for any such vector $\psi$ on $n$ copies for which one individual Alice or Bob qutrit has reduced density matrix of rank at most two.

To see this, take a rank-two projection $P$ containing the support on the qutrit in question, say Alice's. Compress $W$ on that factor. On $P\mathbb C^3\otimes\mathbb C^3$ the compression is $2I-|v\rangle\langle v|$, where $v=(P\otimes I)u$ and $\|v\|^2=2$. It is positive. Its partial transpose on Bob is the compression of $2I-F$, also positive. Hence the compressed operator is separable by the $2\times3$ PPT criterion. Expand it as a sum of positive multiples of projectors onto product vectors $a_j\otimes b_j$. Each local contraction $\psi_j=(\langle a_j|\otimes\langle b_j|)\psi$ on this copy has Schmidt rank at most two across the remaining parties. The desired expectation is a positive linear combination of $\langle\psi_j,W^{\otimes(n-1)}\psi_j\rangle$. Exchange Alice and Bob for the other case. [Horodecki, Horodecki and Horodecki](https://arxiv.org/abs/quant-ph/9605038)

Consequently, at the smallest copy number admitting a counterexample, every individual qutrit of every negative Schmidt-rank-two witness has local rank three. The one-copy case follows from $|\langle u,\psi\rangle|^2\le2\|\psi\|^2$ for Schmidt rank at most two. The full-local-rank case is the outstanding one in this reduction.
