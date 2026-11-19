::: {.lead}
A proof in combinatorial commutative algebra, developed from squarefree
monomials to links and local cohomology, with the checked Lean code beside
the mathematics.
:::

::: {.link-row}
[Read the quotient basis](#basis) · [Read the quotient grading](#grading) ·
[Read the augmentation result](#augmentation) · [Read coordinate primes](#facet-primes) ·
[Read the dimension theorem](#dimension) ·
[Read the localized grading](#localized-grading) ·
[Read the finite Čech complex](#cech-complex) ·
[Read the Čech degree decomposition](#cech-termwise-decomposition) ·
[Explore the blueprint](blueprint.html) ·
[Browse the Lean source](#full-source)
:::

::: {.milestone}
**Current milestone — checked in Lean.** The actual variable-product
localizations carry an integer grading. Each admissible degree has a
Laurent monomial basis vector, and the other components are zero.
The transition maps preserve degrees and send surviving basis vectors
to their counterparts. The finite extended Čech cochains form a genuine
cochain complex, and its differential has the checked signed insertion
formula on monomial coordinate cochains. Each cochain module is the internal
direct sum of its fine-degree submodules.
:::

## The target {#target}

Let $k$ be **any field** and $K$ a simplicial complex on a finite ambient
vertex set $V$, containing the empty face. Its face ring is

$$ k[K]=k[x_v:v\in V]/I_K,\qquad
I_K=\left(\prod_{v\in F}x_v:F\notin K\right). $$

Reisner’s criterion says that this ring is Cohen–Macaulay if and only if

$$ \widetilde H_i(\operatorname{lk}_K\sigma;k)=0
\quad\text{for every }\sigma\in K\text{ and }i<\dim(\operatorname{lk}_K\sigma). $$

The empty face is included. Cohen–Macaulayness has its usual **algebraic**
meaning: the Noetherian ring’s localizations have depth equal to Krull
dimension. It is not defined using the homology condition above.
The target follows [Panov, Theorem 2.5](https://arxiv.org/html/math/0506526v3).

<details class="conventions"><summary>Conventions: empty faces, ghost vertices, and degree −1</summary>

The faces of $K$ are finite vertex sets closed under taking subsets.
A vertex of the ambient type need not occur in any face: if $\{v\}\notin K$,
it is a *ghost vertex*, and $x_v\in I_K$.
The complex $\{\varnothing\}$ is allowed; the void collection is excluded.

The link consists of the faces $\tau$ disjoint from $\sigma$ whose union
with $\sigma$ is a face. In particular the link of the empty face is $K$.
Dimension is the maximum face cardinality minus one, so
$\dim\{\varnothing\}=-1$. Reduced chains are augmented in degree $-1$:
$\widetilde H_{-1}(\{\varnothing\};k)=k$, and all groups below $-1$ vanish.

</details>

## Polynomial membership is termwise {#membership}

Write an exponent vector as $\alpha:V\to_0\mathbb N$, a function with
finitely many nonzero values. Its support is a set of vertices:

$$ \operatorname{supp}\alpha=\{v:\alpha(v)\ne0\}. $$

The earlier checked monomial result is the foundation:

$$ \boxed{x^\alpha\in I_K\quad\Longleftrightarrow\quad
\operatorname{supp}\alpha\notin K.} $$

The polynomial theorem applies the general monomial-ideal API to every
exponent in `f.support`:

::: {.theorem-box}
$$ f\in I_K\quad\Longleftrightarrow\quad
\forall\alpha\in\operatorname{support}(f),\;\operatorname{supp}(\alpha)\notin K. $$

<span class="checked-badge">Checked in Lean</span>
[Polynomial membership](#lean-L@@LINE:mem_stanleyReisnerIdeal_iff@@) · [Monomial foundation](#lean-L@@LINE:monomial_mem_stanleyReisnerIdeal_iff@@) ·
[Blueprint node](blueprint.html#thm:membership)
:::

The exact polynomial-membership declaration is shown here:

<!-- LEAN:polynomial-membership -->

For the boundary of a triangle on $\{a,b,c\}$, every proper subset is a
face and $I_K=(x_ax_bx_c)$:

| Monomial | Vertex support | In the ideal? |
|:--|:--|:--|
| $x_a^2x_bx_c^3$ | $\{a,b,c\}$, a nonface | Yes |
| $x_ax_b^2$ | $\{a,b\}$, a face | No |
| $1=x^0$ | $\varnothing$, a face | No |

Changing positive exponents does not change the answer. The theorem works
over any **nontrivial commutative semiring**, without requiring $V$ to be
finite. Polynomial membership needs only a commutative semiring, including
the trivial one; the actual quotient ring is defined for commutative-ring
coefficients.

## The standard monomials form a quotient basis {#basis}

Define the standard exponent set
$$ E_K=\{\alpha:V\to_0\mathbb N:\operatorname{supp}(\alpha)\in K\}. $$
Its elements index the monomials that survive in the face ring. The checked
Lean declaration `faceRingBasis` is a `Module.Basis` of the actual quotient
`K.FaceRing k`, not merely a spanning family. Its value formula is

$$ b_\alpha=\operatorname{mk}_{I_K}(x^\alpha),\qquad \alpha\in E_K. $$

[View the basis in Lean](#lean-L@@LINE:faceRingBasis@@) ·
[Exact vector formula](#lean-L@@LINE:faceRingBasis_apply@@) ·
[Blueprint node](blueprint.html#prop:basis)

The proof has three steps. First, termwise polynomial membership identifies
the ideal, as a coefficient submodule, with polynomials supported on the
complementary exponent set $E_K^c$. Second, mathlib’s monomial basis of the
polynomial ring splits into complementary spans indexed by $E_K^c$ and
$E_K$. The ideal and the face-supported submodule are therefore
complementary. Finally, the quotient by the first summand is linearly
equivalent to the second summand; transport its restricted monomial basis
through the inverse of this quotient equivalence. The exact value is checked by
`faceRingBasis_apply`.

This works for any ambient type and any commutative coefficient ring. The
scalar map into the quotient is injective for every such ring. If the
coefficient ring is nontrivial, the zero exponent belongs to $E_K$ because
its support is the empty face, so $1$ survives even for
$K=\{\varnothing\}$ and ghost vertices; the quotient is then nontrivial.
The target theorem specializes to fields.

<details><summary>Checked basis construction and exact monomial value</summary>

<!-- LEAN:basis -->

</details>

<details><summary>Checked scalar injectivity and nontriviality</summary>

<!-- LEAN:consequences -->

</details>

## Weighted homogeneity of the polynomial ideal {#homogeneity}

Let $R$ be a commutative semiring, $M$ any additive commutative monoid, and
assign a weight $w(v)\in M$ to every variable. The weighted degree of an
exponent is
$$ |\alpha|_w=\sum_v\alpha(v)w(v). $$
The polynomial projection $\pi_d$ keeps exactly the terms of weighted
degree $d$. The checked result says that the existing generator-defined
Stanley–Reisner ideal is homogeneous for every such weight:

::: {.theorem-box}
$$ p\in I_K\quad\Longrightarrow\quad\pi_d(p)\in I_K\qquad(d\in M). $$

<span class="checked-badge">Checked in Lean</span>
[Ideal homogeneity](#lean-L@@LINE:stanleyReisnerIdeal_isHomogeneous@@) ·
[Component preservation](#lean-L@@LINE:weightedHomogeneousComponent_mem_stanleyReisnerIdeal@@) ·
[Blueprint node](blueprint.html#lem:homogeneous)
:::

The proof works directly with the actual ideal span. Every monomial
generator is homogeneous in its exponent's weighted degree; mathlib's
`Ideal.homogeneous_span` then proves the whole span homogeneous. The
weighted component theorem gives the displayed preservation result. Since
weights take values only in an additive commutative monoid, no order,
cancellation, nonzero weight, finite ambient variable set, or nontrivial
coefficient hypothesis is needed. Different component degrees can combine
to the same output degree after multiplying by a generator, and the
homogeneous-span API accounts for all such contributions.

For a small example, give $x_a$ weight $2$ and $x_b$ weight $0$ in
$\mathbb N$. If $\{a,b\}$ is a nonface, its generator $x_ax_b$ has
weighted degree $2$. A multiplier term $x_a^m x_b^n$ contributes degree
$2m$, so projection to degree $d$ keeps precisely the multiplier terms with
$2m+2=d$; multiplying those terms by $x_ax_b$ stays in the ideal. A zero
weight simply means that changes to that exponent do not change the degree.

Two checked identities recover familiar gradings on the polynomial ring.
The fine weight $w(v)=e_v$, the finitely supported unit vector at $v$,
satisfies $|\alpha|_w=\alpha$. Constant unit weights in $\mathbb N$ give
$|\alpha|_w=\sum_v\alpha(v)$, the usual total degree:

<!-- LEAN:homogeneous -->

<div class="notice"><strong>Scope.</strong> This lemma proves polynomial
ideal homogeneity for arbitrary weights over commutative semirings. The
quotient-level construction and degree-zero result are handled separately
below for commutative-ring coefficients.</div>

## Fine and total gradings on the actual quotient {#grading}

Now let $R$ be a commutative ring and keep the actual face ring
$A=R[x_v:v\in V]/I_K$. Its checked standard monomial basis is indexed by
the face-supported exponents
$$ J=\{\alpha:V\to_0\mathbb N:\operatorname{supp}(\alpha)\in K\},
\qquad b_\alpha=[x^\alpha]\in A. $$
For any weight $w:V\to M$ into an additive commutative monoid, group these
basis vectors by weighted degree:
$$ B_d=\operatorname{span}_R\{b_\alpha:\alpha\in J,
|\alpha|_w=d\}. $$

Because each basis index lies in exactly one degree fiber, the coordinate
submodules give an internal direct sum of the actual quotient. Each element
has only finitely many nonzero components. This coordinate construction is
also checked to equal the image under the quotient map of the matching
weighted homogeneous submodule of the polynomial ring. Polynomial ideal
homogeneity ensures that the weighted homogeneous projections of polynomial
representatives descend to well-defined projections on the quotient.
Multiplying basis monomials adds their
exponents; if the resulting support is a face the product is its basis
vector, and otherwise the product is zero. Thus component multiplication
adds degrees and these components define a genuine `GradedAlgebra` on $A$.

<span class="checked-badge">Checked in Lean</span>
[General weighted graded algebra](#lean-L@@LINE:weightedFaceRingGradedAlgebra@@) ·
[Blueprint node](blueprint.html#prop:grading)

<details><summary>Coordinate fibers, quotient images, and graded multiplication in Lean</summary>

<!-- LEAN:grading-core -->

</details>

For the fine weight $w(v)=e_v$, the degree identity $|\alpha|_w=\alpha$
makes each component the span of its single monomial class, or zero when
$\operatorname{supp}(\alpha)$ is a nonface. This is a grading indexed by
$V\to_0\mathbb N$; when $V$ is finite it is the usual $\mathbb N^V$
grading. Constant unit weights give the usual total-degree grading. Its
degree-$n$ component is spanned by face-supported monomials whose exponent
sum is $n$, equivalently the supremum of all fine components in that total
degree fiber. Thus total degree is proved as a coarsening of the fine
grading.

<span class="checked-badge">Checked in Lean</span>
[Fine graded algebra](#lean-L@@LINE:faceRingFineGradedAlgebra@@) ·
[Total graded algebra](#lean-L@@LINE:faceRingTotalGradedAlgebra@@) ·
[Fine-to-total coarsening](#lean-L@@LINE:faceRingTotalComponent_eq_iSup_fine@@)

<details><summary>Fine and total component descriptions and coarsening in Lean</summary>

<!-- LEAN:grading-specializations -->

</details>

The zero exponent is the only exponent of total degree zero, and its support
is the empty face. Therefore both degree-zero components are
$R\,1=\operatorname{span}_R\{1\}$. This is a subalgebra of $A$, and the
scalar map restricts to an algebra equivalence
$$ R\simeq_R A_0. $$
The checked value theorem says that this equivalence sends each $r\in R$ to
the actual scalar class $\operatorname{algebraMap}(R,A)(r)$. The argument
also works for a trivial coefficient ring. For $K=\{\varnothing\}$ both
gradings are concentrated in degree zero and the face ring is equivalent to
$R$; for a ghost vertex $v$, the fine component at $e_v$ is zero.

<span class="checked-badge">Checked in Lean</span>
[Degree-zero algebra equivalence](#lean-L@@LINE:faceRingDegreeZeroEquiv@@) ·
[Its value on scalars](#lean-L@@LINE:faceRingDegreeZeroEquiv_apply@@) ·
[Blueprint node](blueprint.html#prop:grading)

<details><summary>Degree-zero components and scalar algebra equivalence in Lean</summary>

<!-- LEAN:degree-zero -->

</details>

## Evaluation at zero, augmentation, and residue algebra {#augmentation}

Let $R$ be any commutative ring, $K$ any augmented complex on an ambient
type $V$, and $A=R[K]$ the existing quotient. The polynomial
constant-coefficient map descends to the augmentation algebra map
$$ \varepsilon:A\longrightarrow_R R,\qquad
\varepsilon([p])=[x^0]p. $$
It is well-defined because no nonface generator has exponent zero: the empty
set is a face. The map fixes scalar classes, so it is surjective, even when
$R$ is the trivial ring.

Define the variable ideal inside this same quotient and define the positive
degree ideal precisely as the ideal generated by all positive-total-degree
homogeneous components:
$$ \mathfrak m=([x_v]:v\in V),\qquad
A_{>0}=\operatorname{Ideal.span}\{a:\exists n>0,\ a\in T_n\}. $$
The checked kernel calculation is
$$ \ker\varepsilon=\mathfrak m=A_{>0}. $$
In the polynomial ring, vanishing constant coefficient is exactly membership
in the ideal generated by the variables. Passing that ideal to the actual
quotient gives $\mathfrak m$. The already-checked polynomial-image theorem
for graded components then identifies the same kernel with the ideal
generated by the positive degree components. This ideal is homogeneous for
the total grading.

<span class="checked-badge">Checked in Lean</span>
[Augmentation map](#lean-L@@LINE:faceRingAugmentation@@) ·
[Kernel and positive-degree ideal](#lean-L@@LINE:faceRingAugmentation_ker@@) ·
[Positive-degree equality](#lean-L@@LINE:faceRingAugmentationIdeal_eq_positive@@) ·
[Homogeneity](#lean-L@@LINE:faceRingAugmentationIdeal_isHomogeneous@@) ·
[Blueprint node](blueprint.html#prop:augmentation)

The first isomorphism theorem identifies the residue algebra with the
coefficient ring itself:
$$ A/\mathfrak m\simeq_R R. $$
The equivalence sends the class of $a\in A$ to $\varepsilon(a)$. For a
general commutative ring $R$, this is a residue algebra, not necessarily a
field. If $R=k$ is a field, the surjective augmentation has maximal kernel,
so $\mathfrak m$ is maximal and the residue field is exactly $k$. This is
the same homogeneous maximal ideal used in the dimension proposition; no
finite-ambient-type hypothesis is needed for maximality.

<span class="checked-badge">Checked in Lean</span>
[Residue algebra equivalence](#lean-L@@LINE:faceRingResidueEquiv@@) ·
[Value on quotient classes](#lean-L@@LINE:faceRingResidueEquiv_mk@@) ·
[Maximality over a field](#lean-L@@LINE:faceRingAugmentationIdeal_isMaximal@@)

If $V$ is finite, the quotient is a finite-type $R$-algebra. If in addition
$R$ is Noetherian, then $A$ is Noetherian. Thus the finite-ambient field
case has the finite-type and Noetherian hypotheses needed by the dimension
argument:

<span class="checked-badge">Checked in Lean</span>
[Finite type](#lean-L@@LINE:faceRing_finiteType@@) ·
[Noetherian under the stated assumptions](#lean-L@@LINE:faceRing_isNoetherianRing@@) ·
[Blueprint node](blueprint.html#prop:augmentation)

Ghost ambient variables cause no change to these statements: a ghost
variable has zero class in $A$, so omitting ghost variables from the
generating set of $\mathfrak m$ gives the same ideal in the same quotient.
If every ambient singleton is a nonface, then $K=\{\varnothing\}$,
$\mathfrak m=\bot$, and the augmentation itself is an algebra equivalence
$A\simeq_R R$. The argument includes an empty ambient type and arbitrarily
many ghost vertices; it does not claim the broader ambient-removal and
homology result in the still-future `prop:ghost`.

<details><summary>Checked augmentation, kernel, finite-type, and edge-case proofs</summary>

<!-- LEAN:augmentation-map -->
<!-- LEAN:augmentation-kernel -->
<!-- LEAN:augmentation-algebra -->
<!-- LEAN:augmentation-edge-cases -->

</details>

## Coordinate quotients and facet primes {#facet-primes}

This checked result supplies the coordinate-prime structure used by the
future face-ring dimension proof. For any finite $F\subseteq V$, define
$$ P_F=(x_v:v\notin F)\subseteq S=R[x_v:v\in V]. $$
The termwise membership criterion holds over any commutative semiring:
$$ p\in P_F\quad\Longleftrightarrow\quad
\forall\alpha\in\operatorname{supp}(p),\;\operatorname{supp}(\alpha)\not\subseteq F. $$
Equivalently, each supported exponent has some variable outside $F$.

<span class="checked-badge">Checked in Lean</span>
[Membership criterion](#lean-L@@LINE:mem_coordinateIdeal_iff@@) ·
[Blueprint node](blueprint.html#prop:facet-primes)

For commutative-ring coefficients, restriction to variables indexed by the
subtype $\{v\in V:v\in F\}$ kills variables outside $F$ and fixes those
inside. Its kernel is $P_F$, and it is surjective by renaming the retained
variables back into $V$. Thus the quotient equivalence is an equivalence of
the actual quotient:
$$ S/P_F\simeq_R R[x_v:v\in F]. $$
The variable formulas make the map explicit. The ideal is prime when $R$ is
an integral domain. When $R=k$ is a field, the quotient has ring Krull
dimension $|F|$ (in Lean, `Nat.card` cast to the extended dimension type).
These coordinate results need no finite ambient $V$; the selected $F$ is
already finite.

<span class="checked-badge">Checked in Lean</span>
[Quotient equivalence and value](#lean-L@@LINE:coordinateQuotientEquiv@@) ·
[Inside and outside variables](#lean-L@@LINE:coordinateRestriction_X_inside@@) ·
[Primality](#lean-L@@LINE:coordinateIdeal_isPrime@@) ·
[Coordinate-quotient dimension](#lean-L@@LINE:coordinateQuotient_ringKrullDim@@) ·
[Blueprint node](blueprint.html#prop:facet-primes)

Now assume $V$ is finite and let $\operatorname{Fac}(K)$ be the finite,
nonempty type of maximal faces. Every face extends to a facet, including
when the only face is $\varnothing$. The checked identity compares arbitrary
polynomial terms:
$$ I_K=\bigcap_{F\in\operatorname{Fac}(K)}P_F. $$
A nonface-supported term lies in every facet ideal. Conversely, if a
polynomial lies in each facet ideal, any term whose support were a face
would extend to a facet and violate termwise membership there. For any prime
$Q\supseteq I_K$, the product of the finitely many $P_F$ lies in $Q$;
primality forces at least one $P_F\subseteq Q$.

<span class="checked-badge">Checked in Lean</span>
[Facet extension and intersection](#lean-L@@LINE:stanleyReisnerIdeal_eq_iInf_coordinateIdeal@@) ·
[Prime containment](#lean-L@@LINE:exists_facet_coordinateIdeal_le@@) ·
[Blueprint node](blueprint.html#prop:facet-primes)

Ghost vertices remain outside every facet, so their variables belong to each
$P_F$. If every ambient vertex is a ghost, the empty face is the sole facet;
then $I_K=P_{\varnothing}$ and its coordinate quotient is the coefficient
ring (the coefficient field when coefficients are a field). These results
supply the coordinate quotients and prime-containment step for the
[checked dimension argument](#dimension) below.

<details><summary>Checked coordinate and facet proofs</summary>

<!-- LEAN:coordinate-membership -->
<!-- LEAN:coordinate-quotient -->
<!-- LEAN:facet-decomposition -->
<!-- LEAN:facet-edge-cases -->

</details>

## Global and localized dimension {#dimension}

Let $k$ be any field and let the ambient vertex type be finite. Define
$d(K)=\max_{F\in K}|F|$. The maximum exists because the faces form a finite,
nonempty family; a facet attains it. The simplicial dimension is the integer
$d(K)-1$.

::: {.theorem-box}
$$ \dim k[K]=\dim k[K]_{\mathfrak m}=d(K),\qquad
\mathfrak m=(\bar x_v:v\in V). $$

<span class="checked-badge">Checked in Lean</span>
[Global dimension](#lean-L@@LINE:faceRing_ringKrullDim@@) ·
[Localized dimension](#lean-L@@LINE:faceRing_atAugmentation_ringKrullDim@@) ·
[Blueprint node](blueprint.html#prop:dimension)
:::

For the upper bound, take a finite strict prime chain over $I_K$. Its first
prime contains a facet coordinate ideal $P_F$, so the whole chain lies over
$P_F$. The quotient prime correspondence preserves its length, which is at
most $\dim(S/P_F)=|F|\leq d(K)$.

For the lower bound, remove the vertices of a face $F$ one at a time.
The corresponding coordinate ideals give a strict prime chain from $P_F$
to $P_{\varnothing}$ of length $|F|$. Strictness follows from
$x_v\in P_G\Longleftrightarrow v\notin G$. Since $F$ is a face,
$I_K\subseteq P_F$; the chain descends to the actual quotient and ends at
$\mathfrak m$. Choosing a face of maximum cardinality proves

$$ d(K)\leq\operatorname{ht}\mathfrak m\leq\dim k[K]\leq d(K). $$

Mathlib’s localization-height theorem identifies the dimension of the actual
`Localization.AtPrime` with $\operatorname{ht}\mathfrak m$. Both required
equalities follow. The earlier augmentation result supplies finite type,
Noetherianity, maximality, and the residue algebra $k[K]/\mathfrak m\cong k$.
No purity, infinite-field, or no-ghost hypothesis is needed.

When only the empty face occurs, $d(K)=0$, the chain has length zero, and
both ring dimensions are zero; the simplicial dimension remains $-1$.
The lower chain and height bound for an individual finite face also work
when the ambient type is infinite.

<details><summary>Maximum face cardinality and the augmented dimension convention</summary>

<!-- LEAN:dimension-objects -->

</details>

<details><summary>Checked prime-chain upper and lower bounds</summary>

<!-- LEAN:coordinate-chain -->
<!-- LEAN:dimension-upper -->
<!-- LEAN:dimension-lower -->

</details>

<details><summary>Checked global dimension, height, and localized dimension</summary>

<!-- LEAN:dimension-result -->

</details>

## Localization kernels and transition maps {#localizations}

For a finite set $F$ of ambient vertices, put
$x_F=\prod_{v\in F}\bar x_v$. The implemented object is the actual
`Localization.Away x_F` of the face ring. Every element is represented by
a polynomial fraction $\bar p/x_F^r$ with $r\in\mathbb N$.

::: {.theorem-box}
$$ \frac{\bar p}{x_F^r}=0\text{ in }R[K]_{x_F}
\quad\Longleftrightarrow\quad x_F\bar p=0\text{ in }R[K]
\quad\Longleftrightarrow\quad
\forall\alpha\in\operatorname{supp}p,\;
F\cup\operatorname{supp}\alpha\notin K. $$

<span class="checked-badge">Checked in Lean</span>
[Fraction criterion](#lean-L@@LINE:faceRingLocalizationFraction_eq_zero_iff@@) ·
[Kernel annihilation](#lean-L@@LINE:faceRingLocalization_algebraMap_eq_zero_iff@@) ·
[Blueprint node](blueprint.html#lem:localization-kernel)
:::

The polynomial-fraction criterion holds over every commutative coefficient
ring, including the zero ring, and for any ambient vertex type. The generic
localization equality criterion first says that $\bar p/1=0$ exactly when
some $x_F^n\bar p=0$, for $n\geq0$. The squarefree Stanley--Reisner
argument sharpens this to one factor. For $n>0$, lifting $x_F^n$ to the
monic polynomial $x^{n\mathbf1_F}$ translates each exponent $\alpha$ to
$\alpha+n\mathbf1_F$ and leaves its coefficient unchanged. This
translation is injective, so distinct support terms cannot cancel, even over
a ring with zero divisors. The shifted support is exactly
$F\cup\operatorname{supp}\alpha$. Thus if any positive power kills the
class, every such union is a nonface; by the termwise ideal criterion one
factor already kills it. A witness $n=0$ means $\bar p=0$ already, so the
same conclusion holds. Conversely, if all the unions are nonfaces, one
factor shifts every term into the ideal. The first-power conclusion depends
on squarefree support behavior; it is not true for arbitrary monomial ideals.

### Why one factor suffices {#kernel-audit}

For comparison, in $B=k[x,y]/(x^2y)$ with $k$ a field, inverting $x$ kills
$\bar y$ because $x^2\bar y=0$, but $x\bar y\ne0$ since $xy\notin(x^2y)$.
The support of $xy$ and $x^2y$ is the same, but this ideal distinguishes
the exponents. This shows why the first-power criterion comes from the
squarefree Stanley--Reisner ideal, not from localization alone.

<p><a href="source/LocalizationKernelAudit.lean" download>Download the compiled localization-kernel regression checks</a>. They cover zero numerators; an <code>x</code> monomial that survives because its joined support with the inverted set is a face; the nonzero face-ring class of <code>y</code> killed after inverting <code>x</code> because the joined support is a nonface; nonface and ghost localizations; scalar injectivity and a monic constant fraction over trivial coefficients; the empty-product equivalence; and the squarefree criterion over <code>ZMod 4</code>. The <code>k[x,y]/(x²y)</code> example above is a mathematical comparison; the Lean regression for failure of a general first-power rule is <code>Away (2 : ZMod 4)</code>, where <code>2² = 0</code> but <code>2 · 1 ≠ 0</code>.</p>

The coefficient hypotheses for the neighboring statements differ. Over a
nontrivial coefficient ring, a monic monomial fraction survives exactly
when $F\cup\operatorname{supp}\alpha$ is a face, and the localization
is nontrivial exactly when $F$ is a face. Inverting a nonface product gives
the zero ring, including for a product containing ghost variables. The
scalar map for a face localization is injective for every commutative ring,
including the zero ring (where this is vacuous). For $F=\varnothing$,
localization at the unit is equivalent to the original face ring for every
commutative coefficient ring. In the zero ring the polynomial support is
empty, so the universal support criterion is vacuous, as it should be.

For $F\subseteq G$, the product $x_F$ divides $x_G$, hence is a unit in
$R[K]_{x_G}$. The universal property gives a coefficient-algebra map
$\rho_{FG}:R[K]_{x_F}\to R[K]_{x_G}$. It fixes the image of the face ring,
and the checked fraction formula is

$$ \rho_{FG}\left(\frac{\bar p}{x_F^r}\right)
=\frac{x_{G\setminus F}^{\,r}\bar p}{x_G^r}. $$

The maps satisfy $\rho_{FF}=\mathrm{id}$ and
$\rho_{GH}\circ\rho_{FG}=\rho_{FH}$. These statements include zero
localizations; no face assumption is needed for the maps.

These kernel and map formulas are used below to construct the
[localized grading](#localized-grading).

<details><summary>The actual localizations and polynomial fractions</summary>

<!-- LEAN:localization-objects -->

</details>

<details><summary>Checked polynomial and monomial vanishing criteria</summary>

<!-- LEAN:localization-kernel -->
<!-- LEAN:localization-nonzero -->

</details>

<details><summary>Checked empty-product equivalence and transition maps</summary>

<!-- LEAN:localization-maps -->

</details>


## Integer grading of the localizations {#localized-grading}

For an integer exponent vector $a$, write $N(a)$ and $P(a)$ for its
negative and positive supports. A degree is admissible in $k[K]_{x_F}$
when $N(a)\subseteq F$ and $F\cup P(a)$ is a face. Lean uses finitely
supported integer exponents, which give all integer exponent vectors
when the ambient type is finite.

::: {.theorem-box}
$$
\dim_k (k[K]_{x_F})_a =
\begin{cases}
1,&N(a)\subseteq F\ \text{and}\ F\cup P(a)\in K,\\
0,&\text{otherwise}.
\end{cases}
$$

<span class="checked-badge">Checked in Lean</span>
[Integer grading](#lean-L@@LINE:faceRingLocalizationGradedAlgebra@@) ·
[Component basis](#lean-L@@LINE:faceRingLocalizationComponentBasis@@) ·
[Transition on basis vectors](#lean-L@@LINE:faceRingLocalizationMap_basis@@) ·
[Blueprint node](blueprint.html#lem:localized)
:::

In an admissible degree, the basis vector is
$\bar x^{a+r\mathbf1_F}/x_F^r$, where $r$ clears the negative
exponents. Increasing $r$ multiplies the numerator and denominator by
the same power. Expanding a polynomial numerator gives spanning. For
independence, clear a common denominator in a finite relation. The
numerator terms then have distinct exponents and face supports after
adjoining $F$. The kernel criterion forces their coefficients to vanish.

Multiplication adds degrees and the unit has degree zero. The resulting
components form an internal direct sum on the actual localization.
When $F\subseteq G$, changing the denominator multiplies the numerator
by the complementary product power. The new exponent is
$a+r\mathbf1_G$, so the transition sends the vector to the same
Laurent monomial in an admissible target degree, or to zero otherwise.

<details><summary>Laurent monomials and the localization basis</summary>

<!-- LEAN:laurent-monomials -->

</details>

<details><summary>Integer grading, homogeneous components, and transition maps</summary>

<!-- LEAN:laurent-grading -->
<!-- LEAN:laurent-transitions -->

</details>

## The finite extended Čech complex {#cech-complex}

For finite linearly ordered $V$, degree $q$ is the finite product of the
actual localizations $A_{x_F}$ over **all** subsets $F\subseteq V$ of size
$q$, canonically equivalent to their finite direct sum. Thus the empty set
is the unique degree-zero coordinate, and every nonface subset remains in
the index; its localization is the zero ring, including for ghost vertices.
The cochain differential at $G$ sums the transition maps from $G\setminus\{v\}$
with sign $(-1)^{|\{u\in G:u<v\}|}$. The checked `ModuleCat` cochain complex
has square-zero differential. Its coordinatewise fine-degree submodules are
preserved by the differential.

::: {.theorem-box}
**Checked prerequisite `lem:cech-complex`.** The product/direct-sum
identification, actual signed localization maps, cochain-complex law, and
degree preservation are compiled and axiom-checked. The construction retains
the empty-face and ghost-vertex conventions.

[Cochain complex](#@@ANCHOR:Reisner.Complex.cechComplex@@) ·
[Square-zero differential](#@@ANCHOR:Reisner.Complex.cechDifferential_comp_eq_zero@@) ·
[Degree restriction](#@@ANCHOR:Reisner.Complex.cechDifferentialDegree@@) ·
[Blueprint node](blueprint.html#lem:cech-complex)

[Download the compiled edge-case and axiom checks](source/Checks-Cech.lean)
:::

<details><summary>Checked finite Čech implementation</summary>

<!-- LEAN:cech-complex -->

</details>

<details><summary>Complete finite Čech Lean source</summary>

<!-- LEAN:full-cech-source -->

</details>

The complete degreewise cohomology decomposition, positive-coordinate
contracting homotopy, and comparison to local cohomology are not part of this
checked prerequisite. In particular, the full statement of
`lem:cech-grading` remains future work.

### Signed action on monomial cochains {#cech-basis-action}

For an admissible degree-$a$ monomial at a subset $F$, the cochain supported
at $F$ has differential given by the signed sum over every insertion
$v\notin F$. The sign counts the vertices of $F$ below $v$. Each target
coordinate is checked, so a target that is a nonface or contains a ghost
vertex contributes zero through the localization map and monomial API.

::: {.theorem-box}
**Checked prerequisite `lem:cech-basis-action`.** The compiled theorem
`cechDifferential_monomialCochain` proves the full cochain equality for every
admissible source. Regression checks include the empty ambient complex,
ordinary face insertion, and an inadmissible ghost target.

[Differential action theorem](#@@ANCHOR:Reisner.Complex.cechDifferential_monomialCochain@@) ·
[Blueprint node](blueprint.html#lem:cech-basis-action) ·
[Axiom inspection](source/Axioms.lean)
:::

<details><summary>Checked monomial cochain action</summary>

<!-- LEAN:cech-basis-action -->

</details>

This establishes the monomial basis-action prerequisite. A separate checked
node now proves the termwise direct-sum decomposition of each cochain module.

### Termwise decomposition by fine degree {#cech-termwise-decomposition}

For every cochain degree $q$, the submodules whose localization coordinates
all have a fixed fine degree $a$ form an internal direct sum equal to the
whole cochain module. The proof uses the finite product basis assembled from
the admissible Laurent monomial bases. It retains every subset coordinate,
including nonfaces and ghost vertices, and works over any commutative ring.

::: {.theorem-box}
**Checked prerequisite `lem:cech-termwise-decomposition`.**
`cechDegreeSubmodule_isInternal` proves the direct-sum decomposition of
`CechCochain R q` into its `cechDegreeSubmodule R q a` terms. The Lean
declaration asks for `[Fintype V] [DecidableEq V]`; the latter is supplied
classically for any finite ambient type.

[Internal direct-sum theorem](#@@ANCHOR:Reisner.Complex.cechDegreeSubmodule_isInternal@@) ·
[Blueprint node](blueprint.html#lem:cech-termwise-decomposition) ·
[Axiom inspection](source/Axioms.lean)
:::

<details><summary>Checked termwise cochain decomposition</summary>

<!-- LEAN:cech-termwise-decomposition -->

</details>

This is a decomposition of cochain modules. The cohomology decomposition
asserted in the full `lem:cech-grading`, positive-coordinate contraction,
link formula, and local-cohomology comparison remain future work.

## The objects, as Lean sees them {#objects}

The implementation uses mathlib’s actual polynomials and ideal spans.
Its small complex structure adds the empty-face convention while allowing
ghost vertices:

<!-- LEAN:complex -->

`Finset V` represents a finite vertex set. `LowerSet` makes the family
downward closed under inclusion; `empty_mem` supplies the empty face.
An exponent is `V →₀ ℕ`. The squarefree exponent of a set is its indicator:

<!-- LEAN:indicator-definition -->

Next, take the indicators of nonfaces, then their monic polynomials, and
finally the ideal they generate:

<!-- LEAN:ideal -->

Here `f '' S` means the image of a set under a function. The ideal is
defined from generators, independently of the membership theorem.
The proved helper `monomial_squarefreeExponent_eq_prod` identifies each
indicator monomial with the usual product of distinct variables.

<details><summary>The actual face-ring quotient</summary>

<!-- LEAN:quotient -->

This uses mathlib’s quotient of a ring by an ideal. Its coefficient
assumption is `[CommRing R]`; the monomial-membership theorem itself needs
only `[CommSemiring k] [Nontrivial k]`.

</details>

## The proof, in mathematics and Lean {#proof}

### 1. Translate an inequality into support inclusion

For a finite set $F$, let $\mathbf1_F$ be its indicator. Pointwise order gives

$$ \mathbf1_F\le\alpha\quad\Longleftrightarrow\quad
F\subseteq\operatorname{supp}\alpha. $$

At a vertex in $F$, the inequality is $1\le\alpha(v)$, equivalent to a
nonzero natural-number exponent. At every other vertex it is $0\le\alpha(v)$.
This proves both directions.

<details><summary>Read the checked Lean proof of this step</summary>

<!-- LEAN:comparison -->

`constructor` splits the equivalence. The forward direction checks each
vertex of $F$; the reverse direction splits into membership in $F$ and
nonmembership. `.mp` uses the forward direction of an equivalence, and
`.mpr` uses the reverse direction.

</details>

### 2. Reuse the general monomial-ideal theorem

Mathlib’s `MvPolynomial.mem_ideal_span_monomial_image` says that a polynomial
is in an ideal generated by monic monomials exactly when **each exponent
in its polynomial support dominates a generator exponent**. With our
nonface generators, and since the polynomial support of $x^\alpha$ is the
singleton $\{\alpha\}$, it yields

$$ x^\alpha\in I_K\quad\Longleftrightarrow\quad
\exists F\notin K\text{ with }\mathbf1_F\le\alpha. $$

There are two supports here: `α.support` is a set of **vertices**;
the support of a polynomial is a set of **exponent vectors**.
For $x_a^2x_c^3$, the former has two vertices and the latter has one exponent.

### 3. Prove the forward implication

If $x^\alpha\in I_K$, choose a nonface $F$ whose indicator is at most
$\alpha$. Step 1 gives $F\subseteq\operatorname{supp}\alpha$. If that
support were a face, downward closure would make $F$ a face. This is a
contradiction, so the support is a nonface.

### 4. Construct the reverse witness

If $\operatorname{supp}\alpha$ is a nonface, choose that set itself as $F$.
The inclusion $F\subseteq\operatorname{supp}\alpha$ is reflexive, so step 1
gives $\mathbf1_F\le\alpha$. It is the generator witness required in step 2.

<details class="main-proof" open><summary>The earlier checked monomial proof</summary>

<!-- LEAN:main-proof -->

The theorem specializes polynomial membership to one monomial. The proof
uses mathlib’s monomial-ideal membership theorem to extract a nonface
generator, then applies downward closure; in the reverse direction the
monomial's own vertex support is the generator witness.

The pattern `⟨β, ⟨F, hF, rfl⟩, hle⟩` unpacks a generator exponent, the
nonface it came from, and its domination. `rfl` substitutes the indicator
for that exponent. The final tuple constructs the same data in reverse.

</details>

## The route to the full criterion {#route}

The completed result is the entry point to a longer proof. The
[blueprint](blueprint.html) gives precise statements, full informal proofs,
and dependencies for all **@@TOTAL@@ nodes**. Only **@@CHECKED@@ nodes**
currently have checked Lean implementations.

<!-- ROUTE -->

The algebraic branch computes the face-ring dimension and relates depth to
local-cohomology vanishing. The combinatorial branch computes the
multigraded Čech terms using monomials and identifies their cohomology with
that of links. Over a field, homology and cohomology have the same vanishing.

For a nonpositive multidegree $a$ with negative support $N\in K$, the planned
calculation is

$$ H^q_{\mathfrak m}(k[K])_a\cong
\widetilde H^{q-|N|-1}(\operatorname{lk}_K N;k). $$

Positive coordinates give a contracting homotopy; a nonface negative
support gives zero. This is a **local-cohomology formula using links**.
Panov’s Hochster Tor formula uses **induced subcomplexes** and is a different
result.

The converse also needs a real step: linkwise vanishing forces purity.
Only after proving purity can the link dimension be replaced by the
uniform bound $d-|F|-1$, where $d=\max_{F\in K}|F|$.
These comparisons and the purity argument are written in the blueprint,
and remain unformalized.

## What is actually checked {#checked}

<!-- STATUS -->

The main theorem and its supporting project declarations contain no proof
placeholders or custom axioms. Axiom inspection reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean’s standard foundational principles. They are distinct from
assuming an unproved mathematical theorem as a new project axiom.
`classical` and `noncomputable` do not bypass kernel checking.

The checked localization grading supplies the modules and transition maps
for each multidegree of the Čech complex. The finite extended Čech complex,
its signed differential, square-zero law, and degree restrictions are checked.
The cohomology decomposition, positive-coordinate contraction, graded local test,
local-cohomology comparison, augmented homology, link calculus, purity,
and the full criterion are future formalization work.

## Reproduce and inspect {#reproduce}

Lean is pinned to `leanprover/lean4:v4.35.0`; mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake build
lake env lean Checks/Axioms.lean
lake env lean Checks/Cech.lean
python3 site/build.py
python3 -m http.server 8000 --directory site/dist
```

[Build and axiom output](validation.txt) ·
[API and reference audit](source/AUDIT.md) ·
[Dependency pins](source/lake-manifest.json) ·
[Blueprint PDF](blueprint.pdf) ·
[Face-ring Lean source](source/StanleyReisner.lean) ·
[Čech Lean source](source/Cech.lean) ·
[Čech regression checks](source/Checks-Cech.lean)

All the mathematical text, rendered equations, styles, and page interactions
are included locally. No account or external math-rendering service is needed.

<details id="full-source"><summary>Complete Lean source</summary>

<!-- LEAN:full-source -->

</details>

::: {.colophon}
Presentation inspired by the [GQ₂ project](https://roed314.github.io/gq2/).
This site describes the Reisner project’s own code and proof status.
:::
