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
[Read augmented simplicial cochains](#augmented-cochains) ·
[Read integer cochain reindexing](#integer-reindex) ·
[Read signed link coordinates](#cech-link-comparison) ·
[Read shifted link cohomology](#cech-link-cohomology) ·
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
The homogeneous projections commute with the differential, detect cocycles,
and give homogeneous primitives for homogeneous boundaries.
The fine-degree subcomplex is contractible whenever one coordinate of its
degree is positive, so its Čech cohomology vanishes.
In nonpositive degree, the admissible localization indices are matched with
faces of the link of the negative support. The actual-face augmented cochain
complex is also checked: its signed deletion differential squares to zero,
its empty-face term is canonically the coefficient ring, and its modules
above the ambient cardinality vanish. The coordinate formula for signed basis
insertion and the degree-minus-one cohomology endpoints are checked. The
integer reindexing $i=(n:\mathbb Z)-1$, its restriction and homology
isomorphisms, and the low/high term and cohomology cutoffs are also checked.
The signed termwise comparison with augmented link cochains, its extension to
a shifted cochain-complex isomorphism, and the induced actual cohomology
identification are checked. Below the shift, both cohomology objects vanish;
at and above it, the result identifies Čech cohomology with link reduced
cohomology in integer degree $r-1$. In particular, vanishing of total Čech
cohomology below any finite cutoff is equivalent to vanishing of the matching
reduced cohomology of every link. This result also covers cutoff zero and
degree $-1$. The degree-zero comparison with
Ext-colimit local cohomology is checked over every commutative coefficient
ring. Over a field, the augmentation localization is Cohen–Macaulay exactly
when its maximal-ideal local cohomology vanishes below the maximum face
cardinality. The augmentation ideal is the unique maximal proper homogeneous
ideal, and global Cohen–Macaulayness implies this vanishing. The graded-local
converse and the positive-degree Ext–Čech comparison remain external or open.
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

The degreewise Čech cohomology decomposition and its positive-coordinate
contracting homotopy are checked below. The comparison to local cohomology
in positive cohomological degrees remains open.

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

### Cycles and boundaries by fine degree {#cech-cycle-boundary-components}

The finite decomposition gives a projection $\pi_a^q:C^q\to C_a^q$.
Because the differential preserves degree, projecting before or after applying
it gives the same result. Therefore a cochain is a cocycle exactly when each
of its homogeneous components is a cocycle. If a homogeneous cochain in
degree $q+1$ is a boundary, projecting any primitive gives a primitive of
the same fine degree. In cochain degree zero there is no incoming boundary.

::: {.theorem-box}
**Checked prerequisite `lem:cech-cycle-boundary-components`.** The
projections and criteria hold for arbitrary commutative rings, including the
zero ring, and retain all subset coordinates.

[Differential compatibility](#@@ANCHOR:Reisner.Complex.cechHomogeneousComponent_differential@@) ·
[Cycle criterion](#@@ANCHOR:Reisner.Complex.cechDifferential_eq_zero_iff_components@@) ·
[Homogeneous primitive](#@@ANCHOR:Reisner.Complex.cechBoundary_homogeneous_primitive@@) ·
[Blueprint node](blueprint.html#lem:cech-cycle-boundary-components)
:::

<details><summary>Checked projections and cycle and boundary criteria</summary>

<!-- LEAN:cech-cycle-boundary-components -->

</details>

### Čech cohomology decomposes by degree {#cech-cohomology-decomposition}

The degree submodules and restricted differentials form actual subcomplexes
$C_a^\bullet$. Their inclusions induce the canonical isomorphism
$$\bigoplus_a H^q(C_a^\bullet)\cong H^q(C^\bullet).$$
The inverse is induced by the homogeneous projections. A representative
cochain has finite degree support, so the inverse really lands in the direct
sum even though the degree index set can be infinite. The checked quotient
equivalences identify these actual module-category homology objects with
cycles modulo boundaries; the incoming boundaries in degree zero vanish.
This holds over any commutative ring, including the zero ring.

::: {.theorem-box}
**Checked `lem:cech-cohomology-decomposition` and `lem:cech-grading`.**
[Cohomology isomorphism](#@@ANCHOR:Reisner.Complex.cechCohomologyDecomposition@@) ·
[Action on summands](#@@ANCHOR:Reisner.Complex.cechCohomologyDecomposition_lof@@) ·
[Inverse components](#@@ANCHOR:Reisner.Complex.cechCohomologyDecomposition_symm_apply@@) ·
[Blueprint node](blueprint.html#lem:cech-cohomology-decomposition)
:::

<details><summary>Checked Čech cohomology decomposition</summary>

<!-- LEAN:cech-cohomology-decomposition -->

</details>

### Positive-coordinate contraction {#cech-positive-contraction}

If a fine degree $a$ has a positive coordinate $a_p>0$, the degree-$a$
Čech subcomplex is contractible. On monomial cochains the contracting map
removes $p$ with the usual alternating sign when $p$ is present, and gives
zero otherwise. The checked homotopy proves $dh+hd=1$, including the endpoint
in cochain degree zero. Hence all cohomology of this subcomplex vanishes.
The result works over every commutative ring, including the zero ring.

::: {.theorem-box}
**Checked `lem:contraction`.**
[Contracting homotopy](#@@ANCHOR:Reisner.Complex.cechPositiveContractingHomotopy@@) ·
[Cohomology vanishing](#@@ANCHOR:Reisner.Complex.cechPositiveCohomology_isZero@@) ·
[Blueprint node](blueprint.html#lem:contraction)
:::

<details><summary>Checked positive-coordinate contraction</summary>

<!-- LEAN:cech-positive-contraction -->

</details>

### Nonpositive degrees and link faces {#cech-nonpositive-indices}

For a face $N$ of $K$, its link consists of faces $T$ disjoint from $N$
such that $N\cup T$ is a face of $K$. The empty face is included; the link
of a facet is the complex containing just the empty face.

Let $a\leq 0$ and let $N=\{v:a_v<0\}$. If $N$ is a face, an admissible
Čech index $F$ corresponds to the link face $F\setminus N$, with inverse
$T\mapsto N\cup T$ and cardinality $|F|=|N|+|T|$. The empty link face is
therefore retained. There are no admissible indices when $q<|N|$. If $N$ is
not a face, every term of the degree-$a$ complex and its cohomology vanish.
These statements hold for arbitrary commutative coefficient rings.

::: {.theorem-box}
**Checked `def:link` and `lem:cech-nonpositive-indices`.**
[Link definition](#@@ANCHOR:Reisner.Complex.link@@) ·
[Index correspondence](#@@ANCHOR:Reisner.Complex.nonpositiveCechIndexEquivLink@@) ·
[Nonface cohomology vanishing](#@@ANCHOR:Reisner.Complex.cechCohomologyDegree_isZero_of_nonpos_negativeSupport_nonface@@) ·
[Blueprint node](blueprint.html#lem:cech-nonpositive-indices)
:::

<details><summary>Checked nonpositive Čech indices and link faces</summary>

<!-- LEAN:link-definition -->
<!-- LEAN:cech-nonpositive-indices -->

</details>

This establishes the index correspondence. The actual signed cochain
comparison and its differential compatibility are described in the next
section; the positive-degree comparison with local cohomology and the full link formula remain
future work.

## Augmented simplicial cochains by face cardinality {#augmented-cochains}

The project now has a second cochain complex built from the **actual faces**
of $K$. For finite linearly ordered $V$, its cardinality-$n$ term is
$$ C^n(K;R)=\prod_{\substack{F\in K.\mathrm{faces}\\|F|=n}}R. $$
It is the finite product, equivalently a finite direct sum, of one copy of
$R$ for every $n$-element face. Nonfaces and ghost singletons are not
coordinates. At $n=0$, the only coordinate is $\varnothing$, so this is the
augmented reduced cochain term of degree $-1$.

For each $(n+1)$-element face $G$, the checked differential deletes one
vertex at a time:
$$ (\delta^n f)(G)=\sum_{v\in G}(-1)^{|\{u\in G:u<v\}|}
                f(G\setminus\{v\}). $$
Every deletion is a face by downward closure. In the composite of two
differentials, an ordered pair of distinct deleted vertices is paired with
the reverse order. Both terms evaluate $f$ on the same twice-deleted face,
and their orientation signs are additive inverses. This proves
$\delta^{n+1}\circ\delta^n=0$ over any commutative ring, including
characteristic two and the zero ring, and packages the terms and maps as an
actual `CochainComplex (ModuleCat R)`.

::: {.theorem-box}
**Checked `lem:augmented-cochain-complex`.** The finite product/direct-sum
equivalence, coordinate basis, signed deletion formula, square-zero law,
empty-face scalar term, and high-cardinality zero modules compile in Lean.

[Face index and cochains](#@@ANCHOR:Reisner.Complex.SimplicialFaceIndex@@) ·
[Differential formula](#@@ANCHOR:Reisner.Complex.simplicialDifferential_apply@@) ·
[Square-zero theorem](#@@ANCHOR:Reisner.Complex.simplicialDifferential_comp_eq_zero@@) ·
[Cochain complex](#@@ANCHOR:Reisner.Complex.simplicialCochainComplex@@) ·
[Checked blueprint node](blueprint.html#lem:augmented-cochain-complex)
:::

Evaluation at the unique empty face gives a checked equivalence
$C^0(K;R)\simeq_R R$. The differential sends a scalar to the constant
cochain on the **actual** singleton faces; if no actual singleton exists,
the outgoing map is zero. The checked basis-coordinate formula evaluates
the differential on $e_F$ by summing over deletions and testing whether
$G\setminus\{v\}=F$.

The separate checked node `lem:augmented-basis-insertion` proves the
coordinate formula: a target coordinate receives a signed contribution
exactly when it is obtained by inserting a vertex into $F$. The checked
node `lem:augmented-cohomology-minus-one` identifies the actual homology
object at index zero with $\ker\delta^0$ and proves it is $R$ for
$K=\{\varnothing\}$ or zero when an actual vertex exists. Higher-degree
cohomology vanishing is not part of these endpoint results.

<details><summary>Checked face-cardinality terms and coordinate basis</summary>

<!-- LEAN:simplicial-cochain-modules -->

</details>

<details><summary>Checked signed deletion and square-zero complex</summary>

<!-- LEAN:simplicial-differential -->

</details>

<details><summary>Checked empty-face, no-vertex, and cardinality cases</summary>

<!-- LEAN:simplicial-boundaries -->

</details>

### Integer reduced-degree reindexing and cutoffs {#integer-reindex}

The face-cardinality index $n\in\mathbb N$ represents reduced degree
$i=(n:\mathbb Z)-1$. Lean extends the natural-indexed complex to
$\mathbb Z$ along the embedding $e(n)=n-1$, putting zero objects below
$-1$. For $i\geq-1$, the corresponding natural index is
$n_i=(i+1).\mathrm{toNat}$; the proof first establishes nonnegativity and
then proves $(n_i:\mathbb Z)-1=i$, avoiding truncated natural subtraction.
The integer complex restricts back to the natural complex along this
embedding, and its cohomology objects at $e(n)$ are canonically isomorphic
to the natural-indexed ones.

The actual integer cochain terms and cohomology objects vanish for $i<-1$.
They also vanish for $i>(|V|:\mathbb Z)-1$, equivalent to
$|V|<n_i$ in the nonzero range. The natural complex has zero homology for
$n>|V|$. At degree $-1$, the previous endpoint results transport: the
cohomology is $R$ for $K=\{\varnothing\}$ and zero when an actual vertex
exists, including over the zero ring.

::: {.theorem-box}
**Checked `lem:augmented-cochains`.** The integer extension, component and
restriction isomorphisms, homology comparison, and both cutoff theorems are
compiled. The degree-minus-one endpoint cases are transported to the
integer-indexed complex.

[Integer cochain complex](#@@ANCHOR:Reisner.Complex.simplicialCochainComplexInt@@) ·
[Restriction isomorphism](#@@ANCHOR:Reisner.Complex.simplicialCochainComplexIntRestrictionIso@@) ·
[Homology isomorphism](#@@ANCHOR:Reisner.Complex.simplicialCochainComplexIntHomologyIso@@) ·
[Low cutoff](#@@ANCHOR:Reisner.Complex.simplicialCochainComplexInt_homology_isZero_of_lt_minus_one@@) ·
[High cutoff](#@@ANCHOR:Reisner.Complex.simplicialCochainComplexInt_homology_isZero_of_card_lt@@) ·
[Blueprint node](blueprint.html#lem:augmented-cochains)
:::

<details><summary>Checked extension, restriction, and homology comparison</summary>

<!-- LEAN:simplicial-integer-reindexing -->

</details>

<details><summary>Checked low and high cochain and cohomology cutoffs</summary>

<!-- LEAN:simplicial-integer-cutoffs -->

</details>

<details><summary>Checked transported degree-minus-one endpoints</summary>

<!-- LEAN:simplicial-integer-endpoints -->

</details>

The local Ext-colimit depth cutoff is now checked: for every finite $d$,
$d\le\operatorname{depth}(B)$ exactly when local cohomology vanishes below
$d$. For a principal localization, the kernel is also checked to be exactly
the submodule of elements killed by some power of the generator. This is the
degree-zero starting point for the Čech comparison. For the face ring and its
augmentation ideal, the degree-zero Ext-colimit module, with scalars
restricted to the coefficient ring, is isomorphic to $H^0$ of the extended
Čech complex. The map first gives a cycle in the kernel of the outgoing
differential and then takes its cohomology class. Every incoming differential
at degree zero vanishes, so this second map is an isomorphism.
[Degree-zero comparison and checked source](blueprint.html#thm:ext-zero-cech-cohomology)

Degree-zero derived Ext at each quotient stage is checked to be the usual Hom
module, and maps from each quotient are identified with elements annihilated
by its ideal. Positive-degree comparison, higher cohomology vanishing below
the simplicial dimension, chain order-independence, homology-cohomology
duality, and the proof of Reisner's criterion remain future work. Its full
statement is linked in Lean with the proof explicitly pending. The augmented
chain complex itself is checked using dual cochain terms and signed deletion.

<details><summary>Checked local depth cutoff theorem</summary>

<!-- LEAN:local-depth-cutoff -->

</details>

Over a field $k$, let $B=k[K]_{\mathfrak m}$ be the face ring localized at
its augmentation ideal, and let $\mathfrak n$ be the maximal ideal of $B$.
For a finite ambient vertex set, write $d$ for the maximum face cardinality.
A regular sequence of length $r$ in $B$ gives a nonzero quotient of dimension
$d-r$, so $\operatorname{depth} B\le d$. Since $\dim B=d$, the checked
cutoff theorem gives the local Cohen–Macaulay criterion
$$
\operatorname{depth}B=\dim B
\quad\Longleftrightarrow\quad
H^q_{\mathfrak n}(B)=0\ \text{for every }0\le q<d.
$$
When the only face is the empty face, $d=0$ and the vanishing condition
is vacuous.
[Augmentation-local criterion and proof](blueprint.html#cor:augmentation-local-cm)

<details><summary>Checked augmentation-local depth bound and vanishing criterion</summary>

<!-- LEAN:full-local-cm-source -->

</details>

For the total grading of $A=k[K]$, every proper homogeneous ideal $I$ is
contained in $\mathfrak m=A_+$. Indeed, if $x\in I$, then $x_0\in I$.
A nonzero $x_0$ would be a unit, since $A_0=k$. Thus $x_0=0$ and
$x\in A_+$. As $A/\mathfrak m=k$, the augmentation ideal is itself
maximal. Testing local Cohen–Macaulayness at every maximal homogeneous
ideal therefore amounts to the single vanishing test above. Global
Cohen–Macaulayness implies this condition by specialization at
$\mathfrak m$. The converse requires the Bruns–Herzog graded local theorem
to extend from maximal homogeneous ideals to arbitrary primes.
[Checked homogeneous maximal ideal test](blueprint.html#cor:homogeneous-maximal-cm-cutoff) ·
[Graded local theorem](blueprint.html#found:graded-cm)

<details><summary>Algebraic Cohen–Macaulayness and the homogeneous maximal ideal test</summary>

<!-- LEAN:full-graded-local-source -->

</details>

<details id="full-simplicial-source"><summary>Complete augmented cochain Lean source</summary>

<!-- LEAN:full-simplicial-source -->

</details>

## Signed coordinates identify nonpositive degrees with link cochains {#cech-link-comparison}

Let $a\leq0$ have negative support $N$, suppose $N$ is a face, and put
$L=\operatorname{lk}_K N$. An admissible Čech index is uniquely
$F=N\sqcup T$ with $T\in L$. Its cardinality is $|N|+|T|$, including
$T=\varnothing$. The checked comparison is an equivalence between the
actual modules over any commutative ring $R$:

::: {.theorem-box}
$$
\Phi_r:C^{|N|+r}_a \simeq_R E^r(L;R),\qquad
\Phi_r(c_{N\cup T}(a))=\sigma_N(T)e_T,
$$
$$
\sigma_N(T)=(-1)^{\sum_{t\in T}|\{n\in N:n<t\}|},
\qquad
\Phi_{r+1}d_a=\delta_L\Phi_r.
$$

<span class="checked-badge">Checked in Lean</span>
[Actual linear equivalence](#@@ANCHOR:Reisner.Complex.cechNonpositiveLinkEquiv@@) ·
[Explicit inverse](#@@ANCHOR:Reisner.Complex.cechNonpositiveLinkEquiv_symm_apply@@) ·
[Differential compatibility](#@@ANCHOR:Reisner.Complex.cechNonpositiveLinkEquiv_differential@@) ·
[Blueprint node](blueprint.html#lem:cech-link-coordinate-comparison)
:::

The forward map extracts the full Laurent-basis coefficient at $N\cup T$
and multiplies it by $\sigma_N(T)$. The inverse is the finite sum
$\sum_T\sigma_N(T)f(T)c_{N\cup T}(a)$. It is an inverse because each sign
squares to one. No nontriviality assumption or division is needed.

For insertion of $v$, disjointness gives
$r_{N\cup T}(v)=r_N(v)+r_T(v)$, while
$\sigma_N(T\cup\{v\})=\sigma_N(T)(-1)^{r_N(v)}$.
The two copies of the negative-support sign cancel. Invalid insertion
targets vanish in the actual localization; valid targets are exactly the
actual link faces. At $r=0$, the empty link face has sign one, so the
commuting equality includes the dual augmentation. Ghosts, characteristic
two, and the zero ring are included.

<details><summary>Checked equivalence, components, and inverse</summary>

<!-- LEAN:cech-link-equivalence -->

</details>

<details><summary>Orientation identities and valid insertion criterion</summary>

<!-- LEAN:cech-link-signs -->
<!-- LEAN:cech-link-compatibility -->

</details>

<details><summary>Full checked differential-compatibility proof</summary>

<!-- LEAN:cech-link-compatibility-proof -->

</details>

This result compares terms and adjacent differentials. The next section
packages the maps as an actual shifted complex isomorphism and transports its
homology. The positive-degree comparison with local cohomology and the full link formula
remain future work.

## Shifted link complex and Čech cohomology {#cech-link-cohomology}

Let $a\leq0$, let $N$ be its negative support, assume $N$ is a face, and
write $m=|N|$ and $L=\operatorname{lk}_K N$. Extend the actual
face-cardinality cochain complex of $L$ by zero along $r\mapsto m+r$.
This gives a genuine cochain complex $D$: its terms below $m$ are zero, and
its term in degree $m+r$ is the link cochain term in cardinality $r$. Under
these term identifications, its differential is exactly the existing signed
link differential, including the zero incoming map at the cutoff.

The signed coordinate equivalence from the previous section supplies the
components of an isomorphism from the degree-$a$ Čech complex to $D$. Below
$m$, the source term is also zero by the nonpositive-index cutoff theorem.
At $m+r$, the comparison square is precisely the checked adjacent-
differential compatibility. The family therefore gives an isomorphism of
actual cochain complexes, and hence an isomorphism of actual homology objects
in every natural degree.

For $q<m$, both cohomology objects are zero. For $q=m+r$, the extended
complex identifies its homology with the link's natural face-cardinality
cohomology in degree $r$. The checked integer reindexing then identifies
this with reduced cohomology in integer degree $(r:\mathbb Z)-1$. This
includes $r=0$, retaining the empty link face and degree $-1$. The hypotheses
allow arbitrary commutative coefficient rings, including the zero ring, and
retain empty ambient types, ghost vertices, characteristic two, and the
case $N=\varnothing$.

::: {.theorem-box}
**Checked `lem:cech-link-cohomology-comparison`.** The zero extension, actual
complex isomorphism and induced homology comparisons are compiled. The
below-cutoff case is stated separately, without truncated subtraction.

[Shifted link complex](#@@ANCHOR:Reisner.Complex.cechLinkShiftedComplex@@) ·
[Complex isomorphism](#@@ANCHOR:Reisner.Complex.cechNonpositiveLinkComplexIso@@) ·
[Integer reduced cohomology](#@@ANCHOR:Reisner.Complex.cechNonpositiveLinkCohomologyIso@@) ·
[Below-cutoff vanishing](#@@ANCHOR:Reisner.Complex.cechCohomologyDegree_isZero_of_nonpos_card_lt_negativeSupport@@) ·
[Blueprint node](blueprint.html#lem:cech-link-cohomology-comparison)
:::

<details><summary>Checked shifted complex and zero cutoff</summary>

<!-- LEAN:cech-link-shifted-complex -->

</details>

<details><summary>Checked cochain-complex isomorphism</summary>

<!-- LEAN:cech-link-complex-iso -->

</details>

<details><summary>Checked actual homology and integer reduced-degree comparison</summary>

<!-- LEAN:cech-link-homology -->

</details>

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

The checked project declarations contain no proof placeholders or custom
axioms. Axiom inspection reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean’s standard foundational principles. They are distinct from
assuming an unproved mathematical theorem as a new project axiom.
`classical` and `noncomputable` do not bypass kernel checking.

The checked localization grading supplies the modules and transition maps
for each multidegree of the Čech complex. The finite extended Čech complex,
its signed differential, square-zero law, and degree restrictions are checked.
Its homogeneous projections commute with the differential and characterize
cocycles and homogeneous boundaries.
The Čech cohomology decomposition and positive-coordinate contraction are
checked. The actual-face augmented cochain complex, its signed deletion
differential, square-zero identity, basis-coordinate and basis-insertion
formulas, empty-face scalar equivalence, no-actual-vertex zero differential,
and zero modules above the ambient cardinality are also checked. The actual
degree-$-1$ cohomology endpoints, integer reindexing, restriction and
homology isomorphisms, and low/high term and cohomology cutoffs are checked.
The signed termwise Čech/link equivalence, its shifted complex isomorphism and
induced actual cohomology identification are also checked over arbitrary
commutative rings. Higher-degree cohomology vanishing, chain order comparison,
duality, the graded local test, positive-degree
local-cohomology comparison, and purity remain future formalization work. The
criterion statement is linked in Lean; its proof remains open and contains
the project's single intentional `sorry`.

The Ext-colimit stage system now has a checked normalization in every
cohomological degree: for $A=R[K]$ and $J_n=(\bar x_v^n:v\in V)$,
augmentation-supported local cohomology of $A$ is the colimit of
$\operatorname{Ext}^q_A(A/J_n,A)$. The bounds
$J_n\subseteq\mathfrak m^n$ and
$\mathfrak m^{|V|n+1}\subseteq J_n$ hold over every commutative
coefficient ring, including the zero ring and the empty vertex set.
This is a cofinality step toward the positive-degree comparison; the
remaining Koszul or acyclic-resolution bridge is not yet checked.

<!-- LEAN:generator-power-ideals -->

<!-- LEAN:generator-power-ext-colimit -->

<!-- LEAN:localized-ext-scalar -->

<!-- LEAN:localized-ext-rows -->

<!-- LEAN:cech-acyclic-terms -->

The actual extended Čech complex is also now packaged in face-ring modules.
Its face-ring-linear differential is proved equal to the existing
coefficient-ring differential, so its square-zero law follows without a
second sign computation. At a fixed augmentation-power quotient and Ext
degree, applying the derived Ext functor gives a complex whose positive
Čech-degree terms and homology are zero. Its degree-zero object and
degree-zero homology are identified with the Ext of the face ring itself.
The double-complex comparison with the colimit remains open.

<!-- LEAN:cech-ext-complex -->

## Reproduce and inspect {#reproduce}

Lean is pinned to `leanprover/lean4:v4.35.0`; mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake build
lake env lean Checks/Axioms.lean
lake env lean Checks/Cech.lean
lake env lean Checks/SimplicialCochain.lean
python3 site/build.py
python3 -m http.server 8000 --directory site/dist
```

[Build and axiom output](validation.txt) ·
[API and reference audit](source/AUDIT.md) ·
[Dependency pins](source/lake-manifest.json) ·
[Blueprint PDF](blueprint.pdf) ·
[Face-ring Lean source](source/StanleyReisner.lean) ·
[Čech Lean source](source/Cech.lean) ·
[Degree-zero Čech and Ext source](source/DegreeZero.lean) ·
[Generator-power Ext comparison source](source/ExtComparison.lean) ·
[Localized-target Ext vanishing source](source/LocalizedExt.lean) ·
[Čech regression checks](source/Checks-Cech.lean) ·
[Augmented cochain Lean source](source/SimplicialCochain.lean) ·
[Augmented cochain checks](source/Checks-SimplicialCochain.lean)

[Local cohomology Lean source](source/LocalCohomology.lean) ·
[Augmentation-local criterion Lean source](source/LocalCohenMacaulay.lean) ·
[Homogeneous maximal ideal test Lean source](source/GradedLocalTest.lean)

[Expand the complete augmented cochain source](#full-simplicial-source)
[Expand the complete local cohomology source](#full-local-cohomology-source)

All the mathematical text, rendered equations, styles, and page interactions
are included locally. No account or external math-rendering service is needed.

<details id="full-source"><summary>Complete Lean source</summary>

<!-- LEAN:full-source -->

</details>

<details id="full-local-cohomology-source"><summary>Complete local cohomology Lean source</summary>

<!-- LEAN:full-local-cohomology-source -->

</details>

::: {.colophon}
Presentation inspired by the [GQ₂ project](https://roed314.github.io/gq2/).
This site describes the Reisner project’s own code and proof status.
:::
