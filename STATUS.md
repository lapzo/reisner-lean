# Milestone status

The current checked milestone includes the standard monomial quotient basis,
weighted homogeneity, quotient fine and total gradings, augmentation/residue
foundations, and coordinate-prime/facet structure. Finite type and Noetherianity
retain their stated hypotheses. The global and augmentation-local face-ring
dimension equalities are checked, including both prime-chain bounds.
Actual variable-product localizations now have checked polynomial-fraction
kernels and transition maps, and their integer grading and Laurent monomial
pieces are checked. The finite extended Čech complex, its signed localization
differential, square-zero law, fine-degree restrictions, signed action on
localization monomial cochains, and internal direct-sum decomposition of each
cochain module by fine degree are now checked. The cohomology decomposition
and criterion remain future work. The
ideal, complex, quotient, and dependency pins are unchanged; all work is
local-only.

## Checked Lean results

The public import `import Reisner` exposes, in namespace `Reisner.Complex`:

```lean
mem_stanleyReisnerIdeal_iff
  {V : Type u} (K : Reisner.Complex V) (k : Type v) [CommSemiring k]
  (f : MvPolynomial V k) :
  f ∈ K.stanleyReisnerIdeal k ↔ ∀ α ∈ f.support, α.support ∉ K.faces

faceRingBasis
  {V : Type u} (K : Reisner.Complex V) (k : Type v) [CommRing k] :
  Module.Basis K.faceExponents k (K.FaceRing k)

faceRingBasis_apply
  {V : Type u} (K : Reisner.Complex V) (k : Type v) [CommRing k]
  (α : K.faceExponents) :
  K.faceRingBasis k α =
    Ideal.Quotient.mk (K.stanleyReisnerIdeal k) (MvPolynomial.monomial α.1 1)
```

Here `faceExponents = {α : V →₀ ℕ | α.support ∈ K.faces}`. The basis is a
basis of the existing ideal quotient, with the stated monomial classes as
its vectors. The ideal remains independently defined by its squarefree
nonface generators. Its coefficient submodule is proved equal to the
polynomials supported on the complementary exponent set, and the two
support submodules are proved complementary.

`faceRing_algebraMap_injective` proves injectivity of `algebraMap k
(K.FaceRing k)` over every commutative ring. The instance
`faceRing_nontrivial` proves quotient nontriviality over every nontrivial
commutative ring, including every field. No finiteness of `V` is needed.
The empty face and ghost vertices are retained: the zero exponent has empty
face support, so constants survive even when the empty face is the only face.
The earlier monomial-membership theorem and its supporting proofs remain
checked.

The current weighted result, exposed from `import Reisner`, is:

```lean
Reisner.Complex.stanleyReisnerIdeal_isHomogeneous
  (K : Reisner.Complex V) (R : Type v) [CommSemiring R]
  {M : Type*} [AddCommMonoid M] (w : V → M) :
  letI : DecidableEq M := Classical.decEq M
  letI := MvPolynomial.weightedGradedAlgebra R w
  (K.stanleyReisnerIdeal R).IsHomogeneous
    (MvPolynomial.weightedHomogeneousSubmodule R w)

Reisner.Complex.weightedHomogeneousComponent_mem_stanleyReisnerIdeal
  (K : Reisner.Complex V) (R : Type v) [CommSemiring R]
  {M : Type*} [AddCommMonoid M] (w : V → M)
  {p : MvPolynomial V R} (hp : p ∈ K.stanleyReisnerIdeal R) (d : M) :
  MvPolynomial.weightedHomogeneousComponent w d p ∈ K.stanleyReisnerIdeal R
```

Both statements allow arbitrary ambient `V`, arbitrary weights (including
zero weights), and arbitrary additive commutative monoids, with no
nontriviality assumption on `R`. The checked identities
`Reisner.weight_fine_eq` and `Reisner.weight_one_eq_sum` identify the fine
weight with the exponent vector and unit weights with total degree. These
are polynomial-ring specializations. They do not construct the quotient
grading.

For quotient grading, all 20 declarations linked by `prop:grading` compile
over arbitrary `V` and commutative-ring coefficients `R`, including the
trivial ring. `weightedFaceRingComponent` is the span of standard basis
vectors in each weighted-degree fiber. These components are proved internal,
equal to images of the polynomial weighted submodules, and multiplicative;
`weightedFaceRingGradedAlgebra` packages the result. `faceRingFineGradedAlgebra`
and `faceRingTotalGradedAlgebra` give the fine and total structures. Fine
components are individual monomial spans or bottom for nonfaces; total
components are the standard basis spans and the supremum of their fine fibers.
Both zero components equal `span R {1}`. The actual degree-zero subalgebra
is `faceRingDegreeZeroSubalgebra`, with
`faceRingDegreeZeroEquiv : R ≃ₐ[R] ...` and a checked scalar-value formula.
No finite-vertex, purity, non-ghost, or nontrivial-coefficient hypothesis is
added.

## Previous changed files and artifacts: standard-basis milestone

| Files | Builder changes |
| --- | --- |
| `Reisner/StanleyReisner.lean` | Polynomial membership, explicit standard exponent set, ideal/submodule identification, complement theorem, actual quotient basis and value formula, scalar injectivity and nontriviality. |
| `Checks/Axioms.lean` | Types and axiom inspection for the new principal declarations and all new supporting declarations. |
| `blueprint/src/content.tex` | Checked `prop:basis`; distinct unformalized `prop:grading`; explicit grading dependencies for `prop:dimension` and `lem:localized`; refreshed formalization boundary and next steps. |
| `scripts/lean_source.py` | Recognize named instances so the nontriviality declaration has a source anchor. |
| `blueprint/web/`, `blueprint/print/print.pdf`, `blueprint/lean_decls`, `blueprint/dep_graph.{dot,svg,pdf}` | Regenerated blueprint, source links, declaration list and graph exports. |
| `STATUS.md`, `AUDIT.md`, `README.md` | Current formalization boundary, actual APIs, verification evidence and handoff. |

`Reisner.lean` already publicly imports the source module. `TASK.md` and all
dependency pins were preserved. This list and its verification counts record
the completed standard-basis stage; later milestones and current counts
follow below.

## Previous validation: standard-basis milestone (2026-11-16)

The following table records the completed preceding basis stage; its counts
are historical and are superseded by the current weighted-homogeneity
validation below.

| Check | Result |
| --- | --- |
| `lake env lean Reisner/StanleyReisner.lean` | Passed without warnings. |
| `lake build` | Passed: 1667 jobs, including the public import. |
| `lake env lean Checks/Axioms.lean` | Passed; every inspected declaration depends exactly on `propext`, `Classical.choice`, `Quot.sound`. Exact new-declaration output is in `AUDIT.md`. |
| Project Lean source scan | Three source files; zero matches for `sorry`, `admit`, `sorryAx`, or `axiom`. |
| `python3 scripts/blueprint.py pdf` | Passed; nine pages; final log has no warnings, undefined references, or overfull/underfull boxes. |
| `python3 scripts/blueprint.py web` | Passed using the real blueprint plugin and dependency graph. Optional `gs`/`pdf2svg` probes still report unavailable programs, as documented in the audit; generation succeeds. |
| `python3 scripts/blueprint.py checkdecls` | Passed for all 21 linked declarations. |
| `python3 scripts/lean_source.py` and `python3 scripts/export_graph.py` | Passed; all source anchors produced and DOT rendered to SVG/PDF. |
| Artifact consistency | 27 unique nodes; no cycles or missing dependencies. All 196 local HTML references and all 21 declaration anchors resolve; no duplicate HTML IDs. |
| Combined site build | Passed: 27 blueprint nodes and 21 validated declarations; both local pages generated. |
| Local site links/assets | Passed: 171 local links resolve; no remote asset requests. |
| Independent field-case type checks | Passed for arbitrary ambient `V`: the requested basis index, exact quotient-monomial values, polynomial membership, scalar injectivity, and quotient nontriviality. |
| Browser QA | Passed in Firefox at 1440- and 390-pixel viewport widths: basis declaration navigation, source expansion, copying without line numbers, graph links/zoom, search/status filters, empty state, and no page overflow. |

The basis-stage validation marked five blueprint nodes checked:
`def:complex`, `def:ring`,
`lem:indicator`, `thm:membership`, and `prop:basis`. The three implemented
lemma/theorem/proposition proofs also carry proof markers. `prop:grading`
has no Lean links or checked markers; fine grading and `A₀ = k` are still
unformalized.

## Remaining mathematical work

In the basis-stage snapshot, the next nodes were `prop:grading`,
`prop:dimension`, and `lem:localized`; the quotient grading has since been
formalized. The latter two explicitly depend on the grading node.
Dimension, graded localizations, the Cech calculation, purity, and both
directions of the criterion remain informal mathematics.

The larger missing comparisons remain visible: standard algebraic
Cohen–Macaulayness and its graded local test, local cohomology versus Cech,
depth detection and its dimension bound, augmented simplicial chains
including degree −1, and field duality. No future result is represented by
an axiom. There is no unresolved mathematical change or failed required
Builder validation.

## Previous Weber handoff: standard-basis milestone

The following line numbers and counts record the earlier basis-stage handoff;
the current site extractor uses declaration names and derives source line
anchors from the source file.

All eight new declarations are in `Reisner/StanleyReisner.lean`; source
anchors use `blueprint/web/lean/find/#doc/` followed by the full name below.
Line numbers are for the completed Builder source:

| Full declaration name | Line |
| --- | --- |
| `Reisner.Complex.mem_stanleyReisnerIdeal_iff` | 115 |
| `Reisner.Complex.faceExponents` | 156 |
| `Reisner.Complex.stanleyReisnerIdeal_restrictScalars_eq_restrictSupport` | 162 |
| `Reisner.Complex.isCompl_stanleyReisnerIdeal_faceSupport` | 169 |
| `Reisner.Complex.faceRingBasis` | 179 |
| `Reisner.Complex.faceRingBasis_apply` | 187 |
| `Reisner.Complex.faceRing_algebraMap_injective` | 201 |
| `Reisner.Complex.faceRing_nontrivial` | 223 |

The stable `prop:basis` node is now checked and links these declarations.
The new `prop:grading` node preserves the fine-grading and degree-zero
claims with dependencies `def:ring,prop:basis`. `prop:dimension` and
`lem:localized` explicitly use `prop:grading`. The graph now has 27 nodes
and the linked declaration list has 21 names. Blueprint HTML/PDF, graph
exports, and source anchors are current.

The local site now displays termwise polynomial membership and the actual
quotient basis, including the proof by complementary support submodules and
the checked monomial value formula. `site/build.py` recognizes the named
nontriviality instance and accepts wrapped axiom output. It embeds the basis
source excerpt and regenerates both the combined mathematics and full
blueprint pages. The site is local-only: nothing was registered, synchronized,
or published. Fine grading and degree zero remain visibly unformalized.

## Previous weighted-homogeneity milestone

The Builder finalized `lem:homogeneous` with four checked Lean links and
proof markers. The statement uses `Ideal.IsHomogeneous` for the genuine
weighted polynomial grading and includes component preservation. The proof
uses the actual squarefree nonface ideal span and does not use closure of the
face family; the chosen generators are the only complex-specific input.
At this historical stage `prop:grading` still retained quotient fine
grading, induced total grading, and `A₀ ≅ k` as an unformalized node
depending on `lem:homogeneous`, `prop:basis`, and `def:ring`.

Formalizer validation on 2026-11-16: `lake build` passed (1667 jobs),
`lake env lean Checks/Axioms.lean` passed, and the project Lean source scan
found no `sorry`, `admit`, or custom axioms. The four new declarations each
depend exactly on `[propext, Classical.choice, Quot.sound]`. Weber's
Its validation had 28 nodes, six checked nodes, and 25 declarations; those
counts and its 10-page PDF are historical and superseded by the current
quotient-grading build below.

Current Weber presentation changes are in `site/content/index.md`,
`site/build.py`, `site/README.md`, and generated `site/dist/` pages and source
snapshots. Root `README.md`, this status, and `AUDIT.md` were refreshed for
the new milestone. The blueprint source remains Builder-owned; Weber
regenerated only its derived HTML/PDF and graph/declaration artifacts.

## Previous quotient-grading milestone

Builder owns `blueprint/src/content.tex`; its finalized `prop:grading` is
checked and links 20 compiled declarations. Formalizer added quotient
components indexed by arbitrary weighted degrees using the existing
standard monomial basis. Basis-coordinate fibers give internal decompositions;
the components are identified with quotient images of polynomial weighted
submodules, and multiplication follows from the polynomial grading. Fine
and total graded algebras are constructed, with total degree proved to be the
coarsening of fine degree. Fine and total degree zero are each `span R {1}`;
the degree-zero subalgebra is algebra-equivalent to `R` by the scalar map.
Empty-face and ghost-vertex behavior is retained, and the results include
trivial commutative coefficient rings.

Formalizer validation on 2026-11-16: the source scan is clean, `lake build`
passed with 1667 jobs, and `Checks/Axioms.lean` reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies. Builder's
blueprint at that stage had 28 nodes and seven checked nodes; `checkdecls` accepted all 45
linked declarations. Its PDF had 11 pages and its log has no warnings,
unresolved references, or overfull/underfull boxes.

The historical site at that stage had 28 nodes, seven checked nodes, and 45
validated declarations. It resolved 216 local references, matched 1,264
displayed Lean lines, and had no remote asset requests. Its 11-page PDF was
clean. Historical root Firefox QA passed at desktop and mobile widths,
including source navigation, graph interaction, copying, search and status
filters, and page-overflow checks. That site showed the 563-line source,
17 proof blocks, and 28 graph links. These checks apply to the preceding
quotient-grading site; current augmentation artifacts are summarized below.


## Previous augmentation milestone and site integration

The checked `prop:augmentation` proves augmentation map/kernel/residue
algebra facts and finite type/Noetherianity under their stated assumptions.
Its site counts and historical Firefox results are superseded by the current
facet-primes milestone below. The full global and localized dimension
statements remain future work.

## Previous coordinate-prime and facet milestone

The checked `prop:facet-primes` covers coordinate ideals for arbitrary finite
subsets `F` of any ambient type. Termwise membership works over commutative
semirings; the coordinate-restriction kernel, surjective map, actual quotient
algebra equivalence, inside/outside variable values, prime ideal over domains,
and quotient ring dimension over fields are checked. The quotient has
`Nat.card F` dimension without requiring finite ambient `V`.

For `[Finite V]`, facets form a finite nonempty type and every face extends
to one. The actual generator-defined Stanley–Reisner ideal is the intersection
of facet coordinate ideals, with a termwise proof for arbitrary polynomials.
Every prime containing it contains one facet coordinate ideal. Ghost vertices
and the only-empty-face case are covered. These results do not establish the
global or localized dimension of the face ring; `def:dimension` and
`prop:dimension` remain unmarked.

Formalizer validation passed `lake build` (2170 jobs), the project source
scan found no placeholders, and the inspected new main declaration depends
only on `[propext, Classical.choice, Quot.sound]`. Blueprint generation has
30 nodes, nine checked nodes, and 85 declarations; its 14-page PDF has no
warning, overfull, underfull, or undefined-reference matches. Static site
checks resolve 301 local links and match 2,277 displayed source rows against
the 982-line Lean source; IDs are unique, there are no remote assets, and
source/document/PDF snapshots match. Independent root Firefox QA passed on
2026-11-17 at 1440- and 390-pixel viewport widths: coordinate-quotient source
expansion, facet-prime graph navigation, copying without line numbers, zoom,
search/status filters, empty results, and no page overflow. All 30 graph
links, 19 proof blocks, 982 full-source lines, and nine checked-node filter
results were present. Root also checked that the compiled source hashes and
all dependency pins are intact and both dimension nodes remain unmarked.

## Previous dimension milestone (2026-11-17)

The complete `prop:dimension` is checked. For any field `k` and finite ambient
vertex type `V`, the actual face ring and its localization at the augmentation
ideal both have Krull dimension `K.maxFaceCard`. The augmentation ideal has
that same height. Existing checked finite-type, Noetherian, maximality, and
residue-algebra results supply the other assertions of the proposition.
No purity, infinite-field, or no-ghost assumption was added.

`def:dimension` is checked as well: `vertices` records actual vertices,
`maxFaceCard` is the finite maximum over all faces, and integer-valued
`dimension` is that maximum minus one. A face and a facet attain the maximum.
The maximum is zero, and the simplicial dimension is minus one, exactly
when every ambient vertex is a ghost.

The global upper bound sends any prime chain over the Stanley–Reisner ideal
into a facet coordinate quotient. The lower bound constructs a coordinate
chain of length `F.card` for every face `F`, descends it through the actual
quotient, and identifies its final prime with the augmentation ideal.
The lower-chain and individual face height results do not require finite
ambient `V`. The localization-height theorem then proves the local equality.
The only-empty-face case gives both ring dimensions zero.

Changed source: `Reisner/StanleyReisner.lean`, `Checks/Axioms.lean`, and
`blueprint/src/content.tex`. Presentation and validation changes are in
`site/build.py`, `site/content/index.md`, `scripts/check_site.py`, both
READMEs, and `AUDIT.md`; generated blueprint/site artifacts were refreshed.
All dependency pins, `AGENTS.md`, and `TASK.md` are unchanged. Nothing was
pushed or published.

Validation passed: incremental Lean compilation; `lake build` (2170 jobs);
`lake env lean Checks/Axioms.lean`; zero project source-scan matches for
proof placeholders or custom axioms; blueprint PDF/HTML generation;
`checkdecls` (106 linked declarations); graph and source-anchor generation;
and the combined site build. All 21 new declarations report exactly
`[propext, Classical.choice, Quot.sound]`. The 14-page PDF has no warning,
undefined-reference, or overfull/underfull-box matches.

The site contains 30 blueprint nodes, 11 checked nodes, and 106 linked
declarations. Static validation resolves 330 local links and matches 2,844
displayed source rows to the 1,204-line Lean source; IDs are unique,
dependencies are acyclic, snapshots match, and there are no remote assets.
Firefox QA passed at 1440- and 390-pixel widths, including the new localized
dimension source link and dimension-node graph navigation, copying, zoom,
status/search filters, empty results, and no page overflow.

The next project-specific node is `lem:localized`: construct the graded
localizations and their monomial pieces. Cech/local-cohomology and depth
comparisons, augmented homology, link calculus, purity, and the full Reisner
criterion remain unformalized. The dimension proposition has no remaining
unproved assertion.

## Previous localization-kernel milestone (2026-11-17)

The new checked node `lem:localization-kernel` supplies necessary dependencies
of `lem:localized`. The full existing localized-piece statement is preserved
and remains unmarked: its integer grading, one-dimensional piece calculation,
and Laurent-monomial basis compatibility are not yet formalized.

`FaceRingLocalization R F` is the actual `Localization.Away` at the product
of the variable classes for a finite set `F`. Every element has a polynomial
numerator and a natural denominator power. For every commutative coefficient
ring, arbitrary ambient type, polynomial `p`, and denominator power `r`,
`faceRingLocalizationFraction_eq_zero_iff` proves that the fraction vanishes
exactly when every exponent in `p.support` has nonface support after joining
it with `F`. The kernel of the localization map is already killed by the
first power of the variable product.

Over nontrivial coefficients, a monic monomial fraction survives exactly
when its support joined with `F` is a face; the localization is nontrivial
exactly when `F` is a face. Inverting a nonface or ghost variable gives the
zero ring. Coefficients embed whenever `F` is a face, even with trivial
coefficients. The empty-product localization is algebra-equivalent to the
original face ring. Canonical coefficient-algebra transition maps for
`F ⊆ G` preserve base-ring images, satisfy identity and composition, and
have the checked numerator/denominator formula using `G \ F`.

Changed Lean source and axiom checks: `Reisner/StanleyReisner.lean` and
`Checks/Axioms.lean` (26 new inspected declarations). Builder updated
`blueprint/src/content.tex`; site integration updated `site/build.py`,
`site/content/index.md`, both READMEs, this status, and `AUDIT.md`, with all
generated blueprint/site artifacts refreshed. `AGENTS.md`, `TASK.md`, and
all dependency pins are unchanged. No push or publication was performed.

Validation passed: incremental source compilation, `lake build` (2170 jobs),
`Checks/Axioms.lean`, a zero-match project placeholder/custom-axiom scan,
blueprint PDF/HTML, `checkdecls`, graph export, source anchors, and the full
site build. All 26 new declarations report only
`[propext, Classical.choice, Quot.sound]`. The 15-page PDF has no warning,
undefined-reference, or overfull/underfull-box matches.

The site contains 31 blueprint nodes, 12 checked nodes, and 132 linked
declarations. Static checks resolve 370 local links and match 3,552 displayed
source rows against the 1,490-line Lean source. IDs are unique, dependency
edges are acyclic, snapshots match, and there are no remote assets. Firefox
QA passes at 1440- and 390-pixel widths, including the new fraction-criterion
source link and localization-node graph link, copying, filters, zoom, and
no page overflow.

Remaining: construct the full integer grading and prove the homogeneous
piece/basis statement of `lem:localized`, then the Cech, local-cohomology,
depth, augmented-homology, link, purity, and criterion comparisons.

## Current localized grading milestone (2026-11-18)

The complete `lem:localized` is checked. The actual variable-product
localization has an internal integer multigrading and a Laurent monomial
basis indexed by admissible degrees. For a field, an admissible component
has dimension one and a specified one-vector basis. Every inadmissible
component is zero. The canonical transition maps preserve degree and send
a source basis vector to its counterpart in an admissible target or to
zero in an inadmissible target.

Lean indexes this grading by `V →₀ ℤ`. For finite `V` these are all the
integer exponent vectors of the blueprint. The grading, ambient Laurent
basis, and transition formulas work over every commutative coefficient
ring and every ambient vertex type. The field hypothesis is used for
the vector-space dimension and one-vector component basis statements.

Builder prepared and finalized the blueprint using GPT-6.2 Astra with
extra-high reasoning. The Lean declarations, axiom checks, blueprint,
site sources, generated artifacts, and milestone documentation were
updated. See `AUDIT.md` for the proof APIs and validation.

At that earlier stage, the next node was `lem:cech-grading`. The differential
complex and its monomial basis-action prerequisite have since been checked;
the cohomology decomposition, positive-coordinate contraction, foundational
depth and local-cohomology comparisons, and Reisner's criterion remain future
work.

At the preceding localized-grading site build, validation passed for `lake build`,
axiom inspection, blueprint declaration checking, the static site checker, and
Firefox at desktop and mobile widths. Those browser results predate the
localization-kernel audit update; root performs current QA separately.


## Localization-kernel audit and proof cleanup (2026-11-18)

This audit preserves the checked `lem:localization-kernel`, the full checked
`lem:localized`, and the dimension results. Four existing localization proofs
were simplified without changing theorem types or coefficient hypotheses; the
Lean source was reduced by 17 lines. The key criterion remains termwise over
all commutative coefficient rings: some power annihilating a fraction numerator
is equivalent to one product factor doing so because squarefree exponent shifts
are injective and preserve coefficients. The generic localization statement
still only supplies some power.

`Checks/LocalizationKernelAudit.lean` is a compiled regression file, not a new
blueprint node. It checks zero numerators; an `x` monomial surviving because its joined
support is a face; the nonzero face-ring class of `y` killed because its
joined support with the inverted variable is a nonface; nonface/ghost
localizations; the nonreduced `ZMod 4` squarefree case; scalar
injectivity and a monic constant fraction over trivial coefficients; and the
empty-product equivalence. It also exhibits `Away (2 : ZMod 4)`, where `2²=0`
but `2*1≠0`, so a general localization does not satisfy a first-power rule.
The site downloads and compiles this file and checks all 13 named regression
axiom reports against the standard axiom set, allowing subsets.

The final build passed `python3 site/build.py`, including `lake build`,
`Checks/Axioms.lean`, and `Checks/LocalizationKernelAudit.lean`; blueprint PDF,
HTML, `checkdecls`, and graph generation succeeded. The PDF has 16 pages and
no warning, overfull, underfull, or undefined-reference matches.
`python3 scripts/lean_source.py` and `python3 scripts/check_site.py` passed:
31 nodes, 13 checked, 159 declarations, 408 local links, and 4,343 displayed
Lean rows all match the current 1,953-line source. IDs are unique, graph
dependencies acyclic, remote assets absent, and source/PDF/graph snapshots
match. The regression source is included in the download and snapshot audit.
Root Firefox QA passed on the regenerated site: desktop 1440-pixel and mobile
390-pixel layouts have no overflow. It verified the localization theorem and
regression-download source links, `lem:localization-kernel` graph navigation,
source expansion/copying, search and status filters, empty results, and zoom.

## Current finite Čech-complex milestone (2026-11-19)

The checked `lem:cech-complex` milestone constructs a genuine finite
`ℕ`-indexed `CochainComplex` in `ModuleCat R`. In degree `q`, its terms are
the dependent product (canonically equivalent to the finite direct sum) of
the actual variable-product localizations indexed by every `q`-element
subset of the finite ambient vertex type. The empty subset supplies degree
zero; nonfaces and sets containing ghost vertices remain indexed and have
their actual zero localizations. The ordered differential uses the sign
`(-1)^(# {u ∈ G | u < v})` and the canonical localization transition map.

Lean exposes `Reisner.Complex.cechComplex` and `cechComplex_d`, with the
square-zero theorem `cechDifferential_comp_eq_zero`. The differential
preserves every fine integer degree, with `cechDegreeSubmodule` defined as
the coordinatewise `Submodule.pi Set.univ`; `cechDifferential_maps_degree`
and `cechDifferentialDegree` provide the preservation and restriction. The
finite dependent product is identified with the direct sum by
`cechCochainDirectSumEquiv`. The principal complex, differential,
square-zero, and degree declarations report only
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.

The full `lem:cech-grading` statement remains intact and unmarked. Its
degreewise cohomology decomposition, positive-coordinate contraction,
link-cohomology formula, and comparison with local cohomology remain future
work. The checked termwise module decomposition does not claim the cohomology
decomposition. `Checks/Cech.lean` checks the public declarations and the empty-ambient,
ghost-singleton, ordinary-face, and monomial-action cases.

## Checked Čech monomial action (2026-11-19)

The new checked blueprint node `lem:cech-basis-action` formalizes the
differential action on a coordinate monomial cochain. In addition to the
admissibility hypothesis at the source subset, the conclusion is the full
cochain equality in the actual product over all subsets. It includes every
insertion target; the localization API proves inadmissible target monomials
zero. The sign is the count of source vertices below the inserted vertex.
`lem:cech-grading` keeps its complete statement and remains unmarked; the
degreewise cohomology decomposition, contraction, link formula, and local
cohomology comparison are future work.

`Reisner.Complex.cechDifferential_monomialCochain` is linked alongside the
index and coordinate-cochain definitions. The axiom audit and finite Cech
regressions include this theorem and the empty ambient, ghost singleton, and
ordinary face cases. Validation passed: `lake build` completed 2,365 jobs;
`Checks/Axioms.lean` and `Checks/Cech.lean` both exited successfully, and the
principal theorem reports `[propext, Classical.choice, Quot.sound]`. Blueprint
PDF/HTML, `checkdecls`, source anchors, and graph export succeeded; the PDF is
17 pages. `python3 site/build.py` and `python3 scripts/check_site.py` passed.
The generated site contains 33 nodes, 15 checked nodes, and 178 declarations.
The static check resolves 459 links and validates 5,136 source rows across
the 1,953-line face-ring source and 397-line Cech source; IDs are unique,
dependencies are acyclic, snapshots match, and no remote assets are used.
Lean emitted three unused-section-variable and five unused-simp-argument
warnings in `Reisner/Cech.lean`; no compilation errors occurred.

## Checked termwise Čech degree decomposition (2026-11-19)

The new checked node `lem:cech-termwise-decomposition` proves the internal
direct-sum decomposition of each cochain module into the coordinatewise
fine-degree submodules. The public basis
`cechCochainMonomialBasis R q` is the dependent-product basis indexed by
`Σ F : CechIndex V q, K.localizationDegrees F.1`. The main result is
`cechDegreeSubmodule_isInternal R q`, whose Lean signature additionally has
`[DecidableEq V]`; this can be supplied classically for any finite ambient
type. It requires no field or nontriviality hypothesis on `R`.

`Checks/Cech.lean` checks the basis and internal-sum theorem, including the
empty ambient, ghost singleton, and ordinary singleton edge cases. The full
`lem:cech-grading` statement remains intact and unmarked. The checked result
decomposes cochain modules only; the direct-sum decomposition of cohomology,
positive-coordinate contraction, link formula, and local-cohomology
comparison remain future work.

Validation passed for this milestone: `lake build` (2,365 jobs),
`lake env lean Checks/Axioms.lean`, `lake env lean Checks/Cech.lean`,
`leanblueprint checkdecls` via `python3 scripts/blueprint.py checkdecls`,
blueprint PDF/HTML generation, source-anchor and graph export,
`python3 site/build.py`, and `python3 scripts/check_site.py`. The principal
internal-sum theorem reports `[propext, Classical.choice, Quot.sound]`.
The generated site has 34 nodes, 16 checked nodes, and 181 linked
declarations. Its static check verifies 473 local links and 5,345 displayed
source rows from the 1,953-line face-ring file and 526-line Cech file;
snapshots match, dependencies are acyclic, IDs are unique, and there are no
remote assets. Lean emits three unused-section-variable and five
unused-simp-argument warnings in `Reisner/Cech.lean`.
