# Milestone status

## Full statement of Reisner's criterion

`Reisner.Complex.reisner_criterion` compiles and is exported by `Reisner`.
Its right-hand side, `LinkHomologyVanishesBelowDimension`, uses integer
reduced homology of every face link over the field, including the link of
the empty face. For the complex consisting of the empty face alone, the
link has dimension `-1` and the required groups are all in degrees below
`-1`. The statement permits any number of ghost vertices.

The criterion's proof is open. Its single `sorry` is in
`Reisner/ReisnerCriterion.lean`. Direct `#print axioms` inspection reports
`[propext, sorryAx, Classical.choice, Quot.sound]` for the theorem and
`[propext, Classical.choice, Quot.sound]` for the linkwise predicate. The
blueprint node `thm:reisner` links to the declaration and retains its open
proof status.

## Previously checked milestones

One checked intermediate theorem is
`faceRingLocalCohomologyIsoGeneratorPowerExtColimit` in
`Reisner/Cech/ExtComparison.lean`. In every cohomological degree `q`, it
identifies augmentation-supported local cohomology of the face ring `A`
with the colimit of derived `Ext^q_A(A / J_n, A)`, where
`J_n = (x_v^n : v ∈ V)`. Both quotient diagrams are cofinal through the
category of ideals whose radical contains the augmentation ideal. The
checked ideal bounds are `J_n ≤ m^n` and `m^(|V|*n+1) ≤ J_n`.
Only finite generation of the augmentation ideal is used, so the result
allows arbitrary commutative coefficient rings, the zero ring, ghost
variables, and an empty vertex set. For empty `V`, all `J_n` are zero,
even at `n = 0`. This theorem normalizes the Ext stages; the remaining
Koszul or acyclic-resolution bridge and positive-degree Ext–Čech
comparison are not yet formalized.

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
cochain module by fine degree are now checked. Homogeneous projections commute
with the differential and characterize cocycles and homogeneous boundaries.
The inclusion-induced direct-sum decomposition of actual Čech cohomology by
fine degree is checked, including the cycles-modulo-boundaries comparison.
Each degree subcomplex with a positive coordinate is contractible and has
zero cohomology. Nonpositive admissible indices correspond to faces of the
link of the negative support, and nonface negative support gives a zero
degree complex. The actual-face augmented simplicial cochain complex is
checked through its signed deletion differential and square-zero law,
empty-face scalar term, coordinate-basis value formula, no-actual-vertex
differential case, and zero modules above the ambient cardinality. The
coordinate formula for basis insertion and the degree-minus-one cohomology
endpoints are checked. Its integer reindexing, natural/integer restriction and
homology isomorphisms, and low/high term and cohomology cutoffs are checked.
The signed termwise comparison between nonpositive Čech degree modules and
augmented link cochains is checked, including explicit inverse/component
formulas and adjacent-differential compatibility over arbitrary commutative
rings. The actual zero-extended shifted link complex, its isomorphism with the
Čech degree complex, and induced actual homology identification are checked,
including the separate below-cutoff zero case and integer reduced degree
`r-1`. The cutoff equivalence between total Čech vanishing and reduced link
cohomology vanishing is also checked over arbitrary commutative rings. The
augmented chain model and canonical integer-indexed homology-cohomology
duality over fields are checked, as is the Čech purity-and-link criterion in
integer reduced homology. The positive-degree Čech-to-local-cohomology
comparison and the full Reisner criterion remain future work. The completed
time-boxed local algebra milestone is the depth
cutoff theorem: for every finite `d`, depth is at least `d` iff local
cohomology vanishes below `d`. At `d = dim(B)`, this gives the depth
lower-bound half of the local Cohen--Macaulay criterion; the standard depth
upper bound remains a separate prerequisite for equality. The project model
uses the derived-category Ext groups used by depth and does not claim a Lean
comparison with Mathlib's older left-derived Ext implementation in its
`localCohomology` constant. This route does not require the graded Čech
comparison or the combinatorial tail. The aligned Ext-colimit diagram,
positive-power stage vanishing, and one-way theorem
`depthExtLocalCohomology_vanishes_below_depth` compile in the project. The
converse is formalized too: `le_depth_iff_localCohomology_vanishes` proves
the finite-cutoff equivalence for every commutative Noetherian local ring,
with no extra smallness hypothesis. Its proof extracts the depth degree,
proves the depth-stage Ext group nonzero, and shows the class survives the
powers colimit. Each adjacent transition is injective: its kernel is the
kernel of `B/m^(n+1) → B/m^n`, finite and supported on `V(m)` because `m`
annihilates it. Rees gives lower Ext vanishing; degree zero uses epi
precomposition. The colimit representative theorem then transports the
nonzero class. The local algebra cutoff target is complete; the graded
Čech-to-local-cohomology comparison, link formula, and full Reisner criterion
remain future work. The separate right-derived-functor conversion is not
claimed. The next degree-zero bridge has started: the checked theorem
`principalLocalization_kernel_iff_torsion` identifies the kernel of
`LocalizedModule.mkLinearMap (.powers f)` with elements killed by some power
of `f`. The checked equivalence
`depthExtLocalCohomology_extZero_quotientHomEquiv` identifies each derived
Ext-zero quotient stage with its ordinary module of linear maps, and
`depthExtQuotientHomTorsionEquiv` identifies maps from `R/J` with elements
annihilated by `J`. Thus the degree-zero stages are concretely the expected
annihilator submodules. The checked lemma
`depthExt_zero_precomp_naturality` shows that degree-zero Ext transition maps
become ordinary precomposition. The checked theorem
`depthExtLocalCohomology_transition_torsion_natural` verifies that the actual
powers-diagram transitions become inclusions of annihilator submodules, and
`principalPowerTorsion_eq` identifies the principal-ideal stages with the
submodules killed by `f^n`, including `n = 0`. The general theorem
`depthExtLocalCohomology_zero_torsionSupEquiv` identifies degree-zero
Ext-colimit local cohomology for any ideal with the supremum of its power
annihilator stages. The principal specialization
`principalExtZeroKernelEquiv` then proves, for every ring, module, and `f`
(including `f = 0`), a linear equivalence with the kernel of localization at
powers of `f`.

Current validation (2026-11-24): `python3 site/build.py` passed, including
`lake build` (2,741 jobs), axiom inspection, localization-kernel regression,
Čech and simplicial-cochain checks, blueprint PDF/HTML generation, and
`checkdecls`. `python3 scripts/check_site.py` passed with 66 blueprint nodes,
52 checked nodes, 370 linked declarations, 876 local links, and 11,813
displayed source rows across 13 Lean modules. Snapshots match, IDs are
unique, dependencies are acyclic, and there are no remote assets. The PDF
log has no box or LaTeX warnings. The static checker does not substitute for
browser QA.

## Checked links and nonpositive Čech indices

`Complex.link` defines the same-ambient link of a face, including the empty
link face, ghost vertices and the facet case. For nonpositive `a`, the
negative support `N` is finite, and admissible subsets are exactly faces
containing `N`. If `N` is a face, `nonpositiveCechIndexEquivLink` identifies
admissible `q`-element indices with link faces `T` satisfying
`N.card + T.card = q`. If `q < N.card`, the degree submodule is zero; if `N`
is a nonface, all terms and cohomology of the degree complex are zero over
any commutative ring. The shifted identification with augmented reduced
cochains and the uniform Čech/link-cohomology cutoff theorem are checked.
Comparison with Ext-colimit local cohomology and Reisner's criterion remain
future work.

Local site generation passed Lean, axiom, localization and Čech checks,
blueprint PDF/HTML generation, `checkdecls`, and source/graph exports. The
site checker verified 37 blueprint nodes, 22 checked nodes, 268 declarations,
606 local links and 7,178 displayed source rows, with matching snapshots,
unique IDs, acyclic dependencies and no remote assets.

## Checked positive-coordinate contraction

For finite linearly ordered `V`, an arbitrary commutative ring `R` and a
fine degree `a` with `0 < a p`, `cechPositiveContractingHomotopy` constructs
a homotopy between the identity and zero on `cechComplexDegree R a`.
The signed removal formula, degree-zero and successor identities, and
cohomology vanishing are checked. This includes zero coefficients, ghost
vertices, and the top and empty cochain degrees. The link formula and the
comparison with local cohomology remain future work.

The local site build passed the Lean build, axiom inspection, localization
and Čech regressions, blueprint PDF/HTML generation, declaration checks and
source and graph exports. The site checker verified 36 blueprint nodes,
20 checked nodes, 243 linked declarations, 566 local links, and 6,716
displayed source rows, with matching snapshots and no remote assets.

## Checked Čech cohomology decomposition

For every cochain degree, the direct sum of the homology objects of the
fine-degree subcomplexes is linearly equivalent to the homology of the
existing Čech complex. The equivalence is induced by subcomplex inclusions;
its inverse components are induced by projections and have finite support
bounded by the support of a representative cocycle. The homology objects
are also identified with the usual quotient of cycles by boundaries, and
the incoming boundary in degree zero is zero. The result allows arbitrary
commutative rings, empty vertex sets, ghosts and nonfaces. Čech-to-local
cohomology comparison and Reisner's criterion remain future work.

The local site build passed Lean compilation, axiom and regression checks,
blueprint PDF/HTML generation, declaration checks and graph export. The site
checker verified 36 blueprint nodes, 19 checked nodes, 224 linked declarations,
540 local links and 6,187 displayed source rows. IDs are unique, dependencies
are acyclic, snapshots match and there are no remote assets.

## Checked Čech cycle and boundary components

The checked node `lem:cech-cycle-boundary-components` constructs the
canonical projections to the fine-degree submodules. Each cochain is the
finite sum of its projections; a projection is the identity on its own
degree and zero on the others. The projections commute with the restricted
Čech differential. Thus a cochain is a cocycle exactly when all its
components are cocycles, and every homogeneous boundary in degree `q + 1`
has a primitive of the same fine degree. Degree zero has no incoming term.
These results use arbitrary commutative rings and the actual localization
coordinates, including the empty subset and nonfaces. The cohomology
isomorphism has since been constructed in the next milestone.

The local site build passed its Lean build, axiom inspection, localization
and Čech checks, blueprint generation and declaration checks. Its static
check reports 35 blueprint nodes, 17 checked nodes, 191 linked declarations,
494 local links, and 5,567 displayed source rows, with matching snapshots,
acyclic dependencies, unique IDs, and no remote assets.

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
The build retains eight existing unused-section-variable and unused-simp
linter warnings in `Reisner/Cech.lean`; the new simplicial cochain source
emitted none.
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

## Checked augmented face-cardinality cochains (2026-11-21)

The checked nodes `lem:augmented-cochain-complex`,
`lem:augmented-basis-insertion`, and `lem:augmented-cohomology-minus-one`
formalize actual cochain modules indexed by faces of each cardinality and package the signed
deletion maps as a `CochainComplex (ModuleCat R)`. Its proof of
`simplicialDifferential_comp_eq_zero` pairs the two orders of deleting each
pair of distinct vertices; the signs are additive inverses, with no division
by two. The construction works for arbitrary commutative-ring coefficients,
including characteristic two and the zero ring.

The checked API includes the product/direct-sum equivalence, coordinate
basis, deletion formula, basis-coordinate value formula, and the coordinate
criterion for signed insertion on a basis vector. The unique
cardinality-zero face gives `simplicialCochainZeroEquiv` to `R`, and the
differential has constant value on actual singleton faces. If there are no
actual vertices, `simplicialDifferential_zero_of_no_vertices` proves the
outgoing map is zero. Cochain modules above `Fintype.card V` are actual zero
objects. Empty ambient sets, ghosts, characteristic two, the zero ring, and
high-cardinality cases are compiled in `Checks/SimplicialCochain.lean`.

At this milestone, `lem:augmented-cochains` is checked for integer
reindexing, restriction/homology isomorphisms, and low/high cutoffs. Higher-
degree cohomology vanishing, full reduced homology and order comparison, and
the Čech/link and local-cohomology comparisons remain future work, as does
the full criterion.

Validation passed on 2026-11-22: `lake build` completed 2,454 jobs;
`Checks/Axioms.lean`, `Checks/Cech.lean`, `Checks/SimplicialCochain.lean`,
and the localization-kernel regression all passed in the site build. The
principal square-zero and cochain-complex declarations report exactly
`[propext, Classical.choice, Quot.sound]`. Blueprint PDF/HTML generation,
`checkdecls`, combined source anchors, and graph export succeeded.
At the signed-coordinate milestone, `python3 scripts/check_site.py` reported
41 blueprint nodes, 26 checked nodes, 310 declarations, 689 local links, and
8,398 displayed source rows. IDs are unique,
dependencies are acyclic, snapshots match, and no remote assets are used.
## Checked integer reindexing and cohomology cutoffs (2026-11-22)

The checked node `lem:augmented-cochains` extends the face-cardinality
complex to integer reduced degrees using `ComplexShape.embeddingUpIntGE (-1)`.
The integer term at degree `i ≥ -1` corresponds to natural cardinality
`n=(i+1).toNat`, with the cast identity proving `(n : ℤ)-1=i`; terms below
`-1` are zero. Restriction along the embedding recovers the original natural
complex, and `simplicialCochainComplexIntHomologyIso` identifies their actual
homology objects in corresponding degrees.

The module and homology cutoffs are both checked: they vanish below `-1` and
above `(Fintype.card V : ℤ)-1`. The natural-indexed homology also vanishes
for `n>Fintype.card V`. The degree-minus-one `R`/zero endpoint results are
transported to the integer complex. These are cutoff results only; vanishing
in intermediate higher degrees is not claimed. The augmented chain model,
order-independence, cohomology duality, Čech/link and local-cohomology
comparisons, and the Reisner criterion remain future work.

## Checked signed Čech/link coordinates (2026-11-22)

For nonpositive `a` whose negative support `N` is a face, the actual
fine-degree Čech module at `N.card + r` is linearly equivalent to the
link's actual cochains on `r`-element faces. The map extracts Laurent
coefficients and multiplies by the explicit negative-support orientation
sign. The inverse, basis and component formulas, and compatibility with
adjacent differentials are checked over arbitrary commutative rings.

The first map includes the empty link face. Invalid insertion coordinates
vanish in their actual localizations, while admissible targets are exactly
link faces. Ghosts, empty supports, characteristic two and the zero ring
are retained. The separate checked node
`lem:cech-link-cohomology-comparison` packages the map as an actual shifted
complex isomorphism and transports homology to reduced link cohomology in
integer degree `r-1`; degrees below the cutoff are zero. The local-cohomology
comparison and full link formula remain future work.

Validation for this milestone passed: full `lake build` (2,454 jobs),
`Checks/Axioms.lean`, `Checks/Cech.lean`, `Checks/SimplicialCochain.lean`,
and the existing localization regression; blueprint PDF/HTML and
`checkdecls`; combined source/graph and local site regeneration; and the
static site checker. The equivalence and differential theorem report
exactly `[propext, Classical.choice, Quot.sound]`. Source scans find no
placeholders or custom axioms. The current artifact counts are reported
above. All work remains local.

## Finite-generator degree-zero localization (2026-11-24)

The finite-generator extension is now checked over arbitrary commutative rings
and modules. `Reisner.finiteGeneratorsLocalizationKernel_eq_powerTorsionSup`
identifies the union of the submodules annihilated by powers of
`Ideal.span (f '' s)` with the intersection of kernels of localization at
each listed generator. The proof chooses a killing exponent for each
generator and uses the explicit bound `1 + ∑ k_i`; this includes the empty
index set, zero generators, and exponent zero. The public equivalence
`Reisner.finiteGeneratorsExtZeroLocalizationKernelEquiv` composes this with
the existing degree-zero Ext-colimit-to-supremum theorem.

The statements are algebraic localization-kernel comparisons. They do not
yet identify the Ext-colimit construction with the project's Čech complex and
make no claim in positive cohomological degrees. Validation passed: `lake
build` (2,650 jobs), `Checks/Axioms.lean`, site generation, and
`scripts/check_site.py`. Both new theorems report only
`[propext, Classical.choice, Quot.sound]`. The site has 56 blueprint nodes,
42 checked nodes, 356 linked declarations, and 802 local links. `git diff
--check` passes; changes remain local.

## Degree-zero Čech cocycle kernel (2026-11-24)

`Reisner.Complex.cechZeroCyclesLocalizationEquiv` now identifies the actual
kernel of the degree-zero Čech differential with the simultaneous kernel of
the face-ring maps to the singleton localizations. The module also proves the
componentwise differential formula and that vanishing of the differential is
equivalent to vanishing under every singleton localization map. The proof
keeps the extended Čech index set, including ghost vertices and nonfaces, and
works over arbitrary commutative coefficient rings.

The subsequent Ext composition is recorded below. The cycle-kernel theorem
depends only on `[propext, Classical.choice, Quot.sound]` and is covered by
the full `lake build` and axiom checks.

## Degree-zero Ext-to-Čech cycles (2026-11-24)

`Reisner.Complex.extZeroCechCyclesEquiv` now composes the finite-generator
Ext/localization-kernel equivalence with the checked Čech cycle-kernel
equivalence. It identifies the degree-zero Ext-colimit local cohomology module
for the face ring supported at the augmentation ideal, after restricting
scalars to the coefficient ring, with the kernel of the outgoing degree-zero
Čech differential. The construction is valid over arbitrary commutative
coefficient rings, including the zero ring.

The equivalence depends only on `[propext, Classical.choice, Quot.sound]`.
The subsequent homology identification is recorded below. Positive-degree
Ext/Čech comparison is still open.

## Degree-zero Ext-to-Čech cohomology (2026-11-24)

`Reisner.Complex.extZeroCechCohomologyEquiv` identifies the face ring's
degree-zero Ext-colimit local cohomology at the augmentation ideal with
`HomologicalComplex.homology (K.cechComplex R) 0`, as an `R`-module after
restricting scalars along `R → K.FaceRing R`. The proof identifies the concrete
outgoing kernel with the categorical cycles object by its universal property,
then uses the natural-number cochain shape: the incoming differential at zero
vanishes, so taking the cohomology class is an isomorphism. This works over
arbitrary commutative coefficient rings, including the zero ring.

Both new equivalences depend only on `[propext, Classical.choice, Quot.sound]`.
Full `lake build` (2,652 jobs), `Checks/Axioms.lean`, site generation, and
`scripts/check_site.py` passed. The site has 59 blueprint nodes, 45 checked
nodes, 360 linked declarations, and 819 local links. Positive-degree
Ext/Čech comparison remains open. Changes remain local.

## Augmentation-local CM cutoff (2026-11-24)

`Reisner.Complex.faceRing_atAugmentation_depth_le` proves that for a finite
complex over a field, the depth of the face ring localized at its augmentation
ideal is at most the maximum face cardinality. The proof takes the supremum
over regular-sequence lengths and uses the regular-sequence Krull-dimension
formula. The companion theorem
`faceRing_atAugmentation_depth_eq_iff_localCohomology_vanishes` packages the
existing local Ext-colimit cutoff theorem with the checked local dimension
formula: local depth equals local Krull dimension exactly when maximal-ideal
Ext-colimit local cohomology vanishes below that dimension. This is the
standard local algebraic CM condition and is independent of any link or
homology criterion.

Both results assume a field and finite ambient vertex type and use only
`[propext, Classical.choice, Quot.sound]`. Full `lake build` (2,739 jobs),
`Checks/Axioms.lean`, site generation, and the static site checker passed. The
site has 61 blueprint nodes, 47 checked nodes, 362 linked declarations, and
835 local links. The remaining bridge to
Reisner is the graded local test transferring global algebraic
Cohen–Macaulayness to the augmentation localization, followed by the link
cohomology vanishing comparison.

## Graded maximal-ideal reduction (2026-11-24)

`Reisner.IsLocalCohenMacaulay` uses the standard local definition
`depth = ringKrullDim`; `Reisner.IsCohenMacaulay` requires every prime
localization to satisfy it. For a face ring over a field, the total grading's
irrelevant ideal equals the augmentation ideal, every proper homogeneous ideal
lies inside it, and it is the unique maximal proper homogeneous ideal.
`faceRing_homogeneousMaximal_cm_iff_localCohomology_vanishes` identifies
Cohen–Macaulayness at all maximal homogeneous ideals with the checked
augmentation-local vanishing criterion. The theorem
`faceRing_localCohomology_vanishes_of_isCohenMacaulay` proves the forward
implication from global algebraic Cohen–Macaulayness to that local vanishing.

This uses only `[propext, Classical.choice, Quot.sound]`. Full `lake build`
(2,740 jobs), `Checks/Axioms.lean`, site generation, and the static site
checker passed. The site has 64 nodes, 51 checked nodes, 369 linked
declarations, and 865 local links. The converse graded-local transfer from
maximal homogeneous localizations to arbitrary prime localizations remains
external. Positive-degree Ext–Čech/link comparison also remains open.

## Localization-transfer audit (2026-11-24)

The next attempted bridge is the converse graded-local transfer. Mathlib's
`RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalization_of_mem`
localizes regular sequences, but the pin has no standard Cohen–Macaulay
localization theorem or depth/height inequality
`depth(R) ≤ depth(R_p) + dim(R/p)` for a Noetherian local ring. The latter,
or an equivalent grade/height result, is what the usual proof of CM stability
under localization needs; its associated-prime/depth lemmas are absent too.
The homogeneous-core argument identifies how the graded maximal test would
reduce to ordinary localization stability, but does not itself prove that
stability. No theorem was added and no checked claim was broadened. The next
formalization task is to establish the depth inequality from pinned APIs, or
to keep this transfer external and proceed to the local-cohomology/link
comparison.

## Graded-local transfer handoff (2026-11-24)

The converse transfer from augmentation-local Cohen--Macaulayness to all
prime localizations is recorded as an external foundation in the blueprint.
Stacks Project Lemma 10.104.5 (tag 00NB) gives the localization theorem for
Cohen--Macaulay local rings; Bruns--Herzog 2.1.27 supplies the graded local
test. No Lean declaration was added for this transfer, and the unavailable
depth/height bridge remains unformalized.

The next active target is the Ext-colimit/extended-Čech comparison feeding
the already checked fine-degree link calculation. Its degree-zero instance
`extZeroCechCohomologyEquiv` is checked. Positive degrees and the grading
compatibility are not. Mathlib's pinned local-cohomology file lists this
comparison as future work and has no Koszul or weak-proregularity API; a
formal proof would first need that infrastructure. The blueprint records
Schenzel's weak-proregularity route, including the arbitrary coefficient-ring
and empty-vertex edge cases. No positive-degree comparison is claimed here.

## Uniform Čech and link-cohomology vanishing (2026-11-24)

`Reisner.Complex.cechCohomology_vanishes_iff_linkCohomology_vanishes` proves,
for every finite linearly ordered ambient vertex type, simplicial complex,
commutative coefficient ring, and finite cutoff `d`, that actual Čech
cohomology vanishes in all degrees below `d` exactly when each link's
augmented reduced cohomology vanishes in degree `r - 1` whenever
`|F| + r < d`. The proof uses the checked fine-degree direct-sum
decomposition, positive-coordinate contraction, zero cases for nonface
negative support and below-cutoff terms, and the shifted link cohomology
isomorphism. It covers `d = 0`, the empty face, ghost vertices, and reduced
degree `-1` without a field hypothesis.

This is a theorem about the project's actual Čech complex. It does not assert
the positive-degree Ext-colimit/Čech comparison or change link cohomology to
homology. The all-degree comparison and the graded-local Cohen--Macaulay
transfer remain external foundations. The new theorem reports only
`[propext, Classical.choice, Quot.sound]`. Validation passed: `lake build`
(2,741 jobs), `python3 site/build.py`, and `python3 scripts/check_site.py`
(66 nodes, 52 checked, 370 declarations). The task tracker now points to
finite-dimensional homology–cohomology duality (`lem:dual`) as the next node.

## Duality prerequisite in progress (2026-11-24)

Pinned Mathlib provides abstract alternating face-map chain/cochain
constructions and finite-dimensional vector-space duality, but no directly
matching simplicial-complex model with this project's actual-face and
augmented degree `-1` conventions. The checked project cochain complex does
have a coordinate basis indexed by actual faces. Added and focused-compiled
the prerequisite that each cochain term over a field is finite-dimensional,
with dimension exactly the number of actual faces of that cardinality. The
empty face is counted in cardinality zero; ghosts contribute no coordinates.
The new declarations report only `[propext, Classical.choice, Quot.sound]`.
Validation passed: focused compilation, `lake build` (2,742 jobs),
`Checks/Axioms.lean`, `python3 site/build.py`, and `python3 scripts/check_site.py`
(68 nodes, 54 checked, 379 declarations, 894 local links). `git diff --check`
also passed. The augmented chain complex is now constructed as the linear
dual of the checked cochain complex, with the actual-face basis, dual signed
boundary, chain-complex law and basis evaluation formula. Its new declarations
also include the canonical evaluation isomorphism from cochains to dual chains
and its differential naturality. They report only `[propext, Classical.choice,
Quot.sound]`. Homology duality remains open.

## Integer reduced duality and the homological Čech criterion (2026-11-24)

`simplicialCohomologyIntDualHomologyEquiv` now canonically identifies
integer reduced cohomology with the linear dual of integer reduced homology
over every field. At `i ≥ -1` it transports the checked face-cardinality
evaluation isomorphism through the existing chain and cochain extension
homology isomorphisms, using natural index `(i + 1).toNat`. The explicit
reindexing equation records this construction. Below `-1` both groups are
zero. Cochain and chain terms and homology vanish above the actual dimension
`maxFaceCard - 1`; the ambient `|V| - 1` chain bounds are checked as well.
The augmented degree `-1`, empty complex and ghost vertices are preserved.

`simplicialCochainInt_homology_isZero_iff_chainInt_homology_isZero` derives
the integer vanishing equivalence from the canonical isomorphism.
`cechCohomology_vanishes_iff_linkHomologyInt_vanishes` states the uniform
cutoff for all integer reduced link degrees: `|F| + i + 1 < d`.
`cechCohomology_vanishes_iff_pure_and_linkHomology_vanishes` presents the
checked Čech purity criterion in integer reduced homology, retaining the
exact facet-cardinality purity conjunct and each link's own dimension bound.
No graph-connectivity assumption or conclusion is added. The graph
comparison is a separate unformalized blueprint node.

Validation passed: focused `lake build Reisner.Cech.LinkHomology` (2,656
jobs), full `lake build` (2,747 jobs), `lake env lean Checks/Axioms.lean`,
`python3 site/build.py`, `python3 scripts/check_site.py`, and `git diff
--check`. The axiom inspection confirms the new duality and cutoff theorems
use only `[propext, Classical.choice, Quot.sound]`. The site has 74 blueprint
nodes, 61 checked nodes, 411 linked declarations, 960 local links, and 12,883
displayed source rows across 19 linked Lean files.
The positive-degree Ext-colimit/Čech comparison, graded-local transfer and
the full algebraic Reisner criterion remain unformalized.

## Generator-power stages for Ext-colimit local cohomology (2026-11-24)

`Reisner/Cech/ExtComparison.lean` proves that the augmentation-supported
derived Ext-colimit for a finite face ring can be computed from the
individual-variable power quotients
`A/(x_v^n : v ∈ V)` in every cohomological degree. The ideal bounds are
`(x_v^n) ≤ m^n` and `m^(|V|*n+1) ≤ (x_v^n)`. Initiality in the category of
ideals whose radical contains the augmentation ideal gives the colimit
isomorphism. The argument uses finite generation of the augmentation ideal,
not Noetherianity, and includes the zero ring, ghost variables, and empty
ambient vertex set. This is a normalization of Ext stages; it is not the
positive-degree Ext-colimit/Čech comparison.

The main declaration
`faceRingLocalCohomologyIsoGeneratorPowerExtColimit` and the power bound use
only `[propext, Classical.choice, Quot.sound]`. Validation passed: focused
compilation, `lake build` (2,748 jobs), `lake env lean Checks/Axioms.lean`,
`python3 site/build.py`, `python3 scripts/check_site.py`, and
`git diff --check`. The site has 76 blueprint nodes, 63 checked nodes, 423
linked declarations, 981 local links, and 13,071 displayed source rows across
20 linked Lean files. The next substep is vanishing of Ext stages with a
localized target, followed by the missing complex comparison.

## Ext vanishing on nonempty Čech rows (2026-11-24)

`Reisner/Cech/LocalizedExt.lean` proves a general derived-Ext vanishing
principle: if a scalar annihilates the source and acts invertibly on the
target, then every Ext class vanishes. For a nonempty localization index,
a selected face-ring variable belongs to the augmentation ideal and becomes
a unit after inverting the product. Thus all augmentation-power Ext stages
vanish against that localization in every cohomological degree. The
colimit/evaluation isomorphism then proves vanishing of the project local
cohomology evaluated at every nonempty Čech localization target. This covers
exponent zero, ghost variables, nonface indices (including zero
localizations), and arbitrary commutative coefficient rings. It is an
acyclicity input, not the comparison of the whole Čech complex with local
cohomology.

Validation passed: full `lake build` (2,749 jobs),
`lake env lean Checks/Axioms.lean`, `python3 site/build.py`,
`python3 scripts/check_site.py`, and `git diff --check`. The new declarations
use only `[propext, Classical.choice, Quot.sound]`. The site now has 78
blueprint nodes, 65 checked nodes, 431 linked declarations, 996 local links,
and 13,263 displayed source rows across 21 linked Lean files. The next task
is to construct the complex or double-complex comparison from the normalized
Ext-colimit stages and nonempty-row acyclicity; no full comparison is yet
claimed.

## Acyclicity of positive Čech terms (2026-11-24)

The Ext-colimit local-cohomology functor is now proved additive in its
coefficient module and therefore preserves finite products in `ModuleCat`.
The proof uses additivity of the derived Ext target functor at each stage and
the pointwise colimit construction in the functor category. For finite `V`,
each positive Čech cochain module is a finite product indexed by the
nonempty subsets of the given cardinality. Combining product preservation
with the checked vanishing on each nonempty localization proves
`faceRingCechCochain_localCohomology_isZero` in every local-cohomology
degree, over any commutative coefficient ring. This is the acyclic-terms
input for a derived comparison; exactness/computing the Ext-colimit of the
whole augmented Čech complex is still open.

Validation passed: full `lake build` (2,750 jobs),
`lake env lean Checks/Axioms.lean`, `python3 site/build.py`,
`python3 scripts/check_site.py`, and `git diff --check`. The new additive,
finite-product, and positive-term acyclicity declarations use only
`[propext, Classical.choice, Quot.sound]`. The site now has 79 blueprint
nodes, 66 checked nodes, 434 linked declarations, 1,004 local links, and
13,416 displayed source rows across 21 linked Lean files. The full
Ext-colimit/Čech cohomology comparison remains open.

The next step added the stronger stagewise version: for each `n`, Ext from
`A/𝔪^n` into every positive Čech cochain term vanishes in all degrees.
The derived Ext target functor preserves finite products, so the already
checked localization-row vanishing passes to the full finite cochain term
before taking the colimit. This is the row-zero input for forming a
derived-Hom double complex; no totalization or comparison map is claimed yet.

Validation passed: full `lake build` (2,750 jobs),
`lake env lean Checks/Axioms.lean`, `python3 site/build.py`,
`python3 scripts/check_site.py`, and `git diff --check`. The stagewise
cochain Ext vanishing, its finite-product dependency, and the local
cohomology cochain vanishing use only `[propext, Classical.choice,
Quot.sound]`. The site reports 79 blueprint nodes, 66 checked nodes, 437
linked declarations, 1,007 local links, and 13,489 displayed source rows.

The current step packages the actual Čech complex over the face ring. Its
localization transition maps are face-ring algebra homomorphisms, and the
resulting face-ring-linear differential is checked equal to the existing
coefficient-ring differential. The induced complex and its fixed-stage
derived Ext image are checked. Positive-degree terms and homology of that
image vanish by the already established stagewise row vanishing. The new
square-zero and homology-vanishing theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

Validation passed: full `lake build` (2,751 jobs),
`lake env lean Checks/Axioms.lean`, `python3 site/build.py`,
`python3 scripts/check_site.py`, and `git diff --check`. The site reports
80 blueprint nodes, 67 checked nodes, 448 linked declarations, 1,022 local
links, and 13,669 displayed source rows across 22 source files. The genuine
double-complex/totalization comparison with the Ext-colimit, and therefore
the positive-degree Čech-to-local-cohomology comparison, remain open.

The next fixed-stage detail is now checked as well: the degree-zero Čech term
is face-ring-linearly equivalent to the face ring, and applying the fixed
stage Ext functor identifies that term with `Ext^q_A(A/𝔪^n,A)`. This does
not assert that applying `Ext^q` termwise commutes with taking cohomology.

Validation passed again: full `lake build` (2,751 jobs),
`lake env lean Checks/Axioms.lean`, site regeneration, site consistency, and
`git diff --check`. The site reports 80 blueprint nodes, 67 checked nodes,
452 linked declarations, 1,026 local links, and 13,735 displayed source rows.

The fixed-stage statement now reaches actual homology: the Ext-applied
complex has degree-zero homology canonically isomorphic to
`Ext^q_A(A/𝔪^n,A)`, and all positive-degree homology vanishes. The proof uses
the zero target in Čech degree one and the absent incoming differential at
degree zero. This remains a statement about the termwise Ext-applied complex;
it is not yet a hypercohomology comparison with the Čech complex's own
cohomology.

Validation passed: full `lake build` (2,751 jobs),
`lake env lean Checks/Axioms.lean`, site regeneration, site consistency, and
`git diff --check`. The new degree-zero homology equivalences use only
`[propext, Classical.choice, Quot.sound]`. The site reports 80 blueprint
nodes, 67 checked nodes, 454 linked declarations, 1,028 local links, and
13,813 displayed source rows.

## Generator-power stagewise Ext--Cech complexes (2026-11-25)

The positive-row argument has now been repeated at the cofinal generator-
power stages `A/(x_v^n : v ∈ V)`, rather than only at augmentation-power
stages `A/m^n`. In every nonempty localization, a selected variable power
annihilates the quotient source and acts invertibly on the target. Finite
product preservation then gives zero for every positive Cech cochain term
after applying derived `Ext^q_A(A/(x_v^n), -)`. Mapping the face-ring-linear
Cech complex through this fixed-stage Ext functor gives a complex with zero
positive terms and therefore zero positive homology. These are the same
stages as in the checked Ext-colimit normalization of local cohomology.

At this point it did not yet provide transition maps between the Ext-applied
complexes, a totalization, or a comparison to positive-degree Cech cohomology.
The first direct packaging attempt was discarded after exposing mathlib's
need for zero-preservation instances. A later proof supplies these instances
locally at each stage, without axioms; that coherent diagram is recorded
below.

Validation passed: full `lake build` (2,751 jobs), `lake env lean
Checks/Axioms.lean`, site generation, `python3 scripts/check_site.py`, and
`git diff --check`. The new generator-power stage homology theorem depends
only on `[propext, Classical.choice, Quot.sound]`. The site reports 80
blueprint nodes, 67 checked nodes, 458 linked declarations, 1,032 local
links, and 13,813 displayed source rows across 22 Lean files.

## Coherent generator-power Ext--Cech diagram (2026-11-25)

`Reisner/Cech/FaceRingLinear.lean` now assembles the fixed generator-power
Ext-applied Cech complexes into a functorial diagram. The arrows are induced
by the quotient-stage maps, and the complex-map functor laws compile using
stage-local zero-preservation instances for the derived Ext functors.
Evaluation in each Cech degree is identified with the corresponding
Ext-functor diagram. In degree zero, the diagram is naturally isomorphic to
the existing `faceRingGeneratorPowerExtDiagram`; hence its colimit is
canonically the project local-cohomology module in each Ext degree.

The degreewise colimit complex has zero terms and zero homology in every
positive Cech degree, since its stagewise positive terms are zero and
evaluation preserves colimits. This is a genuine coherent-colimit result,
but its construction first applies a fixed `Ext^q` to each Cech term and then
takes the stage colimit. It is not the original Cech complex and supplies no
comparison to its positive-degree cohomology. The remaining mathematical
task is the hypercohomology/double-complex or acyclic-resolution comparison.

Validation passed: focused and full `lake build` (2,751 jobs), direct axiom
inspection, `Checks/Axioms.lean`, and `git diff --check`. The new declarations
use only `[propext, Classical.choice, Quot.sound]`.
