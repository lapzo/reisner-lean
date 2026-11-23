# Local mathematical site

The main page combines the mathematical argument, checked Lean excerpts,
and the route to the complete criterion. The separate blueprint page
contains the blueprint nodes, their full statements and informal proofs, an
interactive dependency graph, and status/search filters.

Build from the project root:

```sh
python3 site/build.py
python3 scripts/lean_source.py
python3 scripts/check_site.py
python3 -m http.server 8000 --directory site/dist
```

Then open `http://localhost:8000/`. Both `site/dist/index.html` and
`site/dist/blueprint.html` also work when opened directly. Their mathematics,
CSS, JavaScript, graph, and Lean excerpts are embedded locally. There is no
MathJax CDN or JavaScript package installation. Each HTML file is a complete
reading page; the blueprint and downloaded source files are linked separately.

Requirements: the existing pinned Lean project and blueprint tools,
Python 3, Pandoc (checked with 3.7.0.2), and Graphviz. Pandoc converts TeX
equations to native MathML at build time. A modern Firefox, Safari, or
Chromium browser renders MathML without a library download.

The build reruns `lake build`, `Checks/Axioms.lean`, the standalone
`Checks/LocalizationKernelAudit.lean` regression file, `Checks/Cech.lean`, and
`Checks/SimplicialCochain.lean`. It then generates the
blueprint PDF/HTML, runs `checkdecls`, and exports the dependency graph. Axiom
validation accepts subsets of `{propext, Classical.choice, Quot.sound}` and
rejects every other reported dependency. It extracts code by declaration name from
`Reisner/StanleyReisner.lean`, the six modules under `Reisner/Cech/`, and
`Reisner/SimplicialCochain.lean`, verifies linked declarations, and reads
checked markers and dependency labels from `blueprint/src/content.tex`. Each
file keeps its own line numbering and anchor prefix. Node counts include
definitions. New Lean declarations need matching named excerpts; their source
file and line numbers are derived at build time.

Editable presentation files:

- `content/index.md`: the combined proof-and-Lean reading page.
- `style.css`, `site.js`: styling and small browser interactions.
- `build.py`: checked-source extraction, MathML conversion and blueprint assembly.
- `dist/`: generated local site and downloadable source snapshots.

The original Leanblueprint files remain in `blueprint/`. The site's
blueprint page is generated from them, so it carries the same mathematical
statements, proof texts, labels and dependency graph.

The paper-like navigation and separate blueprint entry follow the user's
reference, <https://roed314.github.io/gq2/>. This project does not copy that
site's mathematical claims, implementation status, or assumed interfaces.
Nothing is registered, pushed, or published by this build.

The generated site presents the actual finite extended Čech complex, the signed
localization differential and square-zero proof, fine-degree restrictions,
the signed insertion formula on monomial cochains, the internal direct-sum
decomposition of each cochain module by fine degree, and the homogeneous
projection, cocycle, and boundary criteria. The inclusion-induced fine-degree
decomposition of actual Čech cohomology in `lem:cech-grading` is checked,
as is the positive-coordinate contraction in `lem:contraction`;
the link definition and nonpositive admissible-index correspondence are also
checked. The signed termwise identification with augmented link cochains and adjacent
differential compatibility are checked over arbitrary commutative rings.
The shifted-complex packaging and induced actual homology identification in
integer reduced degree are checked, including the below-cutoff zero case. The
comparison with local cohomology remains future work. The site
includes downloadable Cech regressions and source snapshots. Each displayed
Lean excerpt is extracted by declaration name. The static checker validates
local links and displayed source rows. It also checks unique IDs, source/artifact snapshots,
acyclic blueprint dependencies, and absence of remote assets. Browser QA has
not been run against this regenerated milestone.

The separate face-cardinality cochain complex uses only actual faces, including
the empty face at index zero and excluding ghost singletons. Its signed deletion
differential, square-zero law, coordinate-basis insertion criterion,
degree-minus-one cohomology endpoints, and zero modules above the ambient
cardinality are checked. The complex is reindexed to integer reduced degrees
by $i=n-1$, with restriction and homology isomorphisms and zero-term and
zero-cohomology cutoffs below $-1$ and above $|V|-1$. Higher-degree cohomology
vanishing, the full augmented chain model and duality, and local cohomology
remain future work. Shifted Čech/link complex and cohomology identifications
are checked.
The complete source and focused checks are available as
`source/SimplicialCochain.lean` and `source/Checks-SimplicialCochain.lean`.

The reading page distinguishes generic localization vanishing (some denominator
power kills a numerator) from the special first-power criterion. It explains
the coefficient-preserving injective support translation, the `n=0` case, and
the counterexample `k[x,y]/(x²y)`. It states the zero-ring boundary and links
to the downloadable compiled regression file, which also checks the generic
`Away (2 : ZMod 4)` counterexample.

The reading page covers coordinate membership, restriction to facet variables,
the actual polynomial quotient equivalence, facet intersection of the
generator-defined ideal, prime containment, and both global and localized
face-ring dimensions. The dimension section includes the maximum-face
convention, coordinate-prime chains, the global upper bound, and the
augmentation-ideal height computation. Its localization section adds the
actual variable-product localizations, exact polynomial-fraction kernels,
monomial nonvanishing, scalar injectivity, empty-product equivalence, and
coherent transition maps with an explicit fraction formula. The localized
grading section gives the Laurent monomial basis, the zero-or-one dimension
formula, and the transition rule for the basis vectors. The full degreewise
depth and local-cohomology comparisons, and the full criterion remain future
work. The full `lem:cech-grading` node is checked.
