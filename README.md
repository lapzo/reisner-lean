# Reisner's criterion: checked face-ring dependencies

A Lean 4 project and complete informal blueprint for Reisner's
Cohen–Macaulay criterion. Checked results include polynomial membership in
the Stanley–Reisner ideal, a standard monomial basis of the actual quotient,
and weighted homogeneity of the polynomial ideal. The original monomial
membership theorem is
`Reisner.Complex.monomial_mem_stanleyReisnerIdeal_iff`:

\[
x^\alpha\in I_K\quad\Longleftrightarrow\quad\operatorname{supp}(\alpha)\notin K.
\]

The ideal is defined by squarefree nonface generators in actual mathlib
multivariate polynomials. The theorem works over any nontrivial commutative
semiring and any ambient vertex type. Polynomial membership holds over any
commutative semiring. `Reisner.Complex.faceRingBasis` is a genuine basis of
the face-ring quotient over any commutative ring;
`faceRingBasis_apply` identifies its vectors with the corresponding
quotient monomials. Scalar injectivity and quotient nontriviality are also
checked. The ideal is homogeneous for arbitrary weights into an additive
commutative monoid, and weighted homogeneous components remain in the ideal.
The checked identities specialize this result to fine and total degree on
the polynomial ring. The actual quotient has checked fine and total
`GradedAlgebra` structures, with total degree a coarsening of the fine
grading. Its degree-zero subalgebra is equivalent to the coefficient ring
through the scalar map. Over any field and a finite ambient type, the
face ring and its localization at the augmentation ideal have dimension
equal to the maximum face cardinality. Actual localizations at finite
variable products have exact polynomial-fraction kernels, coherent
transition maps, and an integer grading with a Laurent monomial basis. The
fraction criterion holds over every commutative ring; the special first-power
criterion follows from squarefree support shifts. Monic-fraction nonvanishing
requires nontrivial coefficients, while scalar injectivity also covers the
zero ring.
Over a field, each admissible degree has dimension one and the other
components are zero.
The eventual criterion concerns arbitrary fields
and finite ambient sets, includes the empty face and ghost vertices, and
uses algebraic depth and Krull dimension to define Cohen–Macaulayness.

## Read the results

- [Combined mathematics and Lean site](site/dist/index.html), with a
  [blueprint page](site/dist/blueprint.html) and [local build instructions](site/README.md).
- [Lean sources](Reisner/StanleyReisner.lean), [axiom inspection](Checks/Axioms.lean), [localization-kernel regressions](Checks/LocalizationKernelAudit.lean), and [Čech regression checks](Checks/Cech.lean).
- [Blueprint HTML](blueprint/web/index.html) and [PDF](blueprint/print/print.pdf).
- [Interactive dependency graph](blueprint/web/dep_graph_document.html), [standalone SVG](blueprint/dep_graph.svg), [PDF](blueprint/dep_graph.pdf), and [DOT](blueprint/dep_graph.dot).
- [Audit, exact mathlib APIs and verified references](AUDIT.md).
- [Completed work and remaining nodes](STATUS.md).

Sixteen blueprint nodes are marked checked: the complex definition, the
face-ring definitions, the indicator comparison, monomial membership, the
standard monomial basis, weighted homogeneity of the polynomial ideal, and
the quotient fine/total gradings with degree-zero algebra equivalence,
augmentation/residue foundations, coordinate-prime/facet structure,
combinatorial dimension, the full global/local dimension proposition,
localization kernels and transition maps, the localized monomial pieces, the
finite extended Čech complex with its signed differential, square-zero law,
and fine-degree restrictions, the monomial cochain insertion formula, and the
internal direct-sum decomposition of each cochain module by fine degree. The
cohomology decomposition remains future work; `lem:cech-grading` remains
unmarked with its full statement. The combined local site presents checked
results and the remaining proof route.
The full criterion and the other dependency nodes are informal mathematics.
The graph's green nodes are checked; blue indicates that the relevant
prerequisites are checked, not that the node itself is implemented.

The current local site build contains 34 blueprint nodes, sixteen checked
nodes, and 181 linked Lean declarations. The static checker resolves 473
local links and verifies 5,345 displayed source rows against the 1,953-line
face-ring source and 526-line Čech source; IDs are unique, dependencies are
acyclic, snapshots match, and no remote assets are requested. The site is
local-only.

## Lean build

Install [elan](https://github.com/leanprover/elan). The project's
`lean-toolchain`, `lakefile.lean` and `lake-manifest.json` fix Lean 4.35.0,
mathlib release 4.35.0 at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, the declaration checker, and
all transitive package revisions. From the project root:

```sh
lake exe cache get
lake build
lake env lean Checks/Axioms.lean
lake env lean Checks/Cech.lean
```

Lake materializes the locked packages when needed; the first command
downloads mathlib's compiled cache. Network access is needed for this
initial setup. `lake update` was used to create the manifest and is not
needed for ordinary builds. Do not change the pins to follow a moving
branch. The axiom check reports only `propext`, `Classical.choice`, and
`Quot.sound`; there are no custom axioms or proof placeholders.

## Blueprint build

Required tools: Python 3 with the packages in
`blueprint/requirements.txt` (including their dependencies), Graphviz
with `dot`, latexmk, and a TeX installation containing `pdflatex`, the AMS
packages, `geometry`, `hyperref`, and `expl3`. The checked environment uses
TeX Live 2025. A conventional Python installation can use:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r blueprint/requirements.txt
```

leanblueprint requires a Git working tree to discover the project. If
working from an archive without `.git`, run `git init` once. No remote or
commit is needed. After the Lean build, run from the project root:

```sh
python3 scripts/blueprint.py pdf
python3 scripts/blueprint.py web
python3 scripts/blueprint.py checkdecls
python3 scripts/lean_source.py
python3 scripts/export_graph.py
```

The wrapper calls the actual `leanblueprint` CLI. On ordinary installations
these first three commands are equivalent to `leanblueprint pdf`,
`leanblueprint web`, and `leanblueprint checkdecls`. On the installed Nix
distribution the wrapper also forwards Python package paths to plasTeX and
fixes permissions on previously generated theme assets. It does not modify
system packages. See `AUDIT.md` for the precise packaging issue.

The commands produce `blueprint/print/print.pdf`,
`blueprint/web/index.html`, `blueprint/web/dep_graph_document.html`, the
generated `blueprint/lean_decls`, local declaration source links, and
`blueprint/dep_graph.{dot,svg,pdf}`. Run them in this order so the declaration
list and exported graph come from the current blueprint.

For the interactive graph, serve the generated directory locally:

```sh
python3 -m http.server 8000 --directory blueprint/web
```

Open `http://localhost:8000/`. The HTML uses the renderer's MathJax CDN;
the blueprint PDF and standalone graph do not require it. Graph and Lean
source links resolve locally. Nothing in these commands publishes the project.

## Combined mathematical site

The paper-style site puts the mathematics, checked Lean code, and full
proof route together. Its separate blueprint page contains the complete
statements and informal proofs, graph navigation, and status filters.
Its generated pages use native MathML and work without external assets.

```sh
python3 site/build.py
python3 scripts/lean_source.py
python3 scripts/check_site.py
python3 -m http.server 8000 --directory site/dist
```

Open `http://localhost:8000/`. The build requires Pandoc in addition to the
existing project and blueprint tools. See [site/README.md](site/README.md).
