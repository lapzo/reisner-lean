# Reisner Lean

Lean 4 project formalizing dependencies for Reisner's Cohen–Macaulay
criterion for Stanley–Reisner rings.

[Project website](https://lapzo.github.io/reisner-lean/)

## Status

The face-ring, dimension, localization, and finite Čech foundations are
partly checked. Čech projections commute with the differential and give
componentwise criteria for cycles and homogeneous boundaries. Čech cohomology
decomposes by fine degree, and positive-degree subcomplexes are contractible.
Nonpositive admissible indices correspond to link faces. Their actual fine-degree
cochain modules are now linearly equivalent to augmented link cochains, with
the orientation sign and adjacent-differential compatibility checked. The
actual shifted-complex isomorphism and induced homology comparison, including
integer reduced degree and the below-cutoff zero case, are also checked. The
local-cohomology comparison and full criterion remain future work. See [STATUS.md](STATUS.md),
[AUDIT.md](AUDIT.md), and the blueprint in
[`blueprint/src`](blueprint/src).

A separate augmented cochain complex indexed by actual face cardinality is
checked: signed deletion, square-zero, the empty-face scalar term, the
coordinate-basis differential and insertion formulas, and the degree-minus-one
cohomology endpoints. Its integer reindexing, restriction and homology
isomorphisms, and low/high term and cohomology cutoffs are checked. Higher-
degree cohomology vanishing, the full augmented chain model and duality,
local-cohomology comparison, and Reisner's criterion remain future work.

## Lean source map

`Reisner.Cech` remains the public import for the Čech development. Its
implementation is divided into modules in dependency order:

- `Reisner.Cech.Core`: localization coordinates, signs, and the full Čech
  cochain complex.
- `Reisner.Cech.Grading`: fine-degree subcomplexes and the cohomology
  decomposition.
- `Reisner.Cech.Contraction`: positive-coordinate contraction and vanishing.
- `Reisner.Cech.Indices`: nonpositive indices and link-face correspondence.
- `Reisner.Cech.LinkComparison`: signed term equivalence and differential
  compatibility.
- `Reisner.Cech.ShiftedLink`: the shifted complex and induced homology maps.

The augmented link cochain complex and integer reindexing live in
`Reisner.SimplicialCochain`. The corresponding regression and axiom audits
are in `Checks/`. Project-specific proof and file-organization conventions are
in [LEAN_STYLE.md](LEAN_STYLE.md).

## Build

Requires [elan](https://github.com/leanprover/elan). Toolchain and dependencies
are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake build
lake env lean Checks/Axioms.lean
lake env lean Checks/Cech.lean
lake env lean Checks/SimplicialCochain.lean
```
