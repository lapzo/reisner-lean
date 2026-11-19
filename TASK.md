# Current task: decompose each Čech cochain module by fine degree

The extended Čech complex (`lem:cech-complex`) and monomial cochain action
(`lem:cech-basis-action`) are checked. The next bounded prerequisite toward
the full degreewise cohomology result is the internal direct-sum decomposition
of each cochain module by its fine integer degrees. Add this as a separate
node, provisionally `lem:cech-termwise-decomposition`.

Preserve all checked results, the full checked `lem:localized` result, all
dimension and localization results, existing public APIs, and dependency
pins. Keep the full statement and label of `lem:cech-grading` intact and
unmarked. Do not claim that cohomology commutes with direct sums or attempt the
full decomposition of cohomology in this milestone. Read `AGENTS.md`,
`STATUS.md`, `AUDIT.md`, blueprint source, `Reisner/Cech.lean`, the public
imports, `Checks/Axioms.lean`, `Checks/Cech.lean`, and pinned mathlib before
implementation. Work locally; do not publish or push.

## Mathematical target and boundary

For finite `V`, a complex `K : Complex V`, a commutative ring `R`, and each
`q : ℕ`, use the existing cochain module
`CechCochain R q = ∀ F : CechIndex V q, FaceRingLocalization R F.1` and the
existing degree submodules

```lean
cechDegreeSubmodule R q a =
  Submodule.pi Set.univ (fun F => faceRingLocalizationComponent R F.1 a)
```

for `a : V →₀ ℤ`. Prove that these submodules form an internal direct-sum
decomposition of the whole cochain module:

```lean
DirectSum.IsInternal (K.cechDegreeSubmodule R q)
```

Equivalently, each cochain is a unique finite sum of cochains whose every
localization coordinate is homogeneous of one common fine degree. The index
`V →₀ ℤ` is infinite in general; the finite-support assertion must follow
from the finite set of coordinates in `CechIndex V q` and the checked
internal grading of each actual localization. Retain every subset index,
including the empty subset, nonfaces, and ghost-containing subsets. Do not
restrict to face indices or replace actual zero localizations by formal
symbols.

This node concerns terms of the complex only. It does not assert or prove
that cycles, boundaries, or cohomology decompose by degree. In particular,
do not use an unproved general claim that homology commutes with direct sums.
The existing complete `lem:cech-grading` statement and proof remain intact
and unmarked; it continues to claim the cohomology direct-sum isomorphism and
other results not covered by this task. If the exact internal-sum statement
does not match the existing `cechDegreeSubmodule` definition or cannot be
proved for arbitrary commutative-ring coefficients, report the mismatch and
propose an honest prerequisite without changing the grading or adding
hypotheses for convenience.

## Stage 1: Builder — mathlib route and blueprint source

Builder owns the mathematical specification and all edits to
`blueprint/src/content.tex`.

1. Confirm pinned APIs and exact types for the existing
   `faceRingLocalization_isInternal`, `DirectSum.IsInternal`,
   `DirectSum.IsInternal.chooseDecomposition`,
   `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`,
   `Submodule.iSup_eq_range_dfinsupp_lsum`, and
   `DirectSum.linearEquivFunOnFintype`. They are in
   `Mathlib/Algebra/DirectSum/Decomposition.lean`,
   `Mathlib/Algebra/DirectSum/Module.lean`, and
   `Mathlib/LinearAlgebra/DFinsupp.lean`. Explain how the finite coordinate
   family combines its per-localization internal gradings and how finite
   degree support is obtained. Do not assert that a ready-made cohomology or
   infinite-index product decomposition API exists unless verified in this
   pin.
2. Add a distinct `lem:cech-termwise-decomposition` node stating the
   internal direct-sum result precisely, with dependencies
   `\uses{lem:cech-complex,lem:localized}`. Make `lem:cech-grading` depend on
   this node while preserving its complete statement, proof text, and stable
   label.
3. Link only declarations that exist or are to be implemented in this task.
   Do not mark the new node formalized or checked. Keep `lem:cech-grading`
   unmarked.
4. Hand Formalizer the exact theorem signature, proof route, source anchors,
   and a regression plan. Do not edit Lean source, checks, status/audit docs,
   generated artifacts, or dependency pins in this stage.

## Stage 2: Formalizer — internal decomposition and validation

Formalizer owns Lean source and checks, not blueprint source. Implement in the
existing `Reisner/Cech.lean`, using the actual localization components and
the current `cechDegreeSubmodule`. A natural principal theorem name is
`cechDegreeSubmodule_isInternal` with result
`DirectSum.IsInternal (K.cechDegreeSubmodule R q)`.

Acceptance requires:

- a compiled internal-decomposition proof for every `q`, finite ambient `V`,
  and commutative coefficient ring `R`, with no field, non-ghost, or
  nonempty-face assumptions;
- independence and spanning of the full family indexed by all
  `a : V →₀ ℤ`, or a proof using an equivalent pinned `DirectSum.IsInternal`
  characterization;
- a clear finite-support argument combining the finitely many coordinates
  with the existing localization gradings;
- preservation of the existing `cechDegreeSubmodule` and Cech APIs; do not
  redefine the complex or alter its differential;
- `lake build`, `lake env lean Checks/Axioms.lean`,
  `lake env lean Checks/Cech.lean`, `#print axioms` for the principal theorem,
  and a source scan with no `sorry`, `admit`, or custom axioms;
- no dependency-pin changes and no blueprint-source edits.

Report the exact theorem type, proof route, source anchors, axiom output, and
commands passed. Stop at the last compiled coherent result if this precise
termwise statement proves infeasible; do not silently weaken it.

## Stage 3: Builder finalization

After a successful Formalizer handoff, Builder adds exact Lean links and marks
only `lem:cech-termwise-decomposition` checked/formalized. Keep the full
`lem:cech-grading` statement complete and unmarked. Reconcile its dependency
on the new termwise result without claiming the later cycles, boundaries, or
cohomology steps are proved.

## Stage 4: Weber — generated artifacts and local documentation

After Builder finalizes the blueprint source, Weber regenerates the blueprint
PDF/HTML, declaration and dependency artifacts, and source anchors; runs
`leanblueprint checkdecls`, `lake build`, both Lean check files,
`python3 site/build.py`, and `python3 scripts/check_site.py`. Update
`STATUS.md`, `AUDIT.md`, both READMEs, and the local site to describe only the
checked termwise module decomposition. Keep the full cohomology decomposition
in `lem:cech-grading` visibly future. Do not create reports, publish, or push.
Report validation results and remaining gaps.

## Constraints

Do not change the mathematical meanings of `lem:localized`,
`lem:cech-complex`, `lem:cech-basis-action`, or the complete
`lem:cech-grading` statement. Do not change face-ring/localization
definitions, checked public results, or dependency pins. Retain every finite
subset coordinate, including the empty subset, nonfaces, and ghosts. Do not
add hypotheses, introduce custom axioms, or use `sorry` or `admit`. Clearly
distinguish proposed mathematics, written code, and successfully checked
declarations.
