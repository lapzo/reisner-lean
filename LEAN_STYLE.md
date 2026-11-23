# Lean development guide for this project

This guide adapts the public [`lean-proof` skill](https://github.com/leanprover/skills/tree/main/skills/lean-proof) to the mathematics and review rules of this repository. The skill's advice about debugging and dependent rewrites is useful; its permission to leave `sorry` placeholders does not apply here.

## Make the proof route visible

- Start each public definition/theorem with a docstring saying what its objects mean and, where helpful, why the result is needed.
- Keep the Lean statement aligned with its blueprint node. Record conventions such as the empty face and reduced degree `-1` in both places.
- Name intermediate facts for mathematical roles (`hface`, `hdisjoint`, `hdegree`) rather than tactic history (`h1`, `h2`).
- Prefer short blocks that each establish one step in the argument. A reader should be able to follow the map from hypotheses to the conclusion without mentally executing a long tactic chain.
- Use `simp` for canonical reductions, but make non-obvious rewrites explicit and explain sign, index, or transport choices in a nearby comment.
- When a dependent rewrite fails, first expose the exact equality and types with `change`, `show`, or a generalized helper lemma. Avoid hiding the issue behind broad transparency options unless a small, named wrapper genuinely improves the interface.

## Organize files by mathematical layer

- Put declarations that are used together in a module with one clear topic and one-way imports.
- Split a file when it contains substantial, independently understandable stages; do not create one-file-per-theorem fragments.
- Preserve a public facade module when splitting an established module, so downstream imports and qualified declaration names stay stable.
- Keep examples and `#print axioms` audits in `Checks/`, not mixed into library modules.

## Iterate and validate

- Read the target theorem and its dependencies before editing; search the pinned mathlib API before adding a local construction.
- Work on the hardest case early, but do not use `sorry` in committed/project code, including temporary helper theorems in shared files.
- After a proof edit, compile the smallest affected module and inspect the first Lean error before changing downstream code. Fix syntax and type errors before tactic failures or linter warnings.
- Before handing off, run the relevant check files and `lake build`; run `#print axioms` on the main result and scan for `sorry`, `admit`, and custom `axiom` declarations.
- Treat compiler success as evidence about the Lean declaration, not as a substitute for checking that the statement says the intended mathematics.
