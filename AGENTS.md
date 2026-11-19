# Project

This project develops a blueprint for Reisner’s Cohen–Macaulay criterion and incrementally formalizes its dependencies in Lean 4.

Read TASK.md for the current objective. Consult the blueprint before changing mathematical definitions or statements.

## Mathematical correctness

- Preserve the intended mathematical meaning of every definition and theorem.
- Use standard algebraic Cohen–Macaulayness; do not define it through Reisner’s homological criterion.
- Make hypotheses and empty-face, dimension, and reduced-homology conventions explicit.
- Do not weaken a conclusion or add hypotheses merely to obtain a proof.
- If a statement appears false or ambiguous, explain the issue and propose a correction explicitly.
- Verify mathematical references and distinguish sourced results from your own arguments.

## Lean development

- Search the pinned mathlib source before introducing definitions or proving auxiliary results.
- Reuse existing APIs where their mathematical meaning matches the project.
- Work on the requested node and its necessary dependencies.
- Completed proofs must contain no `sorry`, `admit`, or new axioms.
- Keep future, unimplemented results in the blueprint rather than introducing them as axioms.
- Use the existing toolchain and dependency pins. Explain any necessary changes.
- Compile incrementally and run `lake build` before reporting completion.
- Inspect the main implemented theorem with `#print axioms`.

## Blueprint

- Give precise statements, informative proofs, and explicit dependencies.
- Use stable labels and `\uses` annotations.
- Link only existing Lean declarations.
- Mark a proof as formalized only after successful compilation.
- Keep the blueprint consistent with changes to Lean definitions.

## Communication

- Give concise updates about findings, decisions, and blockers.
- Distinguish proposed mathematics, written code, and successfully checked code.
- Make routine implementation decisions independently.
- Finish with changed files, validation results, and remaining gaps.
