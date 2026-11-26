# Progress handoff — 2026-11-25

## Current request and result

The user requested a complete formal statement of Reisner's criterion, with
definitions in Lean, but explicitly did not request a proof. The statement is
implemented in `Reisner/ReisnerCriterion.lean` and exported by `Reisner.lean`.
Its proof has the single requested `sorry` placeholder.

`Reisner.Complex.LinkHomologyVanishesBelowDimension K k` means that for every
face `σ` and every integer `i` strictly below the dimension of `link σ`, the
integer-indexed augmented simplicial chain homology of that link over `k` is
subsingleton. `Reisner.Complex.reisner_criterion` states that this predicate
is equivalent to the project's standard algebraic
`Reisner.IsCohenMacaulay (K.FaceRing k)` predicate. Hypotheses are finite
ambient vertex type, an arbitrary linear order for orienting chains, and field
coefficients. No purity assumption is added.

The project already defines algebraic Cohen–Macaulayness by depth equal to
Krull dimension at every prime. Its integer chain complex is augmented, so
degree `-1` represents the empty face. The complex type always contains the
empty face; ghost ambient vertices are allowed. For `{∅}`, the link has
dimension `-1`, and the condition ranges only over degrees below `-1`, as
required. The mathematical statement matches Panov, Theorem 2.5:
<https://arxiv.org/html/math/0506526v3>.

**The theorem is not proved.** `#print axioms Reisner.Complex.reisner_criterion`
includes `sorryAx`. The blueprint links the statement but marks its node as
planned, not checked. Do not describe the criterion as proved or remove the
placeholder unless the user asks for the proof.

## Validation

- `lake build` passed (2,751 jobs).
- `lake env lean Checks/Axioms.lean` passed; the criterion is only `#check`ed
  there. Its `sorryAx` was inspected separately and documented in `STATUS.md`.
- Site/blueprint generation and `python3 scripts/check_site.py` passed after
  registering the planned statement node.
- Current site snapshot reports 80 nodes, 67 checked, 472 linked declarations,
  and 1,047 local links.
- Exactly one Lean source placeholder is intended: the proof of
  `reisner_criterion`; no `admit` or custom axiom was added.

## Main files changed for the criterion statement

- `Reisner/ReisnerCriterion.lean`
- `Reisner.lean`
- `Checks/Axioms.lean`
- `blueprint/src/content.tex` (node `thm:reisner`, linked but not `\\leanok`)
- `scripts/lean_sources.py`, `site/build.py`
- `TASK.md`, `STATUS.md`, `README.md`, `site/README.md`,
  `site/content/index.md`

## Earlier formalization state

The repo also contains the checked simplicial chain/cochain duality,
Čech/link comparisons, link-homology cutoff and purity results, and the
generator-power Ext-colimit and coherent Ext-applied Čech diagram described
in `STATUS.md`. The genuine positive-degree comparison between the original
Čech cohomology and the Ext-colimit local-cohomology model remains open, as
does a proof of Reisner's criterion. No site deployment or Git commit was
requested in this turn. The working tree has other pre-existing uncommitted
project changes; inspect `git status` before editing or committing.
