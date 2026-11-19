# Reisner Lean

Lean 4 project formalizing dependencies for Reisner's Cohen–Macaulay
criterion for Stanley–Reisner rings.

## Status

The face-ring, dimension, localization, and finite Čech foundations are
partly checked. The latest checked Čech result decomposes each cochain module
by fine degree. The cohomology decomposition and full criterion remain future
work. See [STATUS.md](STATUS.md), [AUDIT.md](AUDIT.md), and the blueprint in
[`blueprint/src`](blueprint/src).

## Build

Requires [elan](https://github.com/leanprover/elan). Toolchain and dependencies
are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake build
lake env lean Checks/Axioms.lean
lake env lean Checks/Cech.lean
```
