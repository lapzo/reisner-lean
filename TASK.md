# Current formalization task

## Reisner's criterion statement

The full statement in `Reisner/ReisnerCriterion.lean` compiles. For a finite
ambient vertex type and any field, `Reisner.Complex.reisner_criterion` states
that algebraic Cohen–Macaulayness of the face ring is equivalent to reduced
homology vanishing below each face link's own dimension. It includes the
empty face and ghost vertices. This milestone covers the statement. Its
proof remains open, with one intentional `sorry` in this declaration.

## Current checked milestone

The project now has a checked canonical evaluation isomorphism between augmented simplicial cohomology and the linear dual of augmented simplicial homology in every integer reduced degree. It reindexes the natural face-cardinality theorem, including degree zero (reduced degree -1), and uses the zero extensions below -1. Chain and cochain terms and homology have checked upper bounds at both the ambient vertex count and actual maximal face cardinality. The generic short-complex theorem and simplicial specializations are in `Reisner/DualHomology.lean` and `Reisner/SimplicialDuality.lean`.

The actual Cech complex has also been compared with shifted link cohomology, and its uniform vanishing cutoff is characterized as purity together with integer reduced link homology vanishing below each link dimension. The cohomology form remains available over nontrivial commutative coefficient rings; homology duality uses field coefficients. This checked Cech statement is not yet the algebraic Reisner criterion.

The positive-degree bridge now has checked stage normalization in `Reisner/Cech/ExtComparison.lean`: for every cohomological degree `q`, the face-ring local-cohomology module is canonically isomorphic to the colimit of `Ext^q(A / (x_v^n), A)`. This uses the project's derived-category Ext model and applies over every commutative coefficient ring, including the zero ring and an empty vertex set. It is not yet a comparison with positive-degree Cech cohomology.

The nonempty Čech rows now also have checked acyclicity: for every nonempty `F`, exponent `n`, and cohomological degree `q`, `Ext^q_A(A/m^n, A_{x_F}) = 0`, and the evaluated Ext-colimit local cohomology of `A_{x_F}` vanishes. This includes ghost/nonface localizations, which may be zero rings. No comparison of the whole Čech complex with local cohomology has yet been proved.

The Ext target functor and its local-cohomology colimit are checked additive and preserve finite products. Consequently, for every positive Čech degree, exponent `n`, and Ext degree `q`, both `Ext^q_A(A/m^n, C^p)` and the project Ext-colimit local cohomology of `C^p` vanish. This is stagewise acyclicity input for the full comparison; the augmented Čech complex has not yet been shown to compute the Ext-colimit.

The actual Čech complex is now also available over the face ring: its differential is built from face-ring algebra maps, proved equal to the existing coefficient-ring differential, and its square-zero identity is inherited from the checked complex. For each fixed augmentation-power stage and Ext degree, termwise application of the derived Ext functor gives a complex with zero terms and homology in all positive Čech degrees. For the cofinal generator-power stages, the fixed complexes are now assembled into a coherent diagram; its degree-zero term colimit is the existing local-cohomology Ext colimit, and the colimit complex has zero terms and homology in positive Čech degrees. This still does not identify a double-complex totalization or original Čech cohomology with the colimit.

Its degree-zero Čech cochain module is checked face-ring-linearly equivalent to `A`, and the degree-zero object after fixed-stage Ext is identified with `Ext^q_A(A/m^n,A)`. The next step remains the genuine comparison between these fixed-stage complexes and the Ext-colimit model; the termwise Ext image alone does not commute with cohomology.

More precisely, the fixed-stage Ext-applied Čech complex has degree-zero homology canonically isomorphic to `Ext^q_A(A/m^n,A)`, while all positive-degree homology vanishes. This is a statement about homology after applying the single functor `Ext^q`; it does not identify `Ext^q` of Čech cohomology and must not be used as the desired hypercohomology comparison.

## Open positive-degree comparison

The blueprint's double-complex/totalization or acyclic-resolution argument comparing positive-degree Čech cohomology with the generator-power Ext-colimit remains open. The coherent diagram of generator-power Ext-applied Čech complexes, natural identification of its degree-zero term colimit, and vanishing of positive terms and homology of its colimit complex are now checked. This diagram still applies each fixed `Ext^q` to the Čech terms before taking the colimit; it does not compute the original Čech cohomology. Keep the derived-category Ext model throughout; no bridge to Mathlib's older left-derived Ext has been proved. Do not assume that the generator-power Koszul complexes resolve `A / (x_v^n)`: variables can be zero divisors. If a Koszul route is chosen over general coefficient rings, establish the needed weak-proregularity or restrict the eventual comparison to the blueprint's stated Noetherian case. Preserve the empty complex, ghost vertices, and degree -1 conventions. The separate graph-connectivity comparison remains unformalized and must not be assumed.

## Open dependencies of the blueprint proof

1. The positive-degree comparison between the face ring's actual Čech cohomology and its Ext-colimit local cohomology remains open.
2. The global converse transferring the augmentation-local test to algebraic Cohen–Macaulayness of the face ring remains open.
3. The converse also uses purity deduced from vanishing below each link's own dimension. Its graph-connectivity argument remains in the blueprint.

## Working rules

- Consult the blueprint before changing mathematical statements, and mark a node checked only after Lean compilation succeeds.
- Reuse the pinned mathlib APIs and existing project definitions. Completed proofs must contain no `sorry`, `admit`, or new axioms. The sole placeholder exception is the requested statement `Reisner.Complex.reisner_criterion`.
- After each milestone, run `lake build`, inspect axioms of the main new theorem, and run the site and blueprint checks if their inputs change. Do not deploy the site.
