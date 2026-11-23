# Current task: package the shifted Cech/link cohomology comparison

The signed termwise comparison between a nonpositive fine-degree Cech
subcomplex and augmented cochains of its link is checked, including inverse
formulas and differential compatibility. Positive-coordinate contraction
and the nonface-negative-support zero case are checked. The next dependency
for the local-cohomology link formula is to package these maps as an actual
shifted cochain-complex isomorphism and transport actual homology. This is
not the Cech/local-cohomology comparison or the full theorem thm:lc-link.

Read AGENTS.md, STATUS.md, AUDIT.md, the blueprint, Lean source/checks, and
pinned mathlib. Preserve checked results, APIs, empty-face/ghost conventions,
and pins. Work locally. No commits, publication, sorry/admit, or new axioms.

## Mathematical target

Let V be finite and linearly ordered, K : Complex V, R a commutative ring,
a : V →₀ ℤ with a ≤ 0, N := negativeSupport a, and hN : N ∈ K.faces.
Set L := K.link N hN and m := N.card. The checked source complex is
K.cechComplexDegree R a. Define an actual natural-indexed shifted link
complex D in ModuleCat R by

- D.X q = 0 when q < m;
- D.X (m+r) = ModuleCat.of R (L.SimplicialCochain R r);
- its differential is zero below m and the existing simplicial
  differential at r from m+r to m+(r+1).

Prove D is a cochain complex. Construct an actual cochain-complex
isomorphism K.cechComplexDegree R a ≅ D. Below m, use the already checked
zero theorem for Cech degree modules. At q=m+r, use the checked
cechNonpositiveLinkEquiv and its differential-compatibility theorem.
Prove the induced actual homology-object equivalence in every degree q.
For q=m+r identify the result with the link's actual reduced cohomology
object at integer degree (r:ℤ)-1 using the checked integer reindexing of
augmented cochains. State the q<m zero case separately; do not use truncated
subtraction there. Keep r=0 and the empty link face, so degree -1 remains.

This result is over arbitrary commutative R, including the zero ring and
characteristic two. Do not claim the local-cohomology comparison,
higher-degree vanishing below link dimension, or full thm:lc-link.
The existing nonface-N and positive-coordinate zero results remain intact.

## Builder: API route and blueprint source

Builder owns blueprint/src/content.tex.

1. Define a custom ComplexShape.Embedding (up ℕ) (up ℕ) by r ↦ m+r,
   with injectivity by cancellation and relation preservation by
   m+(r+1)=(m+r)+1. Use HomologicalComplex.extend on the checked link
   complex to obtain D. This supplies the genuine cutoff complex directly,
   with extendXIso for terms, extend_d_eq for the unchanged differential,
   isZero_extend_X below m, and extendHomologyIso at m+r.
   Package the component maps using HomologicalComplex.Hom.isoOfComponents;
   use homologyMapIso for the induced actual homology isomorphism.
   Compose with the checked link integer-reindexing homology isomorphism
   in the inverse direction. A small prototype of this route is compiled
   in /tmp/reisner-link-cutoff-api.lean; no project Lean is implemented yet.
2. Add a distinct node, e.g. lem:cech-link-cohomology-comparison, depending
   on lem:cech-link-coordinate-comparison, lem:cech-nonpositive-indices,
   and the checked augmented cochain/reindexing nodes. State D, the complex
   isomorphism, q<m vanishing, and q=m+r homology identification exactly.
3. Give Formalizer exact types, source anchors, cutoff arithmetic, and
   edge-case expectations. Do not mark claims checked before compilation.
   Do not edit Lean/checks/docs/site/pins in this stage.

## Formalizer: implementation and validation

Formalizer owns Lean and checks, not blueprint source. Reuse
cechComplexDegree, cechNonpositiveLinkEquiv, its differential theorem, and
simplicialCochainComplexInt. Do not create new link differentials or change
signs.

Acceptance:

- D has the exact zero and shifted terms and the specified differentials;
- D satisfies the cochain-complex law;
- the component equivalences form an actual cochain-complex isomorphism,
  not merely a family of termwise maps;
- actual homology is identified for q<m and q=m+r, with the link reduced
  degree r-1 made explicit through the existing integer reindexing;
- focused checks cover N=∅, nonempty face N, empty link, q<m, q=m, r=0,
  and arbitrary coefficients including the zero ring;
- run lake build, lake env lean Checks/Axioms.lean, Checks/Cech.lean, and
  Checks/SimplicialCochain.lean; inspect axioms for D, the complex
  isomorphism, and homology result; scan for sorry/admit/custom axioms.

Do not edit pins, existing checked statements, or blueprint source. Report
exact declarations, proof route, validation, and gaps. If the manual cutoff
does not match the checked term maps, report the blocker; do not add
hypotheses or drop the empty-face case.

## Builder finalization and Weber

After successful Lean handoff, Builder links and marks only compiled shifted
complex and homology statements. Keep full thm:lc-link, found:cech's local
cohomology comparison, def:homology, lem:dual, and the full criterion future
unless their entire statements are proved.

Weber then regenerates local blueprint PDF/HTML, declarations and graph;
runs leanblueprint checkdecls, lake build, axiom/check files,
python3 site/build.py, and python3 scripts/check_site.py; and updates
STATUS.md, AUDIT.md, and README with verified results only. No reports or
publication.

## Scope estimate

Target 35-45 minutes. The termwise maps, sign correction, cutoff zero terms,
cochain complexes, and integer reindexing already exist. New work is one
custom natural-index embedding and its zero extension, packaging component
maps with pinned homological-complex APIs, and transporting actual homology.
Do not expand into local cohomology.
