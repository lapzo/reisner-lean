import Reisner.Cech.Purity

open Reisner Reisner.Complex
open scoped Classical

#check Reisner.Complex.link_link
#check Reisner.Complex.mem_facets_link_iff
#check Reisner.Complex.linkFacetEquiv
#check Reisner.Complex.linkFacetEquiv_apply
#check Reisner.Complex.linkFacetEquiv_symm_apply
#check Reisner.Complex.link_face_card_add_le_maxFaceCard
#check Reisner.Complex.link_maxFaceCard_add_card_le
#check Reisner.Complex.link_dimension_le
#check Reisner.Complex.link_maxFaceCard_eq_zero_of_facet
#check Reisner.Complex.link_dimension_eq_neg_one_of_facet
#check Reisner.Complex.link_maxFaceCard_add_card_eq_of_pure
#check Reisner.Complex.link_dimension_eq_of_pure
#check Reisner.Complex.link_pure_of_pure
#check Reisner.Complex.facet_card_ge_of_uniform_linkCohomology_vanishes
#check Reisner.Complex.facet_card_eq_maxFaceCard_of_uniform_linkCohomology_vanishes
#check Reisner.Complex.facet_card_eq_maxFaceCard_of_cechCohomology_vanishes
#check Reisner.Complex.link_dimension_eq_of_cechCohomology_vanishes
#check Reisner.Complex.linkCohomology_vanishes_below_dimension_of_cechCohomology_vanishes
#check Reisner.Complex.cechCohomology_vanishes_of_pure_linkCohomology_vanishes
#check Reisner.Complex.cechCohomology_vanishes_iff_pure_and_linkCohomology_vanishes

#print axioms Reisner.Complex.link_link
#print axioms Reisner.Complex.mem_facets_link_iff
#print axioms Reisner.Complex.linkFacetEquiv
#print axioms Reisner.Complex.linkFacetEquiv_apply
#print axioms Reisner.Complex.linkFacetEquiv_symm_apply
#print axioms Reisner.Complex.link_face_card_add_le_maxFaceCard
#print axioms Reisner.Complex.link_maxFaceCard_add_card_le
#print axioms Reisner.Complex.link_dimension_le
#print axioms Reisner.Complex.link_maxFaceCard_eq_zero_of_facet
#print axioms Reisner.Complex.link_dimension_eq_neg_one_of_facet
#print axioms Reisner.Complex.link_maxFaceCard_add_card_eq_of_pure
#print axioms Reisner.Complex.link_dimension_eq_of_pure
#print axioms Reisner.Complex.link_pure_of_pure
#print axioms Reisner.Complex.facet_card_ge_of_uniform_linkCohomology_vanishes
#print axioms Reisner.Complex.facet_card_eq_maxFaceCard_of_uniform_linkCohomology_vanishes
#print axioms Reisner.Complex.facet_card_eq_maxFaceCard_of_cechCohomology_vanishes
#print axioms Reisner.Complex.link_dimension_eq_of_cechCohomology_vanishes
#print axioms Reisner.Complex.linkCohomology_vanishes_below_dimension_of_cechCohomology_vanishes
#print axioms Reisner.Complex.cechCohomology_vanishes_of_pure_linkCohomology_vanishes
#print axioms Reisner.Complex.cechCohomology_vanishes_iff_pure_and_linkCohomology_vanishes

/- The empty linked face leaves facets unchanged; no ambient nonemptiness
or non-ghost hypothesis is added to the facet correspondence. -/
example {V : Type*} (K : Reisner.Complex V) (G : K.facets) :
    ∅ ∪ G.1 ∈ K.facets := by simp

/- Iterated links retain the augmentation even when the intermediate face
is empty. -/
example {V : Type*} (K : Reisner.Complex V) (σ : Finset V) (hσ : σ ∈ K.faces) :
    (K.link σ hσ).link ∅ (K.link σ hσ).empty_mem = K.link σ hσ :=
  (K.link σ hσ).link_empty

/- Facet links have dimension -1, rather than dimension zero or the void
complex, including the empty-only ambient complex. -/
example {V : Type*} [Finite V] (K : Reisner.Complex V) (F : K.facets) :
    (K.link F.1 F.2.1).dimension = -1 :=
  K.link_dimension_eq_neg_one_of_facet F.2

/- The Čech purity consequence includes the dimension-zero ring case:
on an empty ambient vertex type its cutoff is zero and vacuous. -/
example (K : Reisner.Complex PEmpty) (R : Type*) [CommRing R] [Nontrivial R]
    (F : K.facets) : F.1.card = K.maxFaceCard := by
  apply K.facet_card_eq_maxFaceCard_of_cechCohomology_vanishes R ?_ F
  have hmax : K.maxFaceCard = 0 :=
    K.maxFaceCard_eq_zero_iff_no_vertices.mpr (fun v => PEmpty.elim v)
  intro q hq
  exact False.elim (Nat.not_lt_zero q (hmax ▸ hq))

/- A uniform cutoff larger than the size of any given facet is impossible
over a nontrivial coefficient ring, as its link has nonzero H^-1. -/
example {V : Type*} [Fintype V] [LinearOrder V] (K : Reisner.Complex V)
    (R : Type*) [CommRing R] [Nontrivial R] (d : ℕ) (F : K.facets)
    (hVanishing : ∀ (G : Finset V) (hG : G ∈ K.faces) (r : ℕ), G.card + r < d →
      Subsingleton (((K.link G hG).simplicialCochainComplexInt R).homology ((r : ℤ) - 1))) :
    ¬ F.1.card < d :=
  Nat.not_lt_of_ge (K.facet_card_ge_of_uniform_linkCohomology_vanishes R d hVanishing F)
