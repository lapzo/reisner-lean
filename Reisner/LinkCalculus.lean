module

public import Reisner.StanleyReisner

/-!
# Links, facets, and simplicial dimension

These results use the same ambient vertex type, retain the empty face, and
allow ghost vertices. Facet correspondence works without ambient finiteness;
dimension statements use the project's finite maximum-face convention.
-/

@[expose] public section

namespace Reisner.Complex

open scoped Classical

universe u

variable {V : Type u} (K : Reisner.Complex V)

private theorem eq_of_face_membership {K L : Reisner.Complex V}
    (h : ∀ T : Finset V, T ∈ K.faces ↔ T ∈ L.faces) : K = L := by
  cases K with
  | mk faces empty_mem =>
    cases L with
    | mk faces' empty_mem' =>
      congr 1
      ext T
      exact h T

/-- Taking a link inside a link amounts to adjoining the two disjoint faces. -/
theorem link_link (σ : Finset V) (hσ : σ ∈ K.faces) (τ : Finset V)
    (hτ : τ ∈ (K.link σ hσ).faces) :
    (K.link σ hσ).link τ hτ =
      K.link (σ ∪ τ) ((K.mem_link_iff σ hσ τ).mp hτ).2 := by
  apply eq_of_face_membership
  intro T
  simp only [mem_link_iff]
  have hτσ := ((K.mem_link_iff σ hσ τ).mp hτ).1
  constructor
  · rintro ⟨hTτ, hUσ, hface⟩
    refine ⟨Finset.disjoint_union_right.mpr
      ⟨hUσ.mono_left Finset.subset_union_right, hTτ⟩, ?_⟩
    simpa only [Finset.union_assoc] using hface
  · rintro ⟨hT, hface⟩
    obtain ⟨hTσ, hTτ⟩ := Finset.disjoint_union_right.mp hT
    refine ⟨hTτ, Finset.disjoint_union_left.mpr ⟨hτσ, hTσ⟩, ?_⟩
    simpa only [Finset.union_assoc] using hface

/-- Facets of a link are precisely the differences of ambient facets
containing the linked face, expressed by their union with that face. -/
theorem mem_facets_link_iff (σ : Finset V) (hσ : σ ∈ K.faces) (T : Finset V) :
    T ∈ (K.link σ hσ).facets ↔ Disjoint T σ ∧ σ ∪ T ∈ K.facets := by
  constructor
  · intro hT
    have hTF := (K.mem_link_iff σ hσ T).mp hT.1
    refine ⟨hTF.1, hTF.2, ?_⟩
    intro G hG hUG
    have hσG : σ ⊆ G := Finset.subset_union_left.trans hUG
    have hdiff : G \ σ ∈ (K.link σ hσ).faces := by
      apply (K.mem_link_iff σ hσ _).mpr
      refine ⟨Finset.sdiff_disjoint, ?_⟩
      rw [Finset.union_sdiff_of_subset hσG]
      exact hG
    have hTdiff : T ⊆ G \ σ := by
      intro v hv
      exact Finset.mem_sdiff.mpr
        ⟨hUG (Finset.mem_union_right σ hv),
          fun hvσ => Finset.disjoint_left.mp hTF.1 hv hvσ⟩
    have hdiffT := hT.le_of_ge hdiff hTdiff
    intro v hvG
    by_cases hvσ : v ∈ σ
    · exact Finset.mem_union_left T hvσ
    · exact Finset.mem_union_right σ (hdiffT (Finset.mem_sdiff.mpr ⟨hvG, hvσ⟩))
  · rintro ⟨hTσ, hU⟩
    refine ⟨(K.mem_link_iff σ hσ T).mpr ⟨hTσ, hU.1⟩, ?_⟩
    intro G hG hTG
    have hGF := (K.mem_link_iff σ hσ G).mp hG
    have hGU := hU.le_of_ge hGF.2 (Finset.union_subset_union_right hTG)
    intro v hvG
    rcases Finset.mem_union.mp (hGU (Finset.mem_union_right σ hvG)) with hvσ | hvT
    · exact False.elim (Finset.disjoint_left.mp hGF.1 hvG hvσ)
    · exact hvT

/-- The actual bijection between facets of a link and ambient facets
containing the linked face. No finite ambient hypothesis is required. -/
noncomputable def linkFacetEquiv (σ : Finset V) (hσ : σ ∈ K.faces) :
    (K.link σ hσ).facets ≃ {G : K.facets // σ ⊆ G.1} where
  toFun T :=
    ⟨⟨σ ∪ T.1, ((K.mem_facets_link_iff σ hσ T.1).mp T.2).2⟩,
      Finset.subset_union_left⟩
  invFun G := by
    refine ⟨G.1.1 \ σ, (K.mem_facets_link_iff σ hσ _).mpr ⟨Finset.sdiff_disjoint, ?_⟩⟩
    rw [Finset.union_sdiff_of_subset G.2]
    exact G.1.2
  left_inv T := by
    apply Subtype.ext
    exact Finset.union_sdiff_cancel_left
      ((K.mem_facets_link_iff σ hσ T.1).mp T.2).1.symm
  right_inv G := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.union_sdiff_of_subset G.2

@[simp]
theorem linkFacetEquiv_apply (σ : Finset V) (hσ : σ ∈ K.faces)
    (T : (K.link σ hσ).facets) : (K.linkFacetEquiv σ hσ T).1.1 = σ ∪ T.1 := rfl

@[simp]
theorem linkFacetEquiv_symm_apply (σ : Finset V) (hσ : σ ∈ K.faces)
    (G : {G : K.facets // σ ⊆ G.1}) :
    ((K.linkFacetEquiv σ hσ).symm G).1 = G.1.1 \ σ := rfl

/-- Every link face gives a disjoint union face of the ambient complex. -/
theorem link_face_card_add_le_maxFaceCard [Finite V] (σ : Finset V)
    (hσ : σ ∈ K.faces) {T : Finset V} (hT : T ∈ (K.link σ hσ).faces) :
    σ.card + T.card ≤ K.maxFaceCard := by
  have h := (K.mem_link_iff σ hσ T).mp hT
  rw [← Finset.card_union_of_disjoint h.1.symm]
  exact K.card_le_maxFaceCard h.2

/-- The finite maximum link-face size is bounded by the ambient maximum
minus the size of the linked face, stated without natural subtraction. -/
theorem link_maxFaceCard_add_card_le [Finite V] (σ : Finset V) (hσ : σ ∈ K.faces) :
    σ.card + (K.link σ hσ).maxFaceCard ≤ K.maxFaceCard := by
  obtain ⟨T, hT, hcard⟩ := (K.link σ hσ).exists_face_card_eq_maxFaceCard
  rw [← hcard]
  exact K.link_face_card_add_le_maxFaceCard σ hσ hT

theorem link_dimension_le [Finite V] (σ : Finset V) (hσ : σ ∈ K.faces) :
    (K.link σ hσ).dimension ≤ K.dimension - (σ.card : ℤ) := by
  have h := K.link_maxFaceCard_add_card_le σ hσ
  unfold dimension
  omega

/-- A facet link has the one empty face, hence maximum face cardinality zero. -/
theorem link_maxFaceCard_eq_zero_of_facet [Finite V] {σ : Finset V} (hσ : σ ∈ K.facets) :
    (K.link σ hσ.1).maxFaceCard = 0 := by
  apply ((K.link σ hσ.1).maxFaceCard_eq_zero_iff_no_vertices).mpr
  intro v hv
  exact Finset.singleton_ne_empty v ((K.mem_link_facet_iff hσ {v}).mp hv)

/-- The augmented facet-link dimension is `-1`, including when the facet is empty. -/
theorem link_dimension_eq_neg_one_of_facet [Finite V] {σ : Finset V} (hσ : σ ∈ K.facets) :
    (K.link σ hσ.1).dimension = -1 := by
  unfold dimension
  rw [K.link_maxFaceCard_eq_zero_of_facet hσ]
  norm_num

/-- If every ambient facet has maximum size, link maximum sizes attain the
dimension bound. This includes the empty face and facet links. -/
theorem link_maxFaceCard_add_card_eq_of_pure [Finite V]
    (hPure : ∀ G : K.facets, G.1.card = K.maxFaceCard)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    σ.card + (K.link σ hσ).maxFaceCard = K.maxFaceCard := by
  apply le_antisymm (K.link_maxFaceCard_add_card_le σ hσ)
  obtain ⟨G, hσG⟩ := K.exists_facet_superset hσ
  let T := (K.linkFacetEquiv σ hσ).symm ⟨G, hσG⟩
  have hT := (K.link σ hσ).card_le_maxFaceCard T.2.1
  have hcard : G.1.card = σ.card + T.1.card :=
    (Finset.card_sdiff_add_card_eq_card hσG).symm.trans (Nat.add_comm _ _)
  rw [hPure G] at hcard
  omega

theorem link_dimension_eq_of_pure [Finite V]
    (hPure : ∀ G : K.facets, G.1.card = K.maxFaceCard)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    (K.link σ hσ).dimension = K.dimension - (σ.card : ℤ) := by
  have h := K.link_maxFaceCard_add_card_eq_of_pure hPure σ hσ
  unfold dimension
  omega

/-- Links of pure finite complexes are pure, with their own maximum-face
convention and without discarding ghost ambient vertices. -/
theorem link_pure_of_pure [Finite V]
    (hPure : ∀ G : K.facets, G.1.card = K.maxFaceCard)
    (σ : Finset V) (hσ : σ ∈ K.faces) (T : (K.link σ hσ).facets) :
    T.1.card = (K.link σ hσ).maxFaceCard := by
  have hF := (K.mem_facets_link_iff σ hσ T.1).mp T.2
  have hcard := hPure ⟨σ ∪ T.1, hF.2⟩
  rw [Finset.card_union_of_disjoint hF.1.symm] at hcard
  have hmax := K.link_maxFaceCard_add_card_eq_of_pure hPure σ hσ
  omega

end Reisner.Complex
