module

public import Reisner.Cech.LinkComparison
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

@[expose] public section

namespace Reisner.Complex

open scoped Classical
open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (K : Reisner.Complex V) (R : Type v) [CommRing R]

/-- Shift the natural face-cardinality complex by the size of the negative
support. The extension inserts zero objects below that cutoff. -/
def cechLinkDegreeEmbedding (m : ℕ) :
    ComplexShape.Embedding (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  f r := m + r
  injective_f := fun _ _ h => Nat.add_left_cancel h
  rel := by
    intro i j h
    change i + 1 = j at h
    change m + i + 1 = m + j
    omega

/-- The link cochain complex shifted to begin in degree `|negativeSupport a|`.
Terms below the cutoff are zero by the `extend` construction. -/
noncomputable def cechLinkShiftedComplex (a : V →₀ ℤ)
    (hN : negativeSupport a ∈ K.faces) : CochainComplex (ModuleCat R) ℕ :=
  ((K.link (negativeSupport a) hN).simplicialCochainComplex R).extend
    (cechLinkDegreeEmbedding (negativeSupport a).card)

/-- A term at or above the cutoff is the corresponding augmented link cochain
module. -/
noncomputable def cechLinkShiftedComplexXIso (a : V →₀ ℤ)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    (K.cechLinkShiftedComplex R a hN).X ((negativeSupport a).card + r) ≅
      ModuleCat.of R ((K.link (negativeSupport a) hN).SimplicialCochain R r) :=
  ((K.link (negativeSupport a) hN).simplicialCochainComplex R).extendXIso
    (cechLinkDegreeEmbedding (negativeSupport a).card) rfl

/-- The shifted complex has the existing link differential under its term
identifications. -/
theorem cechLinkShiftedComplex_d (a : V →₀ ℤ)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    (K.cechLinkShiftedComplex R a hN).d
        ((negativeSupport a).card + r) ((negativeSupport a).card + (r + 1)) ≫
      (K.cechLinkShiftedComplexXIso R a hN (r + 1)).hom =
    (K.cechLinkShiftedComplexXIso R a hN r).hom ≫
      ModuleCat.ofHom ((K.link (negativeSupport a) hN).simplicialDifferential R r) := by
  let e := cechLinkDegreeEmbedding (negativeSupport a).card
  change (((K.link (negativeSupport a) hN).simplicialCochainComplex R).extend e).d
      (e.f r) (e.f (r + 1)) ≫
        (((K.link (negativeSupport a) hN).simplicialCochainComplex R).extendXIso e rfl).hom =
    (((K.link (negativeSupport a) hN).simplicialCochainComplex R).extendXIso e rfl).hom ≫
      ModuleCat.ofHom ((K.link (negativeSupport a) hN).simplicialDifferential R r)
  rw [HomologicalComplex.extend_d_eq _ e rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [(K.link (negativeSupport a) hN).simplicialCochainComplex_d]
  rfl

omit [Fintype V] in
/-- Below the shift, the extended link complex has zero terms. -/
theorem cechLinkShiftedComplex_isZero_of_lt (a : V →₀ ℤ)
    (hN : negativeSupport a ∈ K.faces) {q : ℕ}
    (hq : q < (negativeSupport a).card) :
    CategoryTheory.Limits.IsZero ((K.cechLinkShiftedComplex R a hN).X q) := by
  apply ((K.link (negativeSupport a) hN).simplicialCochainComplex R).isZero_extend_X
    (cechLinkDegreeEmbedding (negativeSupport a).card) q
  intro r h
  change (negativeSupport a).card + r = q at h
  omega

/-- A component with its source cardinality exhibited explicitly. -/
noncomputable def componentIsoOfEq (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) {q : ℕ} (r : ℕ)
    (hr : (negativeSupport a).card + r = q) :
    (K.cechComplexDegree R a).X q ≅ (K.cechLinkShiftedComplex R a hN).X q :=
  eqToIso (congrArg (fun n => (K.cechComplexDegree R a).X n) hr.symm) ≪≫
    (K.cechNonpositiveLinkEquiv R a ha hN r).toModuleIso ≪≫
      (((K.link (negativeSupport a) hN).simplicialCochainComplex R).extendXIso
        (cechLinkDegreeEmbedding (negativeSupport a).card) hr).symm

/-- Compare one Cech term with the corresponding term of the shifted link
complex. The comparison is zero below the negative-support cutoff and is the
checked signed term equivalence at and above the cutoff. -/
noncomputable def cechNonpositiveLinkComplexComponentIso (a : V →₀ ℤ)
    (ha : a ≤ 0) (hN : negativeSupport a ∈ K.faces) (q : ℕ) :
    (K.cechComplexDegree R a).X q ≅ (K.cechLinkShiftedComplex R a hN).X q := by
  by_cases hq : q < (negativeSupport a).card
  · have hbot : K.cechDegreeSubmodule R q a = ⊥ :=
      K.cechDegreeSubmodule_eq_bot_of_card_lt_negativeSupport R a ha q hq
    have hC : CategoryTheory.Limits.IsZero ((K.cechComplexDegree R a).X q) :=
      ModuleCat.isZero_iff_subsingleton.mpr
        (Submodule.subsingleton_iff_eq_bot.mpr hbot)
    exact hC.iso (K.cechLinkShiftedComplex_isZero_of_lt R a hN hq)
  · have hmq : (negativeSupport a).card ≤ q := by omega
    let r := q - (negativeSupport a).card
    have hr : (negativeSupport a).card + r = q := by dsimp [r]; omega
    exact K.componentIsoOfEq R a ha hN r hr

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem cechNonpositiveLinkComplexComponentIso_add (a : V →₀ ℤ)
    (ha : a ≤ 0) (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    K.cechNonpositiveLinkComplexComponentIso R a ha hN
        ((negativeSupport a).card + r) =
      (K.cechNonpositiveLinkEquiv R a ha hN r).toModuleIso ≪≫
        (K.cechLinkShiftedComplexXIso R a hN r).symm := by
  have hn : ¬ (negativeSupport a).card + r < (negativeSupport a).card := by omega
  have hsub : (negativeSupport a).card + r - (negativeSupport a).card = r := by omega
  simp only [cechNonpositiveLinkComplexComponentIso, dite_eq_right hn, hsub]
  simp only [componentIsoOfEq, eqToIso_refl, Iso.refl_trans]
  rfl

attribute [local implicit_reducible] cechComplexDegree cechLinkShiftedComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degreewise comparisons form an isomorphism of actual cochain
complexes, including the zero terms below the negative-support cutoff. -/
noncomputable def cechNonpositiveLinkComplexIso (a : V →₀ ℤ)
    (ha : a ≤ 0) (hN : negativeSupport a ∈ K.faces) :
    K.cechComplexDegree R a ≅ K.cechLinkShiftedComplex R a hN :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => K.cechNonpositiveLinkComplexComponentIso R a ha hN q)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      by_cases hlow : i < (negativeSupport a).card
      · have hbot : K.cechDegreeSubmodule R i a = ⊥ :=
          K.cechDegreeSubmodule_eq_bot_of_card_lt_negativeSupport R a ha i hlow
        have hsource : CategoryTheory.Limits.IsZero ((K.cechComplexDegree R a).X i) :=
          ModuleCat.isZero_iff_subsingleton.mpr
            (Submodule.subsingleton_iff_eq_bot.mpr hbot)
        exact hsource.eq_of_src _ _
      · let r := i - (negativeSupport a).card
        have hir : i = (negativeSupport a).card + r := by dsimp [r]; omega
        rw [hir]
        have hsucc : (negativeSupport a).card + r + 1 =
            (negativeSupport a).card + (r + 1) := by omega
        rw [hsucc]
        rw [K.cechNonpositiveLinkComplexComponentIso_add R a ha hN r,
          K.cechNonpositiveLinkComplexComponentIso_add R a ha hN (r + 1)]
        let φ := (K.cechNonpositiveLinkEquiv R a ha hN r).toModuleIso
        let φ' := (K.cechNonpositiveLinkEquiv R a ha hN (r + 1)).toModuleIso
        let ρ := K.cechLinkShiftedComplexXIso R a hN r
        let ρ' := K.cechLinkShiftedComplexXIso R a hN (r + 1)
        change (φ.hom ≫ ρ.inv) ≫ (K.cechLinkShiftedComplex R a hN).d _ _ =
          (K.cechComplexDegree R a).d _ _ ≫ (φ'.hom ≫ ρ'.inv)
        rw [← cancel_mono ρ'.hom]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [K.cechLinkShiftedComplex_d R a hN r]
        change φ.hom ≫ ρ.inv ≫ ρ.hom ≫
          ModuleCat.ofHom ((K.link (negativeSupport a) hN).simplicialDifferential R r) =
          (K.cechComplexDegree R a).d
            ((negativeSupport a).card + r) (((negativeSupport a).card + r) + 1) ≫ φ'.hom
        rw [ρ.inv_hom_id_assoc]
        rw [K.cechComplexDegree_d]
        apply ModuleCat.hom_ext
        exact (K.cechNonpositiveLinkEquiv_differential R a ha hN r).symm)

/-- Actual homology objects of the Cech degree complex and shifted link complex
are identified in every natural cochain degree. -/
noncomputable def cechNonpositiveLinkHomologyIso (a : V →₀ ℤ)
    (ha : a ≤ 0) (hN : negativeSupport a ∈ K.faces) (q : ℕ) :
    (K.cechComplexDegree R a).homology q ≅
      (K.cechLinkShiftedComplex R a hN).homology q :=
  HomologicalComplex.homologyMapIso (K.cechNonpositiveLinkComplexIso R a ha hN) q

/-- At and above the cutoff, Cech homology is the link's natural
face-cardinality cohomology. -/
noncomputable def cechNonpositiveLinkNaturalHomologyIso (a : V →₀ ℤ)
    (ha : a ≤ 0) (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    (K.cechComplexDegree R a).homology ((negativeSupport a).card + r) ≅
      ((K.link (negativeSupport a) hN).simplicialCochainComplex R).homology r :=
  K.cechNonpositiveLinkHomologyIso R a ha hN _ ≪≫
    ((K.link (negativeSupport a) hN).simplicialCochainComplex R).extendHomologyIso
      (cechLinkDegreeEmbedding (negativeSupport a).card) rfl

/-- At Cech degree `|N|+r`, the actual homology is the augmented link's
reduced cohomology object in integer degree `r-1`, including `r=0`. -/
noncomputable def cechNonpositiveLinkCohomologyIso (a : V →₀ ℤ)
    (ha : a ≤ 0) (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    (K.cechComplexDegree R a).homology ((negativeSupport a).card + r) ≅
      ((K.link (negativeSupport a) hN).simplicialCochainComplexInt R).homology ((r : ℤ) - 1) :=
  K.cechNonpositiveLinkNaturalHomologyIso R a ha hN r ≪≫
    ((K.link (negativeSupport a) hN).simplicialCochainComplexIntHomologyIso R
      (n := r) (i := (r : ℤ) - 1) rfl).symm

/-- Below the cutoff, the corresponding actual Cech cohomology object is zero. -/
theorem cechCohomologyDegree_isZero_of_nonpos_card_lt_negativeSupport
    (a : V →₀ ℤ) (ha : a ≤ 0) (hN : negativeSupport a ∈ K.faces)
    (q : ℕ) (hq : q < (negativeSupport a).card) :
    CategoryTheory.Limits.IsZero (K.cechCohomologyDegree R q a) :=
  CategoryTheory.Limits.IsZero.of_iso
    ((HomologicalComplex.ExactAt.of_isZero
      (K.cechLinkShiftedComplex_isZero_of_lt R a hN hq)).isZero_homology)
    (K.cechNonpositiveLinkHomologyIso R a ha hN q)

end Reisner.Complex
