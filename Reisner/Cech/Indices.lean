module

public import Reisner.Cech.Basic

@[expose] public section

namespace Reisner.Complex

open scoped Classical
open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} (K : Reisner.Complex V)

/-- In nonpositive degree, admissible localization subsets correspond to
faces of the same-ambient link by deleting the negative support. -/
noncomputable def nonpositiveLocalizationIndexEquivLink (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) :
    {F : Finset V // K.LocalizationAdmissible F a} ≃
      {T : Finset V // T ∈ (K.link (negativeSupport a) hN).faces} where
  toFun F := by
    have hF := (K.localizationAdmissible_iff_of_nonpos a ha F.1).mp F.2
    refine ⟨F.1 \ negativeSupport a, (K.mem_link_iff _ hN _).mpr ⟨Finset.sdiff_disjoint, ?_⟩⟩
    rw [Finset.union_sdiff_of_subset hF.1]
    exact hF.2
  invFun T := by
    have hT := (K.mem_link_iff _ hN T.1).mp T.2
    exact ⟨negativeSupport a ∪ T.1,
      (K.localizationAdmissible_iff_of_nonpos a ha _).mpr
        ⟨Finset.subset_union_left, hT.2⟩⟩
  left_inv F := by
    apply Subtype.ext
    exact Finset.union_sdiff_of_subset
      ((K.localizationAdmissible_iff_of_nonpos a ha F.1).mp F.2).1
  right_inv T := by
    apply Subtype.ext
    exact Finset.union_sdiff_cancel_left ((K.mem_link_iff _ hN T.1).mp T.2).1.symm

@[simp]
theorem nonpositiveLocalizationIndexEquivLink_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (F : {F : Finset V // K.LocalizationAdmissible F a}) :
    (K.nonpositiveLocalizationIndexEquivLink a ha hN F).1 = F.1 \ negativeSupport a := rfl

@[simp]
theorem nonpositiveLocalizationIndexEquivLink_symm_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces)
    (T : {T : Finset V // T ∈ (K.link (negativeSupport a) hN).faces}) :
    ((K.nonpositiveLocalizationIndexEquivLink a ha hN).symm T).1 =
      negativeSupport a ∪ T.1 := rfl

/-- The cardinality relation is additive, retaining the empty link face and
avoiding truncated subtraction in low cochain degrees. -/
theorem nonpositiveLocalizationIndex_card (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (F : {F : Finset V // K.LocalizationAdmissible F a}) :
    F.1.card = (negativeSupport a).card +
      (K.nonpositiveLocalizationIndexEquivLink a ha hN F).1.card := by
  have hF := (K.localizationAdmissible_iff_of_nonpos a ha F.1).mp F.2
  exact (Finset.card_sdiff_add_card_eq_card hF.1).symm.trans (Nat.add_comm _ _)

/-- Cardinality-indexed form of the admissible-subset/link-face bijection.
Every actual Čech subset index remains in the ambient cochain family. -/
noncomputable def nonpositiveCechIndexEquivLink (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (q : ℕ) :
    {F : CechIndex V q // K.LocalizationAdmissible F.1 a} ≃
      {T : Finset V // T ∈ (K.link (negativeSupport a) hN).faces ∧
        (negativeSupport a).card + T.card = q} where
  toFun F := by
    let F' : {F : Finset V // K.LocalizationAdmissible F a} := ⟨F.1.1, F.2⟩
    let T := K.nonpositiveLocalizationIndexEquivLink a ha hN F'
    exact ⟨T.1, T.2, (K.nonpositiveLocalizationIndex_card a ha hN F').symm.trans F.1.2⟩
  invFun T := by
    have hT := (K.mem_link_iff _ hN T.1).mp T.2.1
    refine ⟨⟨negativeSupport a ∪ T.1,
      (Finset.card_union_of_disjoint hT.1.symm).trans T.2.2⟩, ?_⟩
    exact (K.localizationAdmissible_iff_of_nonpos a ha _).mpr
      ⟨Finset.subset_union_left, hT.2⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.union_sdiff_of_subset
      ((K.localizationAdmissible_iff_of_nonpos a ha F.1.1).mp F.2).1
  right_inv T := by
    apply Subtype.ext
    exact Finset.union_sdiff_cancel_left ((K.mem_link_iff _ hN T.1).mp T.2.1).1.symm

@[simp]
theorem nonpositiveCechIndexEquivLink_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (q : ℕ)
    (F : {F : CechIndex V q // K.LocalizationAdmissible F.1 a}) :
    (K.nonpositiveCechIndexEquivLink a ha hN q F).1 = F.1.1 \ negativeSupport a := rfl

@[simp]
theorem nonpositiveCechIndexEquivLink_symm_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (q : ℕ)
    (T : {T : Finset V // T ∈ (K.link (negativeSupport a) hN).faces ∧
      (negativeSupport a).card + T.card = q}) :
    ((K.nonpositiveCechIndexEquivLink a ha hN q).symm T).1.1 =
      negativeSupport a ∪ T.1 := rfl

theorem not_localizationAdmissible_of_card_lt_negativeSupport (a : V →₀ ℤ)
    (ha : a ≤ 0) (q : ℕ) (hq : q < (negativeSupport a).card) (F : CechIndex V q) :
    ¬ K.LocalizationAdmissible F.1 a := by
  intro h
  have hle := Finset.card_le_card ((K.localizationAdmissible_iff_of_nonpos a ha F.1).mp h).1
  rw [F.2] at hle
  exact (Nat.not_le_of_lt hq) hle

theorem not_localizationAdmissible_of_negativeSupport_nonface (a : V →₀ ℤ)
    (ha : a ≤ 0) (hN : negativeSupport a ∉ K.faces) (F : Finset V) :
    ¬ K.LocalizationAdmissible F a := by
  intro h
  have hF := (K.localizationAdmissible_iff_of_nonpos a ha F).mp h
  exact hN (K.face_of_subset hF.1 hF.2)

variable (R : Type v) [CommRing R] [Fintype V]

theorem cechDegreeSubmodule_eq_bot_of_no_admissible (q : ℕ) (a : V →₀ ℤ)
    (hna : ∀ F : CechIndex V q, ¬ K.LocalizationAdmissible F.1 a) :
    K.cechDegreeSubmodule R q a = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  apply (Submodule.mem_bot R).mpr
  funext F
  have hm := (K.mem_cechDegreeSubmodule R z).mp hz F
  rw [K.faceRingLocalizationComponent_eq_bot R F.1 a (hna F)] at hm
  exact (Submodule.mem_bot R).mp hm

/-- A nonface negative support annihilates every actual degree submodule,
over arbitrary commutative coefficients. -/
theorem cechDegreeSubmodule_eq_bot_of_nonpos_negativeSupport_nonface
    (a : V →₀ ℤ) (ha : a ≤ 0) (hN : negativeSupport a ∉ K.faces) (q : ℕ) :
    K.cechDegreeSubmodule R q a = ⊥ :=
  K.cechDegreeSubmodule_eq_bot_of_no_admissible R q a fun F =>
    K.not_localizationAdmissible_of_negativeSupport_nonface a ha hN F.1

theorem cechDegreeSubmodule_eq_bot_of_card_lt_negativeSupport
    (a : V →₀ ℤ) (ha : a ≤ 0) (q : ℕ) (hq : q < (negativeSupport a).card) :
    K.cechDegreeSubmodule R q a = ⊥ :=
  K.cechDegreeSubmodule_eq_bot_of_no_admissible R q a
    (K.not_localizationAdmissible_of_card_lt_negativeSupport a ha q hq)

theorem cechComplexDegree_isZero_of_nonpos_negativeSupport_nonface [LinearOrder V]
    (a : V →₀ ℤ) (ha : a ≤ 0) (hN : negativeSupport a ∉ K.faces) (q : ℕ) :
    CategoryTheory.Limits.IsZero ((K.cechComplexDegree R a).X q) :=
  ModuleCat.isZero_iff_subsingleton.mpr (Submodule.subsingleton_iff_eq_bot.mpr
    (K.cechDegreeSubmodule_eq_bot_of_nonpos_negativeSupport_nonface R a ha hN q))

theorem cechCohomologyDegree_isZero_of_nonpos_negativeSupport_nonface [LinearOrder V]
    (a : V →₀ ℤ) (ha : a ≤ 0) (hN : negativeSupport a ∉ K.faces) (q : ℕ) :
    CategoryTheory.Limits.IsZero (K.cechCohomologyDegree R q a) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.cechComplexDegree_isZero_of_nonpos_negativeSupport_nonface R a ha hN q)).isZero_homology

end Reisner.Complex
