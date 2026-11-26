module

public import Reisner.Cech.ExtComparison
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

@[expose] public section

/-!
# Vanishing of Ext stages with nonempty localization targets

An element which kills the source of an Ext group and acts invertibly on
its target forces every Ext class to vanish.  Applied to a variable in a
nonempty localization index, this kills every augmentation-power stage.
All Ext groups here use the project's derived-category implementation.
-/

open CategoryTheory Limits Opposite

universe u v w

namespace Reisner

variable {A : Type u} [CommRing A]

/-- Scalar annihilation of the source, together with invertibility on the
target, kills derived Ext in every degree, including degree zero. -/
theorem derivedExt_eq_zero_of_smul_id_eq_zero
    {M N : ModuleCat.{v} A} [Small.{v} A] (r : A)
    (hM : r • 𝟙 M = 0) [IsIso (r • 𝟙 N)] (q : ℕ)
    (e : CategoryTheory.Abelian.Ext M N q) : e = 0 := by
  open CategoryTheory.Abelian in
  have h : r • e = 0 := by
    have he : r • e = (Ext.mk₀ (r • 𝟙 M)).comp e (zero_add q) := by
      simp [Ext.mk₀_smul]
    rw [he, hM]
    simp
  let T := CategoryTheory.Abelian.linearExtFunctorObj A M q
  have hinj : Function.Injective (T.map (r • 𝟙 N)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinj
  simpa [T, CategoryTheory.Abelian.linearExtFunctorObj,
    CategoryTheory.Abelian.Ext.mk₀_smul] using h

/-- An element annihilating the source kills all Ext classes when its image
is a unit in the coefficient algebra. The coefficient algebra may be zero. -/
theorem derivedExt_eq_zero_of_annihilator_isUnit
    {M : ModuleCat.{v} A} [Small.{v} A] (B : Type v) [CommRing B] [Algebra A B]
    (r : A) (hM : r ∈ Module.annihilator A M)
    (hB : IsUnit (algebraMap A B r)) (q : ℕ)
    (e : CategoryTheory.Abelian.Ext M (ModuleCat.of A B) q) : e = 0 := by
  have hsource : r • 𝟙 M = 0 := by
    ext m
    exact Module.mem_annihilator.mp hM m
  have : IsIso (r • 𝟙 (ModuleCat.of A B)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun b : B => r • b)
    simpa only [Algebra.smul_def] using IsUnit.isUnit_iff_mulLeft_bijective.mp hB
  exact derivedExt_eq_zero_of_smul_id_eq_zero r hsource q e

/-- If an ideal contains an element inverted in `B`, all derived Ext from
its quotient into `B` vanishes. No nontriviality assumption is required. -/
theorem derivedExt_quotient_eq_zero_of_mem_of_isUnit
    (J : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    (r : A) (hr : r ∈ J) (hB : IsUnit (algebraMap A B r)) (q : ℕ)
    (e : CategoryTheory.Abelian.Ext (ModuleCat.of A (A ⧸ J)) (ModuleCat.of A B) q) :
    e = 0 := by
  apply derivedExt_eq_zero_of_annihilator_isUnit B r ?_ hB q e
  simpa only [ModuleCat.coe_of, Ideal.annihilator_quotient] using hr

end Reisner

namespace Reisner.Complex

variable {V : Type u} (K : Reisner.Complex V) (R : Type v) [CommRing R]

/-- Every variable indexed by `F` becomes a unit in the actual face-ring
localization, also when a nonface index makes that localization zero. -/
theorem faceRingLocalization_variable_isUnit {F : Finset V} {w : V} (hw : w ∈ F) :
    IsUnit (algebraMap (K.FaceRing R) (K.FaceRingLocalization R F)
      (Ideal.Quotient.mk (K.stanleyReisnerIdeal R) (MvPolynomial.X w))) := by
  classical
  apply IsLocalization.Away.isUnit_of_dvd (K.faceRingFaceProduct R F)
  exact Finset.dvd_prod_of_mem _ hw

/-- Every augmentation-power stage vanishes against a nonempty face-ring
localization, in every derived Ext degree and at exponent zero. The index
need not be a face, and the coefficient ring need not be nontrivial. -/
theorem faceRingLocalization_augmentationPower_ext_eq_zero
    {F : Finset V} (hF : F.Nonempty) (n q : ℕ)
    (e : CategoryTheory.Abelian.Ext
      (ModuleCat.of (K.FaceRing R) (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n))
      (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F)) q) : e = 0 := by
  obtain ⟨w, hw⟩ := hF
  apply Reisner.derivedExt_quotient_eq_zero_of_mem_of_isUnit
    (K.faceRingAugmentationIdeal R ^ n) (K.FaceRingLocalization R F)
    ((Ideal.Quotient.mk (K.stanleyReisnerIdeal R) (MvPolynomial.X w)) ^ n) ?_ ?_ q e
  · have hwmem : Ideal.Quotient.mk (K.stanleyReisnerIdeal R) (MvPolynomial.X w) ∈
        K.faceRingAugmentationIdeal R := Ideal.subset_span ⟨w, rfl⟩
    exact Ideal.pow_mem_pow hwmem n
  · simpa only [map_pow] using (K.faceRingLocalization_variable_isUnit R hw).pow n

/-- The same vanishing holds for the cofinal generator-power quotients. -/
theorem faceRingLocalization_generatorPower_ext_eq_zero
    {F : Finset V} (hF : F.Nonempty) (n q : ℕ)
    (e : CategoryTheory.Abelian.Ext
      (ModuleCat.of (K.FaceRing R) (K.FaceRing R ⧸ K.faceRingGeneratorPowerIdeal R n))
      (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F)) q) : e = 0 := by
  obtain ⟨w, hw⟩ := hF
  apply Reisner.derivedExt_quotient_eq_zero_of_mem_of_isUnit
    (K.faceRingGeneratorPowerIdeal R n) (K.FaceRingLocalization R F)
    ((Ideal.Quotient.mk (K.stanleyReisnerIdeal R) (MvPolynomial.X w)) ^ n) ?_ ?_ q e
  · exact Ideal.subset_span ⟨w, rfl⟩
  · simpa only [map_pow] using (K.faceRingLocalization_variable_isUnit R hw).pow n

/-- Every stage of the augmentation-power Ext diagram with a nonempty
localization target is a zero module. -/
theorem faceRingLocalization_augmentationPower_ext_isZero
    {F : Finset V} (hF : F.Nonempty) (n q : ℕ) :
    IsZero (ModuleCat.of (K.FaceRing R) (CategoryTheory.Abelian.Ext
      (ModuleCat.of (K.FaceRing R) (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n))
      (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F)) q)) := by
  have : Subsingleton (CategoryTheory.Abelian.Ext
      (ModuleCat.of (K.FaceRing R) (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n))
      (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F)) q) :=
    subsingleton_of_forall_eq 0
      (K.faceRingLocalization_augmentationPower_ext_eq_zero R hF n q)
  exact ModuleCat.isZero_of_subsingleton _

/-- Augmentation-supported local cohomology of every nonempty face-ring
localization vanishes in every degree in the derived Ext-colimit model.
This is an acyclicity statement for the localization terms, not yet the
comparison of the whole Čech complex with local cohomology. -/
theorem faceRingLocalization_localCohomology_isZero
    {F : Finset V} (hF : F.Nonempty) (q : ℕ) :
    IsZero ((Reisner.depthExtLocalCohomology (K.faceRingAugmentationIdeal R) q).obj
      (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F))) := by
  let D := Reisner.depthExtLocalCohomologyModuleDiagram
    (K.faceRingAugmentationIdeal R) q
    (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F))
  have hD : ∀ j, IsZero (D.obj j) := by
    intro j
    exact K.faceRingLocalization_augmentationPower_ext_isZero R hF j.unop.unop q
  have hcol : IsZero (colimit D) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro j
    exact (hD j).eq_of_src _ _
  exact hcol.of_iso
    (colimitObjIsoColimitCompEvaluation
      (Reisner.depthExtLocalCohomologyDiagram (K.faceRingAugmentationIdeal R) q)
      (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F)))

/-- Every positive Čech cochain module is acyclic for the Ext-colimit local
cohomology functor. The cochain module is a finite product of localization
targets; additivity of the functor transports the rowwise vanishing to that
product. -/
theorem faceRingCechCochain_localCohomology_isZero [Fintype V]
    {p : ℕ} (hp : 0 < p) (q : ℕ) :
    IsZero ((Reisner.depthExtLocalCohomology (K.faceRingAugmentationIdeal R) q).obj
      (ModuleCat.of (K.FaceRing R) (K.CechCochain R p))) := by
  let ι := CechIndex V p
  let T : ι → ModuleCat (K.FaceRing R) :=
    fun F => ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F.1)
  let H := Reisner.depthExtLocalCohomology (K.faceRingAugmentationIdeal R) q
  letI := Reisner.depthExtLocalCohomology_preservesFiniteProducts
    (K.faceRingAugmentationIdeal R) q
  letI : PreservesLimit (Discrete.functor T) H := inferInstance
  let eSource : ModuleCat.of (K.FaceRing R) (∀ F : ι,
      K.FaceRingLocalization R F.1) ≅ limit (Discrete.functor T) :=
    IsLimit.conePointUniqueUpToIso (ModuleCat.HasLimit.productLimitCone T).isLimit
      (limit.isLimit (Discrete.functor T))
  let eTarget := preservesLimitIso H (Discrete.functor T)
  have hTarget : IsZero (limit (Discrete.functor T ⋙ H)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply limit.hom_ext
    intro F
    have hF : F.as.1.Nonempty := Finset.card_pos.mp (by
      rw [F.as.2]
      exact hp)
    exact (K.faceRingLocalization_localCohomology_isZero R hF q).eq_of_tgt _ _
  exact hTarget.of_iso (Functor.mapIso H eSource ≪≫ eTarget)

/-- At a fixed augmentation-power stage, derived Ext into every positive
Čech cochain module vanishes in all degrees. This is the stagewise row
vanishing used to form the eventual derived comparison. -/
theorem faceRingCechCochain_augmentationPower_ext_isZero [Fintype V]
    {p : ℕ} (hp : 0 < p) (n q : ℕ) :
    IsZero (ModuleCat.of (K.FaceRing R)
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of (K.FaceRing R)
          (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n))
        (ModuleCat.of (K.FaceRing R) (K.CechCochain R p)) q)) := by
  let ι := CechIndex V p
  let T : ι → ModuleCat (K.FaceRing R) :=
    fun F => ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F.1)
  let M := ModuleCat.of (K.FaceRing R)
    (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n)
  let H := CategoryTheory.Abelian.linearExtFunctorObj (K.FaceRing R) M q
  letI := Reisner.depthExtTargetFunctor_preservesFiniteProducts M q
  letI : PreservesLimit (Discrete.functor T) H := inferInstance
  let eSource : ModuleCat.of (K.FaceRing R) (∀ F : ι,
      K.FaceRingLocalization R F.1) ≅ limit (Discrete.functor T) :=
    IsLimit.conePointUniqueUpToIso (ModuleCat.HasLimit.productLimitCone T).isLimit
      (limit.isLimit (Discrete.functor T))
  let eTarget := preservesLimitIso H (Discrete.functor T)
  have hTarget : IsZero (limit (Discrete.functor T ⋙ H)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply limit.hom_ext
    intro F
    have hF : F.as.1.Nonempty := Finset.card_pos.mp (by
      rw [F.as.2]
      exact hp)
    exact (K.faceRingLocalization_augmentationPower_ext_isZero R hF n q).eq_of_tgt _ _
  exact hTarget.of_iso (Functor.mapIso H eSource ≪≫ eTarget)

/-- The same row acyclicity holds for the cofinal generator-power stages
`A/(x_v^n : v ∈ V)`. These are the stages used by
`faceRingGeneratorPowerExtDiagram`, so the vanishing is now aligned with the
actual local-cohomology colimit rather than only with augmentation powers. -/
theorem faceRingCechCochain_generatorPower_ext_isZero [Fintype V]
    {p : ℕ} (hp : 0 < p) (n q : ℕ) :
    IsZero (ModuleCat.of (K.FaceRing R)
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of (K.FaceRing R)
          (K.FaceRing R ⧸ K.faceRingGeneratorPowerIdeal R n))
        (ModuleCat.of (K.FaceRing R) (K.CechCochain R p)) q)) := by
  let ι := CechIndex V p
  let T : ι → ModuleCat (K.FaceRing R) :=
    fun F => ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F.1)
  let M := ModuleCat.of (K.FaceRing R)
    (K.FaceRing R ⧸ K.faceRingGeneratorPowerIdeal R n)
  let H := CategoryTheory.Abelian.linearExtFunctorObj (K.FaceRing R) M q
  letI := Reisner.depthExtTargetFunctor_preservesFiniteProducts M q
  letI : PreservesLimit (Discrete.functor T) H := inferInstance
  let eSource : ModuleCat.of (K.FaceRing R) (∀ F : ι,
      K.FaceRingLocalization R F.1) ≅ limit (Discrete.functor T) :=
    IsLimit.conePointUniqueUpToIso (ModuleCat.HasLimit.productLimitCone T).isLimit
      (limit.isLimit (Discrete.functor T))
  let eTarget := preservesLimitIso H (Discrete.functor T)
  have hTarget : IsZero (limit (Discrete.functor T ⋙ H)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply limit.hom_ext
    intro F
    have hF : F.as.1.Nonempty := Finset.card_pos.mp (by
      rw [F.as.2]
      exact hp)
    have hRow : IsZero (ModuleCat.of (K.FaceRing R)
        (CategoryTheory.Abelian.Ext M
          (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F.as.1)) q)) := by
      have hsub : Subsingleton (CategoryTheory.Abelian.Ext M
          (ModuleCat.of (K.FaceRing R) (K.FaceRingLocalization R F.as.1)) q) :=
        subsingleton_of_forall_eq 0
          (K.faceRingLocalization_generatorPower_ext_eq_zero R hF n q)
      exact ModuleCat.isZero_of_subsingleton _
    exact hRow.eq_of_tgt _ _
  exact hTarget.of_iso (Functor.mapIso H eSource ≪≫ eTarget)

end Reisner.Complex
