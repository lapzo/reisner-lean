module

public import Reisner.LocalCohenMacaulay

/-!
# The homogeneous maximal ideal of a face ring

With the total-degree grading over a field, every proper homogeneous ideal lies in
the augmentation ideal. Thus the graded maximal ideal test for Cohen–Macaulayness
has exactly one localization to test.
-/

@[expose] public section

namespace Reisner

universe u v

/-- A Noetherian local ring is Cohen–Macaulay when its depth equals its Krull dimension. -/
def IsLocalCohenMacaulay (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  (IsLocalRing.depth (R := R) (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R

/-- A Noetherian ring is Cohen–Macaulay when its localization at every prime ideal is
a Cohen–Macaulay local ring. -/
def IsCohenMacaulay (R : Type*) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ p : PrimeSpectrum R, IsLocalCohenMacaulay (Localization.AtPrime p.asIdeal)

namespace Complex

variable {V : Type u} (K : Complex V) (k : Type v) [Field k]

local notation "𝒜" => K.faceRingTotalComponent k
local notation "𝔪" => K.faceRingAugmentationIdeal k
local notation "B" => Localization.AtPrime 𝔪

local instance [Finite V] : IsNoetherianRing (K.FaceRing k) := K.faceRing_isNoetherianRing k

noncomputable section Grading

local instance : DecidableEq ℕ := Classical.decEq ℕ
local instance (R : Type v) [CommRing R] : GradedAlgebra (K.faceRingTotalComponent R) :=
  K.faceRingTotalGradedAlgebra R

/-- Over any commutative coefficient ring, the total-degree irrelevant ideal is the
augmentation ideal. -/
theorem faceRing_irrelevant_eq_augmentation (R : Type v) [CommRing R] :
    (HomogeneousIdeal.irrelevant (K.faceRingTotalComponent R)).toIdeal =
      K.faceRingAugmentationIdeal R := by
  rw [HomogeneousIdeal.irrelevant_eq_span, K.faceRingAugmentationIdeal_eq_positive R,
    faceRingPositiveIdeal]
  congr 1
  ext x
  simp

/-- Every proper homogeneous ideal of a face ring over a field lies in the augmentation ideal. -/
theorem faceRing_homogeneousIdeal_le_augmentation (I : HomogeneousIdeal 𝒜) (hI : I ≠ ⊤) :
    I.toIdeal ≤ 𝔪 := by
  rw [← K.faceRing_irrelevant_eq_augmentation k]
  intro x hx
  apply (HomogeneousIdeal.mem_irrelevant_iff 𝒜 x).mpr
  let x₀ : K.FaceRing k := DirectSum.decompose 𝒜 x 0
  have hmem : x₀ ∈ I.toIdeal := I.isHomogeneous 0 hx
  have hdeg : x₀ ∈ 𝒜 0 := (DirectSum.decompose 𝒜 x 0).property
  rw [K.faceRingTotalComponent_zero k] at hdeg
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdeg
  rw [← Algebra.algebraMap_eq_smul_one] at hc
  change (x₀ : K.FaceRing k) = 0
  rw [← hc]
  by_contra hne
  have hc' : c ≠ 0 := fun h => hne (by simp [h])
  have hunit := (isUnit_iff_ne_zero.mpr hc').map (algebraMap k (K.FaceRing k))
  exact hI (HomogeneousIdeal.toIdeal_injective
    (I.toIdeal.eq_top_of_isUnit_mem (hc.symm ▸ hmem) hunit))

/-- Among homogeneous ideals, the augmentation ideal is the unique maximal proper ideal.
Maximality on the left is taken in the lattice of total-homogeneous ideals. -/
theorem faceRing_isCoatom_homogeneousIdeal_iff (I : HomogeneousIdeal 𝒜) :
    IsCoatom I ↔ I.toIdeal = 𝔪 := by
  let J := HomogeneousIdeal.irrelevant 𝒜
  have hJ : J.toIdeal = 𝔪 := K.faceRing_irrelevant_eq_augmentation k
  have hproper : J ≠ ⊤ := fun h =>
    (K.faceRingAugmentationIdeal_isMaximal k).ne_top (hJ.symm.trans (congrArg _ h))
  constructor
  · intro h
    have hle : I ≤ J := by
      change I.toIdeal ≤ J.toIdeal
      rw [hJ]
      exact K.faceRing_homogeneousIdeal_le_augmentation k I h.ne_top
    exact (congrArg HomogeneousIdeal.toIdeal
      (hle.eq_of_not_lt fun hlt => hproper (h.2 J hlt))).trans hJ
  · intro h
    have heq : I = J := HomogeneousIdeal.toIdeal_injective (h.trans hJ.symm)
    subst I
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hproper, fun I hI _ => ?_⟩
    change I.toIdeal ≤ J.toIdeal
    rw [hJ]
    exact K.faceRing_homogeneousIdeal_le_augmentation k I hI

/-- Local algebraic Cohen–Macaulayness at every maximal homogeneous ideal is precisely the
augmentation-local Ext-colimit vanishing test. The primes index ordinary localizations. -/
theorem faceRing_homogeneousMaximal_cm_iff_localCohomology_vanishes [Finite V] :
    (∀ (p : PrimeSpectrum (K.FaceRing k)) (hhom : p.asIdeal.IsHomogeneous 𝒜),
      IsCoatom (⟨p.asIdeal, hhom⟩ : HomogeneousIdeal 𝒜) →
        IsLocalCohenMacaulay (Localization.AtPrime p.asIdeal)) ↔
      ∀ q : ℕ, q < K.maxFaceCard → Subsingleton
        ((depthExtLocalCohomology (R := B) (IsLocalRing.maximalIdeal B) q).obj
          (ModuleCat.of B B)) := by
  rw [← K.faceRing_atAugmentation_depth_eq_iff_localCohomology_vanishes k]
  change _ ↔ IsLocalCohenMacaulay B
  constructor
  · intro h
    let p : PrimeSpectrum (K.FaceRing k) := ⟨𝔪, inferInstance⟩
    have hhom : p.asIdeal.IsHomogeneous 𝒜 := K.faceRingAugmentationIdeal_isHomogeneous k
    exact h p hhom ((K.faceRing_isCoatom_homogeneousIdeal_iff k ⟨p.asIdeal, hhom⟩).mpr rfl)
  · intro h p hhom hp
    have heq : p = ⟨𝔪, inferInstance⟩ := PrimeSpectrum.ext
      ((K.faceRing_isCoatom_homogeneousIdeal_iff k ⟨p.asIdeal, hhom⟩).mp hp)
    subst p
    exact h

end Grading

variable [Finite V]

/-- Global algebraic Cohen–Macaulayness implies vanishing below the dimension at the
augmentation ideal. -/
theorem faceRing_localCohomology_vanishes_of_isCohenMacaulay
    (hCM : IsCohenMacaulay (K.FaceRing k)) :
    ∀ q : ℕ, q < K.maxFaceCard → Subsingleton
      ((depthExtLocalCohomology (R := B) (IsLocalRing.maximalIdeal B) q).obj
        (ModuleCat.of B B)) :=
  (K.faceRing_atAugmentation_depth_eq_iff_localCohomology_vanishes k).mp
    (hCM ⟨𝔪, inferInstance⟩)

end Complex
end Reisner
