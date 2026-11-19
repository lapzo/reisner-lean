import Reisner

/-!
Regression checks for the finite extended Čech construction.

These examples deliberately specialize the actual localization API. The
singleton example carries its nonface hypothesis explicitly so it applies to
any complex on one vertex whose vertex is ghost.
-/

open Reisner
open Reisner.Complex

#check Reisner.Complex.CechIndex
#check Reisner.Complex.CechCochain
#check Reisner.Complex.CechCochainDirectSum
#check Reisner.Complex.cechCochainDirectSumEquiv
#check Reisner.Complex.cechCochainMonomialBasis
#check Reisner.Complex.cechEraseIndex
#check Reisner.Complex.cechDifferentialComponent
#check Reisner.Complex.cechDifferential
#check Reisner.Complex.cechDifferential_apply
#check Reisner.Complex.cechMonomialCochain
#check Reisner.Complex.cechDifferential_monomialCochain
#check Reisner.Complex.cechDegreeSubmodule_isInternal
#check Reisner.Complex.cechDifferential_comp_eq_zero
#check Reisner.Complex.cechComplex
#check Reisner.Complex.cechComplex_X
#check Reisner.Complex.cechComplex_d
#check Reisner.Complex.cechDegreeSubmodule
#check Reisner.Complex.cechDifferential_maps_degree
#check Reisner.Complex.cechDifferentialDegree

#print axioms Reisner.Complex.cechComplex
#print axioms Reisner.Complex.cechDifferential
#print axioms Reisner.Complex.cechDifferential_monomialCochain
#print axioms Reisner.Complex.cechDegreeSubmodule_isInternal
#print axioms Reisner.Complex.cechDifferential_comp_eq_zero
#print axioms Reisner.Complex.cechDifferential_maps_degree
#print axioms Reisner.Complex.cechDifferentialDegree

/- The empty ambient set has exactly one degree-zero localization coordinate,
and that coordinate is the empty-product localization. -/
example (F : Reisner.Complex.CechIndex PEmpty 0) :
    F.1 = ∅ :=
  Finset.card_eq_zero.mp F.2

/- The basis-action formula specializes to the unique degree-zero coordinate
when the ambient type is empty. -/
set_option maxHeartbeats 500000 in
example (K : Reisner.Complex PEmpty) (R : Type*) [CommRing R] :
    K.cechDifferential R 0
        (K.cechMonomialCochain R ⟨∅, by simp⟩ (0 : PEmpty →₀ ℤ)) =
      ∑ v : {v : PEmpty // v ∉ (∅ : Finset PEmpty)},
        ((-1 : R) ^ Reisner.Complex.cechRankBelow (∅ : Finset PEmpty) v.1) •
          K.cechMonomialCochain R
            (Reisner.Complex.cechInsertIndex ⟨∅, by simp⟩ v.1 v.2)
            (0 : PEmpty →₀ ℤ) := by
  have ha : K.LocalizationAdmissible (∅ : Finset PEmpty) (0 : PEmpty →₀ ℤ) := by
    constructor
    · simp
    · simpa [positiveSupport] using K.empty_mem
  exact K.cechDifferential_monomialCochain R ⟨∅, by simp⟩ 0 ha

/- The termwise fine-degree decomposition also applies to the empty ambient
complex, retaining its empty subset coordinate. -/
set_option maxHeartbeats 500000 in
example (K : Reisner.Complex PEmpty) (R : Type*) [CommRing R] :
    DirectSum.IsInternal (K.cechDegreeSubmodule R 0) :=
  K.cechDegreeSubmodule_isInternal R 0

/- A ghost singleton specializes the localization theorem to the degree-one
coordinate of the finite cochain family. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R] [Fintype (Fin 1)]
    [LinearOrder (Fin 1)] (hghost : ({0} : Finset (Fin 1)) ∉ K.faces) :
    Subsingleton (K.FaceRingLocalization R ({0} : Finset (Fin 1))) :=
  K.faceRingLocalization_subsingleton_of_nonface R hghost

/- A ghost singleton remains an actual degree-one coordinate while its
degree-zero localization component vanishes. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R]
    (hghost : ({0} : Finset (Fin 1)) ∉ K.faces) :
    Nonempty (Reisner.Complex.CechIndex (Fin 1) 1) ∧
      K.faceRingLocalizationComponent R ({0} : Finset (Fin 1))
        (0 : Fin 1 →₀ ℤ) = ⊥ := by
  have hna : ¬ K.LocalizationAdmissible ({0} : Finset (Fin 1)) (0 : Fin 1 →₀ ℤ) := by
    intro ha
    exact hghost (by simpa [Reisner.Complex.LocalizationAdmissible, positiveSupport] using ha.2)
  exact ⟨⟨⟨{0}, by simp⟩⟩,
    K.faceRingLocalizationComponent_eq_bot R {0} 0 hna⟩

/- A ghost singleton has zero degree-zero monomial coordinate, although the
singleton remains present in the extended cochain family. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R]
    (hghost : ({0} : Finset (Fin 1)) ∉ K.faces) :
    K.cechMonomialCochain R
      (⟨{0}, by simp⟩ : Reisner.Complex.CechIndex (Fin 1) 1)
      (0 : Fin 1 →₀ ℤ)
      (⟨{0}, by simp⟩ : Reisner.Complex.CechIndex (Fin 1) 1) = 0 := by
  have hna : ¬ K.LocalizationAdmissible ({0} : Finset (Fin 1)) (0 : Fin 1 →₀ ℤ) := by
    intro ha
    exact hghost (by simpa [Reisner.Complex.LocalizationAdmissible, positiveSupport] using ha.2)
  simp [Reisner.Complex.cechMonomialCochain,
    K.localizationMonomial_eq_zero_of_not_admissible R {0} 0 hna]

/- An ordinary singleton face retains an injective coefficient map into its
actual variable localization. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R]
    (hface : ({0} : Finset (Fin 1)) ∈ K.faces) :
    Function.Injective (algebraMap R (K.FaceRingLocalization R ({0} : Finset (Fin 1)))) :=
  K.faceRingLocalization_scalarMap_injective R hface

/- An ordinary singleton face gives a nonzero inserted degree-zero monomial. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R]
    [Nontrivial R] (hface : ({0} : Finset (Fin 1)) ∈ K.faces) :
    K.cechMonomialCochain R
      (⟨{0}, by simp⟩ : Reisner.Complex.CechIndex (Fin 1) 1)
      (0 : Fin 1 →₀ ℤ)
      (⟨{0}, by simp⟩ : Reisner.Complex.CechIndex (Fin 1) 1) ≠ 0 := by
  have ha : K.LocalizationAdmissible ({0} : Finset (Fin 1)) (0 : Fin 1 →₀ ℤ) := by
    constructor
    · simp
    · simpa [positiveSupport] using hface
  simpa [Reisner.Complex.cechMonomialCochain] using
    (K.localizationMonomial_ne_zero_iff R {0} (0 : Fin 1 →₀ ℤ)).2 ha

/- The ordered inclusion from the empty set to an ordinary singleton uses
the canonical transition map and preserves every face-ring element. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R]
    (x : K.FaceRing R) :
    K.faceRingLocalizationMap R
        (Finset.empty_subset ({0} : Finset (Fin 1)))
        (algebraMap (K.FaceRing R) (K.FaceRingLocalization R ∅) x) =
      algebraMap (K.FaceRing R)
        (K.FaceRingLocalization R ({0} : Finset (Fin 1))) x :=
  K.faceRingLocalizationMap_algebraMap R
    (Finset.empty_subset ({0} : Finset (Fin 1))) x

