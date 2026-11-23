import Reisner
import Mathlib.Order.UpperLower.Principal

#check Reisner.Complex.link
#check Reisner.Complex.mem_link_iff
#check Reisner.Complex.link_empty
#check Reisner.Complex.notMem_link_singleton_of_mem
#check Reisner.Complex.mem_link_facet_iff
#check Reisner.Complex.negativeSupport
#check Reisner.Complex.mem_negativeSupport
#check Reisner.Complex.negativeSupport_finite
#check Reisner.Complex.negativeSupport_subset_iff
#check Reisner.Complex.positiveSupport_eq_empty_of_nonpos
#check Reisner.Complex.localizationAdmissible_iff_of_nonpos
#check Reisner.Complex.nonpositiveLocalizationIndexEquivLink
#check Reisner.Complex.nonpositiveLocalizationIndexEquivLink_apply
#check Reisner.Complex.nonpositiveLocalizationIndexEquivLink_symm_apply
#check Reisner.Complex.nonpositiveLocalizationIndex_card
#check Reisner.Complex.nonpositiveCechLinkIndexEquiv
#check Reisner.Complex.nonpositiveCechIndexEquivLink_apply
#check Reisner.Complex.nonpositiveCechIndexEquivLink_symm_apply
#check Reisner.Complex.not_localizationAdmissible_of_card_lt_negativeSupport
#check Reisner.Complex.not_localizationAdmissible_of_negativeSupport_nonface
#check Reisner.Complex.cechDegreeSubmodule_eq_bot_of_no_admissible
#check Reisner.Complex.cechDegreeSubmodule_eq_bot_of_nonpos_negativeSupport_nonface
#check Reisner.Complex.cechDegreeSubmodule_eq_bot_of_card_lt_negativeSupport
#check Reisner.Complex.cechComplexDegree_isZero_of_nonpos_negativeSupport_nonface
#check Reisner.Complex.cechCohomologyDegree_isZero_of_nonpos_negativeSupport_nonface

#print axioms Reisner.Complex.link
#print axioms Reisner.Complex.mem_link_iff
#print axioms Reisner.Complex.link_empty
#print axioms Reisner.Complex.notMem_link_singleton_of_mem
#print axioms Reisner.Complex.mem_link_facet_iff
#print axioms Reisner.Complex.negativeSupport
#print axioms Reisner.Complex.mem_negativeSupport
#print axioms Reisner.Complex.negativeSupport_finite
#print axioms Reisner.Complex.negativeSupport_subset_iff
#print axioms Reisner.Complex.positiveSupport_eq_empty_of_nonpos
#print axioms Reisner.Complex.localizationAdmissible_iff_of_nonpos
#print axioms Reisner.Complex.nonpositiveLocalizationIndexEquivLink
#print axioms Reisner.Complex.nonpositiveLocalizationIndexEquivLink_apply
#print axioms Reisner.Complex.nonpositiveLocalizationIndexEquivLink_symm_apply
#print axioms Reisner.Complex.nonpositiveLocalizationIndex_card
#print axioms Reisner.Complex.nonpositiveCechLinkIndexEquiv
#print axioms Reisner.Complex.nonpositiveCechIndexEquivLink_apply
#print axioms Reisner.Complex.nonpositiveCechIndexEquivLink_symm_apply
#print axioms Reisner.Complex.not_localizationAdmissible_of_card_lt_negativeSupport
#print axioms Reisner.Complex.not_localizationAdmissible_of_negativeSupport_nonface
#print axioms Reisner.Complex.cechDegreeSubmodule_eq_bot_of_no_admissible
#print axioms Reisner.Complex.cechDegreeSubmodule_eq_bot_of_nonpos_negativeSupport_nonface
#print axioms Reisner.Complex.cechDegreeSubmodule_eq_bot_of_card_lt_negativeSupport
#print axioms Reisner.Complex.cechComplexDegree_isZero_of_nonpos_negativeSupport_nonface
#print axioms Reisner.Complex.cechCohomologyDegree_isZero_of_nonpos_negativeSupport_nonface

open CategoryTheory

#check Reisner.Complex.cechDifferentialDegree_comp_eq_zero
#check Reisner.Complex.cechComplexDegree
#check Reisner.Complex.cechComplexDegree_d
#check Reisner.Complex.cechDegreeInclusion
#check Reisner.Complex.cechDegreeProjection
#check Reisner.Complex.cechDegreeInclusion_projection
#check Reisner.Complex.cechDegreeInclusion_projection_of_ne
#check Reisner.Complex.cechCohomologyDegree
#check Reisner.Complex.cechCohomologyAssembly
#check Reisner.Complex.cechCohomologyAssembly_lof
#check Reisner.Complex.cechCohomologyProjection_assembly
#check Reisner.Complex.cechCohomologyAssembly_injective
#check Reisner.Complex.cechCohomologyAssembly_surjective
#check Reisner.Complex.cechCohomologyAssembly_bijective
#check Reisner.Complex.cechCohomologyDecomposition
#check Reisner.Complex.cechCohomologyDecomposition_lof
#check Reisner.Complex.cechCohomologyDecomposition_symm_apply
#check Reisner.Complex.cechCohomologyDecomposition_support_subset
#check Reisner.Complex.cechCohomologyQuotientEquiv
#check Reisner.Complex.cechCohomologyDegreeQuotientEquiv
#check Reisner.Complex.cechCohomology_outgoing
#check Reisner.Complex.cechCohomology_incoming
#check Reisner.Complex.cechCohomologyDegree_outgoing
#check Reisner.Complex.cechCohomologyDegree_incoming
#check Reisner.Complex.cechCohomologyQuotientEquiv_homologyπ
#check Reisner.Complex.cechCohomologyDegreeQuotientEquiv_homologyπ
#check Reisner.Complex.cechCohomology_boundaries_zero
#check Reisner.Complex.cechCohomologyDegree_boundaries_zero

#check Reisner.Complex.cechPositiveContraction
#check Reisner.Complex.cechPositiveContraction_monomial
#check Reisner.Complex.cechPositiveContraction_smul_monomial
#check Reisner.Complex.cechPositiveContraction_zero
#check Reisner.Complex.cechPositiveContraction_succ
#check Reisner.Complex.cechPositiveContractingHomotopy
#check Reisner.Complex.cechPositiveContractingHomotopy_hom
#check Reisner.Complex.cechPositiveSupport_contractible
#check Reisner.Complex.cechPositiveCohomology_isZero
#check Reisner.Complex.cechPositiveCohomology_subsingleton

private def ordinarySingletonComplex : Reisner.Complex (Fin 1) where
  faces := ⊤
  empty_mem := by simp

/- Degree zero uses the homotopy map h¹ after d⁰, over characteristic two. -/
example :
    ordinarySingletonComplex.cechPositiveContraction
        (ZMod 2) (Finsupp.single 0 (1 : ℤ)) 0 0 ∘ₗ
      ordinarySingletonComplex.cechDifferentialDegree
        (ZMod 2) (q := 0) (Finsupp.single 0 (1 : ℤ)) =
        LinearMap.id := by
  have hp : 0 < (Finsupp.single 0 (1 : ℤ) : Fin 1 →₀ ℤ) 0 := by simp
  exact ordinarySingletonComplex.cechPositiveContraction_zero (ZMod 2) _ 0 hp

/- The cancellation sign identity is valid in characteristic two, where
the additive inverse of a sign equals the sign itself. -/
example :
    ((-1 : ZMod 2) ^ Reisner.Complex.cechRankBelow ({0} : Finset (Fin 2)) 0) *
        (-1) ^ Reisner.Complex.cechRankBelow
          (({0} : Finset (Fin 2)).erase 0) 1 =
      - (((-1 : ZMod 2) ^ Reisner.Complex.cechRankBelow
            ({0} : Finset (Fin 2)) 1) *
          (-1) ^ Reisner.Complex.cechRankBelow
            (insert 1 ({0} : Finset (Fin 2))) 0) := by
  exact Reisner.Complex.cechContraction_sign_cancel
    (R := ZMod 2) ({0} : Finset (Fin 2)) (by simp) (by simp)

/- The same construction works over the zero ring without a nontriviality
assumption. -/
example (K : Reisner.Complex (Fin 1)) :
    Nonempty (Homotopy
      (𝟙 (K.cechComplexDegree (ZMod 1) (Finsupp.single 0 (1 : ℤ)))) 0) := by
  have hp : 0 < (Finsupp.single 0 (1 : ℤ) : Fin 1 →₀ ℤ) 0 := by simp
  exact ⟨K.cechPositiveContractingHomotopy (ZMod 1) _ 0 hp⟩

/- The top degree and an index above the vertex count are covered uniformly
by the homotopy. -/
example (K : Reisner.Complex (Fin 1)) :
    CategoryTheory.Limits.IsZero
        ((K.cechComplexDegree (ZMod 2) (Finsupp.single 0 (1 : ℤ))).homology 1) ∧
      CategoryTheory.Limits.IsZero
        ((K.cechComplexDegree (ZMod 2) (Finsupp.single 0 (1 : ℤ))).homology 2) := by
  have hp : 0 < (Finsupp.single 0 (1 : ℤ) : Fin 1 →₀ ℤ) 0 := by simp
  exact ⟨K.cechPositiveCohomology_isZero (ZMod 2) _ 0 hp 1,
    K.cechPositiveCohomology_isZero (ZMod 2) _ 0 hp 2⟩

/- Empty ambient vertex sets have no positive-coordinate witness. -/
example (a : PEmpty →₀ ℤ) : ¬ ∃ p : PEmpty, 0 < a p := by
  rintro ⟨p, _⟩
  cases p

#print axioms Reisner.Complex.cechDifferentialDegree_comp_eq_zero
#print axioms Reisner.Complex.cechComplexDegree
#print axioms Reisner.Complex.cechComplexDegree_d
#print axioms Reisner.Complex.cechDegreeInclusion
#print axioms Reisner.Complex.cechDegreeProjection
#print axioms Reisner.Complex.cechDegreeInclusion_projection
#print axioms Reisner.Complex.cechDegreeInclusion_projection_of_ne
#print axioms Reisner.Complex.cechCohomologyDegree
#print axioms Reisner.Complex.cechCohomologyAssembly
#print axioms Reisner.Complex.cechCohomologyAssembly_lof
#print axioms Reisner.Complex.cechCohomologyProjection_assembly
#print axioms Reisner.Complex.cechCohomologyAssembly_injective
#print axioms Reisner.Complex.cechCohomologyAssembly_surjective
#print axioms Reisner.Complex.cechCohomologyAssembly_bijective
#print axioms Reisner.Complex.cechCohomologyDecomposition
#print axioms Reisner.Complex.cechCohomologyDecomposition_lof
#print axioms Reisner.Complex.cechCohomologyDecomposition_symm_apply
#print axioms Reisner.Complex.cechCohomologyDecomposition_support_subset
#print axioms Reisner.Complex.cechCohomologyQuotientEquiv
#print axioms Reisner.Complex.cechCohomologyDegreeQuotientEquiv
#print axioms Reisner.Complex.cechCohomology_outgoing
#print axioms Reisner.Complex.cechCohomology_incoming
#print axioms Reisner.Complex.cechCohomologyDegree_outgoing
#print axioms Reisner.Complex.cechCohomologyDegree_incoming
#print axioms Reisner.Complex.cechCohomologyQuotientEquiv_homologyπ
#print axioms Reisner.Complex.cechCohomologyDegreeQuotientEquiv_homologyπ
#print axioms Reisner.Complex.cechCohomology_boundaries_zero
#print axioms Reisner.Complex.cechCohomologyDegree_boundaries_zero

/-!
Regression checks for the finite extended Čech construction.

These examples deliberately specialize the actual localization API. The
singleton example carries its nonface hypothesis explicitly so it applies to
any complex on one vertex whose vertex is ghost.
-/

open Reisner
open Reisner.Complex
open DirectSum

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
#check Reisner.Complex.cechDecomposition
#check Reisner.Complex.cechDecomposeLinearEquiv
#check Reisner.Complex.cechHomogeneousComponent
#check Reisner.Complex.cechHomogeneousComponent_eq_self
#check Reisner.Complex.cechHomogeneousComponent_eq_zero_of_ne
#check Reisner.Complex.cechHomogeneousComponent_sum_support
#check Reisner.Complex.cechHomogeneousComponent_eq_zero_iff
#check Reisner.Complex.cechHomogeneousComponent_differential
#check Reisner.Complex.cechDifferential_eq_zero_iff_components
#check Reisner.Complex.cechBoundary_homogeneous_primitive

#print axioms Reisner.Complex.cechComplex
#print axioms Reisner.Complex.cechDifferential
#print axioms Reisner.Complex.cechDifferential_monomialCochain
#print axioms Reisner.Complex.cechDegreeSubmodule_isInternal
#print axioms Reisner.Complex.cechDifferential_comp_eq_zero
#print axioms Reisner.Complex.cechDifferential_maps_degree
#print axioms Reisner.Complex.cechDifferentialDegree
#print axioms Reisner.Complex.cechDecomposition
#print axioms Reisner.Complex.cechDecomposeLinearEquiv
#print axioms Reisner.Complex.cechHomogeneousComponent
#print axioms Reisner.Complex.cechHomogeneousComponent_eq_self
#print axioms Reisner.Complex.cechHomogeneousComponent_eq_zero_of_ne
#print axioms Reisner.Complex.cechHomogeneousComponent_sum_support
#print axioms Reisner.Complex.cechHomogeneousComponent_eq_zero_iff
#print axioms Reisner.Complex.cechHomogeneousComponent_differential
#print axioms Reisner.Complex.cechDifferential_eq_zero_iff_components
#print axioms Reisner.Complex.cechBoundary_homogeneous_primitive

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

/- With no ambient vertices the degree-zero outgoing differential has no
target coordinates, so each homogeneous component is a cocycle. -/
example (K : Reisner.Complex PEmpty) (R : Type*) [CommRing R]
    (z : K.CechCochain R 0) (a : PEmpty →₀ ℤ) :
    K.cechDifferentialDegree R a (K.cechHomogeneousComponent R 0 a z) = 0 := by
  apply (K.cechDifferential_eq_zero_iff_components R z).mp ?_ a
  funext F
  have hzero : F.1.card = 0 := by
    rw [Finset.eq_empty_of_isEmpty F.1]
    rfl
  have hone := F.2
  omega

/- For one ghost vertex every degree-one localization coordinate is zero;
its homogeneous boundary has a primitive in each chosen degree. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R]
    (hghost : ({0} : Finset (Fin 1)) ∉ K.faces) (a : Fin 1 →₀ ℤ)
    (w : K.cechDegreeSubmodule R 1 a) :
    w ∈ LinearMap.range (K.cechDifferentialDegree R (q := 0) a) := by
  have hw : w = 0 := by
    apply Subtype.ext
    funext F
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp F.2
    have hF : F.1 = ({0} : Finset (Fin 1)) := by
      simpa only [Subsingleton.elim v (0 : Fin 1)] using hv
    let := K.faceRingLocalization_subsingleton_of_nonface R (hF ▸ hghost)
    exact Subsingleton.elim _ _
  exact ⟨0, by simp [hw]⟩

/- The zero coefficient ring is allowed by the component, cycle and boundary
criteria, with no nontriviality hypothesis supplied. -/
example (K : Reisner.Complex (Fin 1)) (a : Fin 1 →₀ ℤ)
    (w : K.cechDegreeSubmodule (ZMod 1) 1 a) :
    (w : K.CechCochain (ZMod 1) 1) ∈ LinearMap.range (K.cechDifferential (ZMod 1) 0) ↔
      w ∈ LinearMap.range (K.cechDifferentialDegree (ZMod 1) (q := 0) a) :=
  K.cechBoundary_homogeneous_primitive (ZMod 1) a w

/- There is no incoming differential to cochain degree zero. In particular,
the degree-zero boundary convention cannot use `Nat.pred 0` as a source. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R] (i : ℕ) :
    (K.cechComplex R).d i 0 = 0 := by
  apply HomologicalComplex.shape
  simp [ComplexShape.up_Rel]

/- Actual homology in degree zero for an empty ambient type is covered by
both inverse identities of the canonical decomposition. -/
example (K : Reisner.Complex PEmpty) (R : Type*) [CommRing R]
    (x : (K.cechComplex R).homology 0) :
    K.cechCohomologyDecomposition R 0 ((K.cechCohomologyDecomposition R 0).symm x) = x :=
  (K.cechCohomologyDecomposition R 0).apply_symm_apply x

private def ghostVertexComplex : Reisner.Complex (Fin 1) where
  faces := LowerSet.Iic ∅
  empty_mem := by simp

/- A ghost pivot is permitted; its homogeneous localization terms vanish. -/
example :
    CategoryTheory.Limits.IsZero
      ((ghostVertexComplex.cechComplexDegree (ZMod 2)
        (Finsupp.single 0 (1 : ℤ))).homology 0) := by
  have hp : 0 < (Finsupp.single 0 (1 : ℤ) : Fin 1 →₀ ℤ) 0 := by simp
  exact ghostVertexComplex.cechPositiveCohomology_isZero
    (ZMod 2) _ 0 hp 0

example : ({0} : Finset (Fin 1)) ∉ ghostVertexComplex.faces := by
  simp [ghostVertexComplex]

/- A concrete one-ghost complex uses the same degree-zero cohomology
equivalence; its homogeneous inverse coordinate is the induced projection. -/
example (R : Type*) [CommRing R] (x : (ghostVertexComplex.cechComplex R).homology 0)
    (a : Fin 1 →₀ ℤ) :
    (ghostVertexComplex.cechCohomologyDecomposition R 0).symm x a =
      HomologicalComplex.homologyMap (ghostVertexComplex.cechDegreeProjection R a) 0 x :=
  ghostVertexComplex.cechCohomologyDecomposition_symm_apply R 0 x a

/- Zero coefficient rings require no nontriviality or field hypothesis. -/
example (K : Reisner.Complex (Fin 1))
    (x : ⨁ a : Fin 1 →₀ ℤ, K.cechCohomologyDegree (ZMod 1) 0 a) :
    (K.cechCohomologyDecomposition (ZMod 1) 0).symm
      (K.cechCohomologyDecomposition (ZMod 1) 0 x) = x :=
  (K.cechCohomologyDecomposition (ZMod 1) 0).symm_apply_apply x

/- The canonical generator formula also applies above the ambient vertex
count, where the degree-two cochain module has no coordinates. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R] (a : Fin 1 →₀ ℤ)
    (x : K.cechCohomologyDegree R 2 a) :
    K.cechCohomologyDecomposition R 2 (DirectSum.lof R _ _ a x) =
      HomologicalComplex.homologyMap (K.cechDegreeInclusion R a) 2 x :=
  K.cechCohomologyDecomposition_lof R 2 a x

/- The quotient bridge has bottom incoming boundary submodules in degree
zero, for both the full and degreewise complexes. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R] (a : Fin 1 →₀ ℤ) :
    ((K.cechComplex R).sc 0).moduleCatToCycles.range = ⊥ ∧
      ((K.cechComplexDegree R a).sc 0).moduleCatToCycles.range = ⊥ :=
  ⟨K.cechCohomology_boundaries_zero R, K.cechCohomologyDegree_boundaries_zero R a⟩

@[simp]
private theorem negativeSupport_zero_check (V : Type*) :
    negativeSupport (0 : V →₀ ℤ) = ∅ := by
  ext v
  simp

/- Zero fine degree has empty negative support, and deleting it leaves every
face unchanged. This also checks the inverse convention at the empty face. -/
example {V : Type*} (K : Reisner.Complex V) (F : Finset V) (hF : F ∈ K.faces) :
    (K.nonpositiveLocalizationIndexEquivLink (0 : V →₀ ℤ) le_rfl
      (by simpa using K.empty_mem)
        ⟨F, (K.localizationAdmissible_iff_of_nonpos 0 le_rfl F).mpr
          ⟨by simp, hF⟩⟩).1 = F := by
  simp

/- Empty ambient vertices retain the empty face, and its link is the same
augmented complex. No ambient nonemptiness hypothesis is needed. -/
example (K : Reisner.Complex PEmpty) :
    negativeSupport (0 : PEmpty →₀ ℤ) = ∅ ∧ K.link ∅ K.empty_mem = K :=
  ⟨negativeSupport_zero_check _, K.link_empty⟩

private noncomputable def negativeSingletonDegree : Fin 1 →₀ ℤ := Finsupp.single 0 (-1)

private theorem negativeSingletonDegree_nonpos : negativeSingletonDegree ≤ 0 := by
  apply Finsupp.le_def.mpr
  intro v
  have hv : v = 0 := Subsingleton.elim _ _
  simp [negativeSingletonDegree, hv]

private theorem negativeSingletonDegree_support : negativeSupport negativeSingletonDegree = {0} := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  simp [negativeSingletonDegree, hv]

private theorem ordinarySingleton_facet :
    ({0} : Finset (Fin 1)) ∈ ordinarySingletonComplex.facets := by
  refine ⟨by simp [ordinarySingletonComplex], ?_⟩
  intro G _ _ v _
  exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)

/- The link of this concrete facet has exactly the empty face, rather than
being the void collection. -/
example (T : Finset (Fin 1)) :
    T ∈ (ordinarySingletonComplex.link {0} ordinarySingleton_facet.1).faces ↔ T = ∅ :=
  ordinarySingletonComplex.mem_link_facet_iff ordinarySingleton_facet T

private theorem negativeSingletonDegree_face_ordinary :
    negativeSupport negativeSingletonDegree ∈ ordinarySingletonComplex.faces := by
  simp [ordinarySingletonComplex]

/- The empty face of the link corresponds to F=N, at cochain degree |N|=1. -/
example :
    ((ordinarySingletonComplex.nonpositiveCechIndexEquivLink negativeSingletonDegree
      negativeSingletonDegree_nonpos negativeSingletonDegree_face_ordinary 1).symm
        ⟨∅, (ordinarySingletonComplex.link _ negativeSingletonDegree_face_ordinary).empty_mem,
          by simp [negativeSingletonDegree_support]⟩).1.1 = {0} := by
  simp [negativeSingletonDegree_support]

/- Below |N| there are no admissible coordinates; this is an actual zero
Čech degree submodule over arbitrary coefficients. -/
example (R : Type*) [CommRing R] :
    ordinarySingletonComplex.cechDegreeSubmodule R 0 negativeSingletonDegree = ⊥ :=
  ordinarySingletonComplex.cechDegreeSubmodule_eq_bot_of_card_lt_negativeSupport R
    negativeSingletonDegree negativeSingletonDegree_nonpos 0
      (by simp [negativeSingletonDegree_support])

/- Above the ambient cardinality the actual subset index type is empty. -/
example : IsEmpty {F : CechIndex (Fin 1) 2 //
    ordinarySingletonComplex.LocalizationAdmissible F.1 negativeSingletonDegree} := by
  refine ⟨fun F => ?_⟩
  have h := Finset.card_le_univ F.1.1
  have hc := F.1.2
  simp only [Fintype.card_fin] at h
  omega

private theorem negativeSingletonDegree_nonface_ghost :
    negativeSupport negativeSingletonDegree ∉ ghostVertexComplex.faces := by
  simp [negativeSingletonDegree_support, ghostVertexComplex]

/- The whole actual cochain degree module, rather than only its admissible
index subtype, vanishes above the ambient cardinality in every fine degree. -/
example (K : Reisner.Complex (Fin 1)) (R : Type*) [CommRing R] (a : Fin 1 →₀ ℤ) :
    K.cechDegreeSubmodule R 2 a = ⊥ := by
  apply K.cechDegreeSubmodule_eq_bot_of_no_admissible R 2 a
  intro F _
  have h := Finset.card_le_univ F.1
  have hc := F.2
  simp only [Fintype.card_fin] at h
  omega

/- A ghost in N makes the complete degree submodule zero, without replacing
any of its localization coordinates by formal symbols. -/
example (R : Type*) [CommRing R] (q : ℕ) :
    ghostVertexComplex.cechDegreeSubmodule R q negativeSingletonDegree = ⊥ :=
  ghostVertexComplex.cechDegreeSubmodule_eq_bot_of_nonpos_negativeSupport_nonface R
    negativeSingletonDegree negativeSingletonDegree_nonpos negativeSingletonDegree_nonface_ghost q

/- The nonface consequence includes the zero coefficient ring and the
actual degreewise cohomology object in every cochain degree. -/
example (q : ℕ) : CategoryTheory.Limits.IsZero
    (ghostVertexComplex.cechCohomologyDegree (ZMod 1) q negativeSingletonDegree) :=
  ghostVertexComplex.cechCohomologyDegree_isZero_of_nonpos_negativeSupport_nonface (ZMod 1)
    negativeSingletonDegree negativeSingletonDegree_nonpos negativeSingletonDegree_nonface_ghost q

/- Shifted complex packaging and homology comparison. -/
#check Reisner.Complex.cechLinkDegreeEmbedding
#check Reisner.Complex.cechLinkShiftedComplex
#check Reisner.Complex.cechLinkShiftedComplexXIso
#check Reisner.Complex.cechLinkShiftedComplex_d
#check Reisner.Complex.cechLinkShiftedComplex_isZero_of_lt
#check Reisner.Complex.componentIsoOfEq
#check Reisner.Complex.cechNonpositiveLinkComplexComponentIso
#check Reisner.Complex.cechNonpositiveLinkComplexComponentIso_add
#check Reisner.Complex.cechNonpositiveLinkComplexIso
#check Reisner.Complex.cechNonpositiveLinkHomologyIso
#check Reisner.Complex.cechNonpositiveLinkNaturalHomologyIso
#check Reisner.Complex.cechNonpositiveLinkCohomologyIso
#check Reisner.Complex.cechCohomologyDegree_isZero_of_nonpos_card_lt_negativeSupport

/- With N = ∅, the complex isomorphism has no cutoff and is valid over the
trivial coefficient ring. -/
example : Nonempty
    (ordinarySingletonComplex.cechComplexDegree (ZMod 1) (0 : Fin 1 →₀ ℤ) ≅
      ordinarySingletonComplex.cechLinkShiftedComplex (ZMod 1) (0 : Fin 1 →₀ ℤ)
        (by simpa using ordinarySingletonComplex.empty_mem)) := by
  exact ⟨ordinarySingletonComplex.cechNonpositiveLinkComplexIso (ZMod 1)
    (0 : Fin 1 →₀ ℤ) le_rfl (by simpa using ordinarySingletonComplex.empty_mem)⟩

/- Below the nonempty support cutoff, actual degreewise Cech cohomology is
zero, also over ZMod 1. -/
example : CategoryTheory.Limits.IsZero
    (ordinarySingletonComplex.cechCohomologyDegree (ZMod 1) 0 negativeSingletonDegree) :=
  ordinarySingletonComplex.cechCohomologyDegree_isZero_of_nonpos_card_lt_negativeSupport
    (ZMod 1) negativeSingletonDegree negativeSingletonDegree_nonpos
    negativeSingletonDegree_face_ordinary 0 (by simp [negativeSingletonDegree_support])

/- For nonempty N and r = 0, the link's empty face remains the reduced
degree-minus-one homology coordinate. -/
example : Nonempty
    ((ordinarySingletonComplex.cechComplexDegree (ZMod 2) negativeSingletonDegree).homology 1 ≅
      ((ordinarySingletonComplex.link (negativeSupport negativeSingletonDegree)
        negativeSingletonDegree_face_ordinary).simplicialCochainComplexInt (ZMod 2)).homology
        ((0 : ℤ) - 1)) := by
  simpa [negativeSingletonDegree_support] using
    (show Nonempty _ from ⟨ordinarySingletonComplex.cechNonpositiveLinkCohomologyIso (ZMod 2)
      negativeSingletonDegree negativeSingletonDegree_nonpos
      negativeSingletonDegree_face_ordinary 0⟩)

/- Signed comparison of nonpositive Cech terms with actual link cochains. -/
#check Reisner.Complex.cechLinkSign
#check Reisner.Complex.cechLinkSign_empty
#check Reisner.Complex.cechLinkSign_mul_self
#check Reisner.Complex.cechLinkSign_insert
#check Reisner.Complex.cechRankBelow_union
#check Reisner.Complex.cechLinkSign_insertion_compat
#check Reisner.Complex.nonpositiveCechLinkIndexEquiv
#check Reisner.Complex.cechNonpositiveLinkEquiv
#check Reisner.Complex.cechNonpositiveLinkEquiv_apply
#check Reisner.Complex.cechNonpositiveLinkEquiv_monomial
#check Reisner.Complex.cechNonpositiveLinkEquiv_symm_basis
#check Reisner.Complex.cechNonpositiveLinkEquiv_symm_apply
#check Reisner.Complex.cechNonpositiveLinkEquiv_differential
#check Reisner.Complex.insert_link_admissible_iff

/- At a = 0, N is empty; the term equivalence applies without excluding the
empty link face, over characteristic two. -/
example : Nonempty
    (ordinarySingletonComplex.cechDegreeSubmodule (ZMod 2) 1 (0 : Fin 1 →₀ ℤ) ≃ₗ[ZMod 2]
      (ordinarySingletonComplex.link ∅ ordinarySingletonComplex.empty_mem).SimplicialCochain
        (ZMod 2) 1) := by
  exact ⟨ordinarySingletonComplex.cechNonpositiveLinkEquiv (ZMod 2) 0 le_rfl
    (by simpa using ordinarySingletonComplex.empty_mem) 1⟩

/- A nonempty N with T = ∅ is the first shifted differential, and the empty
face is a genuine basis coordinate in the link. -/
example :
    (ordinarySingletonComplex.cechNonpositiveLinkEquiv (ZMod 2)
      negativeSingletonDegree negativeSingletonDegree_nonpos
      negativeSingletonDegree_face_ordinary 0).symm
        ((ordinarySingletonComplex.link (negativeSupport negativeSingletonDegree)
          negativeSingletonDegree_face_ordinary).simplicialCochainBasis (ZMod 2) 0
          ⟨∅, (ordinarySingletonComplex.link (negativeSupport negativeSingletonDegree)
            negativeSingletonDegree_face_ordinary).empty_mem, by simp⟩) =
      Reisner.Complex.cechLinkSign (R := ZMod 2) (negativeSupport negativeSingletonDegree) ∅ •
        ordinarySingletonComplex.cechMonomialCochainDegree (ZMod 2)
          ((ordinarySingletonComplex.nonpositiveCechLinkIndexEquiv
            negativeSingletonDegree negativeSingletonDegree_nonpos
            negativeSingletonDegree_face_ordinary 0).symm
              ⟨∅, (ordinarySingletonComplex.link (negativeSupport negativeSingletonDegree)
                negativeSingletonDegree_face_ordinary).empty_mem, by simp⟩).1 negativeSingletonDegree := by
  exact ordinarySingletonComplex.cechNonpositiveLinkEquiv_symm_basis (ZMod 2)
    negativeSingletonDegree negativeSingletonDegree_nonpos negativeSingletonDegree_face_ordinary
    0 ⟨∅, (ordinarySingletonComplex.link (negativeSupport negativeSingletonDegree)
      negativeSingletonDegree_face_ordinary).empty_mem, by simp⟩

/- The actual differential square commutes at r = 0 over characteristic two,
including the first map out of the nonempty negative support. -/
example :
    (ordinarySingletonComplex.cechNonpositiveLinkEquiv (ZMod 2)
      negativeSingletonDegree negativeSingletonDegree_nonpos
      negativeSingletonDegree_face_ordinary 1).toLinearMap ∘ₗ
        ordinarySingletonComplex.cechDifferentialDegree (ZMod 2) negativeSingletonDegree =
      ((ordinarySingletonComplex.link (negativeSupport negativeSingletonDegree)
        negativeSingletonDegree_face_ordinary).simplicialDifferential (ZMod 2) 0) ∘ₗ
          (ordinarySingletonComplex.cechNonpositiveLinkEquiv (ZMod 2)
            negativeSingletonDegree negativeSingletonDegree_nonpos
            negativeSingletonDegree_face_ordinary 0).toLinearMap := by
  simpa [negativeSingletonDegree_support] using
    ordinarySingletonComplex.cechNonpositiveLinkEquiv_differential (ZMod 2)
    negativeSingletonDegree negativeSingletonDegree_nonpos negativeSingletonDegree_face_ordinary 0

/- Valid insertion when N = ∅: the singleton is an actual face. -/
example : ordinarySingletonComplex.LocalizationAdmissible {0} (0 : Fin 1 →₀ ℤ) ↔
    ({0} : Finset (Fin 1)) ∈
      (ordinarySingletonComplex.link ∅ ordinarySingletonComplex.empty_mem).faces := by
  simpa using ordinarySingletonComplex.insert_link_admissible_iff
    (0 : Fin 1 →₀ ℤ) le_rfl (by simpa using ordinarySingletonComplex.empty_mem)
    (∅ : Finset (Fin 1))
    ((ordinarySingletonComplex.link ∅ ordinarySingletonComplex.empty_mem).empty_mem)
    (v := 0) (by simp)

/- The same insertion into a ghost coordinate has no admissible target and
vanishes in the actual localization. -/
example : ¬ ghostVertexComplex.LocalizationAdmissible {0} (0 : Fin 1 →₀ ℤ) := by
  intro h
  have hiff := ghostVertexComplex.insert_link_admissible_iff
    (0 : Fin 1 →₀ ℤ) le_rfl (by simpa using ghostVertexComplex.empty_mem)
    (∅ : Finset (Fin 1))
    ((ghostVertexComplex.link ∅ ghostVertexComplex.empty_mem).empty_mem)
    (v := 0) (by simp)
  have hlink := hiff.mp (by simpa using h)
  simp [ghostVertexComplex] at hlink

/- The same signed term equivalence is available over the trivial coefficient
ring; no nontriviality assumption is hidden in the comparison. -/
example : Nonempty
    (ordinarySingletonComplex.cechDegreeSubmodule (ZMod 1) 1 (0 : Fin 1 →₀ ℤ) ≃ₗ[ZMod 1]
      (ordinarySingletonComplex.link ∅ ordinarySingletonComplex.empty_mem).SimplicialCochain
        (ZMod 1) 1) := by
  exact ⟨ordinarySingletonComplex.cechNonpositiveLinkEquiv (ZMod 1) 0 le_rfl
    (by simpa using ordinarySingletonComplex.empty_mem) 1⟩

