import Reisner
import Mathlib.Data.ZMod.Basic

/-!
Concrete regression checks for the localization-kernel argument. These are
kept separate from the library API: they demonstrate both the squarefree
Stanley–Reisner phenomenon and why the first-power conclusion does not hold
for arbitrary localization denominators.
-/

namespace LocalizationKernelAudit

open Reisner

/- The complex on two vertices with both singletons as faces and the edge
  absent. Its face ring is the familiar `ℚ[x,y]/(xy)`. -/
def singletonFaces : LowerSet (Finset Bool) where
  carrier := {s | s.card ≤ 1}
  lower' := by
    intro a b hab hb
    exact (Finset.card_le_card hab).trans hb

def disjointPair : Reisner.Complex Bool :=
  ⟨singletonFaces, by change (∅ : Finset Bool).card ≤ 1; simp⟩

noncomputable def x : MvPolynomial Bool ℚ := MvPolynomial.X false
noncomputable def y : MvPolynomial Bool ℚ := MvPolynomial.X true

theorem x_is_a_face : ({false} : Finset Bool) ∈ disjointPair.faces := by
  change ({false} : Finset Bool).card ≤ 1
  simp

theorem y_is_a_face : ({true} : Finset Bool) ∈ disjointPair.faces := by
  change ({true} : Finset Bool).card ≤ 1
  simp

theorem edge_is_a_nonface : ({false, true} : Finset Bool) ∉ disjointPair.faces := by
  change ¬ ({false, true} : Finset Bool).card ≤ 1
  simp

/-- The `y` class survives in the disconnected two-vertex face ring. -/
theorem y_ne_zero_in_faceRing :
    Ideal.Quotient.mk (disjointPair.stanleyReisnerIdeal ℚ) y ≠ 0 := by
  intro h
  have hy := (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [disjointPair.mem_stanleyReisnerIdeal_iff] at hy
  have hterm := hy (Finsupp.single true 1) (by simp [y])
  have hsingle : ({true} : Finset Bool) ∈ disjointPair.faces := y_is_a_face
  have hterm' := hterm (by simpa using hsingle)
  exact hterm'

/-- Inverting `x` kills `y`, although `y` is nonzero before localization. -/
theorem y_maps_to_zero_after_localizing_at_x :
    algebraMap (disjointPair.FaceRing ℚ) (disjointPair.FaceRingLocalization ℚ {false})
      (Ideal.Quotient.mk (disjointPair.stanleyReisnerIdeal ℚ) y) = 0 := by
  apply (disjointPair.faceRingLocalization_algebraMap_mk_eq_zero_iff ℚ {false} y).2
  intro a ha
  simp only [y, MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  apply disjointPair.nonface_of_subset (F := ({false, true} : Finset Bool))
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp
  · exact edge_is_a_nonface

/-- The variable `x` itself survives at the localization where `x` is inverted. -/
theorem x_survives_after_localizing_at_x :
    disjointPair.faceRingLocalizationFraction ℚ {false} x 0 ≠ 0 := by
  apply (disjointPair.faceRingLocalization_monomialFraction_ne_zero_iff ℚ
    {false} (Finsupp.single false 1) 0).2
  simpa [x, MvPolynomial.support_X] using x_is_a_face

/-! The generic localization criterion supplies an arbitrary denominator
power. The following example shows why that cannot be replaced by one factor
without the squarefree monomial structure. -/

/-- In `Away(2 : ZMod 4)`, the image of `1` vanishes since `2² = 0`. -/
theorem one_maps_to_zero_in_away_two :
    (algebraMap (ZMod 4) (Localization.Away (2 : ZMod 4))) 1 = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (2 : ZMod 4))]
  exact ⟨⟨(2 : ZMod 4) ^ 2,
    Submonoid.pow_mem _ (Submonoid.mem_powers (2 : ZMod 4)) 2⟩, by decide⟩

/-- One factor `2` does not kill `1` in `ZMod 4`. -/
theorem two_does_not_kill_one : (2 : ZMod 4) * 1 ≠ 0 := by decide

/-- The squarefree face-ring kernel criterion also works over the
nonreduced coefficient ring `ZMod 4`. -/
theorem y_fraction_zero_over_zmod_four :
    disjointPair.faceRingLocalizationFraction (ZMod 4) {false}
      (MvPolynomial.X true) 2 = 0 := by
  let : Nontrivial (ZMod 4) :=
    nontrivial_of_ne (0 : ZMod 4) 1 (by decide)
  apply (disjointPair.faceRingLocalizationFraction_eq_zero_iff
    (ZMod 4) {false} (MvPolynomial.X true) 2).2
  intro a ha
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  apply disjointPair.nonface_of_subset (F := ({false, true} : Finset Bool))
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp
  · exact edge_is_a_nonface

/-! Cheap edge checks for the polynomial criterion and existing localization
consequences. -/

theorem zero_numerator_fraction_eq_zero (K : Reisner.Complex Bool) (F : Finset Bool)
    (r : ℕ) : K.faceRingLocalizationFraction ℚ F 0 r = 0 := by
  apply (K.faceRingLocalizationFraction_eq_zero_iff ℚ F 0 r).2
  simp

theorem edge_localization_is_subsingleton :
    Subsingleton
      (disjointPair.FaceRingLocalization ℚ ({false, true} : Finset Bool)) :=
  disjointPair.faceRingLocalization_subsingleton_of_nonface ℚ edge_is_a_nonface

def ghostOnlyFaces : LowerSet (Finset Bool) where
  carrier := {s | s = ∅}
  lower' := by
    intro a b hab hb
    subst a
    exact Finset.subset_empty.mp hab

def ghostVertexComplex : Reisner.Complex Bool :=
  ⟨ghostOnlyFaces, by rfl⟩

/-- A singleton ghost vertex makes its face product zero and hence its
localization the zero ring. -/
theorem ghost_vertex_localization_is_subsingleton :
    Subsingleton (ghostVertexComplex.FaceRingLocalization ℚ {false}) := by
  apply ghostVertexComplex.faceRingLocalization_subsingleton_of_nonface ℚ
  change ({false} : Finset Bool) ≠ ∅
  simp

theorem x_face_localization_scalars_injective :
    Function.Injective
      (algebraMap ℚ (disjointPair.FaceRingLocalization ℚ {false})) :=
  disjointPair.faceRingLocalization_scalarMap_injective ℚ x_is_a_face

/-- Scalar injectivity remains valid for the trivial coefficient ring. -/
theorem trivial_coeff_face_scalars_injective :
    Function.Injective
      (algebraMap (ZMod 1)
        (disjointPair.FaceRingLocalization (ZMod 1) {false})) :=
  disjointPair.faceRingLocalization_scalarMap_injective (ZMod 1) x_is_a_face

/-- For trivial coefficients, even the monic constant fraction vanishes in
the localization at a face. -/
theorem monic_one_fraction_zero_over_trivial_ring :
    disjointPair.faceRingLocalizationFraction (ZMod 1) {false}
      (MvPolynomial.monomial 0 (1 : ZMod 1)) 0 = 0 := by
  rw [disjointPair.faceRingLocalizationFraction_zero_power]
  exact Subsingleton.elim _ _

noncomputable def empty_product_localization (K : Reisner.Complex Bool) :
    K.FaceRing ℚ ≃ₐ[ℚ] K.FaceRingLocalization ℚ ∅ :=
  K.faceRingLocalizationEmptyEquiv ℚ

#print axioms y_ne_zero_in_faceRing
#print axioms y_maps_to_zero_after_localizing_at_x
#print axioms x_survives_after_localizing_at_x
#print axioms one_maps_to_zero_in_away_two
#print axioms two_does_not_kill_one
#print axioms y_fraction_zero_over_zmod_four
#print axioms zero_numerator_fraction_eq_zero
#print axioms edge_localization_is_subsingleton
#print axioms ghost_vertex_localization_is_subsingleton
#print axioms x_face_localization_scalars_injective
#print axioms trivial_coeff_face_scalars_injective
#print axioms monic_one_fraction_zero_over_trivial_ring
#print axioms empty_product_localization

end LocalizationKernelAudit
