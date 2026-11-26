module

public import Reisner.LinkCalculus
public import Reisner.Cech.UniformLink

/-!
# Uniform cohomological vanishing forces purity

The cutoff hypothesis here uses the ambient maximum face cardinality. This
is distinct from vanishing below each link's own dimension, whose implication
to purity is a separate theorem in the blueprint. Nontrivial coefficients
are essential: over the zero ring every cohomology module vanishes.
-/

@[expose] public section

namespace Reisner.Complex

open scoped Classical

universe u v

variable {V : Type u} (K : Reisner.Complex V) (R : Type v)
  [CommRing R] [Nontrivial R] [Fintype V] [LinearOrder V]

omit [Fintype V] in
/-- Uniform reduced-link cohomology vanishing below `d` forces each facet
to have at least `d` vertices, detected by its nonzero degree `-1` group. -/
theorem facet_card_ge_of_uniform_linkCohomology_vanishes (d : ℕ)
    (hVanishing : ∀ (F : Finset V) (hF : F ∈ K.faces) (r : ℕ), F.card + r < d →
      Subsingleton (((K.link F hF).simplicialCochainComplexInt R).homology ((r : ℤ) - 1)))
    (F : K.facets) : d ≤ F.1.card := by
  by_contra hle
  have hsmall : F.1.card < d := lt_of_not_ge hle
  have hV : ∀ v : V, ({v} : Finset V) ∉ (K.link F.1 F.2.1).faces := by
    intro v hv
    exact Finset.singleton_ne_empty v ((K.mem_link_facet_iff F.2 {v}).mp hv)
  let e := (K.link F.1 F.2.1).simplicialCochainComplexIntHomologyMinusOneEquivOfNoVertices R hV
  have hH : Subsingleton (((K.link F.1 F.2.1).simplicialCochainComplexInt R).homology (-1)) := by
    simpa only [Nat.add_zero, Int.natCast_zero, zero_sub] using
      hVanishing F.1 F.2.1 0 (by simpa only [Nat.add_zero] using hsmall)
  have h01 : (0 : R) = 1 := e.symm.injective (hH.elim _ _)
  exact zero_ne_one h01

/-- At the ambient maximum-face cutoff, the uniform vanishing condition
forces every facet to attain that maximum. -/
theorem facet_card_eq_maxFaceCard_of_uniform_linkCohomology_vanishes
    (hVanishing : ∀ (F : Finset V) (hF : F ∈ K.faces) (r : ℕ),
      F.card + r < K.maxFaceCard →
        Subsingleton (((K.link F hF).simplicialCochainComplexInt R).homology ((r : ℤ) - 1)))
    (F : K.facets) : F.1.card = K.maxFaceCard :=
  le_antisymm (K.card_le_maxFaceCard F.2.1)
    (K.facet_card_ge_of_uniform_linkCohomology_vanishes R K.maxFaceCard hVanishing F)

/-- Vanishing of the actual Čech cohomology below the face-ring dimension
forces combinatorial purity. No Ext/Čech comparison is assumed here. -/
theorem facet_card_eq_maxFaceCard_of_cechCohomology_vanishes
    (hVanishing : ∀ q : ℕ, q < K.maxFaceCard → Subsingleton ((K.cechComplex R).homology q))
    (F : K.facets) : F.1.card = K.maxFaceCard :=
  K.facet_card_eq_maxFaceCard_of_uniform_linkCohomology_vanishes R
    ((K.cechCohomology_vanishes_iff_linkCohomology_vanishes R K.maxFaceCard).mp hVanishing) F

/-- The same actual Čech vanishing hypothesis makes every link attain the
ambient dimension bound, including the empty face and links of facets. -/
theorem link_dimension_eq_of_cechCohomology_vanishes
    (hVanishing : ∀ q : ℕ, q < K.maxFaceCard → Subsingleton ((K.cechComplex R).homology q))
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    (K.link σ hσ).dimension = K.dimension - (σ.card : ℤ) :=
  K.link_dimension_eq_of_pure (K.facet_card_eq_maxFaceCard_of_cechCohomology_vanishes R hVanishing)
    σ hσ

omit [Nontrivial R] in
/-- Actual Čech vanishing implies the reduced-cohomology vanishing bound
using each link's own simplicial dimension, in every integer degree. -/
theorem linkCohomology_vanishes_below_dimension_of_cechCohomology_vanishes
    (hVanishing : ∀ q : ℕ, q < K.maxFaceCard → Subsingleton ((K.cechComplex R).homology q))
    (σ : Finset V) (hσ : σ ∈ K.faces) (i : ℤ)
    (hi : i < (K.link σ hσ).dimension) :
    Subsingleton (((K.link σ hσ).simplicialCochainComplexInt R).homology i) := by
  by_cases hlow : i < -1
  · exact ModuleCat.subsingleton_of_isZero
      ((K.link σ hσ).simplicialCochainComplexInt_homology_isZero_of_lt_minus_one R hlow)
  · have hlow : -1 ≤ i := le_of_not_gt hlow
    let r := (i + 1).toNat
    have hr : (r : ℤ) - 1 = i := by
      dsimp [r]
      exact simplicialCochainInt_natDegree hlow
    have hdim := K.link_dimension_le σ hσ
    have hbound : σ.card + r < K.maxFaceCard := by
      unfold dimension at hdim hi
      omega
    have h := (K.cechCohomology_vanishes_iff_linkCohomology_vanishes R K.maxFaceCard).mp
      hVanishing σ hσ r hbound
    simpa only [hr] using h

omit [Nontrivial R] in
/-- For a pure complex, vanishing below the own dimension of every link
recovers the uniform cutoff and hence the actual Čech vanishing statement. -/
theorem cechCohomology_vanishes_of_pure_linkCohomology_vanishes
    (hPure : ∀ F : K.facets, F.1.card = K.maxFaceCard)
    (hLink : ∀ (σ : Finset V) (hσ : σ ∈ K.faces) (i : ℤ),
      i < (K.link σ hσ).dimension →
        Subsingleton (((K.link σ hσ).simplicialCochainComplexInt R).homology i)) :
    ∀ q : ℕ, q < K.maxFaceCard → Subsingleton ((K.cechComplex R).homology q) := by
  apply (K.cechCohomology_vanishes_iff_linkCohomology_vanishes R K.maxFaceCard).mpr
  intro σ hσ r hbound
  apply hLink σ hσ ((r : ℤ) - 1)
  rw [K.link_dimension_eq_of_pure hPure σ hσ]
  unfold dimension
  omega

/-- A checked Čech-side characterization with purity visible as an explicit
conjunct. Deriving purity from the link-dimension bound alone is not claimed. -/
theorem cechCohomology_vanishes_iff_pure_and_linkCohomology_vanishes :
    (∀ q : ℕ, q < K.maxFaceCard → Subsingleton ((K.cechComplex R).homology q)) ↔
      (∀ F : K.facets, F.1.card = K.maxFaceCard) ∧
        (∀ (σ : Finset V) (hσ : σ ∈ K.faces) (i : ℤ),
          i < (K.link σ hσ).dimension →
            Subsingleton (((K.link σ hσ).simplicialCochainComplexInt R).homology i)) := by
  constructor
  · intro h
    exact ⟨K.facet_card_eq_maxFaceCard_of_cechCohomology_vanishes R h,
      K.linkCohomology_vanishes_below_dimension_of_cechCohomology_vanishes R h⟩
  · rintro ⟨hPure, hLink⟩
    exact K.cechCohomology_vanishes_of_pure_linkCohomology_vanishes R hPure hLink

end Reisner.Complex
