module

public import Reisner.Cech.ShiftedLink

@[expose] public section

namespace Reisner.Complex

open CategoryTheory CategoryTheory.Limits
open DirectSum

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (K : Complex V) (R : Type v) [CommRing R]

private noncomputable def faceNegativeDegree (F : Finset V) : V →₀ ℤ :=
  Finsupp.onFinset F (fun x => if x ∈ F then -1 else 0) (by
    intro x hx
    by_contra hxF
    simp [hxF] at hx)

omit [Fintype V] in
private theorem faceNegativeDegree_apply (F : Finset V) (x : V) :
    faceNegativeDegree F x = if x ∈ F then -1 else 0 := by
  classical
  simp [faceNegativeDegree]

omit [Fintype V] in
private theorem faceNegativeDegree_nonpos (F : Finset V) :
    faceNegativeDegree F ≤ 0 := by
  intro x
  rw [faceNegativeDegree_apply]
  split <;> norm_num

omit [Fintype V] in
private theorem negativeSupport_faceNegativeDegree (F : Finset V) :
    negativeSupport (faceNegativeDegree F) = F := by
  classical
  ext x
  rw [mem_negativeSupport, faceNegativeDegree_apply]
  by_cases hx : x ∈ F <;> simp [hx]

private theorem subsingleton_of_linearEquiv_right {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (hM : Subsingleton M) : Subsingleton N := by
  constructor
  intro x y
  have h := hM.elim (e.symm x) (e.symm y)
  simpa using congrArg e h

private theorem subsingleton_of_linearEquiv_left {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (hN : Subsingleton N) : Subsingleton M := by
  constructor
  intro x y
  exact e.injective (hN.elim (e x) (e y))

private theorem cechCohomologyDegree_subsingleton_of_total (q : ℕ)
    (a : V →₀ ℤ) (h : Subsingleton ((K.cechComplex R).homology q)) :
    Subsingleton (K.cechCohomologyDegree R q a) := by
  let f := (HomologicalComplex.homologyMap (K.cechDegreeInclusion R a) q).hom
  have hf : Function.Injective f := by
    intro x y hxy
    have hsum : DirectSum.lof R (V →₀ ℤ)
        (fun b => K.cechCohomologyDegree R q b) a x =
      DirectSum.lof R (V →₀ ℤ) (fun b => K.cechCohomologyDegree R q b) a y := by
      apply (K.cechCohomologyDecomposition R q).injective
      simpa [f, K.cechCohomologyDecomposition_lof] using hxy
    have := congrArg (DirectSum.component R (V →₀ ℤ)
      (fun b => K.cechCohomologyDegree R q b) a) hsum
    simpa using this
  exact ⟨fun x y => hf (h.elim (f x) (f y))⟩

/-- Vanishing of the actual Čech cohomology below a cutoff is equivalent to
vanishing of the corresponding augmented reduced link cohomology groups.
This is a Čech-side statement; it does not identify Čech cohomology with the
Ext-colimit definition of local cohomology. -/
theorem cechCohomology_vanishes_iff_linkCohomology_vanishes (d : ℕ) :
    (∀ q : ℕ, q < d → Subsingleton ((K.cechComplex R).homology q)) ↔
      ∀ (F : Finset V) (hF : F ∈ K.faces) (r : ℕ),
        F.card + r < d →
          Subsingleton (((K.link F hF).simplicialCochainComplexInt R).homology
            ((r : ℤ) - 1)) := by
  constructor
  · intro h F hF r hbound
    let a := faceNegativeDegree F
    have ha : a ≤ 0 := faceNegativeDegree_nonpos F
    have hN : negativeSupport a = F := negativeSupport_faceNegativeDegree F
    have hNmem : negativeSupport a ∈ K.faces := hN ▸ hF
    have hq : (negativeSupport a).card + r < d := by simpa [hN] using hbound
    have htotal : Subsingleton ((K.cechComplex R).homology
        ((negativeSupport a).card + r)) := h _ hq
    have hstrand : Subsingleton (K.cechCohomologyDegree R
        ((negativeSupport a).card + r) a) :=
      cechCohomologyDegree_subsingleton_of_total K R _ a htotal
    have hlink : Subsingleton
        (((K.link (negativeSupport a) hNmem).simplicialCochainComplexInt R).homology
          ((r : ℤ) - 1)) :=
      subsingleton_of_linearEquiv_right R
        (K.cechNonpositiveLinkCohomologyIso R a ha hNmem r).toLinearEquiv hstrand
    simpa [hN, cechCohomologyDegree] using hlink
  · intro h q hq
    have hstrand : ∀ a : V →₀ ℤ, Subsingleton (K.cechCohomologyDegree R q a) := by
      intro a
      by_cases hp : ∃ p : V, 0 < a p
      · obtain ⟨p, hp⟩ := hp
        exact K.cechPositiveCohomology_subsingleton R a p hp q
      · have ha : a ≤ 0 := by
          intro p
          exact le_of_not_gt (fun hp' => hp ⟨p, hp'⟩)
        by_cases hN : negativeSupport a ∈ K.faces
        · by_cases hlow : q < (negativeSupport a).card
          · exact ModuleCat.subsingleton_of_isZero
              (K.cechCohomologyDegree_isZero_of_nonpos_card_lt_negativeSupport
                R a ha hN q hlow)
          · let r := q - (negativeSupport a).card
            have hr : (negativeSupport a).card + r = q := by dsimp [r]; omega
            have hlink : Subsingleton
                (((K.link (negativeSupport a) hN).simplicialCochainComplexInt R).homology
                  ((r : ℤ) - 1)) := h (negativeSupport a) hN r (by omega)
            have hsource : Subsingleton
                ((K.cechComplexDegree R a).homology
                  ((negativeSupport a).card + r)) :=
              subsingleton_of_linearEquiv_left R
                (K.cechNonpositiveLinkCohomologyIso R a ha hN r).toLinearEquiv hlink
            simpa [cechCohomologyDegree, hr] using hsource
        · exact ModuleCat.subsingleton_of_isZero
            (K.cechCohomologyDegree_isZero_of_nonpos_negativeSupport_nonface
              R a ha hN q)
    have hsum : Subsingleton
        (⨁ a : V →₀ ℤ, K.cechCohomologyDegree R q a) := by
      classical
      constructor
      intro x y
      apply DFinsupp.ext
      intro a
      exact (hstrand a).elim _ _
    exact subsingleton_of_linearEquiv_right R
      (K.cechCohomologyDecomposition R q) hsum

end Reisner.Complex

end
