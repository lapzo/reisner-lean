module

public import Reisner.Cech.UniformLink
public import Reisner.Cech.Purity
public import Reisner.SimplicialDuality
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Čech cutoff in link homology

Over a field, finite-dimensional duality converts the already checked Čech
cutoff criterion in link cohomology to the corresponding criterion in link
homology. The statement remains about the actual Čech complex; comparison
with algebraic local cohomology is a separate dependency.
-/

@[expose] public section

namespace Reisner.Complex

open CategoryTheory.Limits

universe u v

variable {V : Type u} (K : Reisner.Complex V)
variable (k : Type v) [Field k] [Fintype V] [LinearOrder V]

/-- Vanishing of actual Čech cohomology below `d` is equivalent to vanishing
of augmented link homology in the corresponding reduced degrees. Here `r`
is face-cardinality degree, hence reduced degree `r - 1`; `r = 0` includes
the empty face. -/
theorem cechCohomology_vanishes_iff_linkHomology_vanishes (d : ℕ) :
    (∀ q : ℕ, q < d → Subsingleton ((K.cechComplex k).homology q)) ↔
      ∀ (F : Finset V) (hF : F ∈ K.faces) (r : ℕ),
        F.card + r < d →
          Subsingleton (((K.link F hF).simplicialChainComplex k).homology r) := by
  rw [K.cechCohomology_vanishes_iff_linkCohomology_vanishes k d]
  refine forall_congr' fun F => forall_congr' fun hF => forall_congr' fun r =>
    imp_congr_right fun _ => ?_
  let L := K.link F hF
  change Subsingleton ((L.simplicialCochainComplexInt k).homology ((r : ℤ) - 1)) ↔
      Subsingleton ((L.simplicialChainComplex k).homology r)
  rw [← ModuleCat.isZero_iff_subsingleton, ← ModuleCat.isZero_iff_subsingleton,
    ← L.simplicialCochain_homology_isZero_iff_chain_homology_isZero k r]
  let e := L.simplicialCochainComplexIntHomologyIso k (n := r) rfl
  exact ⟨fun h => IsZero.of_iso h e.symm, fun h => IsZero.of_iso h e⟩

/-- The uniform Čech cutoff in integer reduced homology degrees. Degrees
below `-1` vanish by the zero extension; the cutoff at `i = -1` includes
the augmented empty face, even when the link has no actual vertices. -/
theorem cechCohomology_vanishes_iff_linkHomologyInt_vanishes (d : ℕ) :
    (∀ q : ℕ, q < d → Subsingleton ((K.cechComplex k).homology q)) ↔
      ∀ (F : Finset V) (hF : F ∈ K.faces) (i : ℤ),
        (F.card : ℤ) + i + 1 < d →
          Subsingleton (((K.link F hF).simplicialChainComplexInt k).homology i) := by
  rw [K.cechCohomology_vanishes_iff_linkHomology_vanishes k d]
  constructor
  · intro h F hF i hi
    by_cases hlow : i < -1
    · exact ModuleCat.subsingleton_of_isZero
        ((K.link F hF).simplicialChainComplexInt_homology_isZero_of_lt_minus_one k hlow)
    · have hdegree := simplicialCochainInt_natDegree (le_of_not_gt hlow)
      have hbound : F.card + (i + 1).toNat < d := by omega
      let := h F hF (i + 1).toNat hbound
      exact (K.link F hF).simplicialChainComplexIntHomologyIso k hdegree
        |>.toLinearEquiv.toEquiv.subsingleton_congr.mpr inferInstance
  · intro h F hF r hr
    have hbound : (F.card : ℤ) + ((r : ℤ) - 1) + 1 < d := by omega
    let := h F hF ((r : ℤ) - 1) hbound
    exact (K.link F hF).simplicialChainComplexIntHomologyIso k (n := r) rfl
      |>.toLinearEquiv.toEquiv.subsingleton_congr.mp inferInstance

/-- The checked Čech-side characterization in reduced homology form.
The exact facet-purity conjunct and each link's own integer dimension
cutoff are retained. No connectivity assumption is imposed. -/
theorem cechCohomology_vanishes_iff_pure_and_linkHomology_vanishes :
    (∀ q : ℕ, q < K.maxFaceCard → Subsingleton ((K.cechComplex k).homology q)) ↔
      (∀ F : K.facets, F.1.card = K.maxFaceCard) ∧
        (∀ (σ : Finset V) (hσ : σ ∈ K.faces) (i : ℤ),
          i < (K.link σ hσ).dimension →
            Subsingleton (((K.link σ hσ).simplicialChainComplexInt k).homology i)) := by
  rw [K.cechCohomology_vanishes_iff_pure_and_linkCohomology_vanishes k]
  apply and_congr_right
  intro _
  refine forall_congr' fun σ => forall_congr' fun hσ => forall_congr' fun i =>
    imp_congr_right fun _ => ?_
  rw [← ModuleCat.isZero_iff_subsingleton, ← ModuleCat.isZero_iff_subsingleton]
  exact (K.link σ hσ).simplicialCochainInt_homology_isZero_iff_chainInt_homology_isZero k i

end Reisner.Complex
