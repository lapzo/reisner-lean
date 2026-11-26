module

public import Reisner.SimplicialChain
public import Reisner.DualHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

/-!
# Canonical reduced homology-cohomology duality

This module identifies augmented cohomology with the linear dual of
augmented homology over a field. Face-cardinality degree `n` corresponds to
reduced degree `n - 1`, including the empty-face degree `-1`.
-/

namespace Reisner.Complex

open CategoryTheory

variable {V : Type*} (K : Reisner.Complex V) (k : Type*)
  [Field k] [Fintype V] [LinearOrder V]

private theorem eval_comm (i j : ℕ) :
    (K.simplicialCochainEvalEquivDualChain k i).toModuleIso.hom ≫
        ModuleCat.ofHom ((K.simplicialChainComplex k).d j i).hom.dualMap =
      ((K.simplicialCochainComplex k).d i j) ≫
        (K.simplicialCochainEvalEquivDualChain k j).toModuleIso.hom := by
  by_cases h : i + 1 = j
  · subst j
    rw [K.simplicialChainComplex_d k i, K.simplicialCochainComplex_d k i]
    exact ModuleCat.hom_ext (K.simplicialCochainEvalEquivDualChain_naturality k i)
  · rw [(K.simplicialChainComplex k).shape j i h,
      (K.simplicialCochainComplex k).shape i j h]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro f
    change (K.simplicialCochainEvalEquivDualChain k i x) 0 =
      (K.simplicialCochainEvalEquivDualChain k j 0) f
    rw [map_zero, map_zero]
    rfl

private noncomputable def evalScIso (i j l : ℕ) :
    (K.simplicialCochainComplex k).sc' i j l ≅
      Reisner.DualHomology.dualShort ((K.simplicialChainComplex k).sc' l j i) :=
  ShortComplex.isoMk (K.simplicialCochainEvalEquivDualChain k i).toModuleIso
    (K.simplicialCochainEvalEquivDualChain k j).toModuleIso
    (K.simplicialCochainEvalEquivDualChain k l).toModuleIso
    (K.eval_comm k i j) (K.eval_comm k j l)

/-- The canonical linear isomorphism from augmented cohomology in degree
`n - 1` to the dual of augmented homology in that degree. -/
noncomputable def simplicialCohomologyDualHomologyEquiv (n : ℕ) :
    (K.simplicialCochainComplex k).homology n ≃ₗ[k]
      Module.Dual k ((K.simplicialChainComplex k).homology n) := by
  let A := K.simplicialCochainComplex k
  let B := K.simplicialChainComplex k
  have ha : (ComplexShape.up ℕ).prev n = n - 1 := by cases n <;> simp
  have hb : (ComplexShape.down ℕ).next n = n - 1 := by cases n <;> simp
  let a := A.homologyIsoSc' (n - 1) n (n + 1) ha (by simp)
  let b := B.homologyIsoSc' (n + 1) n (n - 1) (by simp) hb
  exact a.toLinearEquiv.trans ((ShortComplex.homologyMapIso
    (K.evalScIso k (n - 1) n (n + 1))).toLinearEquiv.trans
    ((Reisner.DualHomology.homologyDualEquiv _).trans b.toLinearEquiv.dualMap))

/-- Canonical reduced homology-cohomology duality in every integer degree.
For `i ≥ -1` this is the face-cardinality evaluation isomorphism transported
along `n ↦ n - 1`; below `-1` it is the unique isomorphism of zero modules. -/
noncomputable def simplicialCohomologyIntDualHomologyEquiv (i : ℤ) :
    (K.simplicialCochainComplexInt k).homology i ≃ₗ[k]
      Module.Dual k ((K.simplicialChainComplexInt k).homology i) := by
  by_cases hi : i < -1
  · letI := ModuleCat.subsingleton_of_isZero
      (K.simplicialCochainComplexInt_homology_isZero_of_lt_minus_one k hi)
    letI := ModuleCat.subsingleton_of_isZero
      (K.simplicialChainComplexInt_homology_isZero_of_lt_minus_one k hi)
    exact LinearEquiv.ofSubsingleton _ _
  · have hdegree := simplicialCochainInt_natDegree (le_of_not_gt hi)
    exact (K.simplicialCochainComplexIntHomologyIso k hdegree).toLinearEquiv.trans
      ((K.simplicialCohomologyDualHomologyEquiv k (i + 1).toNat).trans
        (K.simplicialChainComplexIntHomologyIso k hdegree).toLinearEquiv.dualMap)

/-- In a face-cardinality degree the integer duality is exactly the
transport of the natural evaluation isomorphism, including `n = 0`. -/
theorem simplicialCohomologyIntDualHomologyEquiv_reindex (i : ℤ) (hi : -1 ≤ i) :
    K.simplicialCohomologyIntDualHomologyEquiv k i =
      (K.simplicialCochainComplexIntHomologyIso k
        (simplicialCochainInt_natDegree hi)).toLinearEquiv.trans
        ((K.simplicialCohomologyDualHomologyEquiv k (i + 1).toNat).trans
          (K.simplicialChainComplexIntHomologyIso k
            (simplicialCochainInt_natDegree hi)).toLinearEquiv.dualMap) := by
  unfold simplicialCohomologyIntDualHomologyEquiv
  rw [dite_eq_right (not_lt_of_ge hi)]

/-- Integer reduced cohomology vanishes exactly when integer reduced
homology vanishes, with no connectivity or nonemptiness hypothesis. -/
theorem simplicialCochainInt_homology_isZero_iff_chainInt_homology_isZero
    (i : ℤ) :
    CategoryTheory.Limits.IsZero ((K.simplicialCochainComplexInt k).homology i) ↔
      CategoryTheory.Limits.IsZero ((K.simplicialChainComplexInt k).homology i) := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton,
    (K.simplicialCohomologyIntDualHomologyEquiv k i).toEquiv.subsingleton_congr,
    Module.subsingleton_dual_iff]

end Reisner.Complex
