module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

/-!
# Homology of a dual short complex

The dual of a short complex reverses its arrows. The evaluation pairing of
cycles descends to a canonical linear equivalence from the dual complex's
homology to the dual of the original homology. This theorem is valid over any
field and does not require finite-dimensional chain modules.
-/

open CategoryTheory

namespace Reisner.DualHomology

universe u v

variable {k : Type v} [Field k] (S : ShortComplex (ModuleCat.{u} k))

/-- Dual short complex, with both arrows reversed. -/
@[expose] public noncomputable def dualShort : ShortComplex (ModuleCat.{max u v} k) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap (by
    ext φ x
    have hx := S.moduleCat_zero_apply x
    change φ (S.g (S.f x)) = 0
    rw [hx, map_zero])

private abbrev H := S.g.hom.ker ⧸ S.moduleCatToCycles.range

/-- Restrict a dual cycle to cycles, and descend across boundaries. -/
private noncomputable def pair : S.f.hom.dualMap.ker →ₗ[k] Module.Dual k (H S) :=
  (Submodule.dualQuotEquivDualAnnihilator _).symm.toLinearMap.comp <|
    (S.g.hom.ker.dualRestrict.comp S.f.hom.dualMap.ker.subtype).codRestrict
      S.moduleCatToCycles.range.dualAnnihilator (by
        intro φ
        apply (Submodule.mem_dualAnnihilator _).2
        rintro _ ⟨x, rfl⟩
        change φ.1 (S.f x) = 0
        exact DFunLike.congr_fun (LinearMap.mem_ker.mp φ.2) x)

private lemma pair_mk (φ : S.f.hom.dualMap.ker) (x : S.g.hom.ker) :
    pair S φ (Submodule.Quotient.mk x) = φ.1 x.1 := rfl

private lemma pair_surj : Function.Surjective (pair S) := by
  intro ψ
  let ψ' := ψ.comp S.moduleCatToCycles.range.mkQ
  obtain ⟨φ, hφ⟩ := (Subspace.dualRestrict_surjective (W := S.g.hom.ker)) ψ'
  have hφ_apply (x : S.g.hom.ker) : φ (x : S.X₂) = ψ' x := DFunLike.congr_fun hφ x
  have hcycle : φ ∈ S.f.hom.dualMap.ker := by
    apply LinearMap.mem_ker.mpr
    ext x
    change φ (S.f x) = 0
    have h := hφ_apply (S.moduleCatToCycles x)
    rw [show ψ' (S.moduleCatToCycles x) = 0 by
      change ψ (Submodule.Quotient.mk _) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _), map_zero]] at h
    exact h
  refine ⟨⟨φ, hcycle⟩, ?_⟩
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x => exact hφ_apply x

private lemma pair_ker : (pair S).ker = (dualShort S).moduleCatToCycles.range := by
  ext φ
  constructor
  · intro hφ
    have hAnn : φ.1 ∈ S.g.hom.ker.dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).2
      intro x hx
      exact DFunLike.congr_fun (LinearMap.mem_ker.mp hφ)
        (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hAnn
    obtain ⟨ψ, hψ⟩ := hAnn
    exact ⟨ψ, Subtype.ext hψ⟩
  · rintro ⟨ψ, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      let ψ' : Module.Dual k S.X₃ := ψ
      change ψ' (S.g x.1) = 0
      rw [show S.g x.1 = 0 from x.2, map_zero]

private noncomputable def knownKernel {X Y : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (f : X →ₗ[k] Y) (p : Submodule k X)
    (hker : f.ker = p) (hs : Function.Surjective f) : (X ⧸ p) ≃ₗ[k] Y :=
  (Submodule.quotEquivOfEq p f.ker hker.symm).trans (f.quotKerEquivOfSurjective hs)

private noncomputable def quotPair : H (dualShort S) ≃ₗ[k] Module.Dual k (H S) :=
  knownKernel (pair S) _ (pair_ker S) (pair_surj S)

private noncomputable def homologyQuot : S.homology ≃ₗ[k] H S :=
  S.moduleCatHomologyIso.toLinearEquiv

/-- The canonical dual-cycle pairing on actual homology objects. -/
public noncomputable def homologyDualEquiv :
    (dualShort S).homology ≃ₗ[k] Module.Dual k S.homology :=
  (homologyQuot (dualShort S)).trans ((quotPair S).trans (homologyQuot S).dualMap)

private theorem quotPair_mk (φ : S.f.hom.dualMap.ker) (x : S.g.hom.ker) :
    quotPair S (Submodule.Quotient.mk φ) (Submodule.Quotient.mk x) = φ.1 x.1 := by
  simp only [quotPair, knownKernel, LinearEquiv.trans_apply]
  rfl

private theorem homologyQuot_π (z : S.g.hom.ker) :
    homologyQuot S (S.homologyπ (S.moduleCatCyclesIso.inv z)) = Submodule.Quotient.mk z := by
  exact (congrArg (fun f => (f : S.moduleCatLeftHomologyData.K ⟶ _) z)
    (show S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatLeftHomologyData.π by simp))

/-- On cycles the equivalence is the ordinary evaluation pairing. -/
theorem homologyDualEquiv_apply_cycle (φ : S.f.hom.dualMap.ker) (x : S.g.hom.ker) :
    homologyDualEquiv S ((dualShort S).homologyπ ((dualShort S).moduleCatCyclesIso.inv φ))
      (S.homologyπ (S.moduleCatCyclesIso.inv x)) = φ.1 x.1 := by
  change quotPair S (homologyQuot _ _) (homologyQuot _ _) = _
  exact (congrArg₂ (fun z w => quotPair S z w)
    (homologyQuot_π (dualShort S) φ) (homologyQuot_π S x)).trans (quotPair_mk S φ x)

end Reisner.DualHomology
