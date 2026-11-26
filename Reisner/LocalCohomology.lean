module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Local cohomology from the depth Ext model

This file packages the derived-category Ext groups used by Mathlib's depth
API into the standard Ext-colimit model of local cohomology. It deliberately
does not identify this model with Mathlib's older left-derived-functor
`localCohomology` construction.
-/

open CategoryTheory Limits

set_option linter.style.haveILetI false

universe u v w

namespace Reisner

variable {R : Type u} [CommRing R]

/-- For a principal ideal, the annihilator submodule at stage `n` is exactly
the submodule of elements killed by `f ^ n`. This includes exponent zero. -/
lemma principalPowerTorsion_eq (f : R) (n : ℕ) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Submodule.torsionBySet R M (((Ideal.span {f}) ^ n : Ideal R) : Set R) =
      Submodule.torsionBy R M (f ^ n) := by
  rw [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq]

/-- The kernel of localization at powers of one element consists exactly of
the elements annihilated by some power of that element. -/
lemma principalLocalization_kernel_iff_torsion
    {M : Type*} [AddCommMonoid M] [Module R M]
    (f : R) (m : M) :
    m ∈ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers f) M) ↔
      ∃ n : ℕ, f ^ n • m = 0 := by
  rw [LocalizedModule.mem_ker_mkLinearMap_iff]
  simp [Submonoid.mem_powers_iff]

/-- Evaluate a map out of `R/J` at `1 + J`; its image is the submodule
annihilated by every element of `J`. -/
noncomputable def depthExtQuotientHomTorsionEval (J : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    (R ⧸ J →ₗ[R] M) →ₗ[R] Submodule.torsionBySet R M (J : Set R) :=
  (LinearMap.applyₗ (Submodule.mkQ J 1)).codRestrict
    (Submodule.torsionBySet R M (J : Set R)) (by
      intro φ
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      have ha : (a : R) • (Submodule.mkQ J 1 : R ⧸ J) = 0 := by
        rw [← map_smul]
        apply LinearMap.mem_ker.mp
        rw [Submodule.ker_mkQ]
        simp
      calc
        (a : R) • φ (Submodule.mkQ J 1) = φ ((a : R) • Submodule.mkQ J 1) :=
          (map_smul φ (a : R) (Submodule.mkQ J 1)).symm
        _ = φ 0 := by rw [ha]
        _ = 0 := map_zero φ)

lemma depthExtQuotientHomTorsionEval_bijective (J : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Function.Bijective (depthExtQuotientHomTorsionEval J M) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := J) x ?_
    intro r
    change φ (Submodule.mkQ J r) = ψ (Submodule.mkQ J r)
    have hmk : Submodule.mkQ J r = (r : R) • Submodule.mkQ J 1 := by
      rw [← map_smul (Submodule.mkQ J) r (1 : R)]
      simp
    rw [hmk, map_smul, map_smul]
    have h1 : φ (Submodule.mkQ J 1) = ψ (Submodule.mkQ J 1) :=
      congrArg Subtype.val h
    rw [h1]
  · intro x
    let g : R →ₗ[R] M := LinearMap.toSpanSingleton R M (x : M)
    have hg : J ≤ LinearMap.ker g := by
      intro r hr
      change g r = 0
      rw [LinearMap.toSpanSingleton_apply]
      exact (Submodule.mem_torsionBySet_iff (R := R) (M := M) (J : Set R) x).mp
        x.property ⟨r, hr⟩
    let φ := J.liftQ g hg
    refine ⟨φ, ?_⟩
    apply Subtype.ext
    change φ (Submodule.mkQ J (1 : R)) = (x : M)
    change g 1 = (x : M)
    exact LinearMap.toSpanSingleton_apply_one R M (x : M)

/-- Evaluation at one commutes with precomposition by a quotient map that
sends one to one; the associated torsion submodules are nested by inclusion. -/
lemma depthExtQuotientHomTorsionEval_natural_of_one
    (K J : Ideal R) (hKJ : K ≤ J) (M : Type v)
    [AddCommGroup M] [Module R M]
    (f : (R ⧸ K) →ₗ[R] (R ⧸ J))
    (h1 : f (Submodule.mkQ K 1) = Submodule.mkQ J 1)
    (φ : (R ⧸ J) →ₗ[R] M) :
    Submodule.inclusion
        (Submodule.torsionBySet_le_torsionBySet_of_subset
          (R := R) (M := M) (show (K : Set R) ⊆ (J : Set R) from hKJ))
      (depthExtQuotientHomTorsionEval J M φ) =
      depthExtQuotientHomTorsionEval K M (φ.comp f) := by
  apply Subtype.ext
  change φ (Submodule.mkQ J 1) = (φ.comp f) (Submodule.mkQ K 1)
  rw [LinearMap.comp_apply, h1]

/-- Linear maps from `R/J` correspond to elements annihilated by `J`. -/
noncomputable def depthExtQuotientHomTorsionEquiv (J : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    (R ⧸ J →ₗ[R] M) ≃ₗ[R] Submodule.torsionBySet R M (J : Set R) :=
  LinearEquiv.ofBijective (depthExtQuotientHomTorsionEval J M)
    (depthExtQuotientHomTorsionEval_bijective J M)

/-- The powers diagram of quotient modules, followed by the Ext functor used
by the depth API. -/
noncomputable def depthExtLocalCohomologyDiagram (I : Ideal R) (q : ℕ) :
    (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).op ⋙
    CategoryTheory.Abelian.linearExtFunctor R (ModuleCat.{u} R) q

/-- The quotient map from the `(n + 1)`-st power stage to the `n`-th
power stage. -/
noncomputable def depthExtPowerStepQuotientMap (I : Ideal R) (n : ℕ) :
    ModuleCat.of R (R ⧸ I ^ (n + 1)) ⟶ ModuleCat.of R (R ⧸ I ^ n) :=
  ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id
    (Ideal.pow_le_pow_right (R := R) (I := I) (Nat.le_succ n)))

/-- An object of the twice-opposite powers indexing category. -/
def depthExtPowerStepIndex (n : ℕ) : (ℕᵒᵖ)ᵒᵖ :=
  Opposite.op (Opposite.op n)

/-- The forward arrow between adjacent objects of the opposite powers diagram. -/
def depthExtPowerStepIndexMap (n : ℕ) :
    depthExtPowerStepIndex n ⟶ depthExtPowerStepIndex (n + 1) :=
  Opposite.op (Opposite.op (CategoryTheory.homOfLE (show n ≤ n + 1 by omega)))

/-- Local cohomology in the derived-category Ext-colimit model shared with
the Mathlib depth development. -/
noncomputable def depthExtLocalCohomology (I : Ideal R) (q : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  colimit (depthExtLocalCohomologyDiagram I q)

/-- Derived Ext is additive in its coefficient module. -/
instance depthExtTargetFunctor_additive
    (M : ModuleCat.{u} R) (q : ℕ) :
    Functor.Additive (CategoryTheory.Abelian.linearExtFunctorObj R M q) where
  map_add := by
    intro X Y f g
    ext e
    simp only [CategoryTheory.Abelian.linearExtFunctorObj,
      CategoryTheory.Abelian.Ext.mk₀_add]
    simp

/-- The derived Ext functor in its coefficient module preserves finite
products, by additivity. -/
theorem depthExtTargetFunctor_preservesFiniteProducts
    (M : ModuleCat.{u} R) (q : ℕ) :
    PreservesFiniteProducts (CategoryTheory.Abelian.linearExtFunctorObj R M q) := by
  infer_instance

/-- The Ext-colimit local-cohomology functor is additive in its coefficient
module. In particular it preserves finite biproducts in `ModuleCat`. -/
theorem depthExtLocalCohomology_additive (I : Ideal R) (q : ℕ) :
    Functor.Additive (depthExtLocalCohomology I q) := by
  refine ⟨?_⟩
  intro X Y f g
  change (colimit (depthExtLocalCohomologyDiagram I q)).map (f + g) =
    (colimit (depthExtLocalCohomologyDiagram I q)).map f +
      (colimit (depthExtLocalCohomologyDiagram I q)).map g
  apply colimit_obj_ext (H := depthExtLocalCohomologyDiagram I q) (k := X)
  intro j
  letI : Functor.Additive ((depthExtLocalCohomologyDiagram I q).obj j) := by
    change Functor.Additive (CategoryTheory.Abelian.linearExtFunctorObj R _ q)
    infer_instance
  calc
    (colimit.ι (depthExtLocalCohomologyDiagram I q) j).app X ≫
        (colimit (depthExtLocalCohomologyDiagram I q)).map (f + g) =
        ((depthExtLocalCohomologyDiagram I q).obj j).map (f + g) ≫
          (colimit.ι (depthExtLocalCohomologyDiagram I q) j).app Y :=
            ((colimit.ι (depthExtLocalCohomologyDiagram I q) j).naturality (f + g)).symm
    _ = _ := by rw [Functor.map_add, Preadditive.add_comp]; simp [NatTrans.naturality]

/-- Additivity gives preservation of finite products in the module category. -/
theorem depthExtLocalCohomology_preservesFiniteProducts (I : Ideal R) (q : ℕ) :
    PreservesFiniteProducts (depthExtLocalCohomology I q) := by
  letI := depthExtLocalCohomology_additive I q
  infer_instance

/-- Evaluate the powers diagram of Ext groups at a fixed coefficient module. -/
noncomputable def depthExtLocalCohomologyModuleDiagram (I : Ideal R) (q : ℕ)
    (M : ModuleCat.{u} R) : (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} R :=
  depthExtLocalCohomologyDiagram I q ⋙ (evaluation _ _).obj M

/-- In degree zero, the local-cohomology transition map is precomposition
with the quotient map between adjacent power stages. -/
lemma depthExtLocalCohomologyModuleDiagram_map_succ
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (x : CategoryTheory.Abelian.Ext (ModuleCat.of R (R ⧸ I ^ n)) M 0) :
    ((depthExtLocalCohomologyModuleDiagram I 0 M).map
      (depthExtPowerStepIndexMap n)).hom x =
      (CategoryTheory.Abelian.Ext.mk₀ (depthExtPowerStepQuotientMap I n)).precompOfLinear
        R M (zero_add 0) x := by
  rfl


/-- Degree-zero derived Ext at a quotient stage is concretely the module of
linear maps from that quotient. -/
noncomputable def depthExtLocalCohomology_extZero_quotientHomEquiv
    (J : Ideal R) (M : ModuleCat.{u} R) :
    (((CategoryTheory.Abelian.linearExtFunctor R (ModuleCat.{u} R) 0).obj
      (Opposite.op (ModuleCat.of R (R ⧸ J)))).obj M) ≃ₗ[R]
      (ModuleCat.of R (R ⧸ J) ⟶ M) := by
  simpa [CategoryTheory.Abelian.linearExtFunctor,
    CategoryTheory.Abelian.linearExtFunctorObj] using
      (CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := R) (X := ModuleCat.of R (R ⧸ J)) (Y := M))

/-- Under the degree-zero Ext/Hom equivalence, precomposition by a
module map becomes ordinary composition by that map. -/
lemma depthExt_zero_precomp_naturality
    (X Y M : ModuleCat.{u} R) (f : X ⟶ Y)
    (x : CategoryTheory.Abelian.Ext Y M 0) :
    CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R) (X := X) (Y := M)
      ((CategoryTheory.Abelian.Ext.mk₀ f).precompOfLinear R M (zero_add 0) x) =
      f ≫ CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R) (X := Y) (Y := M) x := by
  change CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R)
    ((CategoryTheory.Abelian.Ext.mk₀ f).comp x (zero_add 0)) = _
  rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply x]
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  simpa [CategoryTheory.Abelian.Ext.linearEquiv₀] using
    (CategoryTheory.Abelian.Ext.addEquiv₀.apply_symm_apply
      (f ≫ CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R) (X := Y) (Y := M) x))

/-- The Ext-zero/Hom/torsion identifications commute with each transition
in the powers diagram: the induced map on annihilator submodules is inclusion. -/
lemma depthExtLocalCohomology_transition_torsion_natural
    (I : Ideal R) (n : ℕ) (M : ModuleCat.{u} R)
    (x : CategoryTheory.Abelian.Ext (ModuleCat.of R (R ⧸ I ^ n)) M 0) :
    Submodule.inclusion
        (Submodule.torsionBySet_le_torsionBySet_pow n (n + 1) (by omega) I)
      (depthExtQuotientHomTorsionEval (I ^ n) (M : Type u)
        (ModuleCat.homEquiv (CategoryTheory.Abelian.Ext.linearEquiv₀
          (R := R) (X := ModuleCat.of R (R ⧸ I ^ n)) (Y := M) x))) =
      depthExtQuotientHomTorsionEval (I ^ (n + 1)) (M : Type u)
        (ModuleCat.homEquiv (CategoryTheory.Abelian.Ext.linearEquiv₀
          (R := R) (X := ModuleCat.of R (R ⧸ I ^ (n + 1))) (Y := M)
          ((CategoryTheory.Abelian.Ext.mk₀ (depthExtPowerStepQuotientMap I n)).precompOfLinear
            R M (zero_add 0) x))) := by
  have hnat := depthExt_zero_precomp_naturality
    (ModuleCat.of R (R ⧸ I ^ (n + 1))) (ModuleCat.of R (R ⧸ I ^ n)) M
    (depthExtPowerStepQuotientMap I n) x
  have hnat' :
      ModuleCat.homEquiv (CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := R) (X := ModuleCat.of R (R ⧸ I ^ (n + 1))) (Y := M)
        ((CategoryTheory.Abelian.Ext.mk₀ (depthExtPowerStepQuotientMap I n)).precompOfLinear
          R M (zero_add 0) x)) =
      (ModuleCat.homEquiv (CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := R) (X := ModuleCat.of R (R ⧸ I ^ n)) (Y := M) x)).comp
        (depthExtPowerStepQuotientMap I n).hom := by
    rw [hnat]
    change (ModuleCat.ofHom (depthExtPowerStepQuotientMap I n).hom ≫
      CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := R) (X := ModuleCat.of R (R ⧸ I ^ n)) (Y := M) x).hom = _
    rw [ModuleCat.hom_comp]
    rfl
  have hbase := depthExtQuotientHomTorsionEval_natural_of_one
    (I ^ (n + 1)) (I ^ n)
    (Ideal.pow_le_pow_right (show n ≤ n + 1 by omega))
    (M : Type u) (depthExtPowerStepQuotientMap I n).hom
    (by
      change (Submodule.mapQ (I ^ (n + 1)) (I ^ n) LinearMap.id
        (Ideal.pow_le_pow_right (R := R) (I := I) (Nat.le_succ n)))
          (Submodule.Quotient.mk (1 : R)) = _
      rw [Submodule.mapQ_apply]
      rfl)
    (ModuleCat.homEquiv (CategoryTheory.Abelian.Ext.linearEquiv₀
      (R := R) (X := ModuleCat.of R (R ⧸ I ^ n)) (Y := M) x))
  rw [hnat']
  exact hbase

/-- A positive-power stage of the local cohomology colimit vanishes below
the depth of the local ring. -/
lemma depthExtLocalCohomology_stage_subsingleton
    [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]
    (q n : ℕ) (hn : n ≠ 0)
    (hq : (q : ℕ∞) < IsLocalRing.depth (ModuleCat.of R R)) :
    Subsingleton
      (((CategoryTheory.Abelian.linearExtFunctor R (ModuleCat.{u} R) q).obj
        (Opposite.op (ModuleCat.of R
          (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)))).obj (ModuleCat.of R R)) := by
  let I := IsLocalRing.maximalIdeal R
  letI : I.IsMaximal := by simpa [I] using IsLocalRing.maximalIdeal.isMaximal R
  letI : I.IsPrime := inferInstance
  have hneq : I ^ n ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (Ideal.pow_le_self hn) (‹I.IsPrime›.ne_top).lt_top
  have hN : Nontrivial (R ⧸ I ^ n) := Submodule.Quotient.nontrivial_iff.mpr hneq
  have hsupp : Module.support R (R ⧸ I ^ n) = PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
      PrimeSpectrum.zeroLocus_pow _ hn]
  have hsmul : I • (⊤ : Submodule R R) < ⊤ := by
    have heq : I • (⊤ : Submodule R R) = I := by
      ext x
      simp
    rw [heq]
    exact (‹I.IsPrime›.ne_top).lt_top
  let N : ModuleCat R := ModuleCat.of R (R ⧸ I ^ n)
  letI : Nontrivial N := inferInstance
  let M : ModuleCat R := ModuleCat.of R R
  have hdepth : N.depth M = IsLocalRing.depth M := by
    rw [ModuleCat.depth_eq_depth_of_support_eq I N M hsmul hsupp]
    rfl
  exact ModuleCat.subsingleton_ext_of_lt_depth (lt_of_lt_of_eq hq hdepth.symm)

/-- A finite natural cutoff strictly above an ENat depth contains a natural
degree equal to that depth. -/
lemma exists_nat_eq_depth_below_nat (e : ℕ∞) (d : ℕ) (h : e < (d : ℕ∞)) :
    ∃ q : ℕ, (q : ℕ∞) = e ∧ q < d := by
  have htop : e < ⊤ := lt_trans h (ENat.natCast_lt_top d)
  obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt htop)
  refine ⟨q, hq, ?_⟩
  exact ENat.natCast_lt_natCast.mp (hq ▸ h)

/-- At the depth degree, every positive-power Ext stage is nonzero. This is
the stagewise input for the converse cutoff implication. -/
lemma depthExtLocalCohomology_stage_nontrivial
    [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]
    (q n : ℕ) (hn : n ≠ 0)
    (hq : (q : ℕ∞) = IsLocalRing.depth (ModuleCat.of R R)) :
    Nontrivial
      (((CategoryTheory.Abelian.linearExtFunctor R (ModuleCat.{u} R) q).obj
        (Opposite.op (ModuleCat.of R
          (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)))).obj (ModuleCat.of R R)) := by
  let I := IsLocalRing.maximalIdeal R
  letI : I.IsMaximal := by simpa [I] using IsLocalRing.maximalIdeal.isMaximal R
  letI : I.IsPrime := inferInstance
  have hneq : I ^ n ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (Ideal.pow_le_self hn) (‹I.IsPrime›.ne_top).lt_top
  letI : Nontrivial (R ⧸ I ^ n) := Submodule.Quotient.nontrivial_iff.mpr hneq
  have hsupp : Module.support R (R ⧸ I ^ n) = PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
      PrimeSpectrum.zeroLocus_pow _ hn]
  have hsmul : I • (⊤ : Submodule R R) < ⊤ := by
    have heq : I • (⊤ : Submodule R R) = I := by
      ext x
      simp
    rw [heq]
    exact (‹I.IsPrime›.ne_top).lt_top
  let N : ModuleCat R := ModuleCat.of R (R ⧸ I ^ n)
  let M : ModuleCat R := ModuleCat.of R R
  have hdepth : N.depth M = q := by
    rw [ModuleCat.depth_eq_depth_of_support_eq I N M hsmul hsupp]
    simpa [IsLocalRing.depth] using hq.symm
  have hntr := (ModuleCat.depth_eq_iff N M q).mp hdepth
  change Nontrivial (CategoryTheory.Abelian.Ext N M q)
  exact hntr.1

/-- Local cohomology of a Noetherian local ring vanishes below depth in the
derived-category Ext-colimit model. The exponent-zero stage is sent to the
next, positive-power stage before taking the colimit. -/
lemma depthExtLocalCohomology_vanishes_below_depth
    [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]
    (q : ℕ) (hq : (q : ℕ∞) < IsLocalRing.depth (ModuleCat.of R R)) :
    Subsingleton
      ((depthExtLocalCohomology (IsLocalRing.maximalIdeal R) q).obj
        (ModuleCat.of R R)) := by
  classical
  letI : IsFiltered ((ℕᵒᵖ)ᵒᵖ) := IsFiltered.of_equivalence (opOpEquivalence ℕ).symm
  let F := depthExtLocalCohomologyModuleDiagram (IsLocalRing.maximalIdeal R) q
    (ModuleCat.of R R)
  have hzero (j : (ℕᵒᵖ)ᵒᵖ) (x : F.obj j) :
      ∃ k, ∃ f : j ⟶ k, (F.map f).hom x = 0 := by
    cases j with
    | op j =>
      cases j with
      | op n =>
        let k : (ℕᵒᵖ)ᵒᵖ := Opposite.op (Opposite.op (n + 1))
        have f0 : n ⟶ n + 1 := homOfLE (Nat.le_succ n)
        let f : (Opposite.op (Opposite.op n)) ⟶ k :=
          Opposite.op (Opposite.op f0)
        have htarget : Subsingleton (F.obj k) := by
          change Subsingleton (((CategoryTheory.Abelian.linearExtFunctor R
            (ModuleCat R) q).obj
              (Opposite.op (ModuleCat.of R
                (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))))).obj
              (ModuleCat.of R R))
          exact depthExtLocalCohomology_stage_subsingleton q (n + 1)
            (by omega) hq
        exact ⟨k, f, Subsingleton.elim _ _⟩
  let Dcol := ModuleCat.FilteredColimits.colimit F
  have hDcol : Subsingleton Dcol := by
    refine ⟨?_⟩
    intro x y
    have hx : x = 0 := by
      obtain ⟨j, a, rfl⟩ := ModuleCat.FilteredColimits.M.mk_surjective F x
      obtain ⟨k, f, hf⟩ := hzero j a
      have hrep : ModuleCat.FilteredColimits.M.mk F ⟨j, a⟩ = 0 := by
        calc
          ModuleCat.FilteredColimits.M.mk F ⟨j, a⟩ =
              ModuleCat.FilteredColimits.M.mk F ⟨k, (F.map f).hom a⟩ :=
                (ModuleCat.FilteredColimits.M.mk_map F f a).symm
          _ = ModuleCat.FilteredColimits.M.mk F ⟨k, 0⟩ := by rw [hf]
          _ = 0 := (ModuleCat.FilteredColimits.colimit_zero_eq F k).symm
      exact hrep
    have hy : y = 0 := by
      obtain ⟨j, a, rfl⟩ := ModuleCat.FilteredColimits.M.mk_surjective F y
      obtain ⟨k, f, hf⟩ := hzero j a
      have hrep : ModuleCat.FilteredColimits.M.mk F ⟨j, a⟩ = 0 := by
        calc
          ModuleCat.FilteredColimits.M.mk F ⟨j, a⟩ =
              ModuleCat.FilteredColimits.M.mk F ⟨k, (F.map f).hom a⟩ :=
                (ModuleCat.FilteredColimits.M.mk_map F f a).symm
          _ = ModuleCat.FilteredColimits.M.mk F ⟨k, 0⟩ := by rw [hf]
          _ = 0 := (ModuleCat.FilteredColimits.colimit_zero_eq F k).symm
      exact hrep
    rw [hx, hy]
  let e : colimit F ≅ Dcol :=
    asIso ((colimit.isColimit F).uniqueUpToIso
      (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)).hom.hom
  have hcol : IsZero (colimit F) :=
    (ModuleCat.isZero_iff_subsingleton.mpr hDcol).of_iso e
  have eeval := colimitObjIsoColimitCompEvaluation
    (depthExtLocalCohomologyDiagram (IsLocalRing.maximalIdeal R) q)
    (ModuleCat.of R R)
  exact ModuleCat.isZero_iff_subsingleton.mp (hcol.of_iso eeval)

open CategoryTheory.Abelian Opposite localCohomology

private abbrev powerIndex (n : ℕ) : (ℕᵒᵖ)ᵒᵖ := op (op n)

private abbrev powerIndexHom {n k : ℕ} (h : n ≤ k) : powerIndex n ⟶ powerIndex k :=
  (homOfLE h).op.op

private abbrev quotientPowerMap (I : Ideal R) (n : ℕ) :
    (R ⧸ I ^ (n + 1)) →ₗ[R] (R ⧸ I ^ n) :=
  ((ringModIdeals (idealPowersDiagram I)).map (homOfLE (Nat.le_succ n)).op).hom

private lemma quotientPowerMap_mk (I : Ideal R) (n : ℕ) (x : R) :
    quotientPowerMap I n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

private lemma quotientPowerMap_surjective (I : Ideal R) (n : ℕ) :
    Function.Surjective (quotientPowerMap I n) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, quotientPowerMap_mk I n a⟩

private lemma le_quotientPowerMap_ker_annihilator (I : Ideal R) (n : ℕ) :
    I ≤ Module.annihilator R (quotientPowerMap I n).ker := by
  intro a ha
  rw [Module.mem_annihilator]
  rintro ⟨x, hx⟩
  apply Subtype.ext
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (I ^ n) b = 0 at hx
  change Ideal.Quotient.mk (I ^ (n + 1)) (a * b) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  rw [pow_succ']
  exact Ideal.mul_mem_mul ha hx

private lemma quotientPowerMap_ext_ker_subsingleton [IsNoetherianRing R] [IsLocalRing R]
    (q n : ℕ) (hq : (q : ℕ∞) < IsLocalRing.depth (ModuleCat.of R R)) :
    Subsingleton (Ext (ModuleCat.of R
      (quotientPowerMap (IsLocalRing.maximalIdeal R) n).ker) (ModuleCat.of R R) q) := by
  let I := IsLocalRing.maximalIdeal R
  let N := ModuleCat.of R (quotientPowerMap I n).ker
  let M := ModuleCat.of R R
  let : Module.Finite R N := by
    change Module.Finite R (quotientPowerMap I n).ker
    infer_instance
  have hsupport : Module.support R N ⊆ PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus]
    exact PrimeSpectrum.zeroLocus_anti_mono_ideal (le_quotientPowerMap_ker_annihilator I n)
  have hsmul : I • (⊤ : Submodule R M) < ⊤ := by
    change I • (⊤ : Submodule R R) < ⊤
    have heq : I • (⊤ : Submodule R R) = I := by ext x; simp
    rw [heq]
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
  have hvan (i : ℕ) (hi : i < q+1) :
      Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) M i) := by
    apply ModuleCat.subsingleton_ext_of_lt_depth
    exact lt_of_le_of_lt (ENat.natCast_le_natCast.mpr (by omega)) hq
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    ((ModuleCat.exists_isRegular_tfae I (q+1) M hsmul).out 2 4).mp hvan
  exact ModuleCat.subsingleton_ext_of_exists_isRegular I N hsupport M hsmul rs hmem hreg q
    (by omega)

private lemma depthExt_step_injective [IsNoetherianRing R] [IsLocalRing R]
    (q n : ℕ) (hq : (q : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of R R)) :
    Function.Injective
      ((depthExtLocalCohomologyModuleDiagram (IsLocalRing.maximalIdeal R) q
        (ModuleCat.of R R)).map (powerIndexHom (Nat.le_succ n))).hom := by
  let f := quotientPowerMap (IsLocalRing.maximalIdeal R) n
  let S := f.shortComplexKer
  let M := ModuleCat.of R R
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer (quotientPowerMap_surjective _ _)
  change Function.Injective ((Ext.mk₀ S.g).precomp M (zero_add q))
  cases q with
  | zero => exact Ext.precomp_mk₀_injective_of_epi M S.g (hg := hS.epi_g)
  | succ q =>
    have hz : Subsingleton (Ext S.X₁ M q) := quotientPowerMap_ext_ker_subsingleton q n
      (lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self q)) hq)
    have hp := (Ext.contravariant_sequence_exact₃' hS M q (q+1) (Nat.add_comm 1 q)).mono_g
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr hz).eq_zero_of_src _)
    exact (AddCommGrpCat.mono_iff_injective _).mp hp

private lemma powerIndexHom_injective_of_step (F : (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} R)
    (hstep : ∀ n, Function.Injective (F.map (powerIndexHom (Nat.le_succ n))).hom)
    {n k : ℕ} (h : n ≤ k) : Function.Injective (F.map (powerIndexHom h)).hom := by
  induction h with
  | refl =>
    have hid : powerIndexHom (le_refl n) = 𝟙 (powerIndex n) := Subsingleton.elim _ _
    rw [hid, F.map_id]
    exact Function.injective_id
  | @step k h ih =>
    have hcomp : powerIndexHom (Nat.le.step h) =
        powerIndexHom h ≫ powerIndexHom (Nat.le_succ k) := Subsingleton.elim _ _
    rw [hcomp, F.map_comp]
    exact (hstep k).comp ih

/-- The local cohomology of a Noetherian local ring is nonzero in its depth degree. -/
theorem depthExtLocalCohomology_nontrivial_at_depth
    [IsNoetherianRing R] [IsLocalRing R]
    (q : ℕ) (hq : (q : ℕ∞) = IsLocalRing.depth (ModuleCat.of R R)) :
    Nontrivial ((depthExtLocalCohomology (IsLocalRing.maximalIdeal R) q).obj
      (ModuleCat.of R R)) := by
  classical
  let : IsFiltered ((ℕᵒᵖ)ᵒᵖ) := IsFiltered.of_equivalence (opOpEquivalence ℕ).symm
  let I := IsLocalRing.maximalIdeal R
  let M := ModuleCat.of R R
  let F := depthExtLocalCohomologyModuleDiagram I q M
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hstep (n : ℕ) : Function.Injective (F.map (powerIndexHom (Nat.le_succ n))).hom :=
    depthExt_step_injective q n hq.le
  have hpos : Nontrivial (F.obj (powerIndex 1)) :=
    depthExtLocalCohomology_stage_nontrivial q 1 one_ne_zero hq
  obtain ⟨x, hx⟩ := exists_ne (0 : F.obj (powerIndex 1))
  have hcol : (colimit.ι F (powerIndex 1)).hom x ≠ 0 := by
    intro h₀
    obtain ⟨j, f, hf⟩ := Concrete.colimit_rep_eq_zero R F _ x h₀
    obtain ⟨⟨k⟩⟩ := j
    have h : 1 ≤ k := leOfHom f.unop.unop
    have hmap : f = powerIndexHom h := Subsingleton.elim _ _
    rw [hmap] at hf
    exact hx (powerIndexHom_injective_of_step F hstep h (by simpa using hf))
  have hn : Nontrivial (colimit F : ModuleCat R) := ⟨(colimit.ι F (powerIndex 1)).hom x, 0, hcol⟩
  let e := colimitObjIsoColimitCompEvaluation (depthExtLocalCohomologyDiagram I q) M
  exact e.toLinearEquiv.toEquiv.nontrivial_congr.mpr hn

/-- A natural cutoff is at most the depth of a Noetherian local ring precisely when
all local cohomology groups in degrees below the cutoff vanish. -/
theorem le_depth_iff_localCohomology_vanishes [IsNoetherianRing R] [IsLocalRing R] (d : ℕ) :
    (d : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of R R) ↔
      ∀ q : ℕ, q < d → Subsingleton
        ((depthExtLocalCohomology (IsLocalRing.maximalIdeal R) q).obj (ModuleCat.of R R)) := by
  constructor
  · intro hd q hq
    exact depthExtLocalCohomology_vanishes_below_depth q
      (lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr hq) hd)
  · intro hvan
    by_contra! h
    obtain ⟨q, hq, hqd⟩ := exists_nat_eq_depth_below_nat _ d h
    exact (not_nontrivial_iff_subsingleton.mpr (hvan q hqd))
      (depthExtLocalCohomology_nontrivial_at_depth q hq)



namespace DepthExtPowerColimit

namespace FilteredModuleChain

variable {M : Type u} [AddCommGroup M] [Module R M]

def chainDiagram (S : ℕ → Submodule R M) (hS : Monotone S) : ℕ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (S n)
  map {i j} f := ModuleCat.ofHom (Submodule.inclusion (hS f.le))
  map_id n := by ext x; rfl
  map_comp f g := by ext x; rfl

def chainCocone (S : ℕ → Submodule R M) (hS : Monotone S) : Cocone (chainDiagram S hS) := by
  refine Cocone.mk (ModuleCat.of R (⨆ n : ℕ, S n : Submodule R M)) ?_
  refine { app := fun n => ModuleCat.ofHom (Submodule.inclusion (le_iSup (fun n : ℕ => S n) n))
           naturality := ?_ }
  intro i j f
  ext x
  rfl

noncomputable abbrev Dcol (S : ℕ → Submodule R M) (hS : Monotone S) :=
  ModuleCat.FilteredColimits.colimit (chainDiagram S hS)

noncomputable def dcolToSup (S : ℕ → Submodule R M) (hS : Monotone S) :
    Dcol S hS ⟶ ModuleCat.of R (⨆ n : ℕ, S n : Submodule R M) :=
  ModuleCat.FilteredColimits.colimitDesc (chainDiagram S hS) (chainCocone S hS)

lemma coconeMorphism_apply_mk (S : ℕ → Submodule R M) (hS : Monotone S)
    (n : ℕ) (x : S n) :
    (ModuleCat.FilteredColimits.coconeMorphism (chainDiagram S hS) n).hom x =
      ModuleCat.FilteredColimits.M.mk (chainDiagram S hS) ⟨n, x⟩ := by
  rfl

lemma dcolToSup_mk (S : ℕ → Submodule R M) (hS : Monotone S)
    (n : ℕ) (x : S n) :
    (dcolToSup S hS).hom (ModuleCat.FilteredColimits.M.mk (chainDiagram S hS) ⟨n, x⟩) =
      ⟨x.1, le_iSup (fun n : ℕ => S n) n x.2⟩ := by
  have h := congrArg (fun f : (chainDiagram S hS).obj n ⟶ (chainCocone S hS).pt => f.hom x)
    (ModuleCat.FilteredColimits.ι_colimitDesc (chainDiagram S hS)
      (chainCocone S hS) n)
  change (dcolToSup S hS).hom
      ((ModuleCat.FilteredColimits.coconeMorphism (chainDiagram S hS) n).hom x) =
    (chainCocone S hS).ι.app n x at h
  rw [coconeMorphism_apply_mk] at h
  have hr : (chainCocone S hS).ι.app n x =
      (⟨x.1, le_iSup (fun n : ℕ => S n) n x.2⟩ : (⨆ n : ℕ, S n : Submodule R M)) := by
    change Submodule.inclusion (le_iSup (fun n : ℕ => S n) n) x = _
    exact Submodule.inclusion_apply _ x
  exact h.trans hr

theorem dcolToSup_injective (S : ℕ → Submodule R M) (hS : Monotone S) :
    Function.Injective (ModuleCat.homEquiv (dcolToSup S hS)) := by
  intro x y h
  let L := ModuleCat.homEquiv (dcolToSup S hS)
  have hzero : L (x - y) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨n, z, hz⟩ := ModuleCat.FilteredColimits.M.mk_surjective
    (chainDiagram S hS) (x - y)
  let zsup : (⨆ n : ℕ, S n : Submodule R M) :=
    ⟨z.1, le_iSup (fun n : ℕ => S n) n z.2⟩
  have hstage : zsup = 0 := by
    calc
      zsup = (dcolToSup S hS).hom
          (ModuleCat.FilteredColimits.M.mk (chainDiagram S hS) ⟨n, z⟩) :=
        (dcolToSup_mk S hS n z).symm
      _ = L (x - y) := by rw [hz]; rfl
      _ = 0 := hzero
  have hval : z.1 = 0 := by
    exact congrArg Subtype.val hstage
  have hz0 : z = 0 := Subtype.ext hval
  have hxy : x - y = 0 := by
    rw [← hz, hz0]
    exact (ModuleCat.FilteredColimits.colimit_zero_eq (chainDiagram S hS) n).symm
  exact sub_eq_zero.mp hxy

theorem dcolToSup_surjective (S : ℕ → Submodule R M) (hS : Monotone S) :
    Function.Surjective (ModuleCat.homEquiv (dcolToSup S hS)) := by
  intro x
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.2
  refine ⟨ModuleCat.FilteredColimits.M.mk (chainDiagram S hS) ⟨n, ⟨x.1, hn⟩⟩, ?_⟩
  change (dcolToSup S hS).hom
      (ModuleCat.FilteredColimits.M.mk (chainDiagram S hS) ⟨n, ⟨x.1, hn⟩⟩) = x
  rw [dcolToSup_mk]

noncomputable def dcolEquivSup (S : ℕ → Submodule R M) (hS : Monotone S) :
    Dcol S hS ≃ₗ[R] (⨆ n : ℕ, S n : Submodule R M) :=
  LinearEquiv.ofBijective (ModuleCat.homEquiv (dcolToSup S hS))
    ⟨dcolToSup_injective S hS, dcolToSup_surjective S hS⟩

end FilteredModuleChain

def S (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M (I ^ n : Ideal R)

theorem hS (I : Ideal R) (M : ModuleCat.{u} R) : Monotone (S I M) := by
  intro n m h
  exact Submodule.torsionBySet_le_torsionBySet_pow n m h I

def T (I : Ideal R) (M : ModuleCat.{u} R) : (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj j := ModuleCat.of R (Submodule.torsionBySet R M (I ^ (j.unop.unop) : Ideal R))
  map {a b} f := by
    let n := a.unop.unop
    let m := b.unop.unop
    exact ModuleCat.ofHom (Submodule.inclusion
      (Submodule.torsionBySet_le_torsionBySet_pow n m (CategoryTheory.leOfHom f.unop.unop) I))
  map_id j := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

noncomputable def F (I : Ideal R) (M : ModuleCat.{u} R) : (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} R :=
  Reisner.depthExtLocalCohomologyModuleDiagram I 0 M

noncomputable def e (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
  (((CategoryTheory.Abelian.linearExtFunctor R (ModuleCat.{u} R) 0).obj
    (Opposite.op (ModuleCat.of R (R ⧸ I ^ n)))).obj M) ≃ₗ[R]
   Submodule.torsionBySet R M (I ^ n : Ideal R) :=
  (CategoryTheory.Abelian.Ext.linearEquiv₀ (R:=R) (X:=ModuleCat.of R (R ⧸ I^n)) (Y:=M)).trans
   ((ModuleCat.homLinearEquiv (S:=R) (R:=R) (M:=ModuleCat.of R (R ⧸ I^n)) (N:=M)).trans
     (Reisner.depthExtQuotientHomTorsionEquiv (I^n) M))

noncomputable def quotientMap (K J : Ideal R) (h : K ≤ J) :
    ModuleCat.of R (R ⧸ K) ⟶ ModuleCat.of R (R ⧸ J) :=
  ModuleCat.ofHom (Submodule.mapQ K J LinearMap.id h)

lemma quotientMap_one (K J : Ideal R) (h : K ≤ J) :
    (quotientMap K J h).hom (Submodule.mkQ K 1) = Submodule.mkQ J 1 := by
  change (Submodule.mapQ K J LinearMap.id h) (Submodule.Quotient.mk (1 : R)) = _
  rw [Submodule.mapQ_apply]
  rfl

noncomputable def eJ (J : Ideal R) (M : ModuleCat.{u} R) :
    (CategoryTheory.Abelian.Ext (ModuleCat.of R (R ⧸ J)) M 0) ≃ₗ[R]
      Submodule.torsionBySet R M (J : Set R) :=
  (CategoryTheory.Abelian.Ext.linearEquiv₀ (R:=R)
    (X:=ModuleCat.of R (R ⧸ J)) (Y:=M)).trans
    ((ModuleCat.homLinearEquiv (S:=R) (R:=R)
      (M:=ModuleCat.of R (R ⧸ J)) (N:=M)).trans
      (Reisner.depthExtQuotientHomTorsionEquiv J M))

lemma genNat (K J : Ideal R) (hKJ : K ≤ J) (M : ModuleCat.{u} R)
    (x : CategoryTheory.Abelian.Ext (ModuleCat.of R (R ⧸ J)) M 0) :
    Submodule.inclusion
        (Submodule.torsionBySet_le_torsionBySet_of_subset
          (R:=R) (M:=M) (show (K:Set R)⊆(J:Set R) from hKJ))
      (eJ J M x) =
    eJ K M ((CategoryTheory.Abelian.Ext.mk₀ (quotientMap K J hKJ)).precompOfLinear
        R M (zero_add 0) x) := by
  have hnat := Reisner.depthExt_zero_precomp_naturality
    (ModuleCat.of R (R ⧸ K)) (ModuleCat.of R (R ⧸ J)) M
    (quotientMap K J hKJ) x
  have hnat' :
      (ModuleCat.homLinearEquiv (S:=R) (R:=R)
        (M:=ModuleCat.of R (R ⧸ K)) (N:=M))
        (CategoryTheory.Abelian.Ext.linearEquiv₀ (R:=R)
          (X:=ModuleCat.of R (R ⧸ K)) (Y:=M)
          ((CategoryTheory.Abelian.Ext.mk₀ (quotientMap K J hKJ)).precompOfLinear
              R M (zero_add 0) x)) =
      ((ModuleCat.homLinearEquiv (S:=R) (R:=R)
        (M:=ModuleCat.of R (R ⧸ J)) (N:=M))
        (CategoryTheory.Abelian.Ext.linearEquiv₀ (R:=R)
          (X:=ModuleCat.of R (R ⧸ J)) (Y:=M) x)).comp
          (quotientMap K J hKJ).hom := by
    rw [hnat]
    change (quotientMap K J hKJ ≫
      CategoryTheory.Abelian.Ext.linearEquiv₀ (R:=R)
        (X:=ModuleCat.of R (R ⧸ J)) (Y:=M) x).hom = _
    rw [ModuleCat.hom_comp]
    rfl
  have hbase := Reisner.depthExtQuotientHomTorsionEval_natural_of_one
    K J hKJ (M : Type u) (quotientMap K J hKJ).hom
    (quotientMap_one K J hKJ) ((ModuleCat.homLinearEquiv (S:=R) (R:=R)
      (M:=ModuleCat.of R (R ⧸ J)) (N:=M))
      (CategoryTheory.Abelian.Ext.linearEquiv₀ (R:=R)
        (X:=ModuleCat.of R (R ⧸ J)) (Y:=M) x))
  rw [← hnat'] at hbase
  simpa [eJ, Reisner.depthExtQuotientHomTorsionEquiv,
    Reisner.depthExtQuotientHomTorsionEval] using hbase

noncomputable def qMap (I : Ideal R) (n m : ℕ) (h : n ≤ m) :
    ModuleCat.of R (R ⧸ I ^ m) ⟶ ModuleCat.of R (R ⧸ I ^ n) :=
  quotientMap (I ^ m) (I ^ n) (Ideal.pow_le_pow_right h)

lemma F_map (I : Ideal R) (M : ModuleCat.{u} R) (n m : ℕ) (h : n ≤ m) :
    (F I M).map ((CategoryTheory.opOp ℕ).map (CategoryTheory.homOfLE h)) =
      ModuleCat.ofHom (CategoryTheory.Abelian.Ext.precompOfLinear
        (CategoryTheory.Abelian.Ext.mk₀ (qMap I n m h)) R M (zero_add 0)) := by
  rfl

noncomputable def stageIso (I : Ideal R) (M : ModuleCat.{u} R) (j : (ℕᵒᵖ)ᵒᵖ) :
    (F I M).obj j ≅ (T I M).obj j := (e I M j.unop.unop).toModuleIso

set_option maxHeartbeats 0 in
noncomputable def natIso (I : Ideal R) (M : ModuleCat.{u} R) : F I M ≅ T I M :=
  NatIso.ofComponents (fun j => stageIso I M j) (by
    intro i j f
    ext x
    let n := i.unop.unop
    let m := j.unop.unop
    have hnm : n ≤ m := CategoryTheory.leOfHom f.unop.unop
    have hf : f = (CategoryTheory.opOp ℕ).map (CategoryTheory.homOfLE hnm) := by
      apply Subsingleton.elim
    subst f
    rw [F_map I M n m hnm]
    change eJ (I ^ m) M
        ((CategoryTheory.Abelian.Ext.mk₀ (qMap I n m hnm)).precompOfLinear
          R M (zero_add 0) x) =
      Submodule.inclusion
        (Submodule.torsionBySet_le_torsionBySet_pow n m hnm I)
        (eJ (I ^ n) M x)
    exact (genNat (I ^ m) (I ^ n)
      (Ideal.pow_le_pow_right hnm) M x).symm)

noncomputable abbrev G (I : Ideal R) (M : ModuleCat.{u} R) : ℕ ⥤ ModuleCat.{u} R :=
  (CategoryTheory.opOpEquivalence ℕ).inverse ⋙ T I M

noncomputable abbrev D (I : Ideal R) (M : ModuleCat.{u} R) : ℕ ⥤ ModuleCat.{u} R :=
  FilteredModuleChain.chainDiagram (S I M) (hS I M)

noncomputable def GTIso (I : Ideal R) (M : ModuleCat.{u} R) : G I M ≅ D I M :=
  NatIso.ofComponents (fun n => by
    dsimp [G, D, T, FilteredModuleChain.chainDiagram, S]
    exact Iso.refl _) (by
    intro n m f
    ext x
    rfl)

noncomputable def TviaG (I : Ideal R) (M : ModuleCat.{u} R) :
    (CategoryTheory.opOpEquivalence ℕ).functor ⋙ G I M ≅ T I M := by
  refine NatIso.ofComponents (fun j => by
    dsimp [G, T]
    exact Iso.refl _) ?_
  intro i j f
  ext x
  rfl

noncomputable def colimitIsoChain (I : Ideal R) (M : ModuleCat.{u} R) :
    colimit (F I M) ≅ colimit (D I M) := by
  calc
    colimit (F I M) ≅ colimit (T I M) := HasColimit.isoOfNatIso (natIso I M)
    _ ≅ colimit (G I M) := HasColimit.isoOfEquivalence
      (CategoryTheory.opOpEquivalence ℕ) (TviaG I M)
    _ ≅ colimit (D I M) := HasColimit.isoOfNatIso (GTIso I M)

noncomputable def customColimitIso {J : Type v} [SmallCategory J] [IsFiltered J]
    (H : J ⥤ ModuleCat.{max v u} R) :
    CategoryTheory.Limits.colimit H ≅ ModuleCat.FilteredColimits.colimit H :=
  (CategoryTheory.Limits.colimit.isColimit H).coconePointUniqueUpToIso
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit H)

noncomputable def colimitIsoChainCustom (I : Ideal R) (M : ModuleCat.{u} R) :
    ModuleCat.FilteredColimits.colimit (F I M) ≅
      FilteredModuleChain.Dcol (S I M) (hS I M) :=
  (customColimitIso (F I M)).symm ≪≫ (colimitIsoChain I M) ≪≫
    customColimitIso (D I M)

noncomputable def extColimitToSup (I : Ideal R) (M : ModuleCat.{u} R) :
    ModuleCat.FilteredColimits.colimit (F I M) ≃ₗ[R]
      (⨆ n : ℕ, S I M n : Submodule R M) :=
  (colimitIsoChainCustom I M).toLinearEquiv.trans
    (FilteredModuleChain.dcolEquivSup (S I M) (hS I M))

lemma principalSup_eq_kernel (f : R) (M : ModuleCat.{u} R) :
    (⨆ n : ℕ, S (Ideal.span {f}) M n : Submodule R M) =
      LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
  ext x
  rw [Submodule.mem_iSup_of_directed (S (Ideal.span {f}) M)
    (hS (Ideal.span {f}) M).directed_le]
  rw [Reisner.principalLocalization_kernel_iff_torsion]
  constructor
  · rintro ⟨n, hn⟩
    change x ∈ Submodule.torsionBySet R M (((Ideal.span {f}) ^ n : Ideal R) : Set R) at hn
    rw [Reisner.principalPowerTorsion_eq f n (M : Type u)] at hn
    exact ⟨n, (Submodule.mem_torsionBy_iff (f ^ n) x).mp hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change x ∈ Submodule.torsionBySet R M (((Ideal.span {f}) ^ n : Ideal R) : Set R)
    rw [Reisner.principalPowerTorsion_eq f n (M : Type u)]
    exact (Submodule.mem_torsionBy_iff (f ^ n) x).mpr hn

noncomputable def principalExtZeroKernelEquivCore (f : R) (M : ModuleCat.{u} R) :
    (Reisner.depthExtLocalCohomology (Ideal.span {f}) 0).obj M ≃ₗ[R]
      LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
  let F := Reisner.depthExtLocalCohomologyModuleDiagram (Ideal.span {f}) 0 M
  let evalIso := CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation
    (Reisner.depthExtLocalCohomologyDiagram (Ideal.span {f}) 0) M
  exact evalIso.toLinearEquiv.trans
    ((customColimitIso F).toLinearEquiv.trans
      ((extColimitToSup (Ideal.span {f}) M).trans
        (LinearEquiv.ofEq _ _ (principalSup_eq_kernel f M))))

end DepthExtPowerColimit

/-- Degree-zero Ext-colimit local cohomology is the supremum of the
annihilator submodules of the powers of its support ideal. -/
noncomputable def depthExtLocalCohomology_zero_torsionSupEquiv
    (I : Ideal R) (M : ModuleCat.{u} R) :
    (depthExtLocalCohomology I 0).obj M ≃ₗ[R]
      (⨆ n : ℕ, DepthExtPowerColimit.S I M n : Submodule R M) := by
  let F := depthExtLocalCohomologyModuleDiagram I 0 M
  let evalIso := CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation
    (depthExtLocalCohomologyDiagram I 0) M
  exact evalIso.toLinearEquiv.trans
    ((DepthExtPowerColimit.customColimitIso F).toLinearEquiv.trans
      (DepthExtPowerColimit.extColimitToSup I M))

/-- Degree-zero local cohomology for the principal ideal `(f)` is linearly
isomorphic to the kernel of localization at the powers of `f`. -/
noncomputable def principalExtZeroKernelEquiv (f : R) (M : ModuleCat.{u} R) :
    (depthExtLocalCohomology (Ideal.span {f}) 0).obj M ≃ₗ[R]
      LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers f) M) :=
  DepthExtPowerColimit.principalExtZeroKernelEquivCore f M

/-! ### Finite-generator degree-zero localization comparison -/

/-- If the indicated powers of a finite family lie in `J`, then a power of
their span lies in `J`. The extra one handles the empty generating family. -/
lemma span_finset_pow_le_of_generator_powers_mem
    {ι : Type w}
    (s : Finset ι) (f : ι → R) (k : ι → ℕ) (J : Ideal R)
    (hk : ∀ i ∈ s, f i ^ k i ∈ J) :
    (Ideal.span (f '' s)) ^ ((∑ i ∈ s, k i) + 1) ≤ J := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hka : f a ^ k a ∈ J := hk a (by simp)
      have hks : ∀ i ∈ s, f i ^ k i ∈ J := fun i hi => hk i (by simp [hi])
      have hsingle : (Ideal.span {f a}) ^ k a ≤ J := by
        rw [Ideal.span_singleton_pow]
        exact Ideal.span_le.mpr (by
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          subst x
          exact hka)
      have hspan : Ideal.span (f '' insert a s) =
          Ideal.span (f '' s) ⊔ Ideal.span {f a} := by
        simp only [Set.image_insert_eq, Ideal.span_insert]
        exact sup_comm _ _
      have hexp : (∑ i ∈ insert a s, k i) + 1 =
          ((∑ i ∈ s, k i) + 1) + k a := by
        simp [Finset.sum_insert ha]
        omega
      rw [Finset.coe_insert, hspan, hexp]
      exact (Ideal.sup_pow_add_le_pow_sup_pow).trans (sup_le (ih hks) hsingle)

/-- The common kernel of localization at the powers of each member of `s`.
For `s = ∅`, this is `⊤`, the kernel of the unique map to the empty product. -/
noncomputable def finiteLocalizationKernel {M : Type v} [AddCommGroup M]
    [Module R M] {ι : Type w} (s : Finset ι) (f : ι → R) : Submodule R M :=
  ⨅ i : {i // i ∈ s},
    LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)

/-- The power-torsion supremum for a finitely generated ideal is the simultaneous
kernel of localization at the powers of its listed generators. -/
theorem finiteGeneratorsLocalizationKernel_eq_powerTorsionSup
    {M : Type v} [AddCommGroup M] [Module R M] {ι : Type w}
    (s : Finset ι) (f : ι → R) :
    (⨆ n : ℕ, Submodule.torsionBySet R M
      (((Ideal.span (f '' s)) ^ n : Ideal R) : Set R) : Submodule R M) =
      finiteLocalizationKernel s f := by
  classical
  let I : Ideal R := Ideal.span (f '' s)
  let S (n : ℕ) : Submodule R M := Submodule.torsionBySet R M (I ^ n : Ideal R)
  have hS : Monotone S := by
    intro n m h
    change Submodule.torsionBySet R M (I ^ n : Ideal R) ≤
      Submodule.torsionBySet R M (I ^ m : Ideal R)
    exact Submodule.torsionBySet_le_torsionBySet_pow n m h I
  ext m
  change m ∈ (⨆ n : ℕ, S n : Submodule R M) ↔ m ∈ finiteLocalizationKernel s f
  rw [Submodule.mem_iSup_of_directed S hS.directed_le]
  change (∃ n, m ∈ S n) ↔ m ∈
    (⨅ i : {i // i ∈ s}, LinearMap.ker
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M))
  rw [Submodule.mem_iInf]
  constructor
  · rintro ⟨n, hm⟩ i
    have hfi : f i ∈ I := Ideal.subset_span ⟨i.1, i.2, rfl⟩
    have hpow : f i ^ n ∈ I ^ n := Ideal.pow_mem_pow hfi n
    have hkill : f i ^ n • m = 0 := by
      have hm' := (Submodule.mem_torsionBySet_iff (R := R) (M := M)
        ((I ^ n : Ideal R) : Set R) m).mp hm
      exact hm' ⟨f i ^ n, hpow⟩
    exact (principalLocalization_kernel_iff_torsion (f i) m).2 ⟨n, hkill⟩
  · intro hloc
    let k : ι → ℕ := fun i => if hi : i ∈ s then Classical.choose
      ((principalLocalization_kernel_iff_torsion (f i) m).mp (hloc ⟨i, hi⟩)) else 0
    have hk : ∀ i ∈ s, f i ^ k i ∈ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
      intro i hi
      have hkill : f i ^ k i • m = 0 := by
        dsimp [k]
        rw [dite_eq_left hi]
        exact Classical.choose_spec
          ((principalLocalization_kernel_iff_torsion (f i) m).mp (hloc ⟨i, hi⟩))
      change LinearMap.toSpanSingleton R M m (f i ^ k i) = 0
      rw [LinearMap.toSpanSingleton_apply]
      exact hkill
    have hpow : I ^ ((∑ i ∈ s, k i) + 1) ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) :=
      span_finset_pow_le_of_generator_powers_mem s f k _ hk
    refine ⟨(∑ i ∈ s, k i) + 1, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have ha : a.1 ∈ LinearMap.ker (LinearMap.toSpanSingleton R M m) := hpow a.2
    change LinearMap.toSpanSingleton R M m a.1 = 0 at ha
    rw [LinearMap.toSpanSingleton_apply] at ha
    exact ha

/-- Degree-zero Ext-colimit local cohomology supported at a finitely generated
ideal is the simultaneous localization kernel at its chosen generators. -/
noncomputable def finiteGeneratorsExtZeroLocalizationKernelEquiv
    {ι : Type w} (s : Finset ι) (f : ι → R) (M : ModuleCat.{u} R) :
    (depthExtLocalCohomology (Ideal.span (f '' s)) 0).obj M ≃ₗ[R]
      finiteLocalizationKernel (R := R) (M := M) s f := by
  exact (depthExtLocalCohomology_zero_torsionSupEquiv (Ideal.span (f '' s)) M).trans
    (LinearEquiv.ofEq _ _ (finiteGeneratorsLocalizationKernel_eq_powerTorsionSup s f))

#print axioms le_depth_iff_localCohomology_vanishes
end Reisner
