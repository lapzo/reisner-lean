module

public import Reisner.Cech.LocalizedExt

@[expose] public section

/-!
# Face-ring-linear transition maps in the Čech diagram

The core Čech complex is currently packaged over the coefficient ring. This
file constructs its basic localization transition maps over the face ring,
which is the scalar ring required by the derived Ext comparison.

The generator-power Ext-applied complexes form a coherent diagram. Its
degree-zero term diagram is naturally isomorphic to the established
generator-power Ext diagram. This does not yet compare the Ext colimit
with the cohomology of the original Čech complex.
-/

namespace Reisner.Complex

open CategoryTheory Limits

universe u v

variable {V : Type u} (K : Complex V) (R : Type v) [CommRing R]

/-- The empty-product localization identified as an algebra over the face
ring itself. -/
noncomputable def faceRingLocalizationEmptyEquivA :
    K.FaceRing R ≃ₐ[K.FaceRing R] K.FaceRingLocalization R ∅ :=
  IsLocalization.atUnit (K.FaceRing R) (K.FaceRingLocalization R ∅)
    (K.faceRingFaceProduct R ∅) (by simp)

@[simp] theorem faceRingLocalizationEmptyEquivA_apply (x : K.FaceRing R) :
    K.faceRingLocalizationEmptyEquivA R x =
      algebraMap (K.FaceRing R) (K.FaceRingLocalization R ∅) x := rfl

/-- The transition between two face-ring localizations as a homomorphism of
face-ring algebras. This is the same canonical localization map as the
coefficient-algebra transition map, with the stronger scalar structure needed
to form an Ext-applied Čech complex. -/
noncomputable def faceRingLocalizationMapA {F G : Finset V} (h : F ⊆ G) :
    K.FaceRingLocalization R F →ₐ[K.FaceRing R] K.FaceRingLocalization R G := by
  let A := K.FaceRing R
  let f : A →ₐ[A] K.FaceRingLocalization R G := IsScalarTower.toAlgHom A A _
  exact IsLocalization.Away.liftAlgHom (K.faceRingFaceProduct R F)
    (f := f) (IsLocalization.Away.isUnit_of_dvd (K.faceRingFaceProduct R G)
      (K.faceRingFaceProduct_dvd R h))

/-- The face-ring-linear transition map preserves the image of each face-ring
element. -/
@[simp] theorem faceRingLocalizationMapA_algebraMap {F G : Finset V}
    (h : F ⊆ G) (a : K.FaceRing R) :
    K.faceRingLocalizationMapA R h
        (algebraMap (K.FaceRing R) (K.FaceRingLocalization R F) a) =
      algebraMap (K.FaceRing R) (K.FaceRingLocalization R G) a := by
  simp [faceRingLocalizationMapA, AlgHom.commutes]

/-- The face-ring-linear transition map has the same underlying ring map as
the transition used by the original coefficient-ring Čech complex. -/
theorem faceRingLocalizationMapA_toRingHom {F G : Finset V} (h : F ⊆ G) :
    (K.faceRingLocalizationMapA R h).toRingHom =
      (K.faceRingLocalizationMap R h).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (K.faceRingFaceProduct R F))
  apply RingHom.ext
  intro a
  change K.faceRingLocalizationMapA R h
      (algebraMap (K.FaceRing R) (K.FaceRingLocalization R F) a) =
    K.faceRingLocalizationMap R h
      (algebraMap (K.FaceRing R) (K.FaceRingLocalization R F) a)
  rw [faceRingLocalizationMapA_algebraMap, faceRingLocalizationMap_algebraMap]

theorem faceRingLocalizationMapA_apply {F G : Finset V} (h : F ⊆ G)
    (x : K.FaceRingLocalization R F) :
    K.faceRingLocalizationMapA R h x = K.faceRingLocalizationMap R h x := by
  exact congrArg (fun f : K.FaceRingLocalization R F →+* K.FaceRingLocalization R G => f x)
    (faceRingLocalizationMapA_toRingHom K R h)

variable [Fintype V] [LinearOrder V]

/-- The signed localization differential as a linear map over the face ring. -/
noncomputable def cechDifferentialComponentA {q : ℕ} (G : CechIndex V (q + 1)) :
    K.CechCochain R q →ₗ[K.FaceRing R] K.FaceRingLocalization R G.1 := by
  classical
  refine ∑ v : {v : V // v ∈ G.1},
    ((algebraMap R (K.FaceRing R)
        ((-1 : R) ^ (G.1.filter (fun u => u < v.1)).card)) •
      ((K.faceRingLocalizationMapA R (Finset.erase_subset v.1 G.1)).toLinearMap.comp
        (LinearMap.proj (cechEraseIndex G v))))

noncomputable def cechDifferentialA (q : ℕ) :
    K.CechCochain R q →ₗ[K.FaceRing R] K.CechCochain R (q + 1) :=
  LinearMap.pi fun G => K.cechDifferentialComponentA R G

theorem cechDifferentialA_apply {q : ℕ} (z : K.CechCochain R q)
    (G : CechIndex V (q + 1)) :
    K.cechDifferentialA R q z G = K.cechDifferential R q z G := by
  classical
  rw [cechDifferential_apply]
  simp only [cechDifferentialA, LinearMap.pi_apply,
    cechDifferentialComponentA, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    AlgHom.toLinearMap_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rw [faceRingLocalizationMapA_apply]
  rw [Algebra.smul_def (R := K.FaceRing R)
    (A := K.FaceRingLocalization R G.1)]
  rw [Algebra.smul_def (R := R)
    (A := K.FaceRingLocalization R G.1)]
  rw [← IsScalarTower.algebraMap_apply R (K.FaceRing R)
    (K.FaceRingLocalization R G.1)]

theorem cechDifferentialA_comp_eq_zero (q : ℕ) :
    (K.cechDifferentialA R (q + 1)).comp (K.cechDifferentialA R q) = 0 := by
  apply LinearMap.ext
  intro z
  ext G
  change K.cechDifferentialA R (q + 1) (K.cechDifferentialA R q z) G = 0
  rw [cechDifferentialA_apply]
  have hinner : K.cechDifferentialA R q z = K.cechDifferential R q z := by
    ext F
    exact K.cechDifferentialA_apply R z F
  rw [hinner]
  have hcomp := congrArg
    (fun f : K.CechCochain R q →ₗ[R] K.CechCochain R (q + 2) => f z)
    (K.cechDifferential_comp_eq_zero R (q := q))
  simpa using congrFun hcomp G

/-- The actual Čech cochains as a cochain complex of face-ring modules, ready
for applying the project’s derived Ext functor. -/
noncomputable def faceRingCechComplex :
    CochainComplex (ModuleCat (K.FaceRing R)) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of (K.FaceRing R) (K.CechCochain R q))
    (fun q => ModuleCat.ofHom (K.cechDifferentialA R q))
    (fun q => by
      rw [← ModuleCat.ofHom_comp]
      rw [K.cechDifferentialA_comp_eq_zero, ModuleCat.ofHom_zero])

@[simp] theorem faceRingCechComplex_X (q : ℕ) :
    (K.faceRingCechComplex R).X q =
      ModuleCat.of (K.FaceRing R) (K.CechCochain R q) := by
  simp [faceRingCechComplex]

@[simp] theorem faceRingCechComplex_d (q : ℕ) :
    (K.faceRingCechComplex R).d q (q + 1) =
      ModuleCat.ofHom (K.cechDifferentialA R q) := by
  change CochainComplex.of.d
    (fun q => ModuleCat.of (K.FaceRing R) (K.CechCochain R q))
    (fun q => ModuleCat.ofHom (K.cechDifferentialA R q)) q (q + 1) = _
  rw [CochainComplex.of_d]

/-- Apply a fixed augmentation-power derived Ext functor to the face-ring
Čech complex. The parameters choose the quotient stage and Ext degree. -/
noncomputable def faceRingCechExtComplex (n q : ℕ) :
    HomologicalComplex (ModuleCat (K.FaceRing R)) (ComplexShape.up ℕ) := by
  let A := K.FaceRing R
  let M := ModuleCat.of A (A ⧸ K.faceRingAugmentationIdeal R ^ n)
  let H := CategoryTheory.Abelian.linearExtFunctorObj A M q
  exact (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (K.faceRingCechComplex R)

/-- Apply a generator-power derived Ext stage to the face-ring Čech
complex. This uses the same quotient stages as the established
local-cohomology colimit normalization. -/
noncomputable def faceRingGeneratorPowerCechExtComplex (n q : ℕ) :
    HomologicalComplex (ModuleCat (K.FaceRing R)) (ComplexShape.up ℕ) := by
  let A := K.FaceRing R
  let M := ModuleCat.of A (A ⧸ K.faceRingGeneratorPowerIdeal R n)
  let H := CategoryTheory.Abelian.linearExtFunctorObj A M q
  exact (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (K.faceRingCechComplex R)

/-- Every positive Čech degree of the generator-power Ext complex is zero.
This is now a statement at the same stages whose Ext colimit is face-ring
local cohomology. -/
theorem faceRingGeneratorPowerCechExtComplex_X_isZero
    {p : ℕ} (hp : 0 < p) (n q : ℕ) :
    CategoryTheory.Limits.IsZero
      ((K.faceRingGeneratorPowerCechExtComplex R n q).X p) := by
  rw [faceRingGeneratorPowerCechExtComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_X,
    faceRingCechComplex_X]
  exact K.faceRingCechCochain_generatorPower_ext_isZero R hp n q

/-- The positive-degree homology of the generator-power Ext complex
vanishes at each cofinal local-cohomology stage. -/
theorem faceRingGeneratorPowerCechExtComplex_homology_isZero
    {p : ℕ} (hp : 0 < p) (n q : ℕ) :
    CategoryTheory.Limits.IsZero
      ((K.faceRingGeneratorPowerCechExtComplex R n q).homology p) := by
  exact (HomologicalComplex.ExactAt.of_isZero
    (K.faceRingGeneratorPowerCechExtComplex_X_isZero R hp n q)).isZero_homology

/-- Every positive Čech degree of a fixed-stage Ext-applied complex is zero.
This gives the checked stagewise row vanishing a complex-level form. -/
theorem faceRingCechExtComplex_X_isZero {p : ℕ} (hp : 0 < p)
    (n q : ℕ) :
    CategoryTheory.Limits.IsZero ((K.faceRingCechExtComplex R n q).X p) := by
  rw [faceRingCechExtComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_X, faceRingCechComplex_X]
  exact K.faceRingCechCochain_augmentationPower_ext_isZero R hp n q

/-- The Ext-applied Čech complex is exact in every positive degree because
its term in that degree is zero. -/
theorem faceRingCechExtComplex_exactAt {p : ℕ} (hp : 0 < p) (n q : ℕ) :
    HomologicalComplex.ExactAt (K.faceRingCechExtComplex R n q) p :=
  HomologicalComplex.ExactAt.of_isZero
    (K.faceRingCechExtComplex_X_isZero R hp n q)

/-- Positive-degree homology of the fixed-stage Ext-applied Čech complex
vanishes. -/
theorem faceRingCechExtComplex_homology_isZero {p : ℕ} (hp : 0 < p)
    (n q : ℕ) :
    CategoryTheory.Limits.IsZero
      ((K.faceRingCechExtComplex R n q).homology p) :=
  (K.faceRingCechExtComplex_exactAt R hp n q).isZero_homology

/-- The degree-zero Čech cochain module as a face-ring-linear map from the
face ring; every index of cardinality zero is the empty set. -/
noncomputable def cechZeroFromFaceRingA :
    K.FaceRing R →ₗ[K.FaceRing R] K.CechCochain R 0 :=
  LinearMap.pi fun F => (IsScalarTower.toAlgHom (K.FaceRing R) (K.FaceRing R)
    (K.FaceRingLocalization R F.1)).toLinearMap

theorem cechZeroFromFaceRingA_bijective :
    Function.Bijective (K.cechZeroFromFaceRingA R) := by
  classical
  letI : Unique (CechIndex V 0) := {
    default := ⟨∅, by simp⟩
    uniq := fun x => Subtype.ext (Finset.card_eq_zero.mp x.2)
  }
  constructor
  · intro x y h
    have hcoord : algebraMap (K.FaceRing R) (K.FaceRingLocalization R ∅) x =
        algebraMap (K.FaceRing R) (K.FaceRingLocalization R ∅) y := by
      have h' := congrFun h default
      change (IsScalarTower.toAlgHom (K.FaceRing R) (K.FaceRing R)
        (K.FaceRingLocalization R ∅)).toLinearMap x = _ at h'
      change (IsScalarTower.toAlgHom (K.FaceRing R) (K.FaceRing R)
        (K.FaceRingLocalization R ∅)) x = _ at h'
      rw [IsScalarTower.toAlgHom_apply] at h'
      exact h'
    have he : (K.faceRingLocalizationEmptyEquivA R) x =
        (K.faceRingLocalizationEmptyEquivA R) y := by
      simpa only [faceRingLocalizationEmptyEquivA_apply] using hcoord
    exact (K.faceRingLocalizationEmptyEquivA R).injective he
  · intro z
    refine ⟨(K.faceRingLocalizationEmptyEquivA R).symm (z default), ?_⟩
    ext F
    have hF : F = default := Subsingleton.elim _ _
    subst F
    change K.faceRingLocalizationEmptyEquivA R
      ((K.faceRingLocalizationEmptyEquivA R).symm (z default)) = z default
    simp

/-- Degree-zero Čech cochains are canonically equivalent to the face ring as
a module over the face ring. -/
noncomputable def cechZeroFaceRingEquivA :
    K.FaceRing R ≃ₗ[K.FaceRing R] K.CechCochain R 0 :=
  LinearEquiv.ofBijective (K.cechZeroFromFaceRingA R)
    (K.cechZeroFromFaceRingA_bijective R)

/-- Applying fixed-stage derived Ext to the degree-zero Čech term gives the
same object as applying it directly to the face ring. -/
noncomputable def faceRingCechExtZeroTermIso (n q : ℕ) :
    (CategoryTheory.Abelian.linearExtFunctorObj (K.FaceRing R)
      (ModuleCat.of (K.FaceRing R)
        (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n)) q).obj
      (ModuleCat.of (K.FaceRing R) (K.CechCochain R 0)) ≅
    ModuleCat.of (K.FaceRing R)
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of (K.FaceRing R)
          (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n))
        (ModuleCat.of (K.FaceRing R) (K.FaceRing R)) q) := by
  exact (CategoryTheory.Abelian.linearExtFunctorObj (K.FaceRing R)
      (ModuleCat.of (K.FaceRing R)
        (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n)) q).mapIso
    (K.cechZeroFaceRingEquivA R).symm.toModuleIso

/-- The degree-zero object of the fixed-stage Ext-applied complex is the Ext
of the face ring itself. -/
noncomputable def faceRingCechExtComplex_zeroTermIso (n q : ℕ) :
    (K.faceRingCechExtComplex R n q).X 0 ≅
    ModuleCat.of (K.FaceRing R)
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of (K.FaceRing R)
          (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n))
        (ModuleCat.of (K.FaceRing R) (K.FaceRing R)) q) := by
  rw [faceRingCechExtComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_X,
    faceRingCechComplex_X]
  exact K.faceRingCechExtZeroTermIso R n q

/-- Since the next Čech term of the Ext-applied complex is zero, its
degree-zero cycles are the whole degree-zero term. There is no incoming
differential at zero, so degree-zero homology is canonically that term. -/
noncomputable def faceRingCechExtComplex_zeroHomologyIso (n q : ℕ) :
    (K.faceRingCechExtComplex R n q).X 0 ≅
      (K.faceRingCechExtComplex R n q).homology 0 := by
  let C := K.faceRingCechExtComplex R n q
  let d := C.d 0 1
  have hz : CategoryTheory.Limits.IsZero (C.X 1) := by
    simpa [C, faceRingCechExtComplex] using
      K.faceRingCechExtComplex_X_isZero R (by omega) n q
  have hd : d = 0 := hz.eq_of_tgt d 0
  let fork : KernelFork d := KernelFork.ofι (𝟙 (C.X 0)) (by rw [hd]; simp)
  let lim := C.cyclesIsKernel 0 1 (by simp)
  let e := lim.lift fork
  have he : e ≫ C.iCycles 0 = 𝟙 _ := by
    simpa [fork] using lim.fac fork WalkingParallelPair.zero
  let cyclesIso : C.X 0 ≅ C.cycles 0 := {
    hom := e
    inv := C.iCycles 0
    hom_inv_id := he
    inv_hom_id := by
      apply (cancel_mono (C.iCycles 0)).1
      calc
        (C.iCycles 0 ≫ e) ≫ C.iCycles 0 =
            C.iCycles 0 ≫ (e ≫ C.iCycles 0) := Category.assoc _ _ _
        _ = C.iCycles 0 := by
          rw [he]
          change C.iCycles 0 ≫ 𝟙 (C.X 0) = C.iCycles 0
          exact Category.comp_id _
  }
  have hin : C.d 0 0 = 0 := C.shape 0 0 (by simp [ComplexShape.up_Rel])
  exact cyclesIso ≪≫ C.isoHomologyπ 0 0 (by simp) hin

/-- The cohomology in Čech degree zero of the fixed-stage Ext-applied complex
is exactly `Ext^q_A(A/𝔪^n,A)`. This is a stagewise statement about the mapped
complex, not yet the desired derived comparison with Čech cohomology. -/
noncomputable def faceRingCechExtComplex_zeroExtIso (n q : ℕ) :
    ModuleCat.of (K.FaceRing R)
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of (K.FaceRing R)
          (K.FaceRing R ⧸ K.faceRingAugmentationIdeal R ^ n))
        (ModuleCat.of (K.FaceRing R) (K.FaceRing R)) q) ≅
      (K.faceRingCechExtComplex R n q).homology 0 :=
  (K.faceRingCechExtComplex_zeroTermIso R n q).symm ≪≫
    K.faceRingCechExtComplex_zeroHomologyIso R n q

/-- The generator-power derived Ext stages, retaining their coefficient
module as a functor variable. Its transition natural transformations come
from the same quotient maps as `faceRingGeneratorPowerExtDiagram`. -/
noncomputable def faceRingGeneratorPowerExtFunctorDiagram (q : ℕ) :
    (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max u v} (K.FaceRing R) ⥤
      ModuleCat.{max u v} (K.FaceRing R) :=
  (localCohomology.ringModIdeals (K.faceRingGeneratorPowersDiagram R)).op ⋙
    CategoryTheory.Abelian.linearExtFunctor (K.FaceRing R)
      (ModuleCat.{max u v} (K.FaceRing R)) q

/-- The fixed generator-power Ext-applied Čech complexes, assembled with
their quotient-induced transition maps. Naturality of derived Ext makes
each transition a cochain map. -/
noncomputable def faceRingGeneratorPowerCechExtDiagram (q : ℕ) :
    (ℕᵒᵖ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} (K.FaceRing R)) ℕ := by
  let E := K.faceRingGeneratorPowerExtFunctorDiagram R q
  letI (n : (ℕᵒᵖ)ᵒᵖ) : (E.obj n).PreservesZeroMorphisms := by
    change Functor.PreservesZeroMorphisms
      (CategoryTheory.Abelian.linearExtFunctorObj (K.FaceRing R) _ q)
    infer_instance
  exact {
    obj n := ((E.obj n).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (K.faceRingCechComplex R)
    map f := ((E.map f).mapHomologicalComplex (ComplexShape.up ℕ)).app
      (K.faceRingCechComplex R)
    map_id n := by simp
    map_comp f g := by simp
  }

/-- The coherent diagram has exactly the previously constructed stages. -/
@[simp] theorem faceRingGeneratorPowerCechExtDiagram_obj (q : ℕ) (n : (ℕᵒᵖ)ᵒᵖ) :
    (K.faceRingGeneratorPowerCechExtDiagram R q).obj n =
      K.faceRingGeneratorPowerCechExtComplex R n.unop.unop q := rfl

/-- Each component of a stage transition is the corresponding natural
transformation of derived Ext evaluated at the actual Čech term. -/
@[simp] theorem faceRingGeneratorPowerCechExtDiagram_map_f
    (q p : ℕ) {i j : (ℕᵒᵖ)ᵒᵖ} (f : i ⟶ j) :
    ((K.faceRingGeneratorPowerCechExtDiagram R q).map f).f p =
      ((K.faceRingGeneratorPowerExtFunctorDiagram R q).map f).app
        ((K.faceRingCechComplex R).X p) := rfl

/-- Evaluation at a Čech degree agrees naturally with evaluating the
generator-power Ext functor diagram at that Čech cochain module. -/
noncomputable def faceRingGeneratorPowerCechExtDiagram_evalIso (q p : ℕ) :
    K.faceRingGeneratorPowerCechExtDiagram R q ⋙
        HomologicalComplex.eval _ (ComplexShape.up ℕ) p ≅
      K.faceRingGeneratorPowerExtFunctorDiagram R q ⋙
        (evaluation _ _).obj (ModuleCat.of (K.FaceRing R) (K.CechCochain R p)) :=
  Iso.refl _

/-- The degree-zero term diagram is naturally the established
generator-power Ext diagram of the face ring. Naturality includes
compatibility with every quotient-induced stage transition. -/
noncomputable def faceRingGeneratorPowerCechExtDiagram_zeroTermIso (q : ℕ) :
    K.faceRingGeneratorPowerCechExtDiagram R q ⋙
        HomologicalComplex.eval _ (ComplexShape.up ℕ) 0 ≅
      K.faceRingGeneratorPowerExtDiagram R q :=
  (K.faceRingGeneratorPowerExtFunctorDiagram R q).flip.mapIso
    (K.cechZeroFaceRingEquivA R).symm.toModuleIso

/-- Every stage of the coherent diagram still has zero positive Čech
terms. No limit or cohomology interchange is used here. -/
theorem faceRingGeneratorPowerCechExtDiagram_X_isZero
    {p : ℕ} (hp : 0 < p) (q : ℕ) (n : (ℕᵒᵖ)ᵒᵖ) :
    IsZero (((K.faceRingGeneratorPowerCechExtDiagram R q).obj n).X p) :=
  K.faceRingGeneratorPowerCechExtComplex_X_isZero R hp n.unop.unop q

/-- The natural degree-zero term identification induces the same
generator-power Ext colimit as the existing local-cohomology stages. -/
noncomputable def faceRingGeneratorPowerCechExtDiagram_zeroTermColimitIso (q : ℕ) :
    colimit (K.faceRingGeneratorPowerCechExtDiagram R q ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℕ) 0) ≅
      colimit (K.faceRingGeneratorPowerExtDiagram R q) :=
  HasColimit.isoOfNatIso (K.faceRingGeneratorPowerCechExtDiagram_zeroTermIso R q)

/-- Colimits of complexes are computed degreewise, so the degree-zero term
of the colimit complex is also the established generator-power Ext colimit. -/
noncomputable def faceRingGeneratorPowerCechExtDiagram_colimitZeroTermIso (q : ℕ) :
    (colimit (K.faceRingGeneratorPowerCechExtDiagram R q)).X 0 ≅
      colimit (K.faceRingGeneratorPowerExtDiagram R q) :=
  preservesColimitIso (HomologicalComplex.eval _ (ComplexShape.up ℕ) 0)
    (K.faceRingGeneratorPowerCechExtDiagram R q) ≪≫
      K.faceRingGeneratorPowerCechExtDiagram_zeroTermColimitIso R q

/-- The colimit of the Ext-applied complexes has zero terms in every
positive Čech degree, by degreewise colimit preservation. -/
theorem faceRingGeneratorPowerCechExtDiagram_colimit_X_isZero
    {p : ℕ} (hp : 0 < p) (q : ℕ) :
    IsZero ((colimit (K.faceRingGeneratorPowerCechExtDiagram R q)).X p) := by
  let D := K.faceRingGeneratorPowerCechExtDiagram R q
  have h : IsZero (colimit (D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro n
    exact (K.faceRingGeneratorPowerCechExtDiagram_X_isZero R hp q n).eq_of_src _ _
  exact h.of_iso (preservesColimitIso
    (HomologicalComplex.eval _ (ComplexShape.up ℕ) p) D)

/-- The colimit complex has zero homology in positive Čech degrees. The
complex is obtained by applying fixed `Ext^q` functors before taking the
colimit; this is not a claim about the original Čech cohomology. -/
theorem faceRingGeneratorPowerCechExtDiagram_colimit_homology_isZero
    {p : ℕ} (hp : 0 < p) (q : ℕ) :
    IsZero ((colimit (K.faceRingGeneratorPowerCechExtDiagram R q)).homology p) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.faceRingGeneratorPowerCechExtDiagram_colimit_X_isZero R hp q)).isZero_homology

/-- Local cohomology is the colimit of the degree-zero terms of the coherent
generator-power Ext-applied Čech diagram. The Ext degree is `q`; this does
not identify local cohomology with degree-`q` Čech cohomology. -/
noncomputable def faceRingLocalCohomologyIsoGeneratorPowerCechExtZeroTermColimit (q : ℕ) :
    (Reisner.depthExtLocalCohomology (K.faceRingAugmentationIdeal R) q).obj
        (ModuleCat.of (K.FaceRing R) (K.FaceRing R)) ≅
      colimit (K.faceRingGeneratorPowerCechExtDiagram R q ⋙
        HomologicalComplex.eval _ (ComplexShape.up ℕ) 0) :=
  K.faceRingLocalCohomologyIsoGeneratorPowerExtColimit R q ≪≫
    (K.faceRingGeneratorPowerCechExtDiagram_zeroTermColimitIso R q).symm

end Reisner.Complex
