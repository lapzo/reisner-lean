module

public import Reisner.Cech.Core

@[expose] public section

namespace Reisner.Complex

open DirectSum
open scoped Classical
open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (K : Reisner.Complex V) (R : Type v) [CommRing R]

/-- The submodule of cochains whose every localization coordinate has fine
integer degree `a`. -/
noncomputable def cechDegreeSubmodule (q : ℕ) (a : V →₀ ℤ) :
    Submodule R (K.CechCochain R q) :=
  Submodule.pi Set.univ fun F => K.faceRingLocalizationComponent R F.1 a

omit [LinearOrder V] in
@[simp]
theorem mem_cechDegreeSubmodule {q : ℕ} {a : V →₀ ℤ}
    (z : K.CechCochain R q) : z ∈ K.cechDegreeSubmodule R q a ↔
      ∀ F : CechIndex V q, z F ∈ K.faceRingLocalizationComponent R F.1 a := by
  simp [cechDegreeSubmodule, Submodule.mem_pi]

omit [Fintype V] [LinearOrder V] in
private theorem cechLocalizationComponent_eq_basisFiber (F : Finset V)
    (a : V →₀ ℤ) :
    K.faceRingLocalizationComponent R F a =
      (Finsupp.supported R R {b : K.localizationDegrees F | b.1 = a}).map
        (K.localizationMonomialBasis R F).repr.symm.toLinearMap := by
  rw [Finsupp.supported_eq_span_single, Submodule.map_span]
  simp only [Set.image_image, LinearEquiv.coe_coe, Module.Basis.repr_symm_single,
    one_smul, localizationMonomialBasis_apply]
  by_cases ha : K.LocalizationAdmissible F a
  · have hset : (fun b : K.localizationDegrees F => K.localizationMonomial R F b.1) ''
        {b | b.1 = a} = {K.localizationMonomial R F a} := by
      ext z
      constructor
      · rintro ⟨b, hb, rfl⟩
        simp [show b.1 = a from hb]
      · intro hz
        exact ⟨⟨a, ha⟩, rfl, (Set.mem_singleton_iff.mp hz).symm⟩
    rw [hset, faceRingLocalizationComponent]
  · rw [K.faceRingLocalizationComponent_eq_bot R F a ha]
    have hempty : {b : K.localizationDegrees F | b.1 = a} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact ha ((show b.1 = a from hb) ▸ b.2)
    simp [hempty]

omit [Fintype V] [LinearOrder V] in
private theorem cechLocalizationComponent_mem_iff_basis_repr (F : Finset V)
    (a : V →₀ ℤ) (z : K.FaceRingLocalization R F) :
    z ∈ K.faceRingLocalizationComponent R F a ↔
      (K.localizationMonomialBasis R F).repr z ∈
        Finsupp.supported R R {b : K.localizationDegrees F | b.1 = a} := by
  rw [K.cechLocalizationComponent_eq_basisFiber R F a, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hweq⟩
    have hrepr : w = (K.localizationMonomialBasis R F).repr z := by
      simpa using congrArg (K.localizationMonomialBasis R F).repr hweq
    simpa [hrepr] using hw
  · intro hz
    exact ⟨(K.localizationMonomialBasis R F).repr z, hz, by simp⟩

omit [LinearOrder V] in
private theorem cechDegreeSubmodule_mem_iff_basis_repr {q : ℕ} {a : V →₀ ℤ}
    (z : K.CechCochain R q) :
    z ∈ K.cechDegreeSubmodule R q a ↔
      (K.cechCochainMonomialBasis R q).repr z ∈
        Finsupp.supported R R
          {i : Σ F : CechIndex V q, K.localizationDegrees F.1 | i.2.1 = a} := by
  rw [K.mem_cechDegreeSubmodule, Finsupp.mem_supported']
  constructor
  · intro hz i hi
    rcases i with ⟨F, b⟩
    have hdegree : b.1 ≠ a := by
      intro h
      exact hi (by cases h; rfl)
    have hlocal := (K.cechLocalizationComponent_mem_iff_basis_repr R F.1 a (z F)).mp
      (hz F)
    have hzero := (Finsupp.mem_supported' R
      ((K.localizationMonomialBasis R F.1).repr (z F))).mp hlocal b hdegree
    simpa [cechCochainMonomialBasis] using hzero
  · intro hz F
    apply (K.cechLocalizationComponent_mem_iff_basis_repr R F.1 a (z F)).mpr
    rw [Finsupp.mem_supported']
    intro b hb
    have hnot : (⟨F, b⟩ : Σ F : CechIndex V q, K.localizationDegrees F.1) ∉
        {i : Σ F : CechIndex V q, K.localizationDegrees F.1 | i.2.1 = a} := by
      simpa using hb
    have hzero := hz ⟨F, b⟩ hnot
    simpa [cechCochainMonomialBasis] using hzero

omit [LinearOrder V] in
private theorem cechDegreeSubmodule_eq_basisFiber (q : ℕ) (a : V →₀ ℤ) :
    K.cechDegreeSubmodule R q a =
      (Finsupp.supported R R
        {i : Σ F : CechIndex V q, K.localizationDegrees F.1 | i.2.1 = a}).map
          (K.cechCochainMonomialBasis R q).repr.symm.toLinearMap := by
  ext z
  rw [Submodule.mem_map, K.cechDegreeSubmodule_mem_iff_basis_repr]
  constructor
  · intro hz
    exact ⟨(K.cechCochainMonomialBasis R q).repr z, hz, by simp⟩
  · rintro ⟨w, hw, hweq⟩
    have hrepr : w = (K.cechCochainMonomialBasis R q).repr z := by
      simpa using congrArg (K.cechCochainMonomialBasis R q).repr hweq
    simpa [hrepr] using hw

omit [LinearOrder V] in
/-- The fine-degree Čech submodules form an internal direct sum of the full
cochain module, including all finite subset coordinates. -/
theorem cechDegreeSubmodule_isInternal [DecidableEq V] (q : ℕ) :
    DirectSum.IsInternal (K.cechDegreeSubmodule R q) := by
  let b := K.cechCochainMonomialBasis R q
  have hcomp : K.cechDegreeSubmodule R q = fun a =>
      (Finsupp.supported R R
        {i : Σ F : CechIndex V q, K.localizationDegrees F.1 | i.2.1 = a}).map
        b.repr.symm.toLinearMap :=
    funext (K.cechDegreeSubmodule_eq_basisFiber R q)
  rw [hcomp]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply LinearMap.iSupIndep_map _ b.repr.symm.injective
    rw [iSupIndep_def]
    intro a
    have hd := Finsupp.disjoint_supported_supported (M := R) (R := R)
      (s := {i : Σ F : CechIndex V q, K.localizationDegrees F.1 | i.2.1 = a})
      (t := {i : Σ F : CechIndex V q, K.localizationDegrees F.1 | i.2.1 = a}ᶜ)
      disjoint_compl_right
    apply hd.mono_right
    refine iSup₂_le fun e he => Finsupp.supported_mono ?_
    intro i hi
    exact fun h => he (hi.symm.trans h)
  · rw [← Submodule.map_iSup, ← Finsupp.supported_iUnion]
    have h :
        (⋃ a : V →₀ ℤ,
          {i : Σ F : CechIndex V q, K.localizationDegrees F.1 | i.2.1 = a}) =
          Set.univ := by
      ext i
      simp
    rw [h, Finsupp.supported_univ, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.repr.symm.surjective

theorem cechDifferential_maps_degree {q : ℕ} (a : V →₀ ℤ) :
    (K.cechDegreeSubmodule R q a).map (K.cechDifferential R q) ≤
      K.cechDegreeSubmodule R (q + 1) a := by
  rintro _ ⟨z, hz, rfl⟩
  have hmem := (K.mem_cechDegreeSubmodule R z).mp hz
  apply (K.mem_cechDegreeSubmodule R _).mpr
  intro G
  rw [cechDifferential_apply]
  apply Submodule.sum_mem
  intro v hv
  apply Submodule.smul_mem
  exact K.faceRingLocalizationMap_component R
    (Finset.erase_subset v.1 G.1) a
    ⟨z (cechEraseIndex G v), hmem (cechEraseIndex G v), rfl⟩

/-- Restriction of the Čech differential to each fine integer degree. -/
noncomputable def cechDifferentialDegree {q : ℕ} (a : V →₀ ℤ) :
    K.cechDegreeSubmodule R q a →ₗ[R] K.cechDegreeSubmodule R (q + 1) a :=
  (K.cechDifferential R q).restrict
    (fun z hz => K.cechDifferential_maps_degree R a ⟨z, hz, rfl⟩)

/-- The canonical decomposition of a Čech cochain into its finitely many
nonzero homogeneous components. -/
@[instance_reducible]
noncomputable def cechDecomposition (q : ℕ) :
    DirectSum.Decomposition (K.cechDegreeSubmodule R q) :=
  (K.cechDegreeSubmodule_isInternal R q).chooseDecomposition

/-- The linear equivalence giving the finite homogeneous decomposition. -/
noncomputable def cechDecomposeLinearEquiv (q : ℕ) :
    K.CechCochain R q ≃ₗ[R] ⨁ a, K.cechDegreeSubmodule R q a := by
  letI := K.cechDecomposition R q
  exact DirectSum.decomposeLinearEquiv (K.cechDegreeSubmodule R q)

/-- Projection to the actual fine-degree submodule. -/
noncomputable def cechHomogeneousComponent (q : ℕ) (a : V →₀ ℤ) :
    K.CechCochain R q →ₗ[R] K.cechDegreeSubmodule R q a :=
  DirectSum.component R (V →₀ ℤ) (fun b => K.cechDegreeSubmodule R q b) a ∘ₗ
    (K.cechDecomposeLinearEquiv R q).toLinearMap

/-- A homogeneous cochain is recovered by projection to its own degree. -/
@[simp]
theorem cechHomogeneousComponent_eq_self {q : ℕ} {a : V →₀ ℤ}
    (z : K.cechDegreeSubmodule R q a) :
    K.cechHomogeneousComponent R q a z = z := by
  let := K.cechDecomposition R q
  change DirectSum.decompose (K.cechDegreeSubmodule R q) (z : K.CechCochain R q) a = z
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same (K.cechDegreeSubmodule R q) z.2

/-- Projection kills a cochain homogeneous of a different degree. -/
theorem cechHomogeneousComponent_eq_zero_of_ne {q : ℕ} {a b : V →₀ ℤ}
    (h : a ≠ b) (z : K.cechDegreeSubmodule R q b) :
    K.cechHomogeneousComponent R q a z = 0 := by
  let := K.cechDecomposition R q
  change DirectSum.decompose (K.cechDegreeSubmodule R q) (z : K.CechCochain R q) a = 0
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne (K.cechDegreeSubmodule R q) z.2 h.symm

open scoped Classical in
/-- Reconstruction is a sum over the finite support of the decomposition. -/
theorem cechHomogeneousComponent_sum_support (q : ℕ) (z : K.CechCochain R q) :
    ∑ a ∈ (K.cechDecomposeLinearEquiv R q z).support,
      (K.cechHomogeneousComponent R q a z : K.CechCochain R q) = z := by
  classical
  let := K.cechDecomposition R q
  exact DirectSum.sum_support_decompose (K.cechDegreeSubmodule R q) z

/-- Homogeneous projections jointly detect zero cochains. -/
theorem cechHomogeneousComponent_eq_zero_iff (q : ℕ) (z : K.CechCochain R q) :
    (∀ a, K.cechHomogeneousComponent R q a z = 0) ↔ z = 0 := by
  constructor
  · intro h
    apply (K.cechDecomposeLinearEquiv R q).injective
    apply DFinsupp.ext
    intro a
    have ha := h a
    change (K.cechDecomposeLinearEquiv R q z) a = 0 at ha
    simpa only [map_zero, DFinsupp.zero_apply] using ha
  · rintro rfl a
    exact map_zero _

/-- Taking a fine-degree component commutes with the Čech differential. -/
theorem cechHomogeneousComponent_differential {q : ℕ} (a : V →₀ ℤ)
    (z : K.CechCochain R q) :
    K.cechHomogeneousComponent R (q + 1) a (K.cechDifferential R q z) =
      K.cechDifferentialDegree R a (K.cechHomogeneousComponent R q a z) := by
  let := K.cechDecomposition R q
  have h : K.cechHomogeneousComponent R (q + 1) a ∘ₗ K.cechDifferential R q =
      K.cechDifferentialDegree R a ∘ₗ K.cechHomogeneousComponent R q a := by
    apply DirectSum.decompose_lhom_ext (K.cechDegreeSubmodule R q)
    intro b
    apply LinearMap.ext
    intro x
    by_cases hab : a = b
    · subst b
      change K.cechHomogeneousComponent R (q + 1) a
        ((K.cechDifferentialDegree R a x : K.cechDegreeSubmodule R (q + 1) a) :
          K.CechCochain R (q + 1)) = _
      simp
    · have hd : K.cechDifferential R q (x : K.CechCochain R q) ∈
          K.cechDegreeSubmodule R (q + 1) b :=
        K.cechDifferential_maps_degree R b ⟨x, x.2, rfl⟩
      change K.cechHomogeneousComponent R (q + 1) a
        (K.cechDifferential R q (x : K.CechCochain R q)) =
          K.cechDifferentialDegree R a (K.cechHomogeneousComponent R q a x)
      rw [K.cechHomogeneousComponent_eq_zero_of_ne R hab x, map_zero]
      exact K.cechHomogeneousComponent_eq_zero_of_ne R hab ⟨_, hd⟩
  exact DFunLike.congr_fun h z

/-- A cochain is a cocycle exactly when each homogeneous component is a cocycle. -/
theorem cechDifferential_eq_zero_iff_components {q : ℕ} (z : K.CechCochain R q) :
    K.cechDifferential R q z = 0 ↔
      ∀ a, K.cechDifferentialDegree R a (K.cechHomogeneousComponent R q a z) = 0 := by
  rw [← K.cechHomogeneousComponent_eq_zero_iff R (q + 1)]
  simp_rw [K.cechHomogeneousComponent_differential R]

/-- A homogeneous incoming boundary in degree `q + 1` has a homogeneous
primitive of the same fine degree. There is no incoming term in degree zero. -/
theorem cechBoundary_homogeneous_primitive {q : ℕ} (a : V →₀ ℤ)
    (w : K.cechDegreeSubmodule R (q + 1) a) :
    (w : K.CechCochain R (q + 1)) ∈ LinearMap.range (K.cechDifferential R q) ↔
      w ∈ LinearMap.range (K.cechDifferentialDegree R (q := q) a) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨K.cechHomogeneousComponent R q a y, ?_⟩
    rw [← K.cechHomogeneousComponent_differential R a, hy]
    exact K.cechHomogeneousComponent_eq_self R w
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩

open CategoryTheory

/-- The restricted differentials also square to zero in their actual degree
submodules. -/
theorem cechDifferentialDegree_comp_eq_zero {q : ℕ} (a : V →₀ ℤ) :
    K.cechDifferentialDegree R (q := q + 1) a ∘ₗ
      K.cechDifferentialDegree R (q := q) a = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change K.cechDifferential R (q + 1) (K.cechDifferential R q x) = 0
  exact LinearMap.congr_fun (K.cechDifferential_comp_eq_zero R (q := q))
    (x : K.CechCochain R q)

/-- The actual subcomplex of the Čech complex in one fine integer degree. -/
noncomputable def cechComplexDegree (a : V →₀ ℤ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R (K.cechDegreeSubmodule R q a))
    (fun q => ModuleCat.ofHom (K.cechDifferentialDegree R (q := q) a))
    (fun q => by
      rw [← ModuleCat.ofHom_comp, K.cechDifferentialDegree_comp_eq_zero,
        ModuleCat.ofHom_zero])

@[simp]
theorem cechComplexDegree_d (a : V →₀ ℤ) (q : ℕ) :
    (K.cechComplexDegree R a).d q (q + 1) =
      ModuleCat.ofHom (K.cechDifferentialDegree R (q := q) a) := by
  apply CochainComplex.of_d

/-- Inclusion of the homogeneous subcomplex in the full Čech complex. -/
noncomputable def cechDegreeInclusion (a : V →₀ ℤ) :
    K.cechComplexDegree R a ⟶ K.cechComplex R :=
  CochainComplex.ofHom
    (fun q => ModuleCat.ofHom (K.cechDegreeSubmodule R q a).subtype)
    (fun q => by
      rw [K.cechComplex_d, K.cechComplexDegree_d]
      rfl)

/-- Projection from the Čech complex to one homogeneous subcomplex. -/
noncomputable def cechDegreeProjection (a : V →₀ ℤ) :
    K.cechComplex R ⟶ K.cechComplexDegree R a :=
  CochainComplex.ofHom
    (fun q => ModuleCat.ofHom (K.cechHomogeneousComponent R q a))
    (fun q => by
      rw [K.cechComplex_d, K.cechComplexDegree_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (K.cechHomogeneousComponent_differential R a z).symm)

/-- Each degree projection is a retraction of the corresponding inclusion. -/
@[simp]
theorem cechDegreeInclusion_projection (a : V →₀ ℤ) :
    K.cechDegreeInclusion R a ≫ K.cechDegreeProjection R a =
      𝟙 (K.cechComplexDegree R a) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact K.cechHomogeneousComponent_eq_self R z

/-- Projection to a different degree annihilates a homogeneous subcomplex. -/
theorem cechDegreeInclusion_projection_of_ne {a b : V →₀ ℤ} (h : a ≠ b) :
    K.cechDegreeInclusion R b ≫ K.cechDegreeProjection R a = 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact K.cechHomogeneousComponent_eq_zero_of_ne R h z

/-- Čech cohomology in one fine degree is the homology of the actual degree
subcomplex. -/
noncomputable abbrev cechCohomologyDegree (q : ℕ) (a : V →₀ ℤ) :=
  (K.cechComplexDegree R a).homology q

/-- The canonical cohomology map induced by inclusions of the homogeneous
subcomplexes, assembled using the direct sum universal property. -/
noncomputable def cechCohomologyAssembly (q : ℕ) :
    (⨁ a : V →₀ ℤ, K.cechCohomologyDegree R q a) →ₗ[R]
      (K.cechComplex R).homology q :=
  DirectSum.toModule R (V →₀ ℤ) ((K.cechComplex R).homology q)
    (fun a => (HomologicalComplex.homologyMap (K.cechDegreeInclusion R a) q).hom)

@[simp]
theorem cechCohomologyAssembly_lof (q : ℕ) (a : V →₀ ℤ)
    (x : K.cechCohomologyDegree R q a) :
    K.cechCohomologyAssembly R q (DirectSum.lof R _ _ a x) =
      HomologicalComplex.homologyMap (K.cechDegreeInclusion R a) q x :=
  DirectSum.toModule_lof R
    (M := fun b => K.cechCohomologyDegree R q b)
    (φ := fun b => (HomologicalComplex.homologyMap (K.cechDegreeInclusion R b) q).hom) a x

/-- The induced projection on cohomology extracts the corresponding direct
sum coordinate after assembly. -/
theorem cechCohomologyProjection_assembly (q : ℕ) (a : V →₀ ℤ) :
    (HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q).hom ∘ₗ
      K.cechCohomologyAssembly R q =
        DirectSum.component R (V →₀ ℤ) (fun b => K.cechCohomologyDegree R q b) a := by
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  change HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q
    (K.cechCohomologyAssembly R q (DirectSum.lof R _ _ b x)) = _
  rw [K.cechCohomologyAssembly_lof]
  change (HomologicalComplex.homologyMap (K.cechDegreeInclusion R b) q ≫
    HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q) x = _
  rw [← HomologicalComplex.homologyMap_comp]
  by_cases h : a = b
  · subst b
    rw [K.cechDegreeInclusion_projection, HomologicalComplex.homologyMap_id]
    simp
  · rw [K.cechDegreeInclusion_projection_of_ne R h, HomologicalComplex.homologyMap_zero]
    simp [DirectSum.component.of, Ne.symm h]

theorem cechCohomologyAssembly_injective (q : ℕ) :
    Function.Injective (K.cechCohomologyAssembly R q) := by
  intro x y h
  apply DFinsupp.ext
  intro a
  have he := congrArg (HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q) h
  change ((HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q).hom ∘ₗ
    K.cechCohomologyAssembly R q) x =
      ((HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q).hom ∘ₗ
        K.cechCohomologyAssembly R q) y at he
  rw [K.cechCohomologyProjection_assembly R q a] at he
  exact he

open scoped Classical in
private theorem cechCycles_sum_components (q : ℕ)
    (z : (K.cechComplex R).cycles q) :
    ∑ a ∈ (K.cechDecomposeLinearEquiv R q ((K.cechComplex R).iCycles q z)).support,
      HomologicalComplex.cyclesMap (K.cechDegreeInclusion R a) q
        (HomologicalComplex.cyclesMap (K.cechDegreeProjection R a) q z) = z := by
  classical
  apply (ModuleCat.mono_iff_injective ((K.cechComplex R).iCycles q)).mp inferInstance
  rw [map_sum]
  have hcomponent (a : V →₀ ℤ) :
      (K.cechComplex R).iCycles q
          (HomologicalComplex.cyclesMap (K.cechDegreeInclusion R a) q
            (HomologicalComplex.cyclesMap (K.cechDegreeProjection R a) q z)) =
        (K.cechHomogeneousComponent R q a ((K.cechComplex R).iCycles q z) :
          K.CechCochain R q) := by
    have hi := CategoryTheory.congr_fun
      (HomologicalComplex.cyclesMap_i (K.cechDegreeInclusion R a) q)
        (HomologicalComplex.cyclesMap (K.cechDegreeProjection R a) q z)
    have hp := CategoryTheory.congr_fun
      (HomologicalComplex.cyclesMap_i (K.cechDegreeProjection R a) q) z
    change _ = ((K.cechDegreeInclusion R a).f q)
      (((K.cechDegreeProjection R a).f q) ((K.cechComplex R).iCycles q z))
    simpa only [ModuleCat.comp_apply] using hi.trans
      (congrArg ((K.cechDegreeInclusion R a).f q) hp)
  change (∑ a ∈ (K.cechDecomposeLinearEquiv R q
      ((K.cechComplex R).iCycles q z)).support,
    ((K.cechComplex R).iCycles q
      (HomologicalComplex.cyclesMap (K.cechDegreeInclusion R a) q
        (HomologicalComplex.cyclesMap (K.cechDegreeProjection R a) q z)) :
          K.CechCochain R q)) =
    ((K.cechComplex R).iCycles q z : K.CechCochain R q)
  have hsum := Finset.sum_congr
    (s₁ := (K.cechDecomposeLinearEquiv R q ((K.cechComplex R).iCycles q z)).support)
    (s₂ := (K.cechDecomposeLinearEquiv R q ((K.cechComplex R).iCycles q z)).support)
    rfl (fun a _ => hcomponent a)
  exact hsum.trans
    (K.cechHomogeneousComponent_sum_support R q ((K.cechComplex R).iCycles q z))

/-- Every cohomology class has a finite decomposition obtained by projecting
a cycle representative to its finitely many nonzero fine degrees. -/
theorem cechCohomologyAssembly_surjective (q : ℕ) :
    Function.Surjective (K.cechCohomologyAssembly R q) := by
  classical
  intro x
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((K.cechComplex R).homologyπ q)).mp inferInstance x
  let s := (K.cechDecomposeLinearEquiv R q ((K.cechComplex R).iCycles q z)).support
  refine ⟨∑ a ∈ s, DirectSum.lof R _ _ a
    (HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q
      ((K.cechComplex R).homologyπ q z)), ?_⟩
  simp only [map_sum, K.cechCohomologyAssembly_lof]
  have h := congrArg ((K.cechComplex R).homologyπ q) (K.cechCycles_sum_components R q z)
  rw [map_sum] at h
  have hcomponent (a : V →₀ ℤ) :
      HomologicalComplex.homologyMap (K.cechDegreeInclusion R a) q
          (HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q
            ((K.cechComplex R).homologyπ q z)) =
        (K.cechComplex R).homologyπ q
          (HomologicalComplex.cyclesMap (K.cechDegreeInclusion R a) q
            (HomologicalComplex.cyclesMap (K.cechDegreeProjection R a) q z)) := by
    have hp := CategoryTheory.congr_fun
      (HomologicalComplex.homologyπ_naturality (K.cechDegreeProjection R a) q) z
    have hi := CategoryTheory.congr_fun
      (HomologicalComplex.homologyπ_naturality (K.cechDegreeInclusion R a) q)
        (HomologicalComplex.cyclesMap (K.cechDegreeProjection R a) q z)
    simpa only [ModuleCat.comp_apply] using
      (congrArg (HomologicalComplex.homologyMap (K.cechDegreeInclusion R a) q) hp).trans hi
  simp_rw [hcomponent]
  exact h

theorem cechCohomologyAssembly_bijective (q : ℕ) :
    Function.Bijective (K.cechCohomologyAssembly R q) :=
  ⟨K.cechCohomologyAssembly_injective R q, K.cechCohomologyAssembly_surjective R q⟩

/-- The canonical direct-sum decomposition of actual Čech cohomology. -/
noncomputable def cechCohomologyDecomposition (q : ℕ) :
    (⨁ a : V →₀ ℤ, K.cechCohomologyDegree R q a) ≃ₗ[R]
      (K.cechComplex R).homology q :=
  LinearEquiv.ofBijective (K.cechCohomologyAssembly R q)
    (K.cechCohomologyAssembly_bijective R q)

@[simp]
theorem cechCohomologyDecomposition_lof (q : ℕ) (a : V →₀ ℤ)
    (x : K.cechCohomologyDegree R q a) :
    K.cechCohomologyDecomposition R q (DirectSum.lof R _ _ a x) =
      HomologicalComplex.homologyMap (K.cechDegreeInclusion R a) q x :=
  K.cechCohomologyAssembly_lof R q a x

/-- The inverse decomposition has the cohomology classes of homogeneous
cycle projections as its coordinates. -/
theorem cechCohomologyDecomposition_symm_apply (q : ℕ)
    (x : (K.cechComplex R).homology q) (a : V →₀ ℤ) :
    (K.cechCohomologyDecomposition R q).symm x a =
      HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q x := by
  have h := LinearMap.congr_fun (K.cechCohomologyProjection_assembly R q a)
    ((K.cechCohomologyDecomposition R q).symm x)
  change HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q
    (K.cechCohomologyDecomposition R q
      ((K.cechCohomologyDecomposition R q).symm x)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

open scoped Classical in
/-- The inverse has no degrees outside the finite support of any chosen
cycle representative of the cohomology class. -/
theorem cechCohomologyDecomposition_support_subset (q : ℕ)
    (z : (K.cechComplex R).cycles q) :
    ((K.cechCohomologyDecomposition R q).symm
        ((K.cechComplex R).homologyπ q z)).support ⊆
      (K.cechDecomposeLinearEquiv R q ((K.cechComplex R).iCycles q z)).support := by
  classical
  intro a ha
  by_contra hnot
  have hp : K.cechHomogeneousComponent R q a ((K.cechComplex R).iCycles q z) = 0 :=
    DFinsupp.notMem_support_iff.mp hnot
  have hc : HomologicalComplex.cyclesMap (K.cechDegreeProjection R a) q z = 0 := by
    apply (ModuleCat.mono_iff_injective ((K.cechComplexDegree R a).iCycles q)).mp
      inferInstance
    rw [map_zero]
    have h := CategoryTheory.congr_fun
      (HomologicalComplex.cyclesMap_i (K.cechDegreeProjection R a) q) z
    exact h.trans hp
  have hh : HomologicalComplex.homologyMap (K.cechDegreeProjection R a) q
      ((K.cechComplex R).homologyπ q z) = 0 := by
    have h := CategoryTheory.congr_fun
      (HomologicalComplex.homologyπ_naturality (K.cechDegreeProjection R a) q) z
    simpa only [ModuleCat.comp_apply, hc, map_zero] using h
  exact (DFinsupp.mem_support_iff.mp ha)
    ((K.cechCohomologyDecomposition_symm_apply R q _ a).trans hh)

/-- The actual homology object is the usual kernel modulo the incoming
boundary image, through mathlib's standard module-category comparison. -/
noncomputable def cechCohomologyQuotientEquiv (q : ℕ) :
    (K.cechComplex R).homology q ≃ₗ[R]
      ((K.cechComplex R).sc q).g.hom.ker ⧸
        ((K.cechComplex R).sc q).moduleCatToCycles.range :=
  ((K.cechComplex R).sc q).moduleCatHomologyIso.toLinearEquiv

/-- The same standard cycles/boundaries quotient for each degree complex. -/
noncomputable def cechCohomologyDegreeQuotientEquiv (q : ℕ) (a : V →₀ ℤ) :
    K.cechCohomologyDegree R q a ≃ₗ[R]
      ((K.cechComplexDegree R a).sc q).g.hom.ker ⧸
        ((K.cechComplexDegree R a).sc q).moduleCatToCycles.range :=
  ((K.cechComplexDegree R a).sc q).moduleCatHomologyIso.toLinearEquiv

/-- The short-complex quotient uses exactly the checked outgoing Čech map. -/
theorem cechCohomology_outgoing (q : ℕ) :
    HEq ((K.cechComplex R).sc q).g.hom (K.cechDifferential R q) := by
  have hn : (ComplexShape.up ℕ).next q = q + 1 :=
    (ComplexShape.up ℕ).next_eq' (by simp [ComplexShape.up_Rel])
  change HEq ((K.cechComplex R).d q ((ComplexShape.up ℕ).next q)).hom _
  rw [hn, K.cechComplex_d]
  rfl

/-- In positive cohomological degree the incoming map is precisely the
previous checked Čech differential. -/
theorem cechCohomology_incoming (q : ℕ) :
    HEq ((K.cechComplex R).sc (q + 1)).f.hom (K.cechDifferential R q) := by
  have hp : (ComplexShape.up ℕ).prev (q + 1) = q :=
    (ComplexShape.up ℕ).prev_eq' (by simp [ComplexShape.up_Rel])
  change HEq ((K.cechComplex R).d ((ComplexShape.up ℕ).prev (q + 1)) (q + 1)).hom _
  rw [hp, K.cechComplex_d]
  rfl

/-- The degreewise quotient uses the actual restricted outgoing map. -/
theorem cechCohomologyDegree_outgoing (q : ℕ) (a : V →₀ ℤ) :
    HEq ((K.cechComplexDegree R a).sc q).g.hom
      (K.cechDifferentialDegree R (q := q) a) := by
  have hn : (ComplexShape.up ℕ).next q = q + 1 :=
    (ComplexShape.up ℕ).next_eq' (by simp [ComplexShape.up_Rel])
  change HEq ((K.cechComplexDegree R a).d q ((ComplexShape.up ℕ).next q)).hom _
  rw [hn, K.cechComplexDegree_d]
  rfl

/-- The degreewise quotient uses the restricted incoming map in positive
cohomological degrees. -/
theorem cechCohomologyDegree_incoming (q : ℕ) (a : V →₀ ℤ) :
    HEq ((K.cechComplexDegree R a).sc (q + 1)).f.hom
      (K.cechDifferentialDegree R (q := q) a) := by
  have hp : (ComplexShape.up ℕ).prev (q + 1) = q :=
    (ComplexShape.up ℕ).prev_eq' (by simp [ComplexShape.up_Rel])
  change HEq ((K.cechComplexDegree R a).d ((ComplexShape.up ℕ).prev (q + 1)) (q + 1)).hom _
  rw [hp, K.cechComplexDegree_d]
  rfl

/-- The standard quotient comparison sends the homology class of a cycle to
the quotient class of its kernel representative. -/
theorem cechCohomologyQuotientEquiv_homologyπ (q : ℕ) :
    (K.cechCohomologyQuotientEquiv R q).toLinearMap ∘ₗ
      ((K.cechComplex R).homologyπ q).hom =
        ((K.cechComplex R).sc q).moduleCatToCycles.range.mkQ ∘ₗ
          (((K.cechComplex R).sc q).moduleCatCyclesIso.hom).hom :=
  congrArg ModuleCat.Hom.hom (((K.cechComplex R).sc q).π_moduleCatCyclesIso_hom)

/-- Compatibility of homogeneous cycle classes with the standard quotient
description of each degree's cohomology. -/
theorem cechCohomologyDegreeQuotientEquiv_homologyπ (q : ℕ) (a : V →₀ ℤ) :
    (K.cechCohomologyDegreeQuotientEquiv R q a).toLinearMap ∘ₗ
      ((K.cechComplexDegree R a).homologyπ q).hom =
        ((K.cechComplexDegree R a).sc q).moduleCatToCycles.range.mkQ ∘ₗ
          (((K.cechComplexDegree R a).sc q).moduleCatCyclesIso.hom).hom :=
  congrArg ModuleCat.Hom.hom (((K.cechComplexDegree R a).sc q).π_moduleCatCyclesIso_hom)

omit [Fintype V] [LinearOrder V] in
private theorem cechBoundaryZero (C : CochainComplex (ModuleCat.{max u v} R) ℕ) :
    (C.sc 0).moduleCatToCycles.range = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  ext x
  change (C.d _ 0) x = 0
  have h (i : ℕ) : C.d i 0 = 0 := C.shape _ _ (by simp [ComplexShape.up_Rel])
  rw [h]
  rfl

/-- Cohomological degree zero has zero incoming boundaries. -/
theorem cechCohomology_boundaries_zero :
    ((K.cechComplex R).sc 0).moduleCatToCycles.range = ⊥ :=
  cechBoundaryZero R (K.cechComplex R)

/-- The degreewise complex also has zero incoming boundaries in degree zero. -/
theorem cechCohomologyDegree_boundaries_zero (a : V →₀ ℤ) :
    ((K.cechComplexDegree R a).sc 0).moduleCatToCycles.range = ⊥ :=
  cechBoundaryZero R (K.cechComplexDegree R a)

/-- Each coordinate monomial cochain belongs to its actual fine-degree
submodule, including when the monomial is zero. -/
theorem cechMonomialCochain_mem_degree {q : ℕ} (F : CechIndex V q) (a : V →₀ ℤ) :
    K.cechMonomialCochain R F a ∈ K.cechDegreeSubmodule R q a := by
  rw [K.mem_cechDegreeSubmodule]
  intro G
  by_cases h : G = F
  · subst G
    rw [K.cechMonomialCochain_apply_self]
    exact Submodule.subset_span (Set.mem_singleton _)
  · rw [K.cechMonomialCochain_apply_of_ne R F G a h]
    exact Submodule.zero_mem _

/-- A coordinate monomial as an element of the degree submodule. -/
noncomputable def cechMonomialCochainDegree {q : ℕ} (F : CechIndex V q) (a : V →₀ ℤ) :
    K.cechDegreeSubmodule R q a :=
  ⟨K.cechMonomialCochain R F a, K.cechMonomialCochain_mem_degree R F a⟩

theorem cechCochainMonomialBasis_apply {q : ℕ} (F : CechIndex V q) (a : V →₀ ℤ)
    (ha : K.LocalizationAdmissible F.1 a) :
    K.cechCochainMonomialBasis R q ⟨F, ⟨a, ha⟩⟩ = K.cechMonomialCochain R F a := by
  classical
  rw [cechCochainMonomialBasis, Pi.basis_apply, K.localizationMonomialBasis_apply]
  funext G
  by_cases h : G = F
  · subst G
    simp [cechMonomialCochain]
  · simp [cechMonomialCochain, h]

theorem cechMonomialCochainDegree_eq_zero {q : ℕ} (F : CechIndex V q) (a : V →₀ ℤ)
    (ha : ¬ K.LocalizationAdmissible F.1 a) :
    K.cechMonomialCochainDegree R F a = 0 := by
  apply Subtype.ext
  funext G
  by_cases h : G = F
  · subst G
    simp [cechMonomialCochainDegree, cechMonomialCochain,
      K.localizationMonomial_eq_zero_of_not_admissible R F.1 a ha]
  · simp [cechMonomialCochainDegree, cechMonomialCochain, h]

/-- Linear maps on a degree submodule are determined by its admissible
coordinate monomials. This uses the full localization basis over `R`. -/
theorem cechDegree_linearMap_ext {q : ℕ} (a : V →₀ ℤ)
    {N : Type*} [AddCommGroup N] [Module R N]
    {f g : K.cechDegreeSubmodule R q a →ₗ[R] N}
    (h : ∀ (F : CechIndex V q), K.LocalizationAdmissible F.1 a →
      f (K.cechMonomialCochainDegree R F a) = g (K.cechMonomialCochainDegree R F a)) :
    f = g := by
  have he : f ∘ₗ K.cechHomogeneousComponent R q a =
      g ∘ₗ K.cechHomogeneousComponent R q a := by
    apply (K.cechCochainMonomialBasis R q).ext
    intro i
    rcases i with ⟨F, b⟩
    rw [K.cechCochainMonomialBasis_apply R F b.1 b.2]
    change f (K.cechHomogeneousComponent R q a
      (K.cechMonomialCochainDegree R F b.1)) =
      g (K.cechHomogeneousComponent R q a (K.cechMonomialCochainDegree R F b.1))
    by_cases hb : a = b.1
    · subst a
      rw [K.cechHomogeneousComponent_eq_self]
      exact h F b.2
    · rw [K.cechHomogeneousComponent_eq_zero_of_ne R hb, map_zero, map_zero]
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun he (z : K.CechCochain R q)
  change f (K.cechHomogeneousComponent R q a z) = g (K.cechHomogeneousComponent R q a z) at hz
  simpa only [K.cechHomogeneousComponent_eq_self] using hz

/-- The checked monomial differential, now in the actual degree submodule. -/
theorem cechDifferentialDegree_monomial {q : ℕ} (F : CechIndex V q) (a : V →₀ ℤ)
    (ha : K.LocalizationAdmissible F.1 a) :
    K.cechDifferentialDegree R a (K.cechMonomialCochainDegree R F a) =
      ∑ v : {v : V // v ∉ F.1}, (-1 : R) ^ cechRankBelow F.1 v.1 •
        K.cechMonomialCochainDegree R (cechInsertIndex F v.1 v.2) a := by
  apply Subtype.ext
  change K.cechDifferential R q (K.cechMonomialCochain R F a) = _
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
    cechMonomialCochainDegree] using K.cechDifferential_monomialCochain R F a ha

end Reisner.Complex
