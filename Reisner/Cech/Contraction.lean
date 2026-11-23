module

public import Reisner.Cech.Grading

@[expose] public section

namespace Reisner.Complex

open DirectSum
open scoped Classical
open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (K : Reisner.Complex V) (R : Type v) [CommRing R]

/-- Linear extension of signed deletion, evaluated on the full product
Laurent basis and taking values in the actual target degree submodule. -/
noncomputable def cechContractionAux (a : V →₀ ℤ) (p : V) (q : ℕ) :
    K.CechCochain R (q + 1) →ₗ[R] K.cechDegreeSubmodule R q a :=
  (K.cechCochainMonomialBasis R (q + 1)).constr R fun i =>
    if i.2.1 = a then
      if hp : p ∈ i.1.1 then
        (-1 : R) ^ cechRankBelow i.1.1 p •
          K.cechMonomialCochainDegree R (cechEraseIndex i.1 ⟨p, hp⟩) a
      else 0
    else 0

/-- The signed degree-lowering operator on a homogeneous Čech complex. -/
noncomputable def cechPositiveContraction (a : V →₀ ℤ) (p : V) (q : ℕ) :
    K.cechDegreeSubmodule R (q + 1) a →ₗ[R] K.cechDegreeSubmodule R q a :=
  K.cechContractionAux R a p q ∘ₗ (K.cechDegreeSubmodule R (q + 1) a).subtype

theorem cechPositiveContraction_monomial_of_admissible {q : ℕ}
    (F : CechIndex V (q + 1)) (a : V →₀ ℤ) (p : V)
    (ha : K.LocalizationAdmissible F.1 a) :
    K.cechPositiveContraction R a p q (K.cechMonomialCochainDegree R F a) =
      if hp : p ∈ F.1 then (-1 : R) ^ cechRankBelow F.1 p •
        K.cechMonomialCochainDegree R (cechEraseIndex F ⟨p, hp⟩) a else 0 := by
  change K.cechContractionAux R a p q (K.cechMonomialCochain R F a) = _
  rw [← K.cechCochainMonomialBasis_apply R F a ha]
  simp [cechContractionAux, Module.Basis.constr_basis]

theorem cechPositiveContraction_monomial_of_not_mem {q : ℕ}
    (F : CechIndex V (q + 1)) (a : V →₀ ℤ) (p : V) (hp : p ∉ F.1) :
    K.cechPositiveContraction R a p q (K.cechMonomialCochainDegree R F a) = 0 := by
  by_cases ha : K.LocalizationAdmissible F.1 a
  · rw [K.cechPositiveContraction_monomial_of_admissible R F a p ha]
    simp [hp]
  · rw [K.cechMonomialCochainDegree_eq_zero R F a ha, map_zero]

/-- The adjacent components of signed deletion as categorical morphisms. -/
noncomputable def cechContractionFamily (a : V →₀ ℤ) (p : V) :
    ∀ i j, (ComplexShape.up ℕ).Rel j i →
      ((K.cechComplexDegree R a).X i ⟶ (K.cechComplexDegree R a).X j) := by
  intro i j h
  change j + 1 = i at h
  subst i
  exact ModuleCat.ofHom (K.cechPositiveContraction R a p j)

/-- The canonical chain map `dh + hd`; its commutation law follows from
the already checked square-zero identity. -/
noncomputable def cechContractionMap (a : V →₀ ℤ) (p : V) :
    K.cechComplexDegree R a ⟶ K.cechComplexDegree R a :=
  Homotopy.nullHomotopicMap' (K.cechContractionFamily R a p)

theorem cechContractionMap_f_zero (a : V →₀ ℤ) (p : V) :
    ((K.cechContractionMap R a p).f 0).hom =
      K.cechPositiveContraction R a p 0 ∘ₗ K.cechDifferentialDegree R (q := 0) a := by
  dsimp only [cechContractionMap, Homotopy.nullHomotopicMap', Homotopy.nullHomotopicMap]
  rw [Homotopy.prevD_zero_cochainComplex, add_zero, Homotopy.dNext_cochainComplex]
  simp [cechContractionFamily, ComplexShape.up_Rel]
  rfl

theorem cechContractionMap_f_succ (a : V →₀ ℤ) (p : V) (q : ℕ) :
    ((K.cechContractionMap R a p).f (q + 1)).hom =
      K.cechPositiveContraction R a p (q + 1) ∘ₗ
        K.cechDifferentialDegree R (q := q + 1) a +
      K.cechDifferentialDegree R (q := q) a ∘ₗ K.cechPositiveContraction R a p q := by
  dsimp only [cechContractionMap, Homotopy.nullHomotopicMap', Homotopy.nullHomotopicMap]
  rw [Homotopy.prevD_succ_cochainComplex, Homotopy.dNext_cochainComplex]
  simp [cechContractionFamily, ComplexShape.up_Rel]
  rfl

omit [Fintype V] in
/-- The two deletion/insertion orders have opposite signs. This identity
holds over every coefficient ring, including characteristic two. -/
theorem cechContraction_sign_cancel (F : Finset V) {p v : V}
    (hp : p ∈ F) (hv : v ∉ F) :
    ((-1 : R) ^ cechRankBelow F p) * (-1) ^ cechRankBelow (F.erase p) v =
      - ((-1 : R) ^ cechRankBelow F v * (-1) ^ cechRankBelow (insert v F) p) := by
  have hne : p ≠ v := fun e => hv (e ▸ hp)
  rcases lt_or_gt_of_ne hne with h | h
  · have hi : cechRankBelow (insert v F) p = cechRankBelow F p := by
      simpa [hv] using (cechRankEraseOfNotLt (insert v F) (not_lt.mpr h.le)).symm
    rw [hi, ← cechRankEraseOfLt F hp h, pow_succ]
    ring
  · have hi : cechRankBelow F p + 1 = cechRankBelow (insert v F) p := by
      simpa [hv] using cechRankEraseOfLt (insert v F) (Finset.mem_insert_self v F) h
    rw [← hi, cechRankEraseOfNotLt F (not_lt.mpr h.le), pow_succ]
    ring

omit [Fintype V] in
theorem localizationAdmissible_insert_positive (F : Finset V) (a : V →₀ ℤ)
    (p : V) (hp : 0 < a p) :
    K.LocalizationAdmissible (insert p F) a ↔ K.LocalizationAdmissible F a := by
  have hpP : p ∈ positiveSupport a :=
    Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (ne_of_gt hp), hp⟩
  let G : Finset V := insert p F
  have hu : (letI : DecidableEq V := Classical.decEq V
      G ∪ positiveSupport a = F ∪ positiveSupport a) := by
    ext v
    simp only [@Finset.mem_union V (Classical.decEq V), G, Finset.mem_insert]
    constructor
    · rintro ((hvp | hf) | hvP)
      · subst v
        exact Or.inr hpP
      · exact Or.inl hf
      · exact Or.inr hvP
    · rintro (hf | hvP)
      · exact Or.inl (Or.inr hf)
      · exact Or.inr hvP
  constructor
  · rintro ⟨hb, hf⟩
    constructor
    · intro v hv
      by_cases hvp : v = p
      · subst v
        exact hp.le
      · exact hb v (by simp [hv, hvp])
    · rw [hu] at hf
      exact hf
  · rintro ⟨hb, hf⟩
    constructor
    · intro v hv
      exact hb v (fun hvF => hv (Finset.mem_insert_of_mem hvF))
    · rw [← hu] at hf
      exact hf

omit [Fintype V] in
theorem localizationAdmissible_erase_positive (F : Finset V) (a : V →₀ ℤ)
    (p : V) (hp : 0 < a p) :
    K.LocalizationAdmissible (F.erase p) a ↔ K.LocalizationAdmissible F a := by
  by_cases hpF : p ∈ F
  · have h := (K.localizationAdmissible_insert_positive (F.erase p) a p hp).symm
    simpa only [Finset.insert_erase hpF] using h
  · rw [Finset.erase_eq_of_notMem hpF]

/-- The deletion formula also holds at inadmissible coordinates: positivity
makes source and deleted degrees simultaneously admissible or zero. -/
theorem cechPositiveContraction_monomial {q : ℕ} (F : CechIndex V (q + 1))
    (a : V →₀ ℤ) (p : V) (hp : 0 < a p) :
    K.cechPositiveContraction R a p q (K.cechMonomialCochainDegree R F a) =
      if hpF : p ∈ F.1 then (-1 : R) ^ cechRankBelow F.1 p •
        K.cechMonomialCochainDegree R (cechEraseIndex F ⟨p, hpF⟩) a else 0 := by
  by_cases ha : K.LocalizationAdmissible F.1 a
  · exact K.cechPositiveContraction_monomial_of_admissible R F a p ha
  · rw [K.cechMonomialCochainDegree_eq_zero R F a ha, map_zero]
    split_ifs with hpF
    · have he : ¬ K.LocalizationAdmissible (F.1.erase p) a :=
        fun h => ha ((K.localizationAdmissible_erase_positive F.1 a p hp).mp h)
      rw [K.cechMonomialCochainDegree_eq_zero R _ a he, smul_zero]
    · rfl

private theorem cechContraction_hd_monomial {q : ℕ} (F : CechIndex V q)
    (a : V →₀ ℤ) (p : V) (hp : 0 < a p) (hpF : p ∉ F.1)
    (ha : K.LocalizationAdmissible F.1 a) :
    K.cechPositiveContraction R a p q
      (K.cechDifferentialDegree R a (K.cechMonomialCochainDegree R F a)) =
        K.cechMonomialCochainDegree R F a := by
  classical
  rw [K.cechDifferentialDegree_monomial R F a ha]
  simp only [map_sum, map_smul]
  rw [Finset.sum_eq_single (⟨p, hpF⟩ : {v : V // v ∉ F.1})]
  · rw [K.cechPositiveContraction_monomial R _ a p hp]
    rw [dite_eq_left (Finset.mem_insert_self p F.1)]
    have he : cechEraseIndex (cechInsertIndex F p hpF)
        ⟨p, Finset.mem_insert_self p F.1⟩ = F := by
      apply Subtype.ext
      exact Finset.erase_insert hpF
    have hr : cechRankBelow (insert p F.1) p = cechRankBelow F.1 p := by
      simp [cechRankBelow, Finset.filter_insert]
    rw [he, hr, smul_smul, ← mul_pow]
    simp
  · intro v hv hne
    have hvp : v.1 ≠ p := fun h => hne (Subtype.ext h)
    have hn : p ∉ (cechInsertIndex F v.1 v.2).1 := by
      simp [hpF, Ne.symm hvp]
    rw [K.cechPositiveContraction_monomial_of_not_mem R _ a p hn, smul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private noncomputable def cechContractionMapLinear (a : V →₀ ℤ) (p : V) (q : ℕ) :
    K.cechDegreeSubmodule R q a →ₗ[R] K.cechDegreeSubmodule R q a :=
  ((K.cechContractionMap R a p).f q).hom

private theorem cechContractionMapLinear_zero (a : V →₀ ℤ) (p : V) :
    K.cechContractionMapLinear R a p 0 =
      K.cechPositiveContraction R a p 0 ∘ₗ K.cechDifferentialDegree R (q := 0) a :=
  K.cechContractionMap_f_zero R a p

private theorem cechContractionMapLinear_succ (a : V →₀ ℤ) (p : V) (q : ℕ) :
    K.cechContractionMapLinear R a p (q + 1) =
      K.cechPositiveContraction R a p (q + 1) ∘ₗ
        K.cechDifferentialDegree R (q := q + 1) a +
      K.cechDifferentialDegree R (q := q) a ∘ₗ K.cechPositiveContraction R a p q :=
  K.cechContractionMap_f_succ R a p q

private theorem cechContractionMapLinear_comm (a : V →₀ ℤ) (p : V) (q : ℕ) :
    K.cechDifferentialDegree R (q := q) a ∘ₗ K.cechContractionMapLinear R a p q =
      K.cechContractionMapLinear R a p (q + 1) ∘ₗ K.cechDifferentialDegree R (q := q) a := by
  have h := congrArg ModuleCat.Hom.hom ((K.cechContractionMap R a p).comm q (q + 1))
  rw [K.cechComplexDegree_d] at h
  exact h

private theorem cechContractionMap_monomial_of_not_mem {q : ℕ} (F : CechIndex V q)
    (a : V →₀ ℤ) (p : V) (hp : 0 < a p) (hpF : p ∉ F.1) :
    K.cechContractionMapLinear R a p q (K.cechMonomialCochainDegree R F a) =
      K.cechMonomialCochainDegree R F a := by
  by_cases ha : K.LocalizationAdmissible F.1 a
  · cases q with
    | zero =>
      rw [K.cechContractionMapLinear_zero]
      exact K.cechContraction_hd_monomial R F a p hp hpF ha
    | succ q =>
      rw [K.cechContractionMapLinear_succ, LinearMap.add_apply, LinearMap.comp_apply,
        K.cechContraction_hd_monomial R F a p hp hpF ha,
        LinearMap.comp_apply, K.cechPositiveContraction_monomial_of_not_mem R F a p hpF,
        map_zero, add_zero]
  · rw [K.cechMonomialCochainDegree_eq_zero R F a ha, map_zero]

private theorem cechContractionMap_monomial {q : ℕ} (F : CechIndex V q)
    (a : V →₀ ℤ) (p : V) (hp : 0 < a p) (ha : K.LocalizationAdmissible F.1 a) :
    K.cechContractionMapLinear R a p q (K.cechMonomialCochainDegree R F a) =
      K.cechMonomialCochainDegree R F a := by
  classical
  by_cases hpF : p ∉ F.1
  · exact K.cechContractionMap_monomial_of_not_mem R F a p hp hpF
  have hpF : p ∈ F.1 := not_not.mp hpF
  cases q with
  | zero =>
    have he := Finset.card_eq_zero.mp F.2
    exact False.elim ((Finset.notMem_empty p) (he ▸ hpF))
  | succ q =>
    let E : CechIndex V q := cechEraseIndex F ⟨p, hpF⟩
    have hpE : p ∉ E.1 := Finset.notMem_erase _ _
    have hEa : K.LocalizationAdmissible E.1 a :=
      (K.localizationAdmissible_erase_positive F.1 a p hp).mpr ha
    let Δ (n : ℕ) : K.cechDegreeSubmodule R n a →ₗ[R] K.cechDegreeSubmodule R n a :=
      K.cechContractionMapLinear R a p n - LinearMap.id
    have hkill (n : ℕ) (G : CechIndex V n) (hn : p ∉ G.1) :
        Δ n (K.cechMonomialCochainDegree R G a) = 0 := by
      change K.cechContractionMapLinear R a p n (K.cechMonomialCochainDegree R G a) -
        K.cechMonomialCochainDegree R G a = 0
      rw [K.cechContractionMap_monomial_of_not_mem R G a p hp hn, sub_self]
    have hdcomm : K.cechDifferentialDegree R (q := q) a ∘ₗ Δ q =
        Δ (q + 1) ∘ₗ K.cechDifferentialDegree R (q := q) a := by
      dsimp only [Δ]
      rw [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id, LinearMap.id_comp,
        K.cechContractionMapLinear_comm]
    have hd : Δ (q + 1)
        (K.cechDifferentialDegree R a (K.cechMonomialCochainDegree R E a)) = 0 := by
      have hc := LinearMap.congr_fun hdcomm
        (K.cechMonomialCochainDegree R E a)
      change K.cechDifferentialDegree R a (Δ q (K.cechMonomialCochainDegree R E a)) =
        Δ (q + 1) (K.cechDifferentialDegree R a (K.cechMonomialCochainDegree R E a)) at hc
      rw [hkill q E hpE, map_zero] at hc
      exact hc.symm
    rw [K.cechDifferentialDegree_monomial R E a hEa] at hd
    simp only [map_sum, map_smul] at hd
    have hs : (∑ v : {v : V // v ∉ E.1}, (-1 : R) ^ cechRankBelow E.1 v.1 •
        Δ (q + 1) (K.cechMonomialCochainDegree R (cechInsertIndex E v.1 v.2) a)) =
        (-1 : R) ^ cechRankBelow E.1 p •
          Δ (q + 1) (K.cechMonomialCochainDegree R F a) := by
      rw [Finset.sum_eq_single (⟨p, hpE⟩ : {v : V // v ∉ E.1})]
      · have hi : cechInsertIndex E p hpE = F := by
          apply Subtype.ext
          exact Finset.insert_erase hpF
        rw [hi]
      · intro v hv hne
        have hvp : v.1 ≠ p := fun h => hne (Subtype.ext h)
        have hn : p ∉ (cechInsertIndex E v.1 v.2).1 := by
          simp [hpE, Ne.symm hvp]
        rw [hkill (q + 1) _ hn, smul_zero]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    rw [hs] at hd
    have hz := congrArg (fun z => (-1 : R) ^ cechRankBelow E.1 p • z) hd
    have hz' : Δ (q + 1) (K.cechMonomialCochainDegree R F a) = 0 := by
      simpa only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul,
        smul_zero] using hz
    change K.cechContractionMapLinear R a p (q + 1) (K.cechMonomialCochainDegree R F a) -
      K.cechMonomialCochainDegree R F a = 0 at hz'
    exact sub_eq_zero.mp hz'

/-- Positive-coordinate signed deletion contracts the identity chain map. -/
theorem cechContractionMap_eq_id (a : V →₀ ℤ) (p : V) (hp : 0 < a p) :
    K.cechContractionMap R a p = 𝟙 (K.cechComplexDegree R a) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  change K.cechContractionMapLinear R a p q = LinearMap.id
  apply K.cechDegree_linearMap_ext R a
  intro F ha
  exact K.cechContractionMap_monomial R F a p hp ha

/-- An actual contracting homotopy for the fine-degree Čech complex. -/
noncomputable def cechPositiveContractingHomotopy (a : V →₀ ℤ) (p : V) (hp : 0 < a p) :
    Homotopy (𝟙 (K.cechComplexDegree R a)) 0 := by
  let H := Homotopy.nullHomotopy' (K.cechContractionFamily R a p)
  exact { hom := H.hom, zero := H.zero, comm := fun q =>
    (congrArg (fun (f : K.cechComplexDegree R a ⟶ K.cechComplexDegree R a) => f.f q)
      (K.cechContractionMap_eq_id R a p hp)).symm.trans (H.comm q) }

/-- The actual homotopy components are exactly the signed deletion maps. -/
theorem cechPositiveContractingHomotopy_hom (a : V →₀ ℤ) (p : V) (hp : 0 < a p)
    (q : ℕ) :
    (K.cechPositiveContractingHomotopy R a p hp).hom (q + 1) q =
      ModuleCat.ofHom (K.cechPositiveContraction R a p q) := by
  change (Homotopy.nullHomotopy' (K.cechContractionFamily R a p)).hom (q + 1) q = _
  simp [Homotopy.nullHomotopy'_hom, cechContractionFamily, ComplexShape.up_Rel]
  rfl

/-- The deletion formula preserves arbitrary coefficients over `R`. -/
theorem cechPositiveContraction_smul_monomial {q : ℕ} (F : CechIndex V (q + 1))
    (a : V →₀ ℤ) (p : V) (hp : 0 < a p) (r : R) :
    K.cechPositiveContraction R a p q (r • K.cechMonomialCochainDegree R F a) =
      r • (if hpF : p ∈ F.1 then (-1 : R) ^ cechRankBelow F.1 p •
        K.cechMonomialCochainDegree R (cechEraseIndex F ⟨p, hpF⟩) a else 0) := by
  rw [map_smul, K.cechPositiveContraction_monomial R F a p hp]

/-- The endpoint identity has no incoming differential in degree zero. -/
theorem cechPositiveContraction_zero (a : V →₀ ℤ) (p : V) (hp : 0 < a p) :
    K.cechPositiveContraction R a p 0 ∘ₗ K.cechDifferentialDegree R (q := 0) a =
      LinearMap.id := by
  rw [← K.cechContractionMap_f_zero, K.cechContractionMap_eq_id R a p hp]
  rfl

/-- The contraction identity in every positive cochain degree. -/
theorem cechPositiveContraction_succ (a : V →₀ ℤ) (p : V) (hp : 0 < a p) (q : ℕ) :
    K.cechDifferentialDegree R (q := q) a ∘ₗ K.cechPositiveContraction R a p q +
      K.cechPositiveContraction R a p (q + 1) ∘ₗ
        K.cechDifferentialDegree R (q := q + 1) a = LinearMap.id := by
  rw [add_comm (K.cechDifferentialDegree R (q := q) a ∘ₗ K.cechPositiveContraction R a p q)
      (K.cechPositiveContraction R a p (q + 1) ∘ₗ
        K.cechDifferentialDegree R (q := q + 1) a),
    ← K.cechContractionMap_f_succ, K.cechContractionMap_eq_id R a p hp]
  rfl

/-- A nonempty positive support supplies an actual contracting homotopy. -/
theorem cechPositiveSupport_contractible (a : V →₀ ℤ)
    (ha : (positiveSupport a).Nonempty) :
    Nonempty (Homotopy (𝟙 (K.cechComplexDegree R a)) 0) := by
  obtain ⟨p, hp⟩ := ha
  exact ⟨K.cechPositiveContractingHomotopy R a p (Finset.mem_filter.mp hp).2⟩

/-- Contractibility annihilates the actual degreewise cohomology object. -/
theorem cechPositiveCohomology_isZero (a : V →₀ ℤ) (p : V) (hp : 0 < a p) (q : ℕ) :
    CategoryTheory.Limits.IsZero ((K.cechComplexDegree R a).homology q) := by
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  have h := (K.cechPositiveContractingHomotopy R a p hp).homologyMap_eq q
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using h

theorem cechPositiveCohomology_subsingleton (a : V →₀ ℤ) (p : V)
    (hp : 0 < a p) (q : ℕ) : Subsingleton (K.cechCohomologyDegree R q a) :=
  ModuleCat.subsingleton_of_isZero (K.cechPositiveCohomology_isZero R a p hp q)

end Reisner.Complex
