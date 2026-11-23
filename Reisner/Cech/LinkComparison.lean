module

public import Reisner.Cech.Indices
public import Reisner.SimplicialCochain

@[expose] public section

namespace Reisner.Complex

open scoped Classical
open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (K : Reisner.Complex V) (R : Type v) [CommRing R]

/-- The orientation correction from a disjoint negative-support block. -/
def cechLinkSign (N T : Finset V) : R :=
  (-1 : R) ^ (∑ t ∈ T, cechRankBelow N t)

omit [Fintype V] in
@[simp]
theorem cechLinkSign_empty (N : Finset V) : cechLinkSign R N ∅ = 1 := by
  simp [cechLinkSign]

omit [Fintype V] in
private theorem negOne_pow_mul_self (m : ℕ) :
    (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

omit [Fintype V] in
theorem cechLinkSign_mul_self (N T : Finset V) :
    cechLinkSign R N T * cechLinkSign R N T = 1 := by
  unfold cechLinkSign
  exact negOne_pow_mul_self R _

omit [Fintype V] in
theorem cechLinkSign_insert (N T : Finset V) {v : V} (hv : v ∉ T) :
    cechLinkSign R N (insert v T) =
      cechLinkSign R N T * (-1 : R) ^ cechRankBelow N v := by
  unfold cechLinkSign
  rw [Finset.sum_insert hv, pow_add]
  ring

omit [Fintype V] in
theorem cechRankBelow_union {N T : Finset V} (hNT : Disjoint N T) (v : V) :
    cechRankBelow (N ∪ T) v = cechRankBelow N v + cechRankBelow T v := by
  unfold cechRankBelow
  rw [Finset.filter_union]
  have hdisj : Disjoint (N.filter (· < v)) (T.filter (· < v)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxN hxT
    exact (Finset.disjoint_left.mp hNT)
      (Finset.mem_filter.mp hxN).1 (Finset.mem_filter.mp hxT).1
  rw [Finset.card_union_of_disjoint hdisj]

omit [Fintype V] in
theorem cechLinkSign_insertion_compat {N T : Finset V} (hNT : Disjoint N T)
    {v : V} (hv : v ∉ T) :
    (-1 : R) ^ cechRankBelow (N ∪ T) v * cechLinkSign R N (insert v T) =
      cechLinkSign R N T * (-1 : R) ^ simplicialRankBelow T v := by
  rw [cechRankBelow_union hNT,
    cechLinkSign_insert (R := R) N T hv]
  rw [pow_add]
  calc
    ((-1 : R) ^ cechRankBelow N v * (-1 : R) ^ simplicialRankBelow T v) *
        (cechLinkSign R N T * (-1 : R) ^ cechRankBelow N v) =
      cechLinkSign R N T *
        ((-1 : R) ^ cechRankBelow N v * (-1 : R) ^ cechRankBelow N v) *
          (-1 : R) ^ simplicialRankBelow T v := by ring
    _ = cechLinkSign R N T * (-1 : R) ^ simplicialRankBelow T v := by
      rw [negOne_pow_mul_self R]
      simp

/-- Admissible subsets of cardinality |N|+r are exactly r-faces of the link. -/
noncomputable def nonpositiveCechLinkIndexEquiv (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    {F : CechIndex V ((negativeSupport a).card + r) //
      K.LocalizationAdmissible F.1 a} ≃
        (K.link (negativeSupport a) hN).SimplicialFaceIndex r :=
  (K.nonpositiveCechIndexEquivLink a ha hN ((negativeSupport a).card + r)).trans
    { toFun := fun T => ⟨T.1, T.2.1, Nat.add_left_cancel T.2.2⟩
      invFun := fun T => ⟨T.1, T.2.1, by rw [T.2.2]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The full Laurent-basis index corresponding to a link face. -/
noncomputable def cechLinkLaurentIndex (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r) :
    Σ F : CechIndex V ((negativeSupport a).card + r), K.localizationDegrees F.1 :=
  let F := (K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T
  ⟨F.1, ⟨a, F.2⟩⟩

/-- Extract the Laurent coefficient at each link face and correct its orientation. -/
noncomputable def cechNonpositiveLinkMap (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    K.cechDegreeSubmodule R ((negativeSupport a).card + r) a →ₗ[R]
      (K.link (negativeSupport a) hN).SimplicialCochain R r :=
  LinearMap.pi fun T =>
    cechLinkSign R (negativeSupport a) T.1 •
      ((K.cechCochainMonomialBasis R ((negativeSupport a).card + r)).coord
        (K.cechLinkLaurentIndex a ha hN r T)).comp
          (K.cechDegreeSubmodule R ((negativeSupport a).card + r) a).subtype

theorem cechNonpositiveLinkMap_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (z : K.cechDegreeSubmodule R ((negativeSupport a).card + r) a)
    (T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r) :
    K.cechNonpositiveLinkMap R a ha hN r z T =
      cechLinkSign R (negativeSupport a) T.1 *
        (K.cechCochainMonomialBasis R ((negativeSupport a).card + r)).repr z.1
          (K.cechLinkLaurentIndex a ha hN r T) := rfl

/-- The signed coefficient map carries an admissible coordinate monomial to its link basis vector. -/
theorem cechNonpositiveLinkMap_monomial (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (F : CechIndex V ((negativeSupport a).card + r))
    (hF : K.LocalizationAdmissible F.1 a) :
    K.cechNonpositiveLinkMap R a ha hN r (K.cechMonomialCochainDegree R F a) =
      cechLinkSign R (negativeSupport a)
        ((K.nonpositiveCechLinkIndexEquiv a ha hN r) ⟨F, hF⟩).1 •
      (K.link (negativeSupport a) hN).simplicialCochainBasis R r
        ((K.nonpositiveCechLinkIndexEquiv a ha hN r) ⟨F, hF⟩) := by
  classical
  let e := K.nonpositiveCechLinkIndexEquiv a ha hN r
  funext T
  rw [K.cechNonpositiveLinkMap_apply]
  change cechLinkSign R (negativeSupport a) T.1 *
      (K.cechCochainMonomialBasis R ((negativeSupport a).card + r)).repr
        (K.cechMonomialCochain R F a) (K.cechLinkLaurentIndex a ha hN r T) = _
  rw [← K.cechCochainMonomialBasis_apply R F a hF, Module.Basis.repr_self_apply]
  simp only [Pi.smul_apply, smul_eq_mul, simplicialCochainBasis_apply]
  have hi : (⟨F, ⟨a, hF⟩⟩ : Σ F : CechIndex V ((negativeSupport a).card + r),
      K.localizationDegrees F.1) = K.cechLinkLaurentIndex a ha hN r T ↔ e ⟨F, hF⟩ = T := by
    constructor
    · intro h
      have he : (⟨F, hF⟩ : {F : CechIndex V ((negativeSupport a).card + r) //
          K.LocalizationAdmissible F.1 a}) = e.symm T :=
        Subtype.ext (congrArg Sigma.fst h)
      simpa using congrArg e he
    · intro h
      have he : e.symm T = ⟨F, hF⟩ := by rw [← h]; exact e.symm_apply_apply _
      change _ = (⟨(e.symm T).1, ⟨a, (e.symm T).2⟩⟩ : Σ F : CechIndex V ((negativeSupport a).card + r), K.localizationDegrees F.1)
      rw [he]
  by_cases h : e ⟨F, hF⟩ = T
  · have hi' := hi.mpr h
    simp [hi', h, e]
  · have hi' := mt hi.mp h
    simp [hi', Ne.symm h, e]


/-- Reconstruct a homogeneous Cech cochain from the signed link coordinates. -/
noncomputable def cechNonpositiveLinkInv (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    (K.link (negativeSupport a) hN).SimplicialCochain R r →ₗ[R]
      K.cechDegreeSubmodule R ((negativeSupport a).card + r) a :=
  ((K.link (negativeSupport a) hN).simplicialCochainBasis R r).constr R fun T =>
    cechLinkSign R (negativeSupport a) T.1 •
      K.cechMonomialCochainDegree R
        ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).1 a

theorem cechNonpositiveLinkInv_basis (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r) :
    K.cechNonpositiveLinkInv R a ha hN r
        ((K.link (negativeSupport a) hN).simplicialCochainBasis R r T) =
      cechLinkSign R (negativeSupport a) T.1 •
        K.cechMonomialCochainDegree R
          ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).1 a := by
  exact Module.Basis.constr_basis _ _ _ _

theorem cechNonpositiveLinkMap_comp_inv (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    K.cechNonpositiveLinkMap R a ha hN r ∘ₗ K.cechNonpositiveLinkInv R a ha hN r =
      LinearMap.id := by
  apply ((K.link (negativeSupport a) hN).simplicialCochainBasis R r).ext
  intro T
  rw [LinearMap.comp_apply, K.cechNonpositiveLinkInv_basis, map_smul,
    K.cechNonpositiveLinkMap_monomial R a ha hN r _
      ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).2]
  change cechLinkSign R (negativeSupport a) T.1 •
    (cechLinkSign R (negativeSupport a)
      (((K.nonpositiveCechLinkIndexEquiv a ha hN r)
        ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T))).1 •
      (K.link (negativeSupport a) hN).simplicialCochainBasis R r
        ((K.nonpositiveCechLinkIndexEquiv a ha hN r)
          ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T))) = _
  rw [Equiv.apply_symm_apply]
  simp only [smul_smul, cechLinkSign_mul_self, one_smul, LinearMap.id_apply]

theorem cechNonpositiveLinkInv_comp_map (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    K.cechNonpositiveLinkInv R a ha hN r ∘ₗ K.cechNonpositiveLinkMap R a ha hN r =
      LinearMap.id := by
  apply K.cechDegree_linearMap_ext R a
  intro F hF
  rw [LinearMap.comp_apply, K.cechNonpositiveLinkMap_monomial R a ha hN r F hF,
    map_smul, K.cechNonpositiveLinkInv_basis]
  simp only [Equiv.symm_apply_apply, smul_smul, cechLinkSign_mul_self, one_smul,
    LinearMap.id_apply]

/-- Signed coordinate equivalence between a nonpositive Cech degree and actual link cochains. -/
noncomputable def cechNonpositiveLinkEquiv (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    K.cechDegreeSubmodule R ((negativeSupport a).card + r) a ≃ₗ[R]
      (K.link (negativeSupport a) hN).SimplicialCochain R r :=
  LinearEquiv.ofLinearMap (K.cechNonpositiveLinkMap R a ha hN r)
    (K.cechNonpositiveLinkInv R a ha hN r)
    (cechNonpositiveLinkMap_comp_inv K R a ha hN r)
    (cechNonpositiveLinkInv_comp_map K R a ha hN r)


omit [Fintype V] in
@[simp]
theorem nonpositiveCechLinkIndexEquiv_symm_val (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r) :
    ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).1.1 =
      negativeSupport a ∪ T.1 := by
  simp [nonpositiveCechLinkIndexEquiv]
  ext v
  simp

omit [Fintype V] in
@[simp]
theorem nonpositiveCechLinkIndexEquiv_val (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (F : {F : CechIndex V ((negativeSupport a).card + r) //
      K.LocalizationAdmissible F.1 a}) :
    ((K.nonpositiveCechLinkIndexEquiv a ha hN r) F).1 =
      F.1.1 \ negativeSupport a := by
  simp [nonpositiveCechLinkIndexEquiv]
  ext v
  simp

/-- Every coordinate monomial has the expected signed coefficient; invalid coordinates are zero. -/
theorem cechNonpositiveLinkMap_monomial_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (F : CechIndex V ((negativeSupport a).card + r))
    (T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r) :
    K.cechNonpositiveLinkMap R a ha hN r (K.cechMonomialCochainDegree R F a) T =
      if F = ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).1 then
        cechLinkSign R (negativeSupport a) T.1 else 0 := by
  classical
  let e := K.nonpositiveCechLinkIndexEquiv a ha hN r
  by_cases hF : K.LocalizationAdmissible F.1 a
  · rw [K.cechNonpositiveLinkMap_monomial R a ha hN r F hF]
    change cechLinkSign R (negativeSupport a) (e ⟨F, hF⟩).1 *
      ((K.link (negativeSupport a) hN).simplicialCochainBasis R r (e ⟨F, hF⟩) T) =
      if F = (e.symm T).1 then cechLinkSign R (negativeSupport a) T.1 else 0
    rw [simplicialCochainBasis_apply]
    have hi : F = (e.symm T).1 ↔ T = e ⟨F, hF⟩ := by
      constructor
      · intro h
        have he : (⟨F, hF⟩ : {F : CechIndex V ((negativeSupport a).card + r) //
            K.LocalizationAdmissible F.1 a}) = e.symm T := Subtype.ext h
        exact (show e ⟨F, hF⟩ = T by simpa using congrArg e he).symm
      · intro h
        have he := congrArg (fun U => (e.symm U).1) h
        simpa using he.symm
    by_cases h : F = (e.symm T).1
    · have ht := hi.mp h
      simp only [ht, Equiv.symm_apply_apply, ite_true, mul_one]
    · have ht := mt hi.mpr h
      simp only [h, ht, ite_false, mul_zero]
  · rw [K.cechMonomialCochainDegree_eq_zero R F a hF, map_zero]
    have hn : F ≠ (e.symm T).1 := by
      intro h
      exact hF (h.symm ▸ (e.symm T).2)
    change 0 = if F = (e.symm T).1 then cechLinkSign R (negativeSupport a) T.1 else 0
    simp only [hn, ite_false]

/-- Forward component formula of the actual signed equivalence. -/
theorem cechNonpositiveLinkEquiv_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (z : K.cechDegreeSubmodule R ((negativeSupport a).card + r) a)
    (T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r) :
    K.cechNonpositiveLinkEquiv R a ha hN r z T =
      cechLinkSign R (negativeSupport a) T.1 *
        (K.cechCochainMonomialBasis R ((negativeSupport a).card + r)).repr z.1
          (K.cechLinkLaurentIndex a ha hN r T) := rfl

theorem cechNonpositiveLinkEquiv_monomial (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (F : CechIndex V ((negativeSupport a).card + r))
    (hF : K.LocalizationAdmissible F.1 a) :
    K.cechNonpositiveLinkEquiv R a ha hN r (K.cechMonomialCochainDegree R F a) =
      cechLinkSign R (negativeSupport a)
        ((K.nonpositiveCechLinkIndexEquiv a ha hN r) ⟨F, hF⟩).1 •
      (K.link (negativeSupport a) hN).simplicialCochainBasis R r
        ((K.nonpositiveCechLinkIndexEquiv a ha hN r) ⟨F, hF⟩) :=
  K.cechNonpositiveLinkMap_monomial R a ha hN r F hF

theorem cechNonpositiveLinkEquiv_symm_basis (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r) :
    (K.cechNonpositiveLinkEquiv R a ha hN r).symm
        ((K.link (negativeSupport a) hN).simplicialCochainBasis R r T) =
      cechLinkSign R (negativeSupport a) T.1 •
        K.cechMonomialCochainDegree R
          ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).1 a :=
  K.cechNonpositiveLinkInv_basis R a ha hN r T

/-- The inverse is the finite signed monomial sum over actual link faces. -/
theorem cechNonpositiveLinkEquiv_symm_apply (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ)
    (f : (K.link (negativeSupport a) hN).SimplicialCochain R r) :
    (K.cechNonpositiveLinkEquiv R a ha hN r).symm f =
      ∑ T : (K.link (negativeSupport a) hN).SimplicialFaceIndex r,
        (cechLinkSign R (negativeSupport a) T.1 * f T) •
          K.cechMonomialCochainDegree R
            ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).1 a := by
  classical
  change K.cechNonpositiveLinkInv R a ha hN r f = _
  rw [cechNonpositiveLinkInv, Module.Basis.constr_apply_fintype]
  apply Finset.sum_congr rfl
  intro T _
  simp [simplicialCochainBasis, smul_smul, mul_comm]

omit [Fintype V] in
theorem cechLinkInsert_iff (N T S : Finset V) (hNT : Disjoint N T)
    (hNS : Disjoint N S) (v : V) :
    (v ∉ N ∪ T ∧ insert v (N ∪ T) = N ∪ S) ↔
      (v ∉ T ∧ insert v T = S) := by
  constructor
  · rintro ⟨hv, h⟩
    have hvN : v ∉ N := fun hx => hv (Finset.mem_union_left _ hx)
    have hvT : v ∉ T := fun hx => hv (Finset.mem_union_right _ hx)
    refine ⟨hvT, ?_⟩
    have he := congrArg (fun U => U \ N) h
    rw [Finset.insert_sdiff_of_notMem _ hvN,
      Finset.union_sdiff_cancel_left hNT, Finset.union_sdiff_cancel_left hNS] at he
    exact he
  · rintro ⟨hvT, h⟩
    have hvS : v ∈ S := by rw [← h]; simp
    have hvN : v ∉ N := fun hx => (Finset.disjoint_left.mp hNS) hx hvS
    refine ⟨by simp [hvN, hvT], ?_⟩
    rw [← Finset.union_insert, h]

omit [LinearOrder V] in
lemma cechSumSubtypeIte (p : V → Prop) [DecidablePred p] [hpF : Fintype {v : V // p v}] (f : V → R) :
    (∑ v : {v : V // p v}, f v.1) = ∑ v : V, if p v then f v else 0 := by
  have hinst : hpF = Subtype.fintype p := Subsingleton.elim _ _
  subst hpF
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun v => if p v then f v else 0)
  have hleft : (∑ i : {v // p v}, if p i.1 then f i.1 else 0) =
      ∑ i : {v // p v}, f i.1 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [i.2]
  have hright : (∑ i : {v // ¬ p v}, if p i.1 then f i.1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [i.2]
  rw [hright, add_zero] at hsplit
  exact hleft.symm.trans hsplit


theorem cechNonpositiveLinkMap_differential (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    K.cechNonpositiveLinkMap R a ha hN (r + 1) ∘ₗ
        K.cechDifferentialDegree R (q := (negativeSupport a).card + r) a =
      (K.link (negativeSupport a) hN).simplicialDifferential R r ∘ₗ
        K.cechNonpositiveLinkMap R a ha hN r := by
  apply K.cechDegree_linearMap_ext R a
  intro F hF
  let T := (K.nonpositiveCechLinkIndexEquiv a ha hN r) ⟨F, hF⟩
  have hFT : F.1 = negativeSupport a ∪ T.1 := by
    have he := congrArg (fun I => I.1.1)
      ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm_apply_apply ⟨F, hF⟩)
    change ((K.nonpositiveCechLinkIndexEquiv a ha hN r).symm T).1.1 = F.1 at he
    rw [K.nonpositiveCechLinkIndexEquiv_symm_val] at he
    exact he.symm
  have hNT : Disjoint (negativeSupport a) T.1 :=
    ((K.mem_link_iff (negativeSupport a) hN T.1).mp T.2.1).1.symm
  funext S
  change K.cechNonpositiveLinkMap R a ha hN (r + 1)
      (K.cechDifferentialDegree R a (K.cechMonomialCochainDegree R F a)) S =
    (K.link (negativeSupport a) hN).simplicialDifferential R r
      (K.cechNonpositiveLinkMap R a ha hN r (K.cechMonomialCochainDegree R F a)) S
  rw [K.cechDifferentialDegree_monomial R F a hF,
    K.cechNonpositiveLinkMap_monomial R a ha hN r F hF]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    cechNonpositiveLinkMap_monomial_apply]
  rw [simplicialDifferential_basis_insertion_apply]
  change (∑ v : {v : V // v ∉ F.1},
    (-1 : R) ^ cechRankBelow F.1 v.1 *
      (if cechInsertIndex F v.1 v.2 =
        ((K.nonpositiveCechLinkIndexEquiv a ha hN (r + 1)).symm S).1 then
        cechLinkSign R (negativeSupport a) S.1 else 0)) =
      cechLinkSign R (negativeSupport a) T.1 *
        ∑ v : {v : V // v ∈ S.1},
          if v.1 ∉ T.1 ∧ insert v.1 T.1 = S.1 then
            (-1 : R) ^ simplicialRankBelow T.1 v.1 else 0
  simp only [Subtype.ext_iff,
    nonpositiveCechLinkIndexEquiv_symm_val]
  rw [cechSumSubtypeIte R (fun v : V => v ∉ F.1)
    (fun v => (-1 : R) ^ cechRankBelow F.1 v *
      (if insert v F.1 = negativeSupport a ∪ S.1 then
        cechLinkSign R (negativeSupport a) S.1 else 0))]
  rw [cechSumSubtypeIte R (fun v : V => v ∈ S.1)
    (fun v => if v ∉ T.1 ∧ insert v T.1 = S.1 then
      (-1 : R) ^ simplicialRankBelow T.1 v else 0), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hNS : Disjoint (negativeSupport a) S.1 :=
    ((K.mem_link_iff (negativeSupport a) hN S.1).mp S.2.1).1.symm
  have hiff : (v ∉ F.1 ∧ insert v F.1 = negativeSupport a ∪ S.1) ↔
      (v ∉ T.1 ∧ insert v T.1 = S.1) := by
    rw [hFT]
    exact cechLinkInsert_iff (negativeSupport a) T.1 S.1 hNT hNS v
  by_cases hL : v ∉ F.1 ∧ insert v F.1 = negativeSupport a ∪ S.1
  · have hR := hiff.mp hL
    have hvS : v ∈ S.1 := by rw [← hR.2]; simp
    simp only [hL.1, hL.2, hR, hvS, ite_true]
    rw [hFT, ← hR.2]
    exact cechLinkSign_insertion_compat R hNT hR.1
  · have hR := mt hiff.mpr hL
    by_cases hv : v ∉ F.1
    · have hn : insert v F.1 ≠ negativeSupport a ∪ S.1 :=
        fun h => hL ⟨hv, h⟩
      simp only [hv, hn, hR, ite_false, mul_zero, ite_self]
    · simp only [hv, hR, ite_false, mul_zero, ite_self]



/-- The signed term equivalences commute with adjacent Cech and augmented-link differentials. -/
theorem cechNonpositiveLinkEquiv_differential (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (r : ℕ) :
    (K.cechNonpositiveLinkEquiv R a ha hN (r + 1)).toLinearMap ∘ₗ
        K.cechDifferentialDegree R (q := (negativeSupport a).card + r) a =
      (K.link (negativeSupport a) hN).simplicialDifferential R r ∘ₗ
        (K.cechNonpositiveLinkEquiv R a ha hN r).toLinearMap :=
  K.cechNonpositiveLinkMap_differential R a ha hN r

omit [Fintype V] in
lemma insert_link_admissible_iff
    (K : Reisner.Complex V) (a : V →₀ ℤ) (ha : a ≤ 0)
    (hN : negativeSupport a ∈ K.faces) (T : Finset V)
    (hT : T ∈ (K.link (negativeSupport a) hN).faces) {v : V}
    (hvN : v ∉ negativeSupport a) :
    K.LocalizationAdmissible (insert v (negativeSupport a ∪ T)) a ↔
      insert v T ∈ (K.link (negativeSupport a) hN).faces := by
  classical
  let N := negativeSupport a
  have hTN : Disjoint T N := (K.mem_link_iff N hN T).mp hT |>.1
  rw [K.localizationAdmissible_iff_of_nonpos a ha]
  constructor
  · rintro ⟨hsub, hface⟩
    have hface' : N ∪ insert v T ∈ K.faces := by
      convert hface using 1
      ext x
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto
    apply (K.mem_link_iff N hN (insert v T)).mpr
    constructor
    · refine Finset.disjoint_left.mpr ?_
      intro x hx hn
      rcases Finset.mem_insert.mp hx with rfl | ht
      · exact hvN hn
      · exact (Finset.disjoint_left.mp hTN) ht hn
    · convert hface' using 1
      ext x
      simp only [Finset.mem_union]
  · intro hlink
    have hconditions := (K.mem_link_iff N hN (insert v T)).mp hlink
    refine ⟨?_, ?_⟩
    · exact Finset.Subset.trans Finset.subset_union_left
        (Finset.subset_insert v (N ∪ T))
    · convert hconditions.2 using 1
      ext x
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

end Reisner.Complex
