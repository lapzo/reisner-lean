module

public import Reisner.StanleyReisner
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The extended Čech cochain complex of a Stanley–Reisner ring

The degree `q` term is the finite product, equivalently finite direct sum,
of the actual localizations indexed by all `q`-element subsets of the ambient
vertex type. In particular, nonfaces and ghost vertices are retained.
-/

@[expose] public section

namespace Reisner.Complex

open DirectSum

universe u v

variable {V : Type u} (K : Reisner.Complex V)

/-- Finite subsets of `V` of cardinality `q`, including nonfaces. -/
abbrev CechIndex (V : Type u) (q : ℕ) := {F : Finset V // F.card = q}

/-- Degree `q` of the extended Čech complex: one actual localization for each
`q`-element subset. The finite dependent product is canonically the finite
direct sum of these modules. -/
abbrev CechCochain (R : Type v) [CommRing R] [Fintype V] (q : ℕ) :=
  (F : CechIndex V q) → K.FaceRingLocalization R F.1

/-- The literal finite direct-sum form of `CechCochain`. The public cochain
API uses the equivalent dependent product for convenient coordinate maps. -/
abbrev CechCochainDirectSum (R : Type v) [CommRing R] [Fintype V] (q : ℕ) :=
  ⨁ (F : CechIndex V q), K.FaceRingLocalization R F.1

/-- The canonical finite direct-sum/product equivalence for a Čech degree. -/
noncomputable def cechCochainDirectSumEquiv (R : Type v) [CommRing R]
    [Fintype V] (q : ℕ) :
    K.CechCochainDirectSum R q ≃ₗ[R] K.CechCochain R q :=
  DirectSum.linearEquivFunOnFintype R (CechIndex V q)
    (fun F => K.FaceRingLocalization R F.1)

/-- The product basis of Čech monomials, indexed by a subset coordinate and
an admissible Laurent degree at that coordinate. -/
noncomputable def cechCochainMonomialBasis (R : Type v) [CommRing R]
    [Fintype V] (q : ℕ) :
    Module.Basis (Σ F : CechIndex V q, K.localizationDegrees F.1) R
      (K.CechCochain R q) :=
  Pi.basis fun F => K.localizationMonomialBasis R F.1

variable (R : Type v) [CommRing R] [Fintype V] [LinearOrder V]

def cechRankBelow (F : Finset V) (v : V) : ℕ :=
  (F.filter (· < v)).card

omit [Fintype V] in
private theorem cechRankEraseOfLt (F : Finset V) {v w : V}
    (hv : v ∈ F) (hvw : v < w) :
    cechRankBelow (F.erase v) w + 1 = cechRankBelow F w := by
  simpa only [cechRankBelow, Finset.filter_erase] using
    Finset.card_erase_add_one (s := F.filter (· < w)) (a := v) (by simp [hv, hvw])

omit [Fintype V] in
private theorem cechRankEraseOfNotLt (F : Finset V) {v w : V}
    (hvw : ¬ v < w) : cechRankBelow (F.erase v) w = cechRankBelow F w := by
  simp [cechRankBelow, Finset.filter_erase, hvw]

private theorem cechSignSwap (F : Finset V) {v w : V}
    (hv : v ∈ F) (hw : w ∈ F) (hne : v ≠ w) :
    (-1 : R) ^ cechRankBelow F v * (-1 : R) ^ cechRankBelow (F.erase v) w =
      -((-1 : R) ^ cechRankBelow F w * (-1 : R) ^ cechRankBelow (F.erase w) v) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [cechRankEraseOfNotLt F (not_lt.mpr h.le)]
    rw [← cechRankEraseOfLt F hv h, pow_succ]
    ring
  · rw [cechRankEraseOfNotLt F (not_lt.mpr h.le)]
    rw [← cechRankEraseOfLt F hw h, pow_succ]
    ring

private abbrev CechDeletionPairs (H : Finset V) :=
  Σ v : {v // v ∈ H}, {w // w ∈ H.erase v.1}

private def cechSwapDeletion {H : Finset V} (p : CechDeletionPairs H) :
    CechDeletionPairs H :=
  ⟨⟨p.2.1, (Finset.mem_erase.mp p.2.2).2⟩,
    ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩

omit [Fintype V] in
private theorem cechSwapDeletion_involutive {H : Finset V}
    (p : CechDeletionPairs H) : cechSwapDeletion (cechSwapDeletion p) = p := rfl

private theorem cechSumDeletionCancel {H : Finset V} {M : Type*}
    [AddCommGroup M] (f : (u : {u // u ∈ H}) → {w // w ∈ H.erase u.1} → M)
    (hcancel : ∀ p : CechDeletionPairs H,
      f p.1 p.2 + f (cechSwapDeletion p).1 (cechSwapDeletion p).2 = 0) :
    ∑ u : {u // u ∈ H}, ∑ w : {w // w ∈ H.erase u.1}, f u w = 0 := by
  rw [← Fintype.sum_sigma']
  apply Finset.sum_involution (fun p _ => cechSwapDeletion p)
  · intro p _
    exact hcancel p
  · intro p _ _ h
    exact (Finset.mem_erase.mp p.2.2).1
      (congrArg (fun t : CechDeletionPairs H => t.1.1) h)
  · exact fun _ _ => Finset.mem_univ _
  · exact fun _ _ => cechSwapDeletion_involutive _

private theorem cechTransition_eq_of_index_eq {q : ℕ} {A B : CechIndex V q}
    (e : A = B) (H : Finset V) (hA : A.1 ⊆ H) (hB : B.1 ⊆ H)
    (z : K.CechCochain R q) :
    K.faceRingLocalizationMap R hA (z A) = K.faceRingLocalizationMap R hB (z B) := by
  subst B
  rfl

private def cechDoubleEraseIndex {q : ℕ} (H : CechIndex V (q + 2))
    (u : {u // u ∈ H.1}) (w : {w // w ∈ H.1.erase u.1}) : CechIndex V q :=
  ⟨H.1.erase u.1 |>.erase w.1, by
    rw [Finset.card_erase_of_mem w.2, Finset.card_erase_of_mem u.2, H.2]
    omega⟩

private noncomputable def cechDoubleTerm {q : ℕ} (H : CechIndex V (q + 2))
    (z : K.CechCochain R q) (p : CechDeletionPairs H.1) :
    K.FaceRingLocalization R H.1 :=
  let u := p.1
  let w := p.2
  ((-1 : R) ^ cechRankBelow H.1 u.1 *
      (-1 : R) ^ cechRankBelow (H.1.erase u.1) w.1) •
    K.faceRingLocalizationMap R
      ((Finset.erase_subset w.1 (H.1.erase u.1)).trans (Finset.erase_subset u.1 H.1))
      (z (cechDoubleEraseIndex H u w))

private theorem cechDoubleTerm_cancel {q : ℕ} (H : CechIndex V (q + 2))
    (z : K.CechCochain R q) (p : CechDeletionPairs H.1) :
    K.cechDoubleTerm R H z p + K.cechDoubleTerm R H z (cechSwapDeletion p) = 0 := by
  let p' := cechSwapDeletion p
  have hindex : cechDoubleEraseIndex H p.1 p.2 =
      cechDoubleEraseIndex H p'.1 p'.2 :=
    Subtype.ext (Finset.erase_right_comm (s := H.1) (a := p.1.val) (b := p.2.val))
  have hpath := cechTransition_eq_of_index_eq (K := K) (R := R) hindex H.1
    ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
    ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) z
  have hsign := cechSignSwap R H.1 p.1.property
    (Finset.mem_erase.mp p.2.property).2 (Finset.mem_erase.mp p.2.property).1.symm
  have cancel {a b : R} {x y : K.FaceRingLocalization R H.1}
      (hab : a = -b) (hxy : x = y) : a • x + b • y = 0 := by
    subst a
    subst x
    simp
  exact cancel hsign hpath

/-- The sub-index obtained by deleting one vertex from a face of cardinality
`q + 1`. -/
abbrev cechEraseIndex {q : ℕ} (G : CechIndex V (q + 1))
    (v : {v : V // v ∈ G.1}) : CechIndex V q :=
  ⟨G.1.erase v.1, by
    rw [Finset.card_erase_of_mem v.2, G.2]
    omega⟩

/-- Insert a vertex outside a `q`-element set, retaining the cardinality
proof in the target cochain index. -/
abbrev cechInsertIndex {q : ℕ} (F : CechIndex V q) (v : V)
    (hv : v ∉ F.1) : CechIndex V (q + 1) :=
  ⟨insert v F.1, by simp [Finset.card_insert_of_notMem hv, F.2]⟩

/-- The degree-`a` monomial cochain supported at one localization coordinate.
If the degree is inadmissible at that coordinate, its value is zero. -/
noncomputable def cechMonomialCochain {q : ℕ} (F : CechIndex V q)
    (a : V →₀ ℤ) : K.CechCochain R q := by
  classical
  exact fun G => if G = F then K.localizationMonomial R G.1 a else 0

@[simp]
theorem cechMonomialCochain_apply_self {q : ℕ} (F : CechIndex V q)
    (a : V →₀ ℤ) : K.cechMonomialCochain R F a F =
      K.localizationMonomial R F.1 a := by
  classical
  simp [cechMonomialCochain]

theorem cechMonomialCochain_apply_of_ne {q : ℕ} (F G : CechIndex V q)
    (a : V →₀ ℤ) (h : G ≠ F) : K.cechMonomialCochain R F a G = 0 := by
  classical
  simp [cechMonomialCochain, h]

/-- The signed localization map contributing to the `G` coordinate of the
Čech differential. -/
noncomputable def cechDifferentialComponent {q : ℕ} (G : CechIndex V (q + 1)) :
    K.CechCochain R q →ₗ[R] K.FaceRingLocalization R G.1 :=
  ∑ v : {v : V // v ∈ G.1},
    ((-1 : R) ^ (G.1.filter (fun u => u < v.1)).card) •
      (K.faceRingLocalizationMap R (Finset.erase_subset v.1 G.1)).toLinearMap.comp
        (LinearMap.proj (cechEraseIndex G v))

/-- The extended Čech differential. At a target subset `G`, sum over the
vertices inserted into `G`; the sign is the parity of the number of smaller
vertices in `G`. -/
noncomputable def cechDifferential (q : ℕ) :
    K.CechCochain R q →ₗ[R] K.CechCochain R (q + 1) :=
  LinearMap.pi fun G => K.cechDifferentialComponent R G

@[simp]
theorem cechDifferential_apply {q : ℕ} (z : K.CechCochain R q)
    (G : CechIndex V (q + 1)) :
    K.cechDifferential R q z G =
      ∑ v : {v : V // v ∈ G.1},
        ((-1 : R) ^ (G.1.filter (fun u => u < v.1)).card) •
          K.faceRingLocalizationMap R (Finset.erase_subset v.1 G.1)
            (z (cechEraseIndex G v)) := by
  simp [cechDifferential, cechDifferentialComponent]

/-- The differential of a Laurent monomial cochain is the signed sum over
all vertices not already in its source index. Inadmissible target terms are
zero because their localization monomial vanishes. -/
theorem cechDifferential_monomialCochain {q : ℕ} (F : CechIndex V q)
    (a : V →₀ ℤ) (ha : K.LocalizationAdmissible F.1 a) :
    K.cechDifferential R q (K.cechMonomialCochain R F a) =
      ∑ v : {v : V // v ∉ F.1},
        ((-1 : R) ^ cechRankBelow F.1 v.1) •
          K.cechMonomialCochain R (cechInsertIndex F v.1 v.2) a := by
  classical
  funext G
  rw [cechDifferential_apply]
  simp only [Fintype.sum_apply, Pi.smul_apply]
  by_cases hFG : F.1 ⊆ G.1
  · have hcard : F.1.card + 1 = G.1.card := by omega
    obtain ⟨v, hv, hvG⟩ := (Finset.exists_eq_insert_iff).2 ⟨hFG, hcard⟩
    have hGI : G = cechInsertIndex F v hv := Subtype.ext hvG.symm
    subst G
    rw [Finset.sum_eq_single ⟨v, Finset.mem_insert_self _ _⟩]
    · rw [Finset.sum_eq_single ⟨v, hv⟩]
      · have herase : cechEraseIndex (cechInsertIndex F v hv)
            ⟨v, Finset.mem_insert_self _ _⟩ = F := by
          apply Subtype.ext
          simp [cechEraseIndex, cechInsertIndex, Finset.erase_insert hv]
        have hsign :
            (-1 : R) ^ (((insert v F.1).filter (fun u => u < v)).card) =
              (-1 : R) ^ cechRankBelow F.1 v := by
          simp [cechRankBelow, Finset.filter_insert, lt_irrefl]
        rw [hsign]
        have hsingle : K.cechMonomialCochain R F a
            (cechEraseIndex (cechInsertIndex F v hv)
              ⟨v, Finset.mem_insert_self _ _⟩) =
              K.localizationMonomial R ((insert v F.1).erase v) a := by
          simp [cechMonomialCochain, herase, Finset.erase_insert hv]
        rw [hsingle]
        have ha' : ∀ u ∉ (insert v F.1).erase v, 0 ≤ a u := by
          simpa [Finset.erase_insert hv] using ha.1
        rw [K.faceRingLocalizationMap_monomial R
          (Finset.erase_subset v (insert v F.1)) a ha']
        simp [cechInsertIndex]
      · intro w hw hwne
        have hne : cechInsertIndex F w.1 w.2 ≠ cechInsertIndex F v hv := by
          intro he
          have hsets := congrArg Subtype.val he
          have hsets' : insert w.1 F.1 = insert v F.1 := by
            simpa [cechInsertIndex] using hsets
          have hwmem : w.1 ∈ insert v F.1 := by
            have : w.1 ∈ insert w.1 F.1 := by simp
            rw [hsets'] at this
            exact this
          rcases Finset.mem_insert.mp hwmem with heq | hF
          · exact hwne (Subtype.ext heq)
          · exact w.2 hF
        change (-1 : R) ^ cechRankBelow F.1 w.1 •
          K.cechMonomialCochain R (cechInsertIndex F w.1 w.2) a
            (cechInsertIndex F v hv) = 0
        rw [K.cechMonomialCochain_apply_of_ne R
          (cechInsertIndex F w.1 w.2) (cechInsertIndex F v hv) a (Ne.symm hne)]
        simp
      · simp
    · intro w hw hwne
      have hwF : w.1 ∈ F.1 := Finset.mem_insert.mp w.2 |>.resolve_left (by
        intro h
        exact hwne (Subtype.ext (by simpa [cechInsertIndex] using h)))
      have hne : cechEraseIndex (cechInsertIndex F v hv) w ≠ F := by
        intro h
        have hsets := congrArg Subtype.val h
        have hvw : v ≠ w.1 := by
          intro he
          exact hwne (Subtype.ext he.symm)
        have hvmem : v ∈ (insert v F.1).erase w.1 := by
          simp [Finset.mem_erase, hvw]
        exact hv (hsets ▸ hvmem)
      simp [cechMonomialCochain, hne]
    · simp
  · have hleft (w : {w : V // w ∈ G.1}) : cechEraseIndex G w ≠ F := by
      intro h
      apply hFG
      have hsets := congrArg Subtype.val h
      rw [← hsets]
      exact Finset.erase_subset w.1 G.1
    have hright (w : {w : V // w ∉ F.1}) :
        cechInsertIndex F w.1 w.2 ≠ G := by
      intro h
      apply hFG
      have hsets := congrArg Subtype.val h
      have hsets' : insert w.1 F.1 = G.1 := by
        simpa [cechInsertIndex] using hsets
      rw [← hsets']
      exact Finset.subset_insert w.1 F.1
    have hrightSum :
        (∑ w : {w : V // w ∉ F.1},
          (-1 : R) ^ cechRankBelow F.1 w.1 •
            K.cechMonomialCochain R (cechInsertIndex F w.1 w.2) a G) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hneq : G ≠ cechInsertIndex F w.1 w.2 := by
        intro he
        exact hright w he.symm
      simp [cechMonomialCochain, hneq]
    have hleftSum :
        (∑ w : {w : V // w ∈ G.1},
          (-1 : R) ^ (G.1.filter (fun u => u < w.1)).card •
            K.faceRingLocalizationMap R (Finset.erase_subset w.1 G.1)
              (K.cechMonomialCochain R F a (cechEraseIndex G w))) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      simp [cechMonomialCochain, hleft w]
    rw [hrightSum, hleftSum]

private theorem cechDifferential_sq_component {q : ℕ} (z : K.CechCochain R q)
    (H : CechIndex V (q + 2)) :
    K.cechDifferential R (q + 1) (K.cechDifferential R q z) H =
      ∑ u : {u // u ∈ H.1}, ∑ w : {w // w ∈ H.1.erase u.1},
        K.cechDoubleTerm R H z ⟨u, w⟩ := by
  rw [cechDifferential_apply]
  simp_rw [cechDifferential_apply]
  simp only [map_sum, map_smul, smul_smul]
  simp_rw [← AlgHom.comp_apply, K.faceRingLocalizationMap_comp]
  simp only [cechDoubleTerm, cechDoubleEraseIndex, cechRankBelow, cechEraseIndex,
    Finset.smul_sum, smul_smul]

/-- The signed Čech differentials square to zero. The coordinate proof pairs
the two possible orders of deleting each pair of vertices. -/
theorem cechDifferential_comp_eq_zero {q : ℕ} :
    (K.cechDifferential R (q + 1)).comp (K.cechDifferential R q) = 0 := by
  apply LinearMap.ext
  intro z
  funext H
  change K.cechDifferential R (q + 1) (K.cechDifferential R q z) H = 0
  rw [cechDifferential_sq_component]
  exact cechSumDeletionCancel
    (fun u w => K.cechDoubleTerm R H z ⟨u, w⟩)
    (fun p => K.cechDoubleTerm_cancel R H z p)

/-- The finite extended Čech cochains and their signed localization maps as
an actual `ℕ`-indexed cochain complex in `ModuleCat R`. -/
noncomputable def cechComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R (K.CechCochain R q))
    (fun q => ModuleCat.ofHom (K.cechDifferential R q))
    (fun q => by
      rw [← ModuleCat.ofHom_comp]
      rw [K.cechDifferential_comp_eq_zero, ModuleCat.ofHom_zero])

@[simp]
theorem cechComplex_X (q : ℕ) :
    (K.cechComplex R).X q = ModuleCat.of R (K.CechCochain R q) :=
  by simp [cechComplex]

@[simp]
theorem cechComplex_d (q : ℕ) :
    (K.cechComplex R).d q (q + 1) = ModuleCat.ofHom (K.cechDifferential R q) := by
  change CochainComplex.of.d
    (fun q => ModuleCat.of R (K.CechCochain R q))
    (fun q => ModuleCat.ofHom (K.cechDifferential R q)) q (q + 1) = _
  rw [CochainComplex.of_d]

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

end Reisner.Complex
