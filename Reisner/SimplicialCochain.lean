module

public import Reisner.StanleyReisner
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Augmented simplicial cochains indexed by face cardinality

The degree `n` term is the finite product of copies of `R` indexed by the
actual `n`-element faces of `K`. The empty face supplies the augmented degree
`-1` term at index zero; ambient ghost vertices are not singleton faces.
-/

@[expose] public section

namespace Reisner.Complex

open DirectSum

universe u v

variable {V : Type u} (K : Reisner.Complex V)

/-- Actual faces of cardinality `n`, including the empty face when `n = 0`. -/
abbrev SimplicialFaceIndex (n : ℕ) :=
  {F : Finset V // F ∈ K.faces ∧ F.card = n}

/-- Augmented simplicial cochains in face-cardinality degree `n`. -/
abbrev SimplicialCochain (R : Type v) [CommRing R] (n : ℕ) :=
  (F : K.SimplicialFaceIndex n) → R

variable (R : Type v) [CommRing R] [Fintype V] [LinearOrder V]

/-- The explicit finite direct-sum form of the cochain term. -/
abbrev SimplicialCochainDirectSum (n : ℕ) :=
  ⨁ (_F : K.SimplicialFaceIndex n), R

/-- Finite direct sum and dependent product agree for this face index. -/
noncomputable def simplicialCochainDirectSumEquiv (n : ℕ) :
    K.SimplicialCochainDirectSum R n ≃ₗ[R] K.SimplicialCochain R n := by
  classical
  exact DirectSum.linearEquivFunOnFintype R (K.SimplicialFaceIndex n) (fun _ => R)

/-- The coordinate basis of the finite product of scalar cochains. -/
noncomputable def simplicialCochainBasis (n : ℕ) :
    Module.Basis (K.SimplicialFaceIndex n) R (K.SimplicialCochain R n) := by
  classical
  exact Pi.basisFun R (K.SimplicialFaceIndex n)

@[simp]
theorem simplicialCochainBasis_apply (n : ℕ) (F G : K.SimplicialFaceIndex n) :
    K.simplicialCochainBasis R n F G = if G = F then 1 else 0 := by
  classical
  simp [simplicialCochainBasis, Pi.basisFun_apply, Pi.single_apply, eq_comm]

omit [LinearOrder V] in

/-- Over a field, each augmented cochain term is finite-dimensional, with one
coordinate for each actual face. In particular, the empty face is counted at
`n = 0`, while ghost vertices contribute no coordinates. -/
theorem simplicialCochain_finiteDimensional (k : Type v) [Field k] (n : ℕ) :
    FiniteDimensional k (K.SimplicialCochain k n) := by
  classical
  exact (K.simplicialCochainBasis k n).finiteDimensional_of_finite

omit [LinearOrder V] in
/-- The dimension of an augmented cochain term is the number of actual faces
of that cardinality. -/
theorem simplicialCochain_finrank (k : Type v) [Field k] (n : ℕ) :
    Module.finrank k (K.SimplicialCochain k n) = Nat.card (K.SimplicialFaceIndex n) := by
  classical
  rw [Module.finrank_eq_card_basis (K.simplicialCochainBasis k n)]
  exact (Nat.card_eq_fintype_card (α := K.SimplicialFaceIndex n)).symm

/-- Insert a new vertex into a face, requiring that the resulting set is an
actual face of `K`. -/
def simplicialFaceInsertIndex {n : ℕ} (F : K.SimplicialFaceIndex n) (v : V)
    (hv : v ∉ F.1) (hface : insert v F.1 ∈ K.faces) :
    K.SimplicialFaceIndex (n + 1) :=
  ⟨insert v F.1, hface, by simp [Finset.card_insert_of_notMem hv, F.2.2]⟩

/-- Delete a vertex from an oriented face index. -/
def simplicialFaceEraseIndex {n : ℕ} (G : K.SimplicialFaceIndex (n + 1))
    (v : {v : V // v ∈ G.1}) : K.SimplicialFaceIndex n :=
  ⟨G.1.erase v.1,
    K.face_of_subset (Finset.erase_subset v.1 G.1) G.2.1,
    by rw [Finset.card_erase_of_mem v.2, G.2.2]; omega⟩

/-- Number of vertices of `F` preceding `v`; this determines the face
orientation sign. -/
def simplicialRankBelow (F : Finset V) (v : V) : ℕ :=
  (F.filter (· < v)).card

omit [Fintype V] in
private theorem simplicialRankEraseOfLt (F : Finset V) {v w : V}
    (hv : v ∈ F) (hvw : v < w) :
    simplicialRankBelow (F.erase v) w + 1 = simplicialRankBelow F w := by
  simpa only [simplicialRankBelow, Finset.filter_erase] using
    Finset.card_erase_add_one (s := F.filter (· < w)) (a := v) (by simp [hv, hvw])

omit [Fintype V] in
private theorem simplicialRankEraseOfNotLt (F : Finset V) {v w : V}
    (hvw : ¬ v < w) :
    simplicialRankBelow (F.erase v) w = simplicialRankBelow F w := by
  simp [simplicialRankBelow, Finset.filter_erase, hvw]

omit [Fintype V] in
private theorem simplicialSignSwap (F : Finset V) {v w : V}
    (hv : v ∈ F) (hw : w ∈ F) (hne : v ≠ w) :
    (-1 : R) ^ simplicialRankBelow F v *
      (-1 : R) ^ simplicialRankBelow (F.erase v) w =
    -((-1 : R) ^ simplicialRankBelow F w *
      (-1 : R) ^ simplicialRankBelow (F.erase w) v) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [simplicialRankEraseOfNotLt F (not_lt.mpr h.le)]
    rw [← simplicialRankEraseOfLt F hv h, pow_succ]
    ring
  · rw [simplicialRankEraseOfNotLt F (not_lt.mpr h.le)]
    rw [← simplicialRankEraseOfLt F hw h, pow_succ]
    ring

private abbrev SimplicialDeletionPairs (G : Finset V) :=
  Σ v : {v // v ∈ G}, {w // w ∈ G.erase v.1}

private def simplicialSwapDeletion {G : Finset V} (p : SimplicialDeletionPairs G) :
    SimplicialDeletionPairs G :=
  ⟨⟨p.2.1, (Finset.mem_erase.mp p.2.2).2⟩,
    ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩

omit [Fintype V] in
private theorem simplicialSwapDeletion_involutive {G : Finset V}
    (p : SimplicialDeletionPairs G) : simplicialSwapDeletion (simplicialSwapDeletion p) = p := rfl

omit [Fintype V] in
private theorem simplicialSumDeletionCancel {G : Finset V} {M : Type*}
    [AddCommGroup M] (f : (u : {u // u ∈ G}) → {w // w ∈ G.erase u.1} → M)
    (hcancel : ∀ p : SimplicialDeletionPairs G,
      f p.1 p.2 + f (simplicialSwapDeletion p).1 (simplicialSwapDeletion p).2 = 0) :
    ∑ u : {u // u ∈ G}, ∑ w : {w // w ∈ G.erase u.1}, f u w = 0 := by
  rw [← Fintype.sum_sigma']
  apply Finset.sum_involution (fun p _ => simplicialSwapDeletion p)
  · intro p _
    exact hcancel p
  · intro p _ _ h
    exact (Finset.mem_erase.mp p.2.2).1
      (congrArg (fun t : SimplicialDeletionPairs G => t.1.1) h)
  · exact fun _ _ => Finset.mem_univ _
  · exact fun _ _ => simplicialSwapDeletion_involutive _

/-- Delete two vertices; the intermediate face is face-closed by downward
closure, and its cardinality is `n`. -/
private def simplicialDoubleEraseIndex {n : ℕ} (G : K.SimplicialFaceIndex (n + 2))
    (u : {u // u ∈ G.1}) (w : {w // w ∈ G.1.erase u.1}) : K.SimplicialFaceIndex n :=
  K.simplicialFaceEraseIndex (K.simplicialFaceEraseIndex G u) w

private noncomputable def simplicialDoubleTerm {n : ℕ}
    (G : K.SimplicialFaceIndex (n + 2)) (f : K.SimplicialCochain R n)
    (p : SimplicialDeletionPairs G.1) : R :=
  let u := p.1
  let w := p.2
  ((-1 : R) ^ simplicialRankBelow G.1 u.1 *
      (-1 : R) ^ simplicialRankBelow (G.1.erase u.1) w.1) *
    f (K.simplicialDoubleEraseIndex G u w)

omit [Fintype V] in
private theorem simplicialDoubleTerm_cancel {n : ℕ}
    (G : K.SimplicialFaceIndex (n + 2)) (f : K.SimplicialCochain R n)
    (p : SimplicialDeletionPairs G.1) :
    K.simplicialDoubleTerm R G f p +
      K.simplicialDoubleTerm R G f (simplicialSwapDeletion p) = 0 := by
  have hindex : K.simplicialDoubleEraseIndex G p.1 p.2 =
      K.simplicialDoubleEraseIndex G (simplicialSwapDeletion p).1
        (simplicialSwapDeletion p).2 := by
    apply Subtype.ext
    exact Finset.erase_right_comm (s := G.1) (a := p.1.1) (b := p.2.1)
  have hval : f (K.simplicialDoubleEraseIndex G p.1 p.2) =
      f (K.simplicialDoubleEraseIndex G (simplicialSwapDeletion p).1
        (simplicialSwapDeletion p).2) := congrArg f hindex
  have hsign := simplicialSignSwap R G.1 p.1.2
    (Finset.mem_erase.mp p.2.2).2 (Finset.mem_erase.mp p.2.2).1.symm
  change (((-1 : R) ^ simplicialRankBelow G.1 p.1.1 *
      (-1 : R) ^ simplicialRankBelow (G.1.erase p.1.1) p.2.1) *
      f (K.simplicialDoubleEraseIndex G p.1 p.2)) +
    (((-1 : R) ^ simplicialRankBelow G.1 (simplicialSwapDeletion p).1.1 *
      (-1 : R) ^ simplicialRankBelow
        (G.1.erase (simplicialSwapDeletion p).1.1) (simplicialSwapDeletion p).2.1) *
      f (K.simplicialDoubleEraseIndex G (simplicialSwapDeletion p).1
        (simplicialSwapDeletion p).2)) = 0
  simp only [simplicialSwapDeletion] at hval ⊢
  rw [hval]
  rw [← add_mul, hsign]
  ring_nf

/-- The signed deletion differential on actual faces. -/
noncomputable def simplicialDifferential (n : ℕ) :
    K.SimplicialCochain R n →ₗ[R] K.SimplicialCochain R (n + 1) :=
  LinearMap.pi fun G =>
    ∑ v : {v : V // v ∈ G.1},
      ((-1 : R) ^ simplicialRankBelow G.1 v.1) •
        (LinearMap.proj (K.simplicialFaceEraseIndex G v))

omit [Fintype V] in
@[simp]
theorem simplicialDifferential_apply {n : ℕ} (f : K.SimplicialCochain R n)
    (G : K.SimplicialFaceIndex (n + 1)) :
    K.simplicialDifferential R n f G =
      ∑ v : {v : V // v ∈ G.1},
        (-1 : R) ^ simplicialRankBelow G.1 v.1 *
          f (K.simplicialFaceEraseIndex G v) := by
  simp [simplicialDifferential, LinearMap.pi_apply, smul_eq_mul]

omit [Fintype V] in
private theorem simplicialDifferential_sq_component {n : ℕ}
    (f : K.SimplicialCochain R n) (G : K.SimplicialFaceIndex (n + 2)) :
    K.simplicialDifferential R (n + 1) (K.simplicialDifferential R n f) G =
      ∑ u : {u // u ∈ G.1}, ∑ w : {w // w ∈ G.1.erase u.1},
        K.simplicialDoubleTerm R G f ⟨u, w⟩ := by
  rw [simplicialDifferential_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [simplicialDifferential_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp [simplicialDoubleTerm, simplicialDoubleEraseIndex,
    simplicialFaceEraseIndex, mul_assoc]

omit [Fintype V] in
theorem simplicialDifferential_comp_eq_zero (n : ℕ) :
    (K.simplicialDifferential R (n + 1)).comp (K.simplicialDifferential R n) = 0 := by
  apply LinearMap.ext
  intro f
  funext G
  change K.simplicialDifferential R (n + 1)
      (K.simplicialDifferential R n f) G = 0
  rw [simplicialDifferential_sq_component]
  exact simplicialSumDeletionCancel (G := G.1)
    (fun u w => K.simplicialDoubleTerm R G f ⟨u, w⟩)
    (fun p => K.simplicialDoubleTerm_cancel R G f p)

/-- The empty face is the unique face index in cardinality zero. -/
@[instance_reducible]
noncomputable def simplicialFaceIndexZeroUnique :
    Unique (K.SimplicialFaceIndex 0) := by
  refine ⟨⟨∅, K.empty_mem, by simp⟩, ?_⟩
  intro F
  apply Subtype.ext
  exact Finset.card_eq_zero.mp F.2.2

/-- Cardinality-index zero is canonically the augmented scalar term `R`. -/
noncomputable def simplicialCochainZeroEquiv :
    K.SimplicialCochain R 0 ≃ₗ[R] R := by
  let _ : Unique (K.SimplicialFaceIndex 0) := K.simplicialFaceIndexZeroUnique
  exact LinearEquiv.piUnique R (fun _ : K.SimplicialFaceIndex 0 => R)

omit [Fintype V] [LinearOrder V] in
@[simp]
theorem simplicialCochainZeroEquiv_apply (f : K.SimplicialCochain R 0) :
    K.simplicialCochainZeroEquiv R f = f ⟨∅, K.empty_mem, by simp⟩ := by
  let _ : Unique (K.SimplicialFaceIndex 0) := K.simplicialFaceIndexZeroUnique
  exact congrArg f (Subsingleton.elim _ _)

omit [Fintype V] in
/-- The augmented differential sends a scalar at the empty face to the same
scalar at every actual singleton face. -/
theorem simplicialDifferential_zero_apply (r : R)
    (G : K.SimplicialFaceIndex 1) :
    K.simplicialDifferential R 0 (fun _ => r) G = r := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp G.2.2
  have hvface : ({v} : Finset V) ∈ K.faces := hv ▸ G.2.1
  have hG : G = ⟨{v}, hvface, by simp⟩ := Subtype.ext hv
  subst G
  have hrank : simplicialRankBelow ({v} : Finset V) v = 0 := by
    simp [simplicialRankBelow]
  simp [simplicialDifferential_apply, hrank]

omit [Fintype V] in
/-- If `K` has no actual vertices, its augmented differential out of the
empty-face term is zero. -/
theorem simplicialDifferential_zero_of_no_vertices
    (hV : ∀ v : V, ({v} : Finset V) ∉ K.faces) :
    K.simplicialDifferential R 0 = 0 := by
  classical
  apply LinearMap.ext
  intro f
  funext G
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp G.2.2
  have hvface : ({v} : Finset V) ∈ K.faces := hv ▸ G.2.1
  exact (hV v hvface).elim

/-- The coefficient of a coordinate basis cochain in the differential is
supported precisely where deleting a vertex recovers its source face. -/
theorem simplicialDifferential_basis_apply (n : ℕ) (F : K.SimplicialFaceIndex n)
    (G : K.SimplicialFaceIndex (n + 1)) :
    K.simplicialDifferential R n (K.simplicialCochainBasis R n F) G =
      ∑ v : {v : V // v ∈ G.1},
        (-1 : R) ^ simplicialRankBelow G.1 v.1 *
          if K.simplicialFaceEraseIndex G v = F then 1 else 0 := by
  rw [simplicialDifferential_apply]
  simp only [simplicialCochainBasis_apply]

/-- On a basis cochain, the differential is supported exactly on faces
obtained by inserting one vertex into the source face. This is the
coordinate form of the signed insertion formula. -/
theorem simplicialDifferential_basis_insertion_apply (n : ℕ)
    (F : K.SimplicialFaceIndex n) (G : K.SimplicialFaceIndex (n + 1)) :
    K.simplicialDifferential R n (K.simplicialCochainBasis R n F) G =
      ∑ v : {v : V // v ∈ G.1},
        if v.1 ∉ F.1 ∧ insert v.1 F.1 = G.1 then
          (-1 : R) ^ simplicialRankBelow F.1 v.1 else 0 := by
  rw [K.simplicialDifferential_basis_apply]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hErase : K.simplicialFaceEraseIndex G v = F
  · have hNot : v.1 ∉ F.1 := by
      intro hvF
      have hvNot : v.1 ∉ (G.1.erase v.1) := Finset.notMem_erase _ _
      have : v.1 ∈ (K.simplicialFaceEraseIndex G v).1 := by
        simpa [hErase] using hvF
      exact hvNot this
    have hEraseVal : (K.simplicialFaceEraseIndex G v).1 = F.1 :=
      congrArg Subtype.val hErase
    have hEraseFinset : G.1.erase v.1 = F.1 := hEraseVal
    have hIns : insert v.1 F.1 = G.1 := by
      calc
        insert v.1 F.1 = insert v.1 (G.1.erase v.1) :=
          congrArg (insert v.1) hEraseVal.symm
        _ = G.1 := Finset.insert_erase v.2
    have hRank : simplicialRankBelow G.1 v.1 = simplicialRankBelow F.1 v.1 := by
      calc
        simplicialRankBelow G.1 v.1 = simplicialRankBelow (G.1.erase v.1) v.1 := by
          simp only [simplicialRankBelow]
          rw [Finset.filter_erase]
          simp
        _ = simplicialRankBelow F.1 v.1 := by
          have h := congrArg (fun s : Finset V => (s.filter (· < v.1)).card) hEraseFinset
          simpa [simplicialRankBelow] using h
    simp [hErase, hNot, hIns, hRank]
  · have hNotIns : ¬ (v.1 ∉ F.1 ∧ insert v.1 F.1 = G.1) := by
      rintro ⟨hNot, hIns⟩
      apply hErase
      apply Subtype.ext
      calc
        G.1.erase v.1 = (insert v.1 F.1).erase v.1 := congrArg (fun s => s.erase v.1) hIns.symm
        _ = F.1 := Finset.erase_insert hNot
    simp [hErase, hNotIns]

omit [LinearOrder V] in
/-- Above the ambient vertex cardinality there are no face indices, hence the
actual cochain module is zero. -/
theorem simplicialCochain_subsingleton_of_card_lt {n : ℕ}
    (h : Fintype.card V < n) : Subsingleton (K.SimplicialCochain R n) := by
  classical
  let : IsEmpty (K.SimplicialFaceIndex n) := ⟨fun F => by
    have hcard := F.1.card_le_univ
    rw [F.2.2] at hcard
    exact (Nat.not_le_of_gt h) hcard⟩
  infer_instance

omit [LinearOrder V] in
theorem simplicialCochain_isZero_of_card_lt {n : ℕ}
    (h : Fintype.card V < n) :
    CategoryTheory.Limits.IsZero (ModuleCat.of R (K.SimplicialCochain R n)) :=
  ModuleCat.isZero_iff_subsingleton.mpr (K.simplicialCochain_subsingleton_of_card_lt R h)

omit [LinearOrder V] in
/-- Above the largest actual face cardinality, the cochain term is zero.
This bound uses actual faces, so it also applies in the presence of ghosts. -/
theorem simplicialCochain_subsingleton_of_maxFaceCard_lt {n : ℕ}
    (h : K.maxFaceCard < n) : Subsingleton (K.SimplicialCochain R n) := by
  classical
  let : IsEmpty (K.SimplicialFaceIndex n) := ⟨fun F => by
    have hcard := K.card_le_maxFaceCard F.2.1
    rw [F.2.2] at hcard
    exact (Nat.not_le_of_gt h) hcard⟩
  infer_instance

omit [LinearOrder V] in
theorem simplicialCochain_isZero_of_maxFaceCard_lt {n : ℕ}
    (h : K.maxFaceCard < n) :
    CategoryTheory.Limits.IsZero (ModuleCat.of R (K.SimplicialCochain R n)) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (K.simplicialCochain_subsingleton_of_maxFaceCard_lt R h)

/-- The actual augmented simplicial cochain complex in face-cardinality
indexing. Index zero is the empty-face/degree-minus-one term. -/
noncomputable def simplicialCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (K.SimplicialCochain R n))
    (fun n => ModuleCat.ofHom (K.simplicialDifferential R n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact K.simplicialDifferential_comp_eq_zero R n)

omit [Fintype V] in
@[simp]
theorem simplicialCochainComplex_X (n : ℕ) :
    (K.simplicialCochainComplex R).X n = ModuleCat.of R (K.SimplicialCochain R n) := rfl

omit [Fintype V] in
@[simp]
theorem simplicialCochainComplex_d (n : ℕ) :
    (K.simplicialCochainComplex R).d n (n + 1) =
      ModuleCat.ofHom (K.simplicialDifferential R n) := by
  simp [simplicialCochainComplex, CochainComplex.of_d]

/-! ## Integer reindexing and cohomology cutoffs -/

open CategoryTheory CategoryTheory.Limits

/-- The cardinality index `n` is sent to reduced degree `n - 1`. Keep this as
an abbreviation so Mathlib can see the embedding's relative-iff instance. -/
abbrev simplicialCochainDegreeEmbedding := ComplexShape.embeddingUpIntGE (-1)

/-- Extend the checked face-cardinality complex by zero below degree `-1`. -/
noncomputable def simplicialCochainComplexInt : CochainComplex (ModuleCat R) ℤ :=
  (K.simplicialCochainComplex R).extend simplicialCochainDegreeEmbedding

/-- The integer-indexed term in reduced degree `i = n - 1`. -/
noncomputable def simplicialCochainComplexIntXIso {n : ℕ} {i : ℤ}
    (h : (n : ℤ) - 1 = i) :
    (K.simplicialCochainComplexInt R).X i ≅
      ModuleCat.of R (K.SimplicialCochain R n) :=
  (K.simplicialCochainComplex R).extendXIso simplicialCochainDegreeEmbedding
    (by simpa [simplicialCochainDegreeEmbedding, add_comm, sub_eq_add_neg] using h)

/-- Restriction along `n ↦ n - 1` recovers the natural face-cardinality
complex, with the term isomorphisms as components. -/
noncomputable def simplicialCochainComplexIntRestrictionIso :
    (K.simplicialCochainComplexInt R).restriction simplicialCochainDegreeEmbedding ≅
      K.simplicialCochainComplex R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (K.simplicialCochainComplex R).extendXIso
      simplicialCochainDegreeEmbedding rfl)
    (by
      intro i j hij
      change _ = ((K.simplicialCochainComplex R).extend
        simplicialCochainDegreeEmbedding).d _ _ ≫ _
      rw [HomologicalComplex.extend_d_eq _ simplicialCochainDegreeEmbedding rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl)

/-- Homology in integer degree `i = n - 1` is canonically the checked
face-cardinality homology in index `n`. -/
noncomputable def simplicialCochainComplexIntHomologyIso {n : ℕ} {i : ℤ}
    (h : (n : ℤ) - 1 = i) :
    (K.simplicialCochainComplexInt R).homology i ≅
      (K.simplicialCochainComplex R).homology n :=
  (K.simplicialCochainComplex R).extendHomologyIso
    simplicialCochainDegreeEmbedding
    (by simpa [simplicialCochainDegreeEmbedding, add_comm, sub_eq_add_neg] using h)

omit [Fintype V] in
/-- The integer differential in reduced degree `n - 1` is the existing
face-cardinality differential under the term identifications. -/
theorem simplicialCochainComplexInt_d {n : ℕ} :
    (K.simplicialCochainComplexInt R).d ((n : ℤ) - 1) n ≫
        (K.simplicialCochainComplexIntXIso R (n := n + 1) (i := (n : ℤ)) (by omega)).hom =
      (K.simplicialCochainComplexIntXIso R (n := n) (i := (n : ℤ) - 1) rfl).hom ≫
        (K.simplicialCochainComplex R).d n (n + 1) := by
  have hsource : simplicialCochainDegreeEmbedding.f n = (n : ℤ) - 1 := by
    simp [simplicialCochainDegreeEmbedding]
    omega
  have htarget : simplicialCochainDegreeEmbedding.f (n + 1) = (n : ℤ) := by
    simp [simplicialCochainDegreeEmbedding]
  change ((K.simplicialCochainComplex R).extend simplicialCochainDegreeEmbedding).d
      ((n : ℤ) - 1) n ≫ _ = _
  rw [HomologicalComplex.extend_d_eq _ simplicialCochainDegreeEmbedding hsource htarget]
  change ((K.simplicialCochainComplex R).extendXIso
      simplicialCochainDegreeEmbedding hsource).hom ≫
      (K.simplicialCochainComplex R).d n (n + 1) ≫
        ((K.simplicialCochainComplex R).extendXIso
          simplicialCochainDegreeEmbedding htarget).inv ≫
            ((K.simplicialCochainComplex R).extendXIso
              simplicialCochainDegreeEmbedding htarget).hom =
    ((K.simplicialCochainComplex R).extendXIso
      simplicialCochainDegreeEmbedding hsource).hom ≫
      (K.simplicialCochainComplex R).d n (n + 1)
  rw [← Category.assoc]
  rw [Iso.inv_hom_id]
  simp only [Category.comp_id]

omit [Fintype V] in
/-- Integer degrees below `-1` lie outside the embedding's image, so their
cochain modules are zero. -/
theorem simplicialCochainComplexInt_isZero_of_lt_minus_one {i : ℤ}
    (hi : i < -1) : IsZero ((K.simplicialCochainComplexInt R).X i) := by
  apply (K.simplicialCochainComplex R).isZero_extend_X
    simplicialCochainDegreeEmbedding i
  intro n h
  change (-1 : ℤ) + (n : ℤ) = i at h
  omega

omit [Fintype V] in
/-- Every differential whose source is below `-1` is the zero morphism. -/
theorem simplicialCochainComplexInt_d_eq_zero_of_lt_minus_one {i : ℤ}
    (hi : i < -1) :
    (K.simplicialCochainComplexInt R).d i (i + 1) = 0 :=
  (K.simplicialCochainComplexInt_isZero_of_lt_minus_one R hi).eq_of_src _ _

omit [Fintype V] in
/-- Integer homology below degree `-1` vanishes because its term is zero. -/
theorem simplicialCochainComplexInt_homology_isZero_of_lt_minus_one {i : ℤ}
    (hi : i < -1) : IsZero ((K.simplicialCochainComplexInt R).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialCochainComplexInt_isZero_of_lt_minus_one R hi)).isZero_homology

/-- Natural face-cardinality homology vanishes above the ambient vertex
count. -/
theorem simplicialCochainComplex_homology_isZero_of_card_lt {n : ℕ}
    (hn : Fintype.card V < n) :
    IsZero ((K.simplicialCochainComplex R).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialCochain_isZero_of_card_lt R hn)).isZero_homology

/-- For `i ≥ -1`, natural cardinality `(i + 1).toNat` corresponds to
integer reduced degree `i`. -/
theorem simplicialCochainInt_natDegree {i : ℤ}
    (hi : -1 ≤ i) : (((i + 1).toNat : ℕ) : ℤ) - 1 = i := by
  have h : 0 ≤ i + 1 := by omega
  rw [Int.toNat_of_nonneg h]
  omega

omit [LinearOrder V] in
/-- The integer inequality `|V| - 1 < i` implies the natural cardinality
bound `|V| < (i + 1).toNat`. -/
theorem simplicialCochainInt_natBound {i : ℤ}
    (hi : (Fintype.card V : ℤ) - 1 < i) :
    Fintype.card V < (i + 1).toNat := by
  have h : 0 ≤ i + 1 := by omega
  have hcast := Int.toNat_of_nonneg h
  omega

/-- Integer cochain modules vanish above `|V| - 1`, by transport from the
natural high-cardinality zero-term theorem. -/
theorem simplicialCochainComplexInt_isZero_of_card_lt {i : ℤ}
    (hi : (Fintype.card V : ℤ) - 1 < i) :
    IsZero ((K.simplicialCochainComplexInt R).X i) := by
  have hlow : -1 ≤ i := by omega
  let n := (i + 1).toNat
  have hdegree : (n : ℤ) - 1 = i := by
    dsimp [n]
    exact simplicialCochainInt_natDegree hlow
  have hcard : Fintype.card V < n := by
    dsimp [n]
    exact simplicialCochainInt_natBound hi
  exact IsZero.of_iso
    (K.simplicialCochain_isZero_of_card_lt R hcard)
    (K.simplicialCochainComplexIntXIso R hdegree)

/-- Integer homology vanishes above `|V| - 1`, by comparison with natural
face-cardinality homology. -/
theorem simplicialCochainComplexInt_homology_isZero_of_card_lt {i : ℤ}
    (hi : (Fintype.card V : ℤ) - 1 < i) :
    IsZero ((K.simplicialCochainComplexInt R).homology i) := by
  have hlow : -1 ≤ i := by omega
  let n := (i + 1).toNat
  have hdegree : (n : ℤ) - 1 = i := by
    dsimp [n]
    exact simplicialCochainInt_natDegree hlow
  have hcard : Fintype.card V < n := by
    dsimp [n]
    exact simplicialCochainInt_natBound hi
  exact IsZero.of_iso
    (K.simplicialCochainComplex_homology_isZero_of_card_lt R hcard)
    (K.simplicialCochainComplexIntHomologyIso R hdegree)

/-- Natural cohomology vanishes above the largest actual face cardinality. -/
theorem simplicialCochainComplex_homology_isZero_of_maxFaceCard_lt {n : ℕ}
    (hn : K.maxFaceCard < n) :
    IsZero ((K.simplicialCochainComplex R).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialCochain_isZero_of_maxFaceCard_lt R hn)).isZero_homology

/-- Integer cochain terms vanish above the complex's actual dimension. -/
theorem simplicialCochainComplexInt_isZero_of_dimension_lt {i : ℤ}
    (hi : K.dimension < i) : IsZero ((K.simplicialCochainComplexInt R).X i) := by
  have hlow : -1 ≤ i := by unfold dimension at hi; omega
  have hdegree := simplicialCochainInt_natDegree hlow
  have hcard : K.maxFaceCard < (i + 1).toNat := by
    unfold dimension at hi
    omega
  exact IsZero.of_iso (K.simplicialCochain_isZero_of_maxFaceCard_lt R hcard)
    (K.simplicialCochainComplexIntXIso R hdegree)

/-- Integer reduced cohomology vanishes above the actual simplicial dimension. -/
theorem simplicialCochainComplexInt_homology_isZero_of_dimension_lt {i : ℤ}
    (hi : K.dimension < i) :
    IsZero ((K.simplicialCochainComplexInt R).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialCochainComplexInt_isZero_of_dimension_lt R hi)).isZero_homology

/-- The actual degree-zero homology object is canonically the kernel of the
augmentation cochain differential. The incoming map is zero at index zero. -/
noncomputable def simplicialCochainHomologyZeroIsoKer :
    (K.simplicialCochainComplex R).homology 0 ≅
      ModuleCat.of R (LinearMap.ker (K.simplicialDifferential R 0)) := by
  let C := K.simplicialCochainComplex R
  let d := ModuleCat.ofHom (K.simplicialDifferential R 0)
  exact C.isoHomologyπ₀.symm ≪≫
    (C.cyclesIsKernel 0 1 (by simp)).conePointUniqueUpToIso (ModuleCat.kernelIsLimit d)

/-- If the complex has no actual vertices, its degree-minus-one cohomology
is the coefficient ring. This is the homology object of the constructed
cochain complex, not merely an index-set calculation. -/
noncomputable def simplicialCochainHomologyZeroEquivOfNoVertices
    (hV : ∀ v : V, ({v} : Finset V) ∉ K.faces) :
    (K.simplicialCochainComplex R).homology 0 ≃ₗ[R] R := by
  have hd : K.simplicialDifferential R 0 = 0 :=
    K.simplicialDifferential_zero_of_no_vertices R hV
  have hker : (K.simplicialDifferential R 0).ker = ⊤ := by
    rw [hd]
    simp
  exact (K.simplicialCochainHomologyZeroIsoKer R).toLinearEquiv.trans <|
    (LinearEquiv.ofEq _ _ hker).trans <|
      Submodule.topEquiv.trans (K.simplicialCochainZeroEquiv R)

omit [Fintype V] in
/-- If an actual vertex exists, the degree-minus-one cohomology object of
the augmented cochain complex is zero. Evaluation at that singleton detects
the scalar at the empty face. -/
theorem simplicialCochainHomologyZero_isZero_of_vertex {v : V}
    (hv : ({v} : Finset V) ∈ K.faces) :
    CategoryTheory.Limits.IsZero ((K.simplicialCochainComplex R).homology 0) := by
  let d := K.simplicialDifferential R 0
  have hinj : Function.Injective d := by
    intro f g hfg
    have hval : f ⟨∅, K.empty_mem, by simp⟩ = g ⟨∅, K.empty_mem, by simp⟩ := by
      have h := congrFun hfg ⟨{v}, hv, by simp⟩
      change K.simplicialDifferential R 0 f ⟨{v}, hv, by simp⟩ =
        K.simplicialDifferential R 0 g ⟨{v}, hv, by simp⟩ at h
      rw [simplicialDifferential_apply] at h
      simp [simplicialRankBelow, Finset.filter_singleton,
        simplicialFaceEraseIndex] at h
      simpa using h
    funext F
    have hF : F = (⟨∅, K.empty_mem, by simp⟩ : K.SimplicialFaceIndex 0) :=
      K.simplicialFaceIndexZeroUnique.uniq F
    subst F
    exact hval
  have hker : d.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsub : Subsingleton d.ker := by rw [hker]; infer_instance
  have hz : CategoryTheory.Limits.IsZero (ModuleCat.of R d.ker) :=
    ModuleCat.isZero_iff_subsingleton.mpr hsub
  exact CategoryTheory.Limits.IsZero.of_iso hz
    (K.simplicialCochainHomologyZeroIsoKer R)

/-- Integer degree `-1` cohomology is `R` when there are no actual
vertices, transported from natural cardinality index zero. -/
noncomputable def simplicialCochainComplexIntHomologyMinusOneEquivOfNoVertices
    (hV : ∀ v : V, ({v} : Finset V) ∉ K.faces) :
    (K.simplicialCochainComplexInt R).homology (-1) ≃ₗ[R] R := by
  have hdegree : (0 : ℤ) - 1 = -1 := by norm_num
  exact (K.simplicialCochainComplexIntHomologyIso R hdegree).toLinearEquiv.trans
    (K.simplicialCochainHomologyZeroEquivOfNoVertices R hV)

omit [Fintype V] in
/-- An actual vertex makes integer degree `-1` cohomology zero. -/
theorem simplicialCochainComplexIntHomologyMinusOne_isZero_of_vertex {v : V}
    (hv : ({v} : Finset V) ∈ K.faces) :
    IsZero ((K.simplicialCochainComplexInt R).homology (-1)) := by
  have hdegree : (0 : ℤ) - 1 = -1 := by norm_num
  exact IsZero.of_iso
    (K.simplicialCochainHomologyZero_isZero_of_vertex R hv)
    (K.simplicialCochainComplexIntHomologyIso R hdegree)

end Reisner.Complex
