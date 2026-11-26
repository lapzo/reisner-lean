module

public import Reisner.SimplicialCochain
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Augmented simplicial chains

The chain module in face-cardinality degree `n` is the linear dual of the
project's cochain module in that degree. Its basis is indexed by actual
`n`-element faces. The boundary is the dual of the signed cochain
differential, so the empty face is the chain in degree zero (reduced degree
`-1`) and ghost vertices do not enter the basis.
-/

@[expose] public section

namespace Reisner.Complex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} (K : Reisner.Complex V)
variable (k : Type v) [Field k] [Fintype V] [LinearOrder V]

/-- Augmented simplicial chains in face-cardinality degree `n`. -/
abbrev SimplicialChain (n : ℕ) :=
  Module.Dual k (K.SimplicialCochain k n)

/-- The coordinate basis of chains, dual to the coordinate cochain basis. -/
noncomputable def simplicialChainBasis (n : ℕ) :
    Module.Basis (K.SimplicialFaceIndex n) k (K.SimplicialChain k n) := by
  classical
  exact (K.simplicialCochainBasis k n).dualBasis

/-- Each chain term is finite-dimensional, with one basis vector for each
actual face of the given cardinality. -/
theorem simplicialChain_finiteDimensional (n : ℕ) :
    FiniteDimensional k (K.SimplicialChain k n) := by
  classical
  exact (K.simplicialChainBasis k n).finiteDimensional_of_finite

/-- The dimension of a chain term is the number of actual faces in that
cardinality. -/
theorem simplicialChain_finrank (n : ℕ) :
    Module.finrank k (K.SimplicialChain k n) = Nat.card (K.SimplicialFaceIndex n) := by
  classical
  rw [Module.finrank_eq_card_basis (K.simplicialChainBasis k n)]
  exact (Nat.card_eq_fintype_card (α := K.SimplicialFaceIndex n)).symm

/-- The canonical evaluation isomorphism identifies each cochain term with
the dual of its chain term. Its value is evaluation of a chain functional on
the cochain. -/
noncomputable def simplicialCochainEvalEquivDualChain (n : ℕ) :
    K.SimplicialCochain k n ≃ₗ[k] Module.Dual k (K.SimplicialChain k n) := by
  classical
  let b := K.simplicialCochainBasis k n
  exact b.toDualEquiv.trans b.dualBasis.toDualEquiv

@[simp]
theorem simplicialCochainEvalEquivDualChain_apply (n : ℕ)
    (f : K.SimplicialCochain k n) :
    K.simplicialCochainEvalEquivDualChain k n f =
      Module.Dual.eval k (K.SimplicialCochain k n) f := by
  classical
  let b := K.simplicialCochainBasis k n
  change b.dualBasis.toDualEquiv (b.toDualEquiv f) =
    Module.Dual.eval k (K.SimplicialCochain k n) f
  exact DFunLike.congr_fun (b.toDual_toDual) f

/-- The augmented simplicial boundary, dual to cochain deletion. -/
noncomputable def simplicialBoundary (n : ℕ) :
    K.SimplicialChain k (n + 1) →ₗ[k] K.SimplicialChain k n :=
  (K.simplicialDifferential k n).dualMap

/-- The canonical evaluation pairings commute with the cochain differential
and the dual chain boundary. This identifies the cochain complex termwise
with the double dual of the chain complex. -/
theorem simplicialCochainEvalEquivDualChain_naturality (n : ℕ) :
    (K.simplicialBoundary k n).dualMap.comp
        (K.simplicialCochainEvalEquivDualChain k n).toLinearMap =
      (K.simplicialCochainEvalEquivDualChain k (n + 1)).toLinearMap.comp
        (K.simplicialDifferential k n) := by
  ext f φ
  simp [simplicialBoundary, LinearMap.dualMap_apply,
    simplicialCochainEvalEquivDualChain_apply]

/-- The dual differentials square to zero, giving the chain-complex law. -/
theorem simplicialBoundary_comp_eq_zero (n : ℕ) :
    (K.simplicialBoundary k n).comp (K.simplicialBoundary k (n + 1)) = 0 := by
  rw [simplicialBoundary, simplicialBoundary, LinearMap.dualMap_comp_dualMap]
  rw [K.simplicialDifferential_comp_eq_zero k n]
  ext φ x
  simp [LinearMap.dualMap_apply]

/-- The augmented simplicial chain complex. Its degree `n` term is indexed
by `n`-element faces, so degree zero is the empty face. -/
noncomputable def simplicialChainComplex : ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of
    (fun n => ModuleCat.of k (K.SimplicialChain k n))
    (fun n => ModuleCat.ofHom (K.simplicialBoundary k n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact K.simplicialBoundary_comp_eq_zero k n)

@[simp]
theorem simplicialChainComplex_X (n : ℕ) :
    (K.simplicialChainComplex k).X n = ModuleCat.of k (K.SimplicialChain k n) := rfl

@[simp]
theorem simplicialChainComplex_d (n : ℕ) :
    (K.simplicialChainComplex k).d (n + 1) n =
      ModuleCat.ofHom (K.simplicialBoundary k n) := by
  simp [simplicialChainComplex, ChainComplex.of_d]

/-! ## Integer reduced-degree indexing -/

/-- Map face-cardinality degree `n` to reduced chain degree `n - 1`. -/
abbrev simplicialChainDegreeEmbedding :=
  ComplexShape.embeddingUpIntGE (-1 : ℤ) |>.op

/-- Extend the augmented chain complex by zero below reduced degree `-1`. -/
noncomputable def simplicialChainComplexInt : ChainComplex (ModuleCat k) ℤ :=
  (K.simplicialChainComplex k).extend simplicialChainDegreeEmbedding

/-- The chain term in reduced degree `i = n - 1`. -/
noncomputable def simplicialChainComplexIntXIso {n : ℕ} {i : ℤ}
    (h : (n : ℤ) - 1 = i) :
    (K.simplicialChainComplexInt k).X i ≅
      ModuleCat.of k (K.SimplicialChain k n) :=
  (K.simplicialChainComplex k).extendXIso simplicialChainDegreeEmbedding
    (by simpa [simplicialChainDegreeEmbedding, add_comm, sub_eq_add_neg] using h)

/-- Integer chain homology in reduced degree `i = n - 1` agrees with the
face-cardinality chain homology in index `n`. -/
noncomputable def simplicialChainComplexIntHomologyIso {n : ℕ} {i : ℤ}
    (h : (n : ℤ) - 1 = i) :
    (K.simplicialChainComplexInt k).homology i ≅
      (K.simplicialChainComplex k).homology n :=
  (K.simplicialChainComplex k).extendHomologyIso simplicialChainDegreeEmbedding
    (by simpa [simplicialChainDegreeEmbedding, add_comm, sub_eq_add_neg] using h)

/-- Integer chain terms below reduced degree `-1` are zero. -/
theorem simplicialChainComplexInt_isZero_of_lt_minus_one {i : ℤ}
    (hi : i < -1) : IsZero ((K.simplicialChainComplexInt k).X i) := by
  apply (K.simplicialChainComplex k).isZero_extend_X simplicialChainDegreeEmbedding i
  intro n h
  change (-1 : ℤ) + (n : ℤ) = i at h
  omega

/-- Chain homology below reduced degree `-1` vanishes. -/
theorem simplicialChainComplexInt_homology_isZero_of_lt_minus_one {i : ℤ}
    (hi : i < -1) : IsZero ((K.simplicialChainComplexInt k).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialChainComplexInt_isZero_of_lt_minus_one k hi)).isZero_homology

omit [LinearOrder V] in
/-- A chain term above the ambient vertex cardinality is zero. -/
theorem simplicialChain_isZero_of_card_lt {n : ℕ}
    (hn : Fintype.card V < n) :
    IsZero (ModuleCat.of k (K.SimplicialChain k n)) := by
  let := K.simplicialCochain_subsingleton_of_card_lt k hn
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

omit [LinearOrder V] in
/-- A chain term above the largest actual face cardinality is zero. -/
theorem simplicialChain_isZero_of_maxFaceCard_lt {n : ℕ}
    (hn : K.maxFaceCard < n) :
    IsZero (ModuleCat.of k (K.SimplicialChain k n)) := by
  let := K.simplicialCochain_subsingleton_of_maxFaceCard_lt k hn
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- Natural chain homology vanishes above the ambient vertex count. -/
theorem simplicialChainComplex_homology_isZero_of_card_lt {n : ℕ}
    (hn : Fintype.card V < n) :
    IsZero ((K.simplicialChainComplex k).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialChain_isZero_of_card_lt k hn)).isZero_homology

/-- Natural chain homology vanishes above the largest actual face cardinality. -/
theorem simplicialChainComplex_homology_isZero_of_maxFaceCard_lt {n : ℕ}
    (hn : K.maxFaceCard < n) :
    IsZero ((K.simplicialChainComplex k).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialChain_isZero_of_maxFaceCard_lt k hn)).isZero_homology

/-- Integer chain terms vanish above the ambient upper degree `|V| - 1`. -/
theorem simplicialChainComplexInt_isZero_of_card_lt {i : ℤ}
    (hi : (Fintype.card V : ℤ) - 1 < i) :
    IsZero ((K.simplicialChainComplexInt k).X i) := by
  have hlow : -1 ≤ i := by omega
  exact IsZero.of_iso
    (K.simplicialChain_isZero_of_card_lt k (simplicialCochainInt_natBound hi))
    (K.simplicialChainComplexIntXIso k (simplicialCochainInt_natDegree hlow))

/-- Integer chain homology vanishes above the ambient upper degree. -/
theorem simplicialChainComplexInt_homology_isZero_of_card_lt {i : ℤ}
    (hi : (Fintype.card V : ℤ) - 1 < i) :
    IsZero ((K.simplicialChainComplexInt k).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialChainComplexInt_isZero_of_card_lt k hi)).isZero_homology

/-- Integer chain terms vanish above the actual simplicial dimension. -/
theorem simplicialChainComplexInt_isZero_of_dimension_lt {i : ℤ}
    (hi : K.dimension < i) : IsZero ((K.simplicialChainComplexInt k).X i) := by
  have hlow : -1 ≤ i := by unfold dimension at hi; omega
  have hdegree := simplicialCochainInt_natDegree hlow
  have hcard : K.maxFaceCard < (i + 1).toNat := by
    unfold dimension at hi
    omega
  exact IsZero.of_iso (K.simplicialChain_isZero_of_maxFaceCard_lt k hcard)
    (K.simplicialChainComplexIntXIso k hdegree)

/-- Integer reduced homology vanishes above the actual simplicial dimension. -/
theorem simplicialChainComplexInt_homology_isZero_of_dimension_lt {i : ℤ}
    (hi : K.dimension < i) :
    IsZero ((K.simplicialChainComplexInt k).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (K.simplicialChainComplexInt_isZero_of_dimension_lt k hi)).isZero_homology

/-- In finite dimension, exactness of two adjacent cochain differentials is
equivalent to exactness of the transposed chain differentials. -/
private lemma dual_range_eq_ker_iff {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module k X] [Module k Y] [Module k Z]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.range g.dualMap = LinearMap.ker f.dualMap ↔
      LinearMap.range f = LinearMap.ker g := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    Subspace.dualAnnihilator_inj, eq_comm]

/-- A face-cardinality cochain homology object is zero exactly when the
corresponding augmented chain homology object is zero. This is the vanishing
part of homology-cohomology duality; the canonical isomorphism on homology
groups is still a separate theorem. -/
theorem simplicialCochain_homology_isZero_iff_chain_homology_isZero
    (n : ℕ) :
    IsZero ((K.simplicialCochainComplex k).homology n) ↔
      IsZero ((K.simplicialChainComplex k).homology n) := by
  let A := K.simplicialCochainComplex k
  let B := K.simplicialChainComplex k
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  change A.ExactAt n ↔ B.ExactAt n
  cases n with
  | zero =>
    rw [A.exactAt_iff' (j := 0) (i := 0) (k := 1) (by simp) (by simp),
        B.exactAt_iff' (j := 0) (i := 1) (k := 0) (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker,
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', A, B,
      simplicialCochainComplex_X, simplicialChainComplex_X,
      simplicialCochainComplex_d, simplicialChainComplex_d, simplicialBoundary]
    rw [(K.simplicialCochainComplex k).shape 0 0 (by simp),
      (K.simplicialChainComplex k).shape 0 0 (by simp)]
    simp only [ModuleCat.hom_ofHom]
    change (0 : K.SimplicialCochain k 0 →ₗ[k] K.SimplicialCochain k 0).range =
        (K.simplicialDifferential k 0).ker ↔
      (K.simplicialDifferential k 0).dualMap.range =
        (0 : K.SimplicialChain k 0 →ₗ[k] K.SimplicialChain k 0).ker
    rw [LinearMap.range_zero, LinearMap.ker_zero, eq_comm,
      LinearMap.ker_eq_bot, LinearMap.range_eq_top,
      LinearMap.dualMap_surjective_iff]
  | succ m =>
    rw [A.exactAt_iff' (j := m + 1) (i := m) (k := m + 2) (by simp) (by simp),
        B.exactAt_iff' (j := m + 1) (i := m + 2) (k := m) (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker,
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simp only [A, B, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
      simplicialCochainComplex_X, simplicialChainComplex_X,
      simplicialCochainComplex_d, simplicialChainComplex_d,
      simplicialBoundary, ModuleCat.hom_ofHom]
    change (K.simplicialDifferential k m).range =
        (K.simplicialDifferential k (m + 1)).ker ↔
      (K.simplicialDifferential k (m + 1)).dualMap.range =
        (K.simplicialDifferential k m).dualMap.ker
    exact (dual_range_eq_ker_iff k _ _).symm

/-- Evaluating a chain boundary at a cochain gives the signed deletion
formula. This verifies that the dual-linear-map construction is the usual
augmented simplicial boundary on the face basis. -/
theorem simplicialBoundary_basis_apply {n : ℕ}
    (G : K.SimplicialFaceIndex (n + 1)) (f : K.SimplicialCochain k n) :
    K.simplicialBoundary k n (K.simplicialChainBasis k (n + 1) G) f =
      ∑ v : {v : V // v ∈ G.1},
        (-1 : k) ^ simplicialRankBelow G.1 v.1 *
          f (K.simplicialFaceEraseIndex G v) := by
  classical
  simp [simplicialBoundary, simplicialChainBasis, LinearMap.dualMap_apply,
    simplicialDifferential_apply, simplicialCochainBasis]

end Reisner.Complex
