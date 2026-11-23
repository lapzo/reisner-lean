import Reisner

/-!
Regression checks for the augmented face-cardinality cochain complex.
These include empty ambient sets, ghost vertices, actual vertices, and rings
of characteristic two and one.
-/

open Reisner.Complex
open CategoryTheory CategoryTheory.Limits

private def onlyEmpty : Reisner.Complex (Fin 1) where
  faces := LowerSet.Iic ∅
  empty_mem := by simp

private def fullSingleton : Reisner.Complex (Fin 1) where
  faces := ⊤
  empty_mem := by simp

noncomputable example (R : Type) [CommRing R] (K : Reisner.Complex PEmpty) :
    K.SimplicialCochain R 0 ≃ₗ[R] R :=
  K.simplicialCochainZeroEquiv R

noncomputable example (R : Type) [CommRing R] (K : Reisner.Complex PEmpty) :
    (K.simplicialCochainComplex R).homology 0 ≃ₗ[R] R :=
  K.simplicialCochainHomologyZeroEquivOfNoVertices R (by
    intro v
    exact isEmptyElim v)

example (K : Reisner.Complex PEmpty) (R : Type) [CommRing R] :
    CategoryTheory.Limits.IsZero
      (ModuleCat.of R (K.SimplicialCochain R 1)) := by
  exact K.simplicialCochain_isZero_of_card_lt R (by simp)

example (R : Type) [CommRing R] :
    onlyEmpty.simplicialDifferential R 0 = 0 := by
  apply onlyEmpty.simplicialDifferential_zero_of_no_vertices R
  intro v
  change ({v} : Finset (Fin 1)) ∉ LowerSet.Iic ∅
  simp

noncomputable example (R : Type) [CommRing R] :
    (onlyEmpty.simplicialCochainComplex R).homology 0 ≃ₗ[R] R :=
  onlyEmpty.simplicialCochainHomologyZeroEquivOfNoVertices R (by
    intro v
    change ({v} : Finset (Fin 1)) ∉ LowerSet.Iic ∅
    simp)

noncomputable example :
    (onlyEmpty.simplicialCochainComplex (ZMod 1)).homology 0 ≃ₗ[ZMod 1] ZMod 1 :=
  onlyEmpty.simplicialCochainHomologyZeroEquivOfNoVertices (R := ZMod 1) (by
    intro v
    change ({v} : Finset (Fin 1)) ∉ LowerSet.Iic ∅
    simp)

example (R : Type) [CommRing R] :
    CategoryTheory.Limits.IsZero ((fullSingleton.simplicialCochainComplex R).homology 0) :=
  fullSingleton.simplicialCochainHomologyZero_isZero_of_vertex R
    (v := 0) (by simp [fullSingleton])

example (r : ZMod 2) :
    fullSingleton.simplicialDifferential (R := ZMod 2) 0 (fun _ => r)
      ⟨{0}, by simp [fullSingleton], by simp⟩ = r :=
  fullSingleton.simplicialDifferential_zero_apply (R := ZMod 2) r _

example (r : ZMod 1) :
    fullSingleton.simplicialDifferential (R := ZMod 1) 0 (fun _ => r)
      ⟨{0}, by simp [fullSingleton], by simp⟩ = r :=
  fullSingleton.simplicialDifferential_zero_apply (R := ZMod 1) r _

noncomputable example (R : Type) [CommRing R] :
    fullSingleton.simplicialDifferential R 0
      (fullSingleton.simplicialCochainBasis R 0
        ⟨∅, by simp [fullSingleton], by simp⟩)
      ⟨{0}, by simp [fullSingleton], by simp⟩ = 1 := by
  classical
  rw [fullSingleton.simplicialDifferential_basis_insertion_apply]
  simp [simplicialRankBelow, Finset.filter_singleton]

example (K : Reisner.Complex (Fin 1)) (n : ℕ)
    (h : Fintype.card (Fin 1) < n) :
    CategoryTheory.Limits.IsZero
      (ModuleCat.of (ZMod 2) (K.SimplicialCochain (ZMod 2) n)) :=
  K.simplicialCochain_isZero_of_card_lt (ZMod 2) h

example (K : Reisner.Complex (Fin 1)) (n : ℕ)
    (h : Fintype.card (Fin 1) < n) :
    CategoryTheory.Limits.IsZero
      (ModuleCat.of (ZMod 1) (K.SimplicialCochain (ZMod 1) n)) :=
  K.simplicialCochain_isZero_of_card_lt (ZMod 1) h

example (R : Type) [CommRing R] (K : Reisner.Complex PEmpty) :
    IsZero ((K.simplicialCochainComplexInt R).X (-2)) :=
  K.simplicialCochainComplexInt_isZero_of_lt_minus_one R (by norm_num)

example (R : Type) [CommRing R] (K : Reisner.Complex PEmpty) :
    IsZero ((K.simplicialCochainComplexInt R).homology (-2)) :=
  K.simplicialCochainComplexInt_homology_isZero_of_lt_minus_one R (by norm_num)

example (R : Type) [CommRing R] (K : Reisner.Complex PEmpty) :
    (K.simplicialCochainComplexInt R).d (-2) (-1) = 0 :=
  K.simplicialCochainComplexInt_d_eq_zero_of_lt_minus_one R (by norm_num)

noncomputable example (R : Type) [CommRing R] :
    (onlyEmpty.simplicialCochainComplexInt R).homology (-1) ≃ₗ[R] R :=
  onlyEmpty.simplicialCochainComplexIntHomologyMinusOneEquivOfNoVertices R (by
    intro v
    change ({v} : Finset (Fin 1)) ∉ LowerSet.Iic ∅
    simp)

noncomputable example :
    (onlyEmpty.simplicialCochainComplexInt (ZMod 1)).homology (-1) ≃ₗ[ZMod 1] ZMod 1 :=
  onlyEmpty.simplicialCochainComplexIntHomologyMinusOneEquivOfNoVertices
    (R := ZMod 1) (by
      intro v
      change ({v} : Finset (Fin 1)) ∉ LowerSet.Iic ∅
      simp)

example (R : Type) [CommRing R] :
    IsZero ((fullSingleton.simplicialCochainComplexInt R).homology (-1)) :=
  fullSingleton.simplicialCochainComplexIntHomologyMinusOne_isZero_of_vertex R
    (v := 0) (by simp [fullSingleton])

example (R : Type) [CommRing R] :
    IsZero ((fullSingleton.simplicialCochainComplexInt R).X 1) :=
  fullSingleton.simplicialCochainComplexInt_isZero_of_card_lt R (by norm_num)

example (R : Type) [CommRing R] :
    IsZero ((fullSingleton.simplicialCochainComplexInt R).homology 1) :=
  fullSingleton.simplicialCochainComplexInt_homology_isZero_of_card_lt R (by norm_num)

noncomputable example (R : Type) [CommRing R] :
    (fullSingleton.simplicialCochainComplexInt R).restriction
      simplicialCochainDegreeEmbedding ≅ fullSingleton.simplicialCochainComplex R :=
  fullSingleton.simplicialCochainComplexIntRestrictionIso R

noncomputable example (R : Type) [CommRing R] :
    (fullSingleton.simplicialCochainComplexInt R).X (-1) ≅
      ModuleCat.of R (fullSingleton.SimplicialCochain R 0) :=
  fullSingleton.simplicialCochainComplexIntXIso R (n := 0) (i := -1) (by norm_num)
