module

public import Reisner.LocalCohomology
public import Reisner.StanleyReisner
public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Depth at the augmentation ideal of a face ring

For a finite ambient vertex type and a field of coefficients, the Krull dimension of
the augmentation localization is the maximum face cardinality. Its depth equals this
dimension exactly when its maximal-ideal local cohomology vanishes below that cutoff.
-/

@[expose] public section

namespace Reisner.Complex

universe u v

private theorem length_le_ringKrullDim_of_isRegular {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (rs : List R) (hreg : RingTheory.Sequence.IsRegular R rs) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim R := by
  have hproper : Ideal.ofList rs ≠ ⊤ := by simpa using hreg.top_ne_smul.symm
  let := Ideal.Quotient.nontrivial_iff.mpr hproper
  rw [← ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg]
  exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial

variable {V : Type u} [Finite V] (K : Complex V) (k : Type v) [Field k]

local notation "B" => Localization.AtPrime (K.faceRingAugmentationIdeal k)

/-- The depth of the augmentation localization is at most the maximum face cardinality. -/
theorem faceRing_atAugmentation_depth_le :
    IsLocalRing.depth (R := B) (ModuleCat.of B B) ≤ K.maxFaceCard := by
  let := K.faceRing_isNoetherianRing k
  rw [IsLocalRing.depth_eq_sSup_length_isRegular]
  apply sSup_le
  rintro _ ⟨rs, hreg, _, rfl⟩
  apply WithBot.coe_le_coe.mp
  calc
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim B := length_le_ringKrullDim_of_isRegular rs hreg
    _ = K.maxFaceCard := K.faceRing_atAugmentation_ringKrullDim k

/-- The local Cohen–Macaulay condition at the augmentation ideal is equivalent to
vanishing of maximal-ideal Ext-colimit local cohomology below the dimension. -/
theorem faceRing_atAugmentation_depth_eq_iff_localCohomology_vanishes :
    (IsLocalRing.depth (R := B) (ModuleCat.of B B) : WithBot ℕ∞) = ringKrullDim B ↔
      ∀ q : ℕ, q < K.maxFaceCard → Subsingleton
        ((depthExtLocalCohomology (R := B) (IsLocalRing.maximalIdeal B) q).obj
          (ModuleCat.of B B)) := by
  let := K.faceRing_isNoetherianRing k
  rw [K.faceRing_atAugmentation_ringKrullDim k, ← le_depth_iff_localCohomology_vanishes]
  change _ = ((K.maxFaceCard : ℕ∞) : WithBot ℕ∞) ↔ _
  rw [WithBot.coe_eq_coe]
  exact ⟨fun h => h.ge, fun h => le_antisymm (K.faceRing_atAugmentation_depth_le k) h⟩

end Reisner.Complex
