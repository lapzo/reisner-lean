module

public import Reisner.GradedLocalTest
public import Reisner.SimplicialChain

/-!
# Reisner's criterion

Blueprint node `thm:reisner`. The statement uses the algebraic Cohen–Macaulay
predicate and the augmented simplicial chain complex. Its proof is open.
-/

@[expose] public section

namespace Reisner.Complex

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V] (K : Reisner.Complex V) (k : Type v) [Field k]

/-- For every face, the reduced homology of its link vanishes strictly below
the link's dimension. The empty face tests `K` itself. A facet has link
dimension `-1`, so its test involves only degrees below `-1`. -/
def LinkHomologyVanishesBelowDimension : Prop :=
  ∀ (σ : Finset V) (hσ : σ ∈ K.faces) (i : ℤ), i < (K.link σ hσ).dimension →
    Subsingleton (((K.link σ hσ).simplicialChainComplexInt k).homology i)

local instance : IsNoetherianRing (K.FaceRing k) := K.faceRing_isNoetherianRing k

/-- Reisner's criterion for a finite simplicial complex over a field.
The vertex order orients the chains. The statement includes ghost vertices
and the complex consisting of the empty face alone. The proof is open. -/
theorem reisner_criterion :
    IsCohenMacaulay (K.FaceRing k) ↔ K.LinkHomologyVanishesBelowDimension k := by
  sorry

end Reisner.Complex
