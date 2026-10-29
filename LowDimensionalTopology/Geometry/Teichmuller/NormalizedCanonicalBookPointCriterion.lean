module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalMarkedReverse
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFrickeRecovery
public import Mathlib.Tactic.Linarith

/-!
# Literal book coordinates and the given native marked point

Native marked equivalence preserves the unique positive-c first representatives.
Conversely, equal literal coordinates recover the marked point conditional only
on the two supplied models' explicit canonical last-pair alternation proofs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation Hyperbolic

namespace NormalizedCanonicalFuchsianModel
variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m n : MarkedRiemannSurface.{0, 0} R}

/-- Native marked equivalence preserves the literal first book coordinates;
the positive-c convention removes the individual special-linear signs. -/
theorem firstBookCoordinates_eq_of_equivalent
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (hmn : MarkedRiemannSurface.Equivalent m n) :
    P.firstBookCoordinates = Q.firstBookCoordinates := by
  have hselected (i : Fin (g - 1)) (b : Fin 2) :
      P.firstBookMatrix i b = Q.firstBookMatrix i b := by
    have hproj : realSLMobius (P.firstBookMatrix i b) =
        realSLMobius (Q.firstBookMatrix i b) :=
      (P.firstBookMatrix_mobius i b).trans
        ((P.generators_eq Q hmn (firstBookIndex i, b)).trans
          (Q.firstBookMatrix_mobius i b).symm)
    rcases (realSLMobius_eq_iff_sign (P.firstBookMatrix i b)
      (Q.firstBookMatrix i b)).mp hproj with h | h
    · exact h.symm
    · exfalso
      have hc := congrArg (fun A : RealSL => A 1 0) h
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at hc
      have hp := P.firstBookMatrix_lowerLeft_pos i b
      have hq := Q.firstBookMatrix_lowerLeft_pos i b
      linarith
  funext i
  exact Prod.ext (congrArg bookMatrixCoordinates (hselected i 0))
    (congrArg bookMatrixCoordinates (hselected i 1))

/-- For the given actual models, literal first book data characterize the
native marked point under the two explicit canonical alternation hypotheses. -/
theorem firstBookCoordinates_eq_iff_equivalent
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (hP : Unproved.Teichmuller.CanonicalLastPairAxisAlternation P)
    (hQ : Unproved.Teichmuller.CanonicalLastPairAxisAlternation Q) :
    P.firstBookCoordinates = Q.firstBookCoordinates ↔
      MarkedRiemannSurface.Equivalent m n := by
  constructor
  · intro hcoords
    exact P.equivalent_of_generators_eq Q
      (P.generators_eq_of_firstBookCoordinates Q hP hQ hcoords)
  · exact P.firstBookCoordinates_eq_of_equivalent Q

end NormalizedCanonicalFuchsianModel
end LowDimensionalTopology.Geometry.Teichmuller
