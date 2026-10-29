/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalPositiveDehnTwist
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# Annular geometry of original embedded circles

A positive annular neighborhood retains the given original circle.
The literal full turn of a positive annulus preserves the original orientation.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Surfaces

open Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- Every original embedded circle has positive annular coordinates identifying
that same circle with one actual interior level. -/
def SimpleCirclePositiveAnnularNeighborhoods (R : ClosedRiemannSurface X) : Prop :=
  ∀ c : Circle → X, Topology.IsEmbedding c →
    Nonempty (OriginalPositiveAnnularNeighborhood R c)

/-- The same positive annular embedding gives an orientation-preserving
literal full-turn homeomorphism of the original surface. -/
def PositiveAnnularFullTurnOrientation (R : ClosedRiemannSurface X) : Prop :=
  ∀ (e : Circle × unitInterval → X) (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})),
    IsOriginalPositiveAnnularChart R e →
      letI := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsOrientationPreservingRS (dehnAmbientHomeomorph e he hopen)

end LowDimensionalTopology.Unproved.Surfaces
