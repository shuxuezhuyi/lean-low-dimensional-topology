/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalDehnTwistAboutCore
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import LowDimensionalTopology.External.LiZhongQC.Ch01.S07_GeometricDefinition
public import Mathlib.Topology.Order.ProjIcc

/-!
# Positive annular coordinates for an original full turn

The local complex coordinates are z=t+iθ, in radial-then-angular order.
Actual local branches of Circle.exp test the same annular embedding in the
original complex atlas. The full turn uses its given core and coordinates.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- The given annular map in transverse-then-angular complex coordinates.
The interval projection only totalizes the expression outside the open annulus. -/
def originalAnnularCoordinatePlane (e : Circle × unitInterval → X) (z : ℂ) : X :=
  e (Circle.exp z.im, Set.projIcc (0 : ℝ) 1 zero_le_one z.re)

/-- Positivity of the same annular coordinates in every original target chart,
on actual injective local angle branches and transverse coordinates 0<t<1. -/
def IsOriginalPositiveAnnularChart (R : ClosedRiemannSurface X)
    (e : Circle × unitInterval → X) : Prop :=
  ∀ a : ℝ,
    let A : OpenPartialHomeomorph ℝ Circle :=
      (isLocalHomeomorph_circleExp.localInverseAt a).symm
    ∀ χ ∈ R.toRiemannAtlas.charts,
      LiZhongQC.IsSensePreserving
        (fun z : ℂ => χ (originalAnnularCoordinatePlane e z))
        ({z : ℂ | 0 < z.re ∧ z.re < 1 ∧ z.im ∈ A.source} ∩
          originalAnnularCoordinatePlane e ⁻¹' χ.source)

/-- A positive closed annular neighborhood of the same parametrized circle. -/
structure OriginalPositiveAnnularNeighborhood (R : ClosedRiemannSurface X)
    (core : Circle → X) where
  map : Circle × unitInterval → X
  closedEmbedding : Topology.IsClosedEmbedding map
  openInterior : IsOpen (map '' {p : Circle × unitInterval |
    0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})
  coreHeight : unitInterval
  coreHeight_mem : 0 < (coreHeight : ℝ) ∧ (coreHeight : ℝ) < 1
  core_eq : ∀ s : Circle, map (s, coreHeight) = core s
  positive : IsOriginalPositiveAnnularChart R map

/-- The actual full turn of the supplied positive annular neighborhood. -/
def OriginalPositiveAnnularNeighborhood.twist {R : ClosedRiemannSurface X}
    {core : Circle → X} (A : OriginalPositiveAnnularNeighborhood R core) : X ≃ₜ X :=
  dehnTwistAboutCore core A.map A.closedEmbedding A.openInterior
    A.coreHeight A.coreHeight_mem A.core_eq

/-- A positive Dehn twist is the literal full turn of such a neighborhood,
with the original circle and ambient carrier unchanged. -/
def IsOriginalPositiveDehnTwistAbout (R : ClosedRiemannSurface X)
    (core : Circle → X) (f : X ≃ₜ X) : Prop :=
  ∃ A : OriginalPositiveAnnularNeighborhood R core, f = A.twist

end LowDimensionalTopology.Geometry.Surfaces
