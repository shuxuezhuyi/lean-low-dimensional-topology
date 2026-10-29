module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.External.Jacobians.Forms.Genus
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The concrete Legendre carrier and its holomorphic differential

The affine coordinates satisfy the actual cubic equation. The compact
carrier has the one-point-compactification topology. A realization supplies
its compact analytic surface and a global holomorphic differential equal
to dz/w on the ordinary affine locus.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped OnePoint Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

/-- A nonsingular parameter of the Legendre cubic. -/
abbrev LegendreParameter := {l : ℂ // l ≠ 0 ∧ l ≠ 1}

/-- The actual affine algebraic curve, with its inherited product topology. -/
abbrev LegendreAffineCurve (l : LegendreParameter) :=
  {zw : ℂ × ℂ // zw.2 ^ 2 = zw.1 * (zw.1 - 1) * (zw.1 - l.val)}

/-- The same affine curve with its actual point at infinity. -/
abbrev LegendreCompactCurve (l : LegendreParameter) := OnePoint (LegendreAffineCurve l)

/-- The finite z coordinate, assigned zero only at infinity. -/
def legendreFiniteZ (l : LegendreParameter) (p : LegendreCompactCurve l) : ℂ :=
  OnePoint.rec 0 (fun a : LegendreAffineCurve l => a.val.1) p

/-- The continued finite w coordinate, assigned zero only at infinity. -/
def legendreFiniteW (l : LegendreParameter) (p : LegendreCompactCurve l) : ℂ :=
  OnePoint.rec 0 (fun a : LegendreAffineCurve l => a.val.2) p

/-- A compact analytic realization on the same concrete cubic carrier, with
the globally holomorphic extension of its actual dz/w differential. -/
structure OriginalLegendreRealization (l : LegendreParameter) where
  surface : ClosedRiemannSurface (LegendreCompactCurve l)
  genus_one : surface.HasGenus 1
  form :
    letI := surface.t2Space
    letI := surface.compactSpace
    letI := surface.connectedSpace
    letI := surface.toRiemannAtlas.toChartedSpace
    letI := surface.toRiemannAtlas.isManifold
    Jacobians.HolomorphicOneForms (LegendreCompactCurve l)
  finiteZ_differentiable :
    letI := surface.toRiemannAtlas.toChartedSpace
    ∀ a : LegendreAffineCurve l,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (legendreFiniteZ l) (a : LegendreCompactCurve l)
  finiteW_differentiable :
    letI := surface.toRiemannAtlas.toChartedSpace
    ∀ a : LegendreAffineCurve l,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (legendreFiniteW l) (a : LegendreCompactCurve l)
  form_eq_dz_div_w :
    letI := surface.t2Space
    letI := surface.compactSpace
    letI := surface.connectedSpace
    letI := surface.toRiemannAtlas.toChartedSpace
    letI := surface.toRiemannAtlas.isManifold
    ∀ a : LegendreAffineCurve l, a.val.2 ≠ 0 →
      form.toFun (a : LegendreCompactCurve l) =
        a.val.2⁻¹ • mfderiv 𝓘(ℂ) 𝓘(ℂ) (legendreFiniteZ l) (a : LegendreCompactCurve l)

end LowDimensionalTopology.Geometry.Surfaces
