module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.FiniteRetainedBoundaryData
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifold
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Path

/-!
# A complete hyperbolic metric on an original retained-boundary surface

The metric induces the original topology and has its actual path-length
distance. Its local models are closed geodesic half-planes. Their interiors
agree with the designated complex atlas, and their native area measures
agree with the area on the same original carrier.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The closed geodesic half-plane in the native hyperbolic plane. -/
abbrev originalBorderedHalfPlane := {z : ℍ // 0 ≤ z.re}

/-- The given complete hyperbolic metric, finite topological presentation and
negative Euler characteristic of the same original retained-boundary surface. -/
structure OriginalBorderedHyperbolicInput
    {S : Type} [tS : TopologicalSpace S]
    (U : TopologicalSpace.Opens S) (A : RiemannAtlas U) where
  metric : MetricSpace S
  topology_eq : tS = metric.toUniformSpace.toTopologicalSpace
  complete : @CompleteSpace S metric.toUniformSpace
  connected : ConnectedSpace S
  length_distance :
    letI := metric.replaceTopology topology_eq
    ∀ x y : S, edist x y = ⨅ γ : Path x y, eVariationOn γ univ
  charts : Set (OpenPartialHomeomorph S originalBorderedHalfPlane)
  cover : ∀ x : S, ∃ e ∈ charts, x ∈ e.source
  local_isometry :
    letI := metric.replaceTopology topology_eq
    ∀ e ∈ charts, Isometry (fun x : e.source => e x.val)
  interior_iff : ∀ e ∈ charts, ∀ x ∈ e.source,
    x ∈ U ↔ 0 < (e x).val.re
  analytic :
    letI := A.toChartedSpace
    letI := A.isManifold
    ∀ e ∈ charts,
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
        (fun x : U => ((e x.val).val : ℂ)) {x : U | x.val ∈ e.source}
  area : @Measure S (borel S)
  area_patch : ∀ e ∈ charts, ∀ B : Set S,
    @MeasurableSet S (borel S) B → B ⊆ e.source →
      area B = volume ((fun x : S => (e x).val) '' B)
  area_finite : area univ < ⊤
  finite_presentation : ∃ X : Type, ∃ tX : TopologicalSpace X,
    letI := tX
    ∃ (R : ClosedRiemannSurface X) (D : FiniteRetainedBoundaryData R)
      (E : D.Carrier ≃ₜ S) (e : D.interiorOpen ≃ₜ U),
        ∀ x, E (D.interiorToCarrier x) = (e x : S)
  negative_euler : ∃ hCW : TauCeti.FiniteCWType S, @TauCeti.eulerChar S tS hCW < 0
  boundary_nonempty : ((U : Set S)ᶜ).Nonempty

end LowDimensionalTopology.Geometry.Surfaces
