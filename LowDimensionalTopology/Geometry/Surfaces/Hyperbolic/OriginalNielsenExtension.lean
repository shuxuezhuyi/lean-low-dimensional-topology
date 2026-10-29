module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalBorderedHyperbolicInput
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalModelConvexCore
public import LowDimensionalTopology.Unproved.Teichmuller.HubbardDecomposition
public import Mathlib.Topology.Homotopy.Basic

/-!
# A Nielsen extension over the same original bordered surface

The independent region data retain the whole group and the actual finite-area
convex region with its closed geodesic frontier. The extension adds the same
original inclusion, faithful complete metric, all outward standard funnels,
and a deformation retraction fixing every original point. No core equality
is a field of either record.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open Set MeasureTheory Fuchsian
open LowDimensionalTopology.Unproved.Teichmuller
open scoped Topology ENNReal

/-- An independent finite-area convex region with its actual geodesic frontier. -/
structure OriginalGeodesicBoundaryRegion
    {Y : Type} [TopologicalSpace Y] {RY : RiemannSurface Y}
    (M : HyperbolicSurfaceModel RY) where
  non_elementary : DiscreteGroups.IsNonElementary M.group
  finitely_generated : M.group.FG
  region : Set Hyperbolic.extendedUnitDisc
  regular_closed : closure (interior region) = region
  interior_nonempty : (interior region).Nonempty
  invariant : ∀ g : M.group, ∀ z ∈ region,
    (⟨g • z.val, M.invariant g z.val z.property⟩ : Hyperbolic.extendedUnitDisc) ∈ region
  convex : (originalHyperbolicDiscGroup M).asFuchsianDisc.HyperbolicallyConvex
    (Subtype.val '' interior region)
  boundary : Set (EssentialSimpleCircle Y)
  boundary_finite : boundary.Finite
  boundary_nonempty : boundary.Nonempty
  boundary_geodesic : IsGeodesicMulticurve M boundary
  frontier_eq : frontier region = M.discCover ⁻¹' hubbardCurveUnion boundary
  area_finite :
    letI : MeasurableSpace Y := borel Y
    letI : BorelSpace Y := ⟨rfl⟩
    M.areaMeasure (M.discCover '' region) < ⊤

/-- The whole extension over the same original surface, retaining every funnel boundary. -/
structure OriginalNielsenExtension
    {S Y : Type} [tS : TopologicalSpace S] [tY : TopologicalSpace Y]
    {U : TopologicalSpace.Opens S} {A : RiemannAtlas U}
    (input : OriginalBorderedHyperbolicInput U A)
    {RY : RiemannSurface Y} (M : HyperbolicSurfaceModel RY)
    extends OriginalGeodesicBoundaryRegion M where
  original : S ≃ₜ (M.discCover '' region)
  interiorOpen : TopologicalSpace.Opens Y
  interiorOpen_eq : (interiorOpen : Set Y) = M.discCover '' interior region
  originalInterior : U ≃ₜ interiorOpen
  originalInterior_eq : ∀ u : U, (original u.val).val = (originalInterior u).val
  interior_analytic : RiemannAnalyticMap A
    (letI := RY.toRiemannAtlas.toChartedSpace
     letI := RY.toRiemannAtlas.isManifold
     RiemannAtlas.ofManifold interiorOpen) originalInterior
  interior_inverse_analytic : RiemannAnalyticMap
    (letI := RY.toRiemannAtlas.toChartedSpace
     letI := RY.toRiemannAtlas.isManifold
     RiemannAtlas.ofManifold interiorOpen) A originalInterior.symm
  boundary_eq : (M.discCover '' region) \ (interiorOpen : Set Y) =
    hubbardCurveUnion boundary
  distance_original : ∀ s t : S,
    (letI := input.metric; edist s t) =
      hubbardPieceLengthInf M (M.discCover '' region) (original s) (original t)
  metric : MetricSpace Y
  topology_eq : tY = metric.toUniformSpace.toTopologicalSpace
  complete : @CompleteSpace Y metric.toUniformSpace
  distance_whole : ∀ y z : Y,
    (letI := metric; edist y z) =
      hubbardPieceLengthInf M univ ⟨y, Set.mem_univ y⟩ ⟨z, Set.mem_univ z⟩
  inclusion : C(S, Y)
  inclusion_eq : ∀ s : S, inclusion s = (original s).val
  isometric_original :
    letI := input.metric.replaceTopology input.topology_eq
    letI := metric.replaceTopology topology_eq
    Isometry inclusion
  retraction : C(Y, S)
  retraction_inclusion : ∀ s : S, retraction (inclusion s) = s
  retract_homotopy : ContinuousMap.HomotopyRel (ContinuousMap.id Y)
    (inclusion.comp retraction) (Set.range inclusion)
  exterior : boundary → HubbardPieceIndex boundary
  exterior_injective : Function.Injective exterior
  exterior_union : (⋃ c : boundary, (exterior c).val) = (M.discCover '' region)ᶜ
  seeds : (c : boundary) → M.discCover ⁻¹' (exterior c).val
  completed : (c : boundary) → HubbardCutCompletion M (exterior c).val (seeds c)
  standard_funnel : ∀ c : boundary, HubbardHalfAnnulusAlternative (completed c)
  exterior_boundary : ∀ c : boundary,
    (completed c).projection '' (Set.range (completed c).inclusion)ᶜ = Set.range c.val.val
  infinite_area :
    letI : MeasurableSpace Y := borel Y
    letI : BorelSpace Y := ⟨rfl⟩
    M.areaMeasure univ = ⊤

/-- An analytic isometry fixing every point of the same original surface. -/
def OriginalNielsenExtensionComparison
    {S Y Z : Type} [TopologicalSpace S] [TopologicalSpace Y] [TopologicalSpace Z]
    {U : TopologicalSpace.Opens S} {A : RiemannAtlas U}
    {input : OriginalBorderedHyperbolicInput U A}
    {RY : RiemannSurface Y} {RZ : RiemannSurface Z}
    {M : HyperbolicSurfaceModel RY} {N : HyperbolicSurfaceModel RZ}
    (D : OriginalNielsenExtension input M) (E : OriginalNielsenExtension input N)
    (J : Y ≃ₜ Z) : Prop :=
  (letI := D.metric.replaceTopology D.topology_eq
   letI := E.metric.replaceTopology E.topology_eq
   Isometry J) ∧
  RiemannAnalyticMap RY.toRiemannAtlas RZ.toRiemannAtlas J ∧
  RiemannAnalyticMap RZ.toRiemannAtlas RY.toRiemannAtlas J.symm ∧
  ∀ s : S, J (D.inclusion s) = E.inclusion s

end LowDimensionalTopology.Geometry.Surfaces
