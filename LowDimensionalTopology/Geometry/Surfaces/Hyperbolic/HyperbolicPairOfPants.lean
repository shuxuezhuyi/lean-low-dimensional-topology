module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalHyperbolicDeckGeodesic
public import LowDimensionalTopology.Geometry.Surfaces.Topology.PairOfPantsModel
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Connected.Basic

/-!
# The book's open hyperbolic pair of pants in the original surface

The open interior has the prescribed triply connected planar type.
The relative boundary remains in the unchanged ambient surface. The consumer
uses that surface's actual cover and the full period of a boundary geodesic.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- An open, relatively compact triply connected subsurface whose relative
boundary components are simple closed geodesics of the original surface.
Simplicity is injectivity of the actual period-circle map. -/
@[expose] def IsHyperbolicPairOfPants
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (P : Set X) : Prop :=
  IsOpen P ∧ IsCompact (closure P) ∧ Nonempty (P ≃ₜ pantsPlanarRegion) ∧
    ∀ x ∈ frontier P, ∃ q : OriginalClosedGeodesic M,
      Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X) ∧
      range q.curve = connectedComponentIn (frontier P) x

/-- Each boundary component retains its actual simple period-circle witness,
with that same geodesic's full-period covering matrix, axis and length. -/
theorem IsHyperbolicPairOfPants.boundary_component_simple_actual_geodesic
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} {P : Set X}
    (hP : IsHyperbolicPairOfPants M P) {x : X} (hx : x ∈ frontier P) :
    ∃ (q : OriginalClosedGeodesic M)
      (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2),
      Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X) ∧
      range q.curve = connectedComponentIn (frontier P) x ∧
      (∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z) ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      range q.curve = M.halfPlaneCover '' (hHyperbolicAxis A hA ht).carrier ∧
      0 < q.length.toReal ∧
      (Matrix.trace A.val) ^ 2 = 4 * Real.cosh (q.length.toReal / 2) ^ 2 := by
  obtain ⟨q, hcircle, hq⟩ := hP.2.2.2 x hx
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hAΓ, hcov, hA, ht⟩ := q.exists_actual_hyperbolic_cover hp
  have hdeck := (hΓ A).1 hAΓ
  have haxis := q.trace_eq_axis_image_of_covers hp A hAΓ hA ht hcov
  exact ⟨q, A, hA, ht, hcircle, hq, hdeck, hcov, haxis, q.length_toReal_pos,
    q.trace_sq_eq_four_cosh_length_sq_of_covers hp A hAΓ ht hcov⟩

/-- Each boundary component is represented by the actual full-period cover
construction, with its projected axis and positive original length. -/
theorem IsHyperbolicPairOfPants.boundary_component_actual_geodesic
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} {P : Set X}
    (hP : IsHyperbolicPairOfPants M P) {x : X} (hx : x ∈ frontier P) :
    ∃ (q : OriginalClosedGeodesic M)
      (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2),
      range q.curve = connectedComponentIn (frontier P) x ∧
      (∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z) ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      range q.curve = M.halfPlaneCover '' (hHyperbolicAxis A hA ht).carrier ∧
      0 < q.length.toReal ∧
      (Matrix.trace A.val) ^ 2 = 4 * Real.cosh (q.length.toReal / 2) ^ 2 := by
  obtain ⟨q, A, hA, ht, _hcircle, hq, hdeck, hcov, haxis, hlength, htrace⟩ :=
    hP.boundary_component_simple_actual_geodesic hx
  exact ⟨q, A, hA, ht, hq, hdeck, hcov, haxis, hlength, htrace⟩

end LowDimensionalTopology.Geometry.Surfaces
