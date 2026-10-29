module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.LocalGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ProjectedGeodesicIntrinsicMinimum
public import Mathlib.Topology.Path

/-!
# Finite geodesic arcs on the original hyperbolic surface

An arc is injective on its entire finite interval and extends to an actual
original-atlas locally minimizing curve, including geodesic germs at both
endpoints. A finite native geodesic segment whose actual projection is
injective supplies this ordinary contract with its literal C1 length.
-/

public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- A finite embedded arc extending to an actual original-atlas locally
minimizing curve on both sides of its endpoints. -/
@[expose] def IsOriginalGeodesicArc
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (c : I → X) : Prop :=
  Function.Injective c ∧ ∃ α : ℝ → X,
    IsOriginalLocallyMinimizingArc M α ∧ ∀ t : I, c t = α (t : ℝ)

/-- Actual injectivity on a closed native segment gives a finite original
geodesic arc with the exact projected parameter and native surface C1 length. -/
theorem HyperbolicSurfaceModel.exists_projected_geodesic_c1_arc
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    (a b : ℝ) (hab : a < b)
    (hinj : InjOn M.halfPlaneCover (closedHSegment (γ a) (γ b))) :
    ∃ c : HyperbolicSurfaceC1CurvePiece M,
      (∀ t : I, c.curve t = M.halfPlaneCover (γ (a + (b - a) * (t : ℝ)))) ∧
      c.length = b - a ∧ IsOriginalGeodesicArc M c.curve := by
  obtain ⟨c, hpoint, hlength⟩ :=
    M.exists_projected_geodesic_c1_piece hγ a b hab.le
  have hsegment (t : I) :
      γ (a + (b - a) * (t : ℝ)) ∈ closedHSegment (γ a) (γ b) := by
    rw [closedHSegment_eq_image_Icc hγ hab]
    refine ⟨a + (b - a) * (t : ℝ), ?_, rfl⟩
    have hlo := mul_nonneg (sub_nonneg.mpr hab.le) t.property.1
    have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab.le) t.property.2
    constructor <;> linarith
  refine ⟨c, hpoint, hlength, ?_⟩
  constructor
  · intro s t hst
    have hγeq := hinj (hsegment s) (hsegment t)
      ((hpoint s).symm.trans (hst.trans (hpoint t)))
    apply Subtype.ext
    exact mul_left_cancel₀ (sub_pos.mpr hab).ne' (add_left_cancel (hγ.1.injective hγeq))
  · exact ⟨fun t => M.halfPlaneCover (γ (a + (b - a) * t)),
      M.original_locallyMinimizingArc_projected_affine_geodesic
        hγ a (b - a) (sub_pos.mpr hab), hpoint⟩

/-- The same finite C1 arc is an actual path between its literal projected
native endpoints; changing endpoint types does not change any path value. -/
theorem HyperbolicSurfaceModel.exists_projected_geodesic_arc_path
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    (a b : ℝ) (hab : a < b)
    (hinj : InjOn M.halfPlaneCover (closedHSegment (γ a) (γ b))) :
    ∃ (c : HyperbolicSurfaceC1CurvePiece M)
      (p : Path (M.halfPlaneCover (γ a)) (M.halfPlaneCover (γ b))),
      (∀ t : I, p t = c.curve t) ∧
      (∀ t : I, p t = M.halfPlaneCover (γ (a + (b - a) * (t : ℝ)))) ∧
      c.length = b - a ∧ IsOriginalGeodesicArc M p := by
  obtain ⟨c, hpoint, hlength, harc⟩ :=
    M.exists_projected_geodesic_c1_arc hγ a b hab hinj
  have h0 : M.halfPlaneCover (γ a) = c.curve 0 := by
    simpa only [Set.Icc.coe_zero, mul_zero, add_zero] using (hpoint 0).symm
  have h1 : M.halfPlaneCover (γ b) = c.curve 1 := by
    have he : a + (b - a) = b := by ring
    simpa only [Set.Icc.coe_one, mul_one, he] using (hpoint 1).symm
  let p : Path (M.halfPlaneCover (γ a)) (M.halfPlaneCover (γ b)) :=
    c.toPath.cast h0 h1
  exact ⟨c, p, fun _ => rfl, hpoint, hlength, harc⟩

end LowDimensionalTopology.Geometry.Surfaces
