module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicTraceUniqueness
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ProjectedGeodesicIntrinsicMinimum

/-!
# Existence and geometric uniqueness for actual original closed geodesics

Every non-null original loop has a freely homotopic closed geodesic in the
original-atlas, all-rectifiable locally minimizing arc definition. The actual
positive full period from the original covering matrix is used unchanged.
All such representatives have one unique geometric image; original arbitrary
parameters and proper-power free classes remain admitted.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Every non-null original loop has an actual original-atlas rectifiable
closed geodesic in its own free homotopy class. No covering, axis, regularity
or primitive-class hypothesis is added to the original surface and loop. -/
theorem HyperbolicSurfaceModel.exists_original_closed_geodesic_of_not_null
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : LiZhongQC.Loop X)
    (hnon : ¬ IsNullHomotopicLoop α) :
    ∃ q : OriginalClosedGeodesic M, LiZhongQC.FreelyHomotopic α q.toLoop := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨β, γ, T, hγ, hT, hperiod, hpoint, hhom, _hlength⟩ :=
    M.exists_closed_geodesic_of_not_null α hnon
  let q : OriginalClosedGeodesic M :=
    { curve := fun t => M.halfPlaneCover (γ (T * t))
      locallyMinimizing := by
        simpa only [zero_add] using
          M.original_locallyMinimizingArc_projected_affine_geodesic hγ 0 T hT
      periodic := by
        intro t
        change M.halfPlaneCover (γ (T * (t + 1))) = M.halfPlaneCover (γ (T * t))
        rw [mul_add, mul_one]
        exact hperiod (T * t) }
  have hβq : LiZhongQC.FreelyHomotopic β q.toLoop :=
    LiZhongQC.s30b_fh_of_eq (fun t => hpoint t)
  exact ⟨q, LiZhongQC.s30b_fh_trans hhom hβq⟩

/-- The source's nontrivial free class has exactly one geometric closed
geodesic image. The quantified representatives use the actual original-atlas
full-BV arc definition, rather than a supplied unit-speed global lift. -/
theorem HyperbolicSurfaceModel.existsUnique_original_closed_geodesic_image
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : LiZhongQC.Loop X)
    (hnon : ¬ IsNullHomotopicLoop α) :
    ∃! S : Set X, ∃ q : OriginalClosedGeodesic M,
      LiZhongQC.FreelyHomotopic α q.toLoop ∧ range q.curve = S := by
  obtain ⟨q, hαq⟩ := M.exists_original_closed_geodesic_of_not_null α hnon
  have hqnon : ¬ IsNullHomotopicLoop q.toLoop := by
    rintro ⟨x, hqx⟩
    exact hnon ⟨x, LiZhongQC.s30b_fh_trans hαq hqx⟩
  refine ⟨range q.curve, ⟨q, hαq, rfl⟩, ?_⟩
  rintro S ⟨r, hαr, hrS⟩
  have hqr := q.trace_eq_of_freelyHomotopic r hqnon
    (LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm hαq) hαr)
  exact hrS.symm.trans hqr.symm

end LowDimensionalTopology.Geometry.Surfaces
