module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ProjectedGeodesicIntrinsicMinimum

/-!
# The original closed geodesic of a specified hyperbolic deck element

The actual full period of the given matrix projects to the unchanged original
surface. No compactness, non-null-loop, primitive-generator or supplied-geodesic
hypothesis is used. The final uniqueness clause uses the same covering element.
-/

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- A specified hyperbolic deck element supplies its full-period original
closed geodesic and its projected axis image. -/
theorem HyperbolicSurfaceModel.exists_original_closed_geodesic_of_hyperbolic_deck
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hdeck : ∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    ∃ q : OriginalClosedGeodesic M,
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      range q.curve = M.halfPlaneCover '' (hHyperbolicAxis A hA ht).carrier ∧
      ∀ r : OriginalClosedGeodesic M,
        LiZhongQC.Covers M.halfPlaneCover A r.toLoop → range r.curve = range q.curve := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hAΓ : A ∈ Γ := (hΓ A).2 hdeck
  obtain ⟨γ, hγ, _hγaxis, hT, hperiod⟩ :=
    exists_unitSpeed_axis_with_actual_period A hA ht
  let T := hTranslationLength (hSLIsometry A)
  let q : OriginalClosedGeodesic M :=
    { curve := fun t => M.halfPlaneCover (γ (T * t))
      locallyMinimizing := by
        simpa only [zero_add] using
          M.original_locallyMinimizingArc_projected_affine_geodesic hγ 0 T hT
      periodic := by
        intro t
        change M.halfPlaneCover (γ (T * (t + 1))) = M.halfPlaneCover (γ (T * t))
        rw [mul_add, mul_one, hperiod, hdeck] }
  have hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop := by
    refine ⟨fun t => γ (T * t),
      (hγ.1.continuous.comp (continuous_const.mul continuous_id)).continuousOn, ?_, ?_⟩
    · intro t htI
      rw [Path.extend_apply q.toLoop.2 htI]
      rfl
    · simpa only [mul_one, mul_zero, zero_add] using hperiod 0
  have htrace := q.trace_eq_axis_image_of_covers hp A hAΓ hA ht hcov
  refine ⟨q, hcov, htrace, ?_⟩
  intro r hr
  exact (r.trace_eq_axis_image_of_covers hp A hAΓ hA ht hr).trans htrace.symm

end LowDimensionalTopology.Geometry.Surfaces
