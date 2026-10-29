module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableCurves
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.RectifiableDistance

/-! # Every continuous lift computes the full original rectifiable length -/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The literal length depends only on the actual parametrized original
curve, not on the proof of its original-atlas rectifiability. -/
theorem HyperbolicSurfaceModel.rectifiableCurveLength_congr
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q r : RiemannSurfaceRectifiableCurvePiece R)
    (hpoint : ∀ t : I, q.curve t = r.curve t) :
    M.rectifiableCurveLength q = M.rectifiableCurveLength r := by
  obtain ⟨ha, hb, hpos, hproj⟩ := M.rectifiableCurveLift_spec q
  exact (M.rectifiableCurveLength_eq_of_lift r (M.rectifiableCurveLift q) ha hb hpos
    (fun t => (hproj t).trans (hpoint t))).symm

/-- Every actual continuous covering lift of an original-atlas rectifiable
curve is itself BV. Its original complex coordinates compute the same full
length; no regularity or rectifiability premise is added for the lift. -/
theorem HyperbolicSurfaceModel.exists_rectifiableCurve_of_continuous_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q : RiemannSurfaceRectifiableCurvePiece R)
    (e : C(I, ℍ)) (he : ∀ t : I, M.halfPlaneCover (e t) = q.curve t) :
    ∃ c : RectifiableCurve, c.a = 0 ∧ c.b = 1 ∧
      (∀ t : I, c.curve t = (e t : ℂ)) ∧
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) =
        M.rectifiableCurveLength q := by
  let f : ℝ → ℍ := fun t => e (projIcc 0 1 zero_le_one t)
  have hf : Continuous f := e.continuous.comp continuous_projIcc
  have hproj : M.halfPlaneCover ∘ f =
      (fun t : ℝ => q.curve (projIcc 0 1 zero_le_one t)) := funext fun t => he _
  have hchart : R.toRiemannAtlas.IsChartwiseBVOn (M.halfPlaneCover ∘ f) (Icc 0 1) := by
    rw [hproj]
    exact q.rectifiable
  have hBV := (M.boundedVariation_iff_chartwiseBV hf.continuousOn).mpr hchart
  have hBVcoe := (halfPlane_boundedVariation_iff_coe_of_continuousOn hf.continuousOn).mp hBV
  let c : RectifiableCurve :=
    { a := 0
      b := 1
      ordered := zero_le_one
      curve := fun t => (f t : ℂ)
      continuous := (UpperHalfPlane.continuous_coe.comp hf).continuousOn
      boundedVariation := hBVcoe }
  have hpoint (t : I) : c.curve t = (e t : ℂ) := by
    change (e (projIcc 0 1 zero_le_one (t : ℝ)) : ℂ) = (e t : ℂ)
    rw [projIcc_of_mem zero_le_one t.property]
  refine ⟨c, rfl, rfl, hpoint, ?_⟩
  exact (M.rectifiableCurveLength_eq_of_lift q c rfl rfl (fun t _ => (f t).im_pos)
    (fun t => by
      change M.halfPlaneCover (f t) = q.curve t
      dsimp only [f]
      rw [projIcc_of_mem zero_le_one t.property]
      exact he t)).symm

/-- Full original-surface rectifiable length dominates the actual endpoint
distance of every continuous covering lift, including singular BV parameters. -/
theorem HyperbolicSurfaceModel.dist_le_rectifiable_length_of_continuous_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q : RiemannSurfaceRectifiableCurvePiece R)
    (e : C(I, ℍ)) (he : ∀ t : I, M.halfPlaneCover (e t) = q.curve t) :
    ENNReal.ofReal (dist (e 0) (e 1)) ≤ M.rectifiableCurveLength q := by
  obtain ⟨c, ha, hb, hpoint, hlen⟩ := M.exists_rectifiableCurve_of_continuous_lift q e he
  have hc : c.IsPathIn LiZhongQC.upperHalf (e 0) (e 1) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ha]
      exact hpoint 0
    · rw [hb]
      exact hpoint 1
    · rintro _ ⟨t, ht, rfl⟩
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [ha, hb] using ht
      rw [hpoint ⟨t, ht'⟩]
      exact (e ⟨t, ht'⟩).im_pos
  rw [← hlen, ← halfPlane_rectifiable_distance (e 0) (e 1)]
  exact iInf₂_le c hc

end LowDimensionalTopology.Geometry.Surfaces
