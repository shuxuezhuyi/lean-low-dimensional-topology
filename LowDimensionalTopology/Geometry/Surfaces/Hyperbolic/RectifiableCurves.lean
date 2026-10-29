module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ChartwiseRectifiability
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableLiftLengthIndependence

/-!
# Rectifiable original-surface curves and their intrinsic hyperbolic length

Rectifiability is defined in the given Riemann atlas. Ordinary path lifting and
the proved chartwise BV equivalence construct a genuine continuous BV lift;
existence of such a lift is not a structure field. Its full hyperbolic
arclength is independent of which continuous BV lift is used.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane unitInterval Topology ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Rectifiability of an original compact-parameter curve, checked locally in
the original analytic atlas. Clamping only extends the given parameter outside
`[0,1]`; the predicate is evaluated on that closed interval, including its ends. -/
@[expose] def RiemannAtlas.IsRectifiableCurve
    {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X) (α : C(I, X)) : Prop :=
  A.IsChartwiseBVOn (fun t : ℝ => α (projIcc 0 1 zero_le_one t)) (Icc 0 1)

/-- An original-atlas rectifiable curve has an actual continuous BV covering
lift, and conversely. The lift is constructed through the same original model;
no C1, absolute continuity or Lipschitz premise is imposed on the input curve. -/
theorem HyperbolicSurfaceModel.chartwiseRectifiable_iff_exists_rectifiable_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : C(I, X)) :
    R.toRiemannAtlas.IsRectifiableCurve α ↔
      ∃ c : RectifiableCurve, c.a = 0 ∧ c.b = 1 ∧
        ∃ hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c.curve t).im,
          ∀ t : I, M.halfPlaneCover ⟨c.curve t, hpos t t.property⟩ = α t := by
  constructor
  · intro hα
    obtain ⟨z, hz⟩ := M.halfPlaneCover_surjective (α 0)
    let e := M.halfPlaneCover_covering.liftPath α z hz.symm
    have he (t : I) : M.halfPlaneCover (e t) = α t :=
      congrFun (M.halfPlaneCover_covering.liftPath_lifts α z hz.symm) t
    let f : ℝ → ℍ := fun t => e (projIcc 0 1 zero_le_one t)
    have hf : Continuous f := e.continuous.comp continuous_projIcc
    have hproj : M.halfPlaneCover ∘ f =
        (fun t : ℝ => α (projIcc 0 1 zero_le_one t)) := funext fun t => he _
    have hchart : R.toRiemannAtlas.IsChartwiseBVOn (M.halfPlaneCover ∘ f) (Icc 0 1) := by
      rw [hproj]
      exact hα
    have hBV := (M.boundedVariation_iff_chartwiseBV hf.continuousOn).mpr hchart
    have hBVcoe := (halfPlane_boundedVariation_iff_coe_of_continuousOn hf.continuousOn).mp hBV
    let c : RectifiableCurve :=
      { a := 0
        b := 1
        ordered := zero_le_one
        curve := fun t => (f t : ℂ)
        continuous := (UpperHalfPlane.continuous_coe.comp hf).continuousOn
        boundedVariation := hBVcoe }
    refine ⟨c, rfl, rfl, fun t _ => (f t).im_pos, ?_⟩
    intro t
    change M.halfPlaneCover (e (projIcc 0 1 zero_le_one (t : ℝ))) = α t
    rw [projIcc_of_mem zero_le_one t.property]
    exact he t
  · rintro ⟨c, ha, hb, hpos, hproj⟩
    have hccont : ContinuousOn c.curve (Icc (0 : ℝ) 1) := by
      simpa only [ha, hb] using c.continuous
    have hcBV : BoundedVariationOn c.curve (Icc (0 : ℝ) 1) := by
      simpa only [ha, hb] using c.boundedVariation
    let e : C(I, ℍ) := ⟨fun t => ⟨c.curve t, hpos t t.property⟩,
      Continuous.upperHalfPlaneMk
        (hccont.comp_continuous continuous_subtype_val (fun t => t.property)) _⟩
    let f : ℝ → ℍ := fun t => e (projIcc 0 1 zero_le_one t)
    have hf : Continuous f := e.continuous.comp continuous_projIcc
    have hval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (f t : ℂ) = c.curve t := by
      change c.curve (projIcc 0 1 zero_le_one t) = c.curve t
      rw [projIcc_of_mem zero_le_one ht]
    have hBVcoe : BoundedVariationOn (fun t => (f t : ℂ)) (Icc (0 : ℝ) 1) := by
      change eVariationOn (fun t => (f t : ℂ)) (Icc (0 : ℝ) 1) ≠ ∞
      rw [eVariationOn.congr (show EqOn (fun t => (f t : ℂ)) c.curve (Icc (0 : ℝ) 1)
        from fun t ht => hval t ht)]
      exact hcBV
    have hBV := (halfPlane_boundedVariation_iff_coe_of_continuousOn hf.continuousOn).mpr hBVcoe
    have hchart := (M.boundedVariation_iff_chartwiseBV hf.continuousOn).mp hBV
    have hprojection : M.halfPlaneCover ∘ f =
        (fun t : ℝ => α (projIcc 0 1 zero_le_one t)) := funext fun t => hproj _
    rw [hprojection] at hchart
    exact hchart

/-- An actual rectifiable curve on a Riemann surface, in the original atlas.
Pauses and repeated traversals are allowed. No covering lift is assumed. -/
structure RiemannSurfaceRectifiableCurvePiece
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X) where
  curve : C(I, X)
  rectifiable : R.toRiemannAtlas.IsRectifiableCurve curve

/-- Choose an actual BV lift whose existence follows from original-atlas
rectifiability; this choice is used only to evaluate an independent length. -/
@[expose] def HyperbolicSurfaceModel.rectifiableCurveLift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q : RiemannSurfaceRectifiableCurvePiece R) : RectifiableCurve :=
  ((M.chartwiseRectifiable_iff_exists_rectifiable_lift q.curve).mp q.rectifiable).choose

theorem HyperbolicSurfaceModel.rectifiableCurveLift_spec
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q : RiemannSurfaceRectifiableCurvePiece R) :
    (M.rectifiableCurveLift q).a = 0 ∧ (M.rectifiableCurveLift q).b = 1 ∧
      ∃ hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((M.rectifiableCurveLift q).curve t).im,
        ∀ t : I, M.halfPlaneCover ⟨(M.rectifiableCurveLift q).curve t, hpos t t.property⟩ =
          q.curve t :=
  ((M.chartwiseRectifiable_iff_exists_rectifiable_lift q.curve).mp q.rectifiable).choose_spec

/-- Literal hyperbolic arclength of an original-atlas rectifiable curve,
including its full parameter traversal multiplicity. -/
@[expose] def HyperbolicSurfaceModel.rectifiableCurveLength
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q : RiemannSurfaceRectifiableCurvePiece R) : ℝ≥0∞ :=
  (M.rectifiableCurveLift q).weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im))

/-- Every actual continuous BV covering lift computes this same literal
original-surface hyperbolic arclength. -/
theorem HyperbolicSurfaceModel.rectifiableCurveLength_eq_of_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q : RiemannSurfaceRectifiableCurvePiece R)
    (c : RectifiableCurve) (ha : c.a = 0) (hb : c.b = 1)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c.curve t).im)
    (hproj : ∀ t : I, M.halfPlaneCover ⟨c.curve t, hpos t t.property⟩ = q.curve t) :
    M.rectifiableCurveLength q =
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
  obtain ⟨hla, hlb, hlpos, hlproj⟩ := M.rectifiableCurveLift_spec q
  refine M.rectifiable_lift_length_independent (M.rectifiableCurveLift q) c
    (hla.trans ha.symm) (hlb.trans hb.symm)
    (fun t ht => hlpos t (by simpa only [hla, hlb] using ht))
    (fun t ht => hpos t (by simpa only [hla, hlb] using ht)) ?_
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [hla, hlb] using ht
  exact (hlproj ⟨t, ht'⟩).trans (hproj ⟨t, ht'⟩).symm

end LowDimensionalTopology.Geometry.Surfaces
