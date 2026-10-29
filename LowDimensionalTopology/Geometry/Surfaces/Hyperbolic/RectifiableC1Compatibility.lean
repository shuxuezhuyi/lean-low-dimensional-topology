module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableCurves
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.C1SourceLength

/-!
# Original native C1 length agrees with the full rectifiable length

Every native C1 curve gives an original-atlas rectifiable curve. Its literal
length agrees with the full BV arclength proved independent of all continuous
covering lifts. Thus native C1 competitors form an actual length-preserving
subclass of the full original-surface rectifiable curves.
-/

public section
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane unitInterval ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A native C1 piece is a genuine continuous BV curve on the same parameter
interval, with the exact original complex coordinates. -/
@[expose] def C1CurvePiece.toRectifiableCurve (c : C1CurvePiece) : RectifiableCurve where
  a := c.a
  b := c.b
  ordered := c.ordered
  curve := fun t => (c.curve t : ℂ)
  continuous := UpperHalfPlane.continuous_coe.comp_continuousOn c.continuous_curve
  boundedVariation := by
    obtain ⟨K, hLip⟩ := c.exists_euclidean_lipschitz
    simpa only [inter_self] using hLip.locallyBoundedVariationOn c.a c.b
      (left_mem_Icc.mpr c.ordered) (right_mem_Icc.mpr c.ordered)

/-- The native C1 inclusion retains the actual starting parameter. -/
@[simp] theorem C1CurvePiece.toRectifiableCurve_a (c : C1CurvePiece) :
    c.toRectifiableCurve.a = c.a := rfl

/-- The native C1 inclusion retains the actual ending parameter. -/
@[simp] theorem C1CurvePiece.toRectifiableCurve_b (c : C1CurvePiece) :
    c.toRectifiableCurve.b = c.b := rfl

/-- On a native unit-interval C1 piece the full rectifiable integral is its
original native hyperbolic length; endpoints remain part of the curve data. -/
theorem C1CurvePiece.toRectifiableCurve_weightedLength
    (c : C1CurvePiece) (ha : c.a = 0) (hb : c.b = 1) :
    c.toRectifiableCurve.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) =
      ENNReal.ofReal c.length := by
  obtain ⟨K, hLip⟩ := c.exists_euclidean_lipschitz
  have hρ : Measurable (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by fun_prop
  calc
    c.toRectifiableCurve.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) =
        LiZhongQC.hypLength (fun t => (c.curve t : ℂ)) := by
      rw [c.toRectifiableCurve.weightedLength_eq_lintegral_deriv hLip hρ]
      unfold LiZhongQC.hypLength
      change (∫⁻ t in Ioo c.a c.b,
        ENNReal.ofReal (1 / (c.curve t).im) * ‖deriv (fun s => (c.curve s : ℂ)) t‖ₑ) = _
      rw [ha, hb]
      refine setLIntegral_congr_fun measurableSet_Ioo fun t _ht => ?_
      rw [one_div, ENNReal.ofReal_inv_of_pos (c.curve t).im_pos, div_eq_mul_inv, mul_comm]
      simp only [UpperHalfPlane.coe_im]
    _ = ENNReal.ofReal c.length := c.hypLength_eq_length ha hb

end LowDimensionalTopology.Geometry.Hyperbolic

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- An actual native original-surface C1 curve has a genuine BV lift of the
same literal length, in the same original model. -/
theorem HyperbolicSurfaceC1CurvePiece.exists_rectifiable_halfPlane_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : HyperbolicSurfaceC1CurvePiece M) :
    ∃ c : RectifiableCurve, c.a = 0 ∧ c.b = 1 ∧
      ∃ hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c.curve t).im,
        (∀ t : I, M.halfPlaneCover ⟨c.curve t, hpos t t.property⟩ = q.curve t) ∧
        c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) = ENNReal.ofReal q.length := by
  let d := q.toQuotient.lift
  let c := d.toHalfPlane.toRectifiableCurve
  have ha : c.a = 0 := q.toQuotient.lift_spec.1
  have hb : c.b = 1 := q.toQuotient.lift_spec.2.1
  refine ⟨c, ha, hb, fun t _ => (d.toHalfPlane.curve t).im_pos, ?_, ?_⟩
  · intro t
    change M.discCover (discFiniteHomeomorph.symm
      (halfPlaneToDisc (discToHalfPlane (d.curve t)))) = q.curve t
    rw [halfPlaneToDisc_discToHalfPlane]
    change M.homeomorph.symm (discQuotientProjection M.invariant (d.curve t)) = q.curve t
    rw [q.toQuotient.lift_spec.2.2 t]
    exact M.homeomorph.symm_apply_apply _
  · change d.toHalfPlane.toRectifiableCurve.weightedLength _ = _
    rw [d.toHalfPlane.toRectifiableCurve_weightedLength ha hb, d.toHalfPlane_length]
    rfl

/-- Include every actual native C1 curve in the original-atlas rectifiable
curve class; covering rectifiability is proved, not added as a new field. -/
@[expose] def HyperbolicSurfaceC1CurvePiece.toRectifiable
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : HyperbolicSurfaceC1CurvePiece M) :
    RiemannSurfaceRectifiableCurvePiece R where
  curve := q.curve
  rectifiable := by
    obtain ⟨c, ha, hb, hpos, hproj, _hlen⟩ := q.exists_rectifiable_halfPlane_lift
    exact (M.chartwiseRectifiable_iff_exists_rectifiable_lift q.curve).mpr
      ⟨c, ha, hb, hpos, hproj⟩

/-- The full original-atlas BV length restricts exactly to the existing native
surface C1 length, so the earlier integral API retains its original meaning. -/
theorem HyperbolicSurfaceC1CurvePiece.toRectifiable_length
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : HyperbolicSurfaceC1CurvePiece M) :
    M.rectifiableCurveLength q.toRectifiable = ENNReal.ofReal q.length := by
  obtain ⟨c, ha, hb, hpos, hproj, hlen⟩ := q.exists_rectifiable_halfPlane_lift
  exact (M.rectifiableCurveLength_eq_of_lift q.toRectifiable c ha hb hpos hproj).trans hlen

end LowDimensionalTopology.Geometry.Surfaces
