module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableCurves
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ChartwiseRectifiableReparam
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableAffineReparam

/-! # Actual original-atlas rectifiable subarcs and their covering length -/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The original curve restricted to the actual interval `[a,b]`, with only
its parameter affinely expressed on `[0,1]`. Rectifiability is proved from the
original atlas on `[a,b]`, with no covering data in the definition. -/
@[expose] def RiemannSurfaceRectifiableCurvePiece.ofInterval
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (α : ℝ → X) (hα : Continuous α) (a b : ℝ) (hab : a ≤ b)
    (hrect : R.toRiemannAtlas.IsChartwiseBVOn α (Icc a b)) :
    RiemannSurfaceRectifiableCurvePiece R where
  curve := ⟨fun t => α (a + (b - a) * (t : ℝ)), hα.comp (by fun_prop)⟩
  rectifiable := by
    have hmap : MapsTo (fun t : ℝ => a + (b - a) * t) (Icc 0 1) (Icc a b) := by
      intro t ht
      have hlo := mul_nonneg (sub_nonneg.mpr hab) ht.1
      have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab) ht.2
      constructor <;> linarith
    have hmono : Monotone (fun t : ℝ => a + (b - a) * t) := by
      intro s t hst
      have hmul := mul_le_mul_of_nonneg_left hst (sub_nonneg.mpr hab)
      change a + (b - a) * s ≤ a + (b - a) * t
      linarith
    have hBV := hrect.comp_monotone (fun t => a + (b - a) * t)
      (by fun_prop) (hmono.monotoneOn (Icc 0 1)) hmap
    apply hBV.congr
    intro t ht
    change α (a + (b - a) * t) = α (a + (b - a) *
      ((projIcc 0 1 zero_le_one t : I) : ℝ))
    rw [projIcc_of_mem zero_le_one ht]

/-- Any actual branch of the given original rectifiable subarc computes its
full literal hyperbolic length, including arbitrary singular parameters. -/
theorem HyperbolicSurfaceModel.rectifiableInterval_length_eq_of_branch
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : ℝ → X) (hα : Continuous α)
    (a b : ℝ) (hab : a ≤ b)
    (hrect : R.toRiemannAtlas.IsChartwiseBVOn α (Icc a b))
    (c : RectifiableCurve) (ha : c.a = a) (hb : c.b = b)
    (hpos : ∀ t ∈ Icc a b, 0 < (c.curve t).im)
    (hproj : ∀ t : ℝ, ∀ ht : t ∈ Icc a b,
      M.halfPlaneCover ⟨c.curve t, hpos t ht⟩ = α t) :
    M.rectifiableCurveLength
      (RiemannSurfaceRectifiableCurvePiece.ofInterval α hα a b hab hrect) =
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
  have hparam (t : I) : c.a + (c.b - c.a) * (t : ℝ) ∈ Icc a b := by
    rw [ha, hb]
    have hlo := mul_nonneg (sub_nonneg.mpr hab) t.property.1
    have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab) t.property.2
    constructor <;> linarith
  calc
    _ = c.unitAffine.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
      apply M.rectifiableCurveLength_eq_of_lift _ c.unitAffine rfl rfl
        (fun t ht => hpos _ (hparam ⟨t, ht⟩))
      intro t
      change M.halfPlaneCover ⟨c.curve (c.a + (c.b - c.a) * (t : ℝ)), _⟩ =
        α (a + (b - a) * (t : ℝ))
      simpa only [ha, hb] using hproj _ (hparam t)
    _ = _ := c.unitAffine_weightedLength _

end LowDimensionalTopology.Geometry.Surfaces
