module

public import LowDimensionalTopology.Geometry.Teichmuller.BersIntegralOperator
public import LowDimensionalTopology.Geometry.Teichmuller.BersWeightedScalarRemainder
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersKernel
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Tactic.Linarith

/-!
# The actual Bers projection has the integral Fréchet derivative

The native compatible measurable coefficients retain their own L-infinity norm.
The Bers projection retains every actual lower-half-plane value in the faithful
weighted supremum realization. A uniform quadratic remainder proves genuine
Fréchet differentiability into that Banach space. Its kernel is consequently
the annihilator of the original quadratic differentials on the original open
fundamental region.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open LiZhongQC Surfaces QuadraticBergman
variable {Γ : Subgroup GammaMeasurableBeltrami.Deck}

private theorem projection_weighted_bound (μ : GammaMeasurableBeltrami.Ball Γ)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖GammaMeasurableBeltrami.bersProjection μ z‖ * z.im ^ 2 ≤ (3 / 2 : ℝ) := by
  rw [GammaMeasurableBeltrami.bersProjection_eq]
  let ν : BeltramiH := (GammaMeasurableBeltrami.toSourceGamma μ).val
  have hN := (bg2_bers_mem ν).2.le
  have hp : ENNReal.ofReal (‖bersFunction ν.val z‖ * z.im ^ 2) ≤
      bersNormL (bersFunction ν.val) :=
    le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  change ‖bersFunction ν.val z‖ * z.im ^ 2 ≤ (3 / 2 : ℝ)
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (3 / 2 : ℝ))).mp (hp.trans hN)

/-- The actual native Bers projection, retained pointwise in its weighted norm. -/
@[no_expose] def projectionValue (μ : GammaMeasurableBeltrami.Ball Γ) : Target :=
  encode (GammaMeasurableBeltrami.bersProjection μ)
    ⟨3 / 2, fun _ hz => projection_weighted_bound μ hz⟩

@[simp] theorem projectionValue_apply (μ : GammaMeasurableBeltrami.Ball Γ) (z : Lower) :
    projectionValue μ z = GammaMeasurableBeltrami.bersProjection μ z * weight z := by
  rw [projectionValue, encode_apply]

/-- Extend the actual projection by zero outside its open coefficient ball.
This extension agrees with the original projection on an open neighborhood of zero. -/
def projection (μ : GammaMeasurableBeltrami.Space Γ) : Target := by
  classical
  exact if h : ‖μ‖ < 1 then
    projectionValue (⟨μ, by simpa only [mem_ball, dist_zero_right] using h⟩ :
      GammaMeasurableBeltrami.Ball Γ)
    else 0

/-- On the original coefficient ball, every actual value is preserved. -/
theorem projection_apply_source (μ : GammaMeasurableBeltrami.Space Γ)
    (hμ : ‖μ‖ < 1) (z : Lower) :
    projection μ z =
      bersFunction (GammaMeasurableBeltrami.planeRepresentative μ.val) z * weight z := by
  classical
  simp only [projection, dite_eq_left hμ, projectionValue_apply,
    GammaMeasurableBeltrami.bersProjection_eq]

/-- The actual zero class has zero Bers image, using only a.e. representative identities. -/
theorem projection_zero : projection (0 : GammaMeasurableBeltrami.Space Γ) = 0 := by
  apply lp.ext
  funext z
  rw [projection_apply_source 0 (by simp) z]
  have hz := (bersFunction_and_derivative_zero_of_norm_zero
    (0 : GammaMeasurableBeltrami.Space Γ) (by simp) z.property).1
  change bersFunction (GammaMeasurableBeltrami.planeRepresentative
    (0 : GammaMeasurableBeltrami.Space Γ).val) z * weight z = 0
  rw [hz, zero_mul]

/-- The norm remainder is genuinely uniform over the complete lower half-plane. -/
theorem projection_quadratic_remainder (μ : GammaMeasurableBeltrami.Space Γ)
    (hsmall : ‖μ‖ < 1 / 4) :
    ‖projection μ - projection (0 : GammaMeasurableBeltrami.Space Γ) -
      integralOperator Γ μ‖ ≤ 48 * ‖μ‖ ^ 2 := by
  rw [projection_zero, sub_zero]
  apply lp.norm_le_of_forall_le (by positivity)
  intro z
  simp only [lp.coeFn_sub, Pi.sub_apply]
  rw [projection_apply_source μ (by linarith) z, integralOperator_apply,
    ← sub_mul, norm_mul]
  simpa only [weight, Complex.norm_real, Real.norm_eq_abs,
    abs_sq] using
    bersFunction_weighted_quadratic_remainder μ hsmall z.property

/-- The literal fourth-kernel integral is the true Banach-space Fréchet
 derivative of the actual native Bers projection at the actual zero class. -/
theorem hasFDerivAt_projection :
    HasFDerivAt (projection (Γ := Γ)) (integralOperator Γ) 0 := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hr : 0 < min (1 / 4 : ℝ) (ε / 48) :=
    lt_min (by norm_num) (div_pos hε (by norm_num))
  filter_upwards [ball_mem_nhds (0 : GammaMeasurableBeltrami.Space Γ) hr] with μ hμ
  have hn : ‖μ‖ < min (1 / 4 : ℝ) (ε / 48) := mem_ball_zero_iff.mp hμ
  have hsmall : ‖μ‖ < (1 / 4 : ℝ) := lt_of_lt_of_le hn (min_le_left _ _)
  have hbound : 48 * ‖μ‖ ≤ ε := by
    have hlt := lt_of_lt_of_le hn (min_le_right _ _)
    linarith
  calc
    ‖projection (0 + μ) - projection (0 : GammaMeasurableBeltrami.Space Γ) -
        integralOperator Γ μ‖ ≤ 48 * ‖μ‖ ^ 2 := by
      simpa only [zero_add] using projection_quadratic_remainder μ hsmall
    _ ≤ ε * ‖μ‖ := by nlinarith [norm_nonneg μ]

/-- Vanishing of the genuine Fréchet derivative is precisely the original
quadratic-differential annihilator on the original native open fundamental region. -/
theorem fderiv_projection_iff_nativeRegionAnnihilator
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℍ} (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    fderiv ℂ (projection (Γ := Γ)) 0 μ = 0 ↔
      ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        ∫ z in UpperHalfPlane.coe '' F,
          GammaMeasurableBeltrami.planeRepresentative μ.val z *
            uniformizedQuadratic R p q z = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have hΓ : IsFuchsian Γ := utm_x_isFuchsian hp
  rw [hasFDerivAt_projection.fderiv, integralOperator_eq_zero_iff]
  refine Iff.trans ?_ (nativeBersDirectional_iff_nativeRegionAnnihilator R P p hp hF μ)
  constructor
  · intro h z hz
    exact (nativeBersLine_directional hΓ μ hz).deriv.trans (h z hz)
  · intro h z hz
    exact (nativeBersLine_directional hΓ μ hz).deriv.symm.trans (h z hz)

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
