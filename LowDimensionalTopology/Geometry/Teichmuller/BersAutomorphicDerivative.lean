module

public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicTarget
public import LowDimensionalTopology.Geometry.Teichmuller.BersFrechetDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.BersIntegralHolomorphic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The Bers map and its Fréchet derivative in the actual automorphic normed space

The original Bers functions and actual fourth-kernel derivatives are proved to
belong to the bounded holomorphic automorphic space. Both maps are restricted
to that actual normed subspace, with their functions and weighted norms
unchanged. The Fréchet derivative follows from the already proved uniform
weighted-norm remainder, without assuming a completeness or image property.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open LiZhongQC Surfaces QuadraticBergman
variable {Γ : Subgroup GammaMeasurableBeltrami.Deck}

/-- The actual native Bers value decodes to the original raw function,
including its prescribed zero extension off the lower half-plane. -/
theorem decode_projectionValue (μ : GammaMeasurableBeltrami.Ball Γ) :
    decode (projectionValue μ) = GammaMeasurableBeltrami.bersProjection μ := by
  funext z
  by_cases hz : z ∈ lowerHalf
  · rw [decode_coe _ (⟨z, hz⟩ : Lower), projectionValue_apply]
    exact mul_div_cancel_right₀ _ (weight_ne_zero ⟨z, hz⟩)
  · rw [decode_off _ hz, GammaMeasurableBeltrami.bersProjection_eq,
      bersFunction, indicator_of_notMem hz]

/-- The actual Bers value satisfies holomorphy and every original group equation. -/
theorem projectionValue_mem_automorphicSubmodule (hΓ : IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Ball Γ) :
    projectionValue μ ∈ automorphicSubmodule Γ := by
  change decode (projectionValue μ) ∈ LiZhongQC.automorphicQD Γ
  rw [decode_projectionValue, GammaMeasurableBeltrami.bersProjection_eq]
  have h := (bersFunctionGamma_mem hΓ (GammaMeasurableBeltrami.toSourceGamma μ)).1
  change bersFunction (GammaMeasurableBeltrami.planeRepresentative μ.val.val) ∈
    LiZhongQC.automorphicQD Γ at h
  exact h

/-- The zero extension of the coefficient-ball projection still has actual automorphic image. -/
theorem projection_mem_automorphicSubmodule (hΓ : IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) : projection μ ∈ automorphicSubmodule Γ := by
  classical
  unfold projection
  split_ifs with hμ
  · exact projectionValue_mem_automorphicSubmodule hΓ _
  · exact (automorphicSubmodule Γ).zero_mem

/-- The actual projection with its precise bounded automorphic codomain. -/
def automorphicProjection (hΓ : IsFuchsian Γ) (μ : GammaMeasurableBeltrami.Space Γ) :
    Automorphic Γ :=
  ⟨projection μ, projection_mem_automorphicSubmodule hΓ μ⟩

@[simp] theorem automorphicProjection_val (hΓ : IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    (automorphicProjection hΓ μ).val = projection μ := rfl

/-- Every point of the actual original Bers function is preserved on its coefficient ball. -/
theorem automorphicProjection_toSource (hΓ : IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) (hμ : ‖μ‖ < 1) :
    EqOn ((automorphicProjection hΓ μ).toSource : ℂ → ℂ)
      (bersFunction (GammaMeasurableBeltrami.planeRepresentative μ.val)) lowerHalf := by
  intro z hz
  rw [Automorphic.toSource_apply, automorphicProjection_val,
    decode_coe _ (⟨z, hz⟩ : Lower), projection_apply_source μ hμ]
  exact mul_div_cancel_right₀ _ (weight_ne_zero ⟨z, hz⟩)

/-- Differentiate the actual automorphic equation of the genuine scalar Bers
family. The initial direction can be any bounded compatible measurable class. -/
theorem bersDerivative_automorphic (hΓ : IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) (γ : GammaMeasurableBeltrami.Deck)
    (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ lowerHalf) :
    bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val)
        (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) /
      ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
    bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z := by
  let κ := GammaMeasurableBeltrami.planeRepresentative μ.val
  let w : ℂ := ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)
  let d : ℂ := (γ 1 0 : ℂ) * z + γ 1 1
  have hw : w ∈ lowerHalf := bg2_a_mem γ hz
  have hdw := (bersFunction_directional hΓ μ hw).div_const (d ^ 4)
  have hdz := bersFunction_directional hΓ μ hz
  have heq : (fun t : ℂ => bersFunction (fun ζ => t * κ ζ) w / d ^ 4) =ᶠ[𝓝 0]
      fun t : ℂ => bersFunction (fun ζ => t * κ ζ) z := by
    have hnear : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ * ‖μ‖ < 1 :=
      (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds (by simp)
    filter_upwards [hnear] with t ht
    let ν : BeltramiGamma Γ := GammaMeasurableBeltrami.sourceGammaOfScalar μ t ht
    have hauto := (bersFunctionGamma_mem hΓ ν).1.2.2 γ hγ z hz
    change bersFunction ν.val.val w / d ^ 4 = bersFunction ν.val.val z at hauto
    simpa only [ν, GammaMeasurableBeltrami.sourceGammaOfScalar_coe] using hauto
  exact (hdw.congr_of_eventuallyEq heq.symm).unique hdz

/-- Decode of the actual bounded integral operator retains the original kernel values. -/
theorem integralOperator_decode_eqOn (μ : GammaMeasurableBeltrami.Space Γ) :
    EqOn (decode (integralOperator Γ μ))
      (bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val)) lowerHalf := by
  intro z hz
  rw [decode_coe _ (⟨z, hz⟩ : Lower), integralOperator_apply]
  exact mul_div_cancel_right₀ _ (weight_ne_zero ⟨z, hz⟩)

/-- Its actual image is holomorphic, canonically zero outside the lower half-plane,
and satisfies the actual fourth-weight automorphy law. -/
theorem integralOperator_mem_automorphicSubmodule (hΓ : IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    integralOperator Γ μ ∈ automorphicSubmodule Γ := by
  have heq := integralOperator_decode_eqOn μ
  change decode (integralOperator Γ μ) ∈ LiZhongQC.automorphicQD Γ
  refine ⟨(integralOperator_raw_differentiableOn μ).congr (fun _ hz => heq hz),
    fun z hz => decode_off _ hz, ?_⟩
  intro γ hγ z hz
  change decode (integralOperator Γ μ)
      (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) /
      ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = decode (integralOperator Γ μ) z
  rw [heq (bg2_a_mem γ hz), heq hz]
  simpa only [mobiusFn] using bersDerivative_automorphic hΓ μ γ hγ hz

/-- The genuine bounded integral operator restricted to its proved automorphic image. -/
def automorphicIntegralOperator (hΓ : IsFuchsian Γ) :
    GammaMeasurableBeltrami.Space Γ →L[ℂ] Automorphic Γ :=
  (integralOperator Γ).codRestrict (automorphicSubmodule Γ)
    (integralOperator_mem_automorphicSubmodule hΓ)

@[simp] theorem automorphicIntegralOperator_val (hΓ : IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    (automorphicIntegralOperator hΓ μ).val = integralOperator Γ μ := rfl

/-- The actual Bers map is Fréchet differentiable into the original bounded
holomorphic automorphic normed space, with its literal integral derivative. -/
theorem hasFDerivAt_automorphicProjection (hΓ : IsFuchsian Γ) :
    HasFDerivAt (automorphicProjection hΓ) (automorphicIntegralOperator hΓ) 0 := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have h := Asymptotics.isLittleO_iff.mp
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp (hasFDerivAt_projection (Γ := Γ))) hε
  filter_upwards [h] with μ hμ
  change ‖projection (0 + μ) - projection (0 : GammaMeasurableBeltrami.Space Γ) -
    integralOperator Γ μ‖ ≤ ε * ‖μ‖
  exact hμ

/-- The actual Fréchet derivative is the unchanged literal integral operator. -/
theorem fderiv_automorphicProjection (hΓ : IsFuchsian Γ) :
    fderiv ℂ (automorphicProjection hΓ) 0 = automorphicIntegralOperator hΓ := by
  let : ContinuousAdd (Automorphic Γ) :=
    (Submodule.isTopologicalAddGroup (automorphicSubmodule Γ)).toContinuousAdd
  exact (hasFDerivAt_automorphicProjection hΓ).fderiv

/-- Its genuine Fréchet kernel is precisely the original quadratic-differential
annihilator on the unchanged original open fundamental region. -/
theorem fderiv_automorphicProjection_iff_nativeRegionAnnihilator
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℍ} (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    let hΓ : IsFuchsian Γ := utm_x_isFuchsian hp
    fderiv ℂ (automorphicProjection hΓ) 0 μ = 0 ↔
      ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        ∫ z in UpperHalfPlane.coe '' F,
          GammaMeasurableBeltrami.planeRepresentative μ.val z *
            uniformizedQuadratic R p q z = 0 := by
  dsimp only
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let hΓ : IsFuchsian Γ := utm_x_isFuchsian hp
  rw [fderiv_automorphicProjection hΓ]
  have hkernel : automorphicIntegralOperator hΓ μ = 0 ↔ integralOperator Γ μ = 0 := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  rw [hkernel]
  have hamb := fderiv_projection_iff_nativeRegionAnnihilator R P p hp hF μ
  rwa [hasFDerivAt_projection.fderiv] at hamb

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
