module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillSection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicDecomposition
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# The literal Ahlfors-Weill section is the existing harmonic inverse

The genuine nonlinear section identity differentiates to the exact integral
right-inverse identity. Actual reflection to an original quadratic differential
identifies every section coefficient with minus twice its literal harmonic
coefficient. Hence the section belongs to the existing harmonic submodule.
Injectivity of the existing harmonic derivative then identifies its inverse
and the original harmonic projection with these actual coefficients.
No harmonic space or norm is redefined.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open GammaMeasurableBeltrami Surfaces

variable {Γ : Subgroup Deck}

/-- Differentiate the genuine nonlinear section; the literal integral is its exact right inverse. -/
theorem automorphicIntegralOperator_comp_ahlforsWeill (hΓ : LiZhongQC.IsFuchsian Γ) :
    (automorphicIntegralOperator hΓ).comp (ahlforsWeill (Γ := Γ)) =
      ContinuousLinearMap.id ℂ (Automorphic Γ) := by
  have hp : HasFDerivAt (automorphicProjection hΓ) (automorphicIntegralOperator hΓ)
      (ahlforsWeill (0 : Automorphic Γ)) := by
    simpa only [map_zero] using hasFDerivAt_automorphicProjection hΓ
  have hc := hp.comp (0 : Automorphic Γ) (ahlforsWeill (Γ := Γ)).hasFDerivAt
  have hid : HasFDerivAt (id : Automorphic Γ → Automorphic Γ)
      ((automorphicIntegralOperator hΓ).comp (ahlforsWeill (Γ := Γ))) 0 := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Automorphic Γ)
      (by norm_num : 0 < (1 / 2 : ℝ))] with φ hφ
    exact (automorphicProjection_ahlforsWeill hΓ φ (mem_ball_zero_iff.mp hφ)).symm
  exact hid.unique (hasFDerivAt_id 0)

@[simp] theorem automorphicIntegralOperator_ahlforsWeill (hΓ : LiZhongQC.IsFuchsian Γ)
    (φ : Automorphic Γ) : automorphicIntegralOperator hΓ (ahlforsWeill φ) = φ := by
  exact congrArg (fun T : Automorphic Γ →L[ℂ] Automorphic Γ => T φ)
    (automorphicIntegralOperator_comp_ahlforsWeill hΓ)

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- The actual section class is minus twice a literal original harmonic coefficient. -/
theorem exists_ahlforsWeill_eq_smul_ofQuadratic (φ : Automorphic Γ) :
    ∃ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      ahlforsWeill φ = (-2 : ℂ) • NativeHarmonicBeltrami.ofQuadratic R p hp q := by
  obtain ⟨q, hq⟩ := exists_reflected_originalQuadratic R p hp φ
  refine ⟨q, ?_⟩
  apply Subtype.ext
  change (ahlforsWeill φ).val = (-2 : ℂ) • (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
  apply Lp.ext
  filter_upwards [ahlforsWeill_coe_ae φ, NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q,
    Lp.coeFn_smul (-2 : ℂ) (NativeHarmonicBeltrami.ofQuadratic R p hp q).val]
    with z hφ hqz hsmul
  have hz : conj (z : ℂ) ∈ LiZhongQC.lowerHalf := by
    change (conj (z : ℂ)).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr z.im_pos
  have hreflect := hq (conj (z : ℂ)) hz
  simp only [Complex.conj_conj] at hreflect
  rw [hφ, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul, hqz]
  rw [ahlforsWeillCoefficient, ← hreflect, NativeHarmonicBeltrami.coefficient_eq_uniformized]
  ring

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces GammaMeasurableBeltrami

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- The literal section lies in the already defined full harmonic submodule. -/
theorem ahlforsWeill_mem_harmonicSubmodule (φ : BersWeighted.Automorphic Γ) :
    BersWeighted.ahlforsWeill φ ∈ harmonicSubmodule R P p hp F hF := by
  obtain ⟨q, hq⟩ := BersWeighted.exists_ahlforsWeill_eq_smul_ofQuadratic R p hp φ
  rw [hq]
  apply (harmonicSubmodule R P p hp F hF).smul_mem
  exact (mem_harmonicSubmodule_iff_exists_quadratic R P p hp F hF _).mpr ⟨q, rfl⟩

/-- The existing harmonic derivative inverse is exactly the original section coefficient class. -/
theorem harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill (hΓ : LiZhongQC.IsFuchsian Γ)
    (φ : BersWeighted.Automorphic Γ) :
    ((harmonicDerivativeEquiv R P p hp F hF hΓ).symm φ).val =
      BersWeighted.ahlforsWeill φ := by
  let w : Harmonic R P p hp F hF :=
    ⟨BersWeighted.ahlforsWeill φ, ahlforsWeill_mem_harmonicSubmodule R P p hp F hF φ⟩
  have hw : harmonicDerivativeEquiv R P p hp F hF hΓ w = φ := by
    rw [harmonicDerivativeEquiv_apply]
    exact BersWeighted.automorphicIntegralOperator_ahlforsWeill hΓ φ
  have he : (harmonicDerivativeEquiv R P p hp F hF hΓ).symm φ = w := by
    apply (harmonicDerivativeEquiv R P p hp F hF hΓ).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, hw]
  exact congrArg Subtype.val he

/-- The existing harmonic projection is the literal section after the literal Bers integral. -/
theorem harmonicProjection_eq_ahlforsWeill_integral (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    harmonicProjection R P p hp F hF μ =
      BersWeighted.ahlforsWeill (BersWeighted.automorphicIntegralOperator hΓ μ) := by
  let w : Harmonic R P p hp F hF :=
    ⟨harmonicProjection R P p hp F hF μ, ⟨μ, rfl⟩⟩
  have hw : (harmonicDerivativeEquiv R P p hp F hF hΓ).symm
      (BersWeighted.automorphicIntegralOperator hΓ μ) = w := by
    apply (harmonicDerivativeEquiv R P p hp F hF hΓ).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, harmonicDerivativeEquiv_apply]
    apply Subtype.ext
    simpa only [BersWeighted.automorphicIntegralOperator_val] using
      (harmonicProjection_bers R P p hp F hF μ).symm
  exact (congrArg Subtype.val hw).symm.trans
    (harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill R P p hp F hF hΓ _)

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
