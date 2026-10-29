module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonOuterPrincipalValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Transposing the original bilinear WP kernel

The lower outer principal value is an ordinary pairing. The actual harmonic
inner principal value agrees with the L² Hilbert representative on the upper
half-plane. Multiplication by the other zero-extended input makes that local
agreement sufficient for the global bilinear Hilbert pairing symmetry.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology Metric
open scoped ComplexConjugate UpperHalfPlane Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open LiZhongQC GammaMeasurableBeltrami Surfaces

private theorem bilinear_ofQuadratic_eq_pairing
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (b : Ambient) (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (ζ z : ℍ) :
    bilinear (fun ξ => b ξ)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) ζ z =
      -(Real.pi : ℂ) * ∫ ξ : ℂ, innerInput (fun η => b η) ζ ξ *
        hilbertH (innerInput
          (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z) ξ := by
  let ν : ℍ → ℂ := fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η
  let f := outerInput (fun ξ => b ξ) ν z
  have hPV := outerInput_ofQuadratic_principalValueExists R hp b q z ζ
  have hlim : Tendsto (fun r : ℝ => -(1 / (Real.pi : ℂ)) *
      ∫ ξ in {ξ : ℂ | r < ‖ξ - conj (ζ : ℂ)‖}, f ξ / (ξ - conj (ζ : ℂ)) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / (Real.pi : ℂ)) *
        ∫ ξ : ℂ, f ξ / (ξ - conj (ζ : ℂ)) ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ζ.im_pos] with r hr
    congr 1
    have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (f := fun ξ : ℂ => f ξ / (ξ - conj (ζ : ℂ)) ^ 2) (μ := (volume : Measure ℂ))
      MeasurableSet.univ (subset_univ {ξ : ℂ | r < ‖ξ - conj (ζ : ℂ)‖})
      (fun ξ hξ => by
        have hn : ‖ξ - conj (ζ : ℂ)‖ ≤ r := not_lt.mp hξ.2
        have hi : ξ.im + ζ.im ≤ ‖ξ - conj (ζ : ℂ)‖ := by
          calc
            ξ.im + ζ.im = (ξ - conj (ζ : ℂ)).im := by
              simp only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add]
            _ ≤ |(ξ - conj (ζ : ℂ)).im| := le_abs_self _
            _ ≤ ‖ξ - conj (ζ : ℂ)‖ := Complex.abs_im_le_norm _
        have hnot : ¬0 < ξ.im := by linarith [hr.2]
        simp only [f, outerInput, upperExtension, hnot, dite_false, zero_div])
    simpa only [setIntegral_univ] using he
  have he : hilbertHSmooth f (conj (ζ : ℂ)) =
      -(1 / (Real.pi : ℂ)) * ∫ ξ : ℂ, f ξ / (ξ - conj (ζ : ℂ)) ^ 2 :=
    tendsto_nhds_unique hPV.2 hlim
  have hproduct : (fun ξ : ℂ => f ξ / (ξ - conj (ζ : ℂ)) ^ 2) =
      (fun ξ : ℂ => innerInput (fun η => b η) ζ ξ *
        hilbertHSmooth (innerInput ν z) ξ) := by
    funext ξ
    by_cases hξ : 0 < ξ.im
    · simp only [f, outerInput, innerInput, upperExtension, hξ, dite_true, cauchySquare,
        div_eq_mul_inv]
      ring
    · simp only [f, outerInput, innerInput, upperExtension, hξ, dite_false,
        zero_div, zero_mul]
  have hlocal := innerInput_ofQuadratic_hilbertHSmooth_eq_hilbertH_ae R hp q z
  have hproductAE :
      (fun ξ : ℂ => innerInput (fun η => b η) ζ ξ *
        hilbertHSmooth (innerInput ν z) ξ) =ᵐ[volume]
      (fun ξ : ℂ => innerInput (fun η => b η) ζ ξ *
        hilbertH (innerInput ν z) ξ) := by
    apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
    · filter_upwards [hlocal] with ξ hξ
      rw [hξ]
    · apply ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl
      intro ξ hξ
      simp only [innerInput, upperExtension, show ¬0 < ξ.im from hξ, dite_false, zero_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold bilinear
  rw [he, hproduct, integral_congr_ae hproductAE]
  field_simp [hπ]; ring

private theorem bilinear_ofQuadratic_transpose
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q₁ q₂ : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ζ z : ℍ) :
    bilinear
        (fun ξ => (NativeHarmonicBeltrami.ofQuadratic R p hp q₁).val ξ)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q₂).val η) ζ z =
      bilinear
        (fun ξ => (NativeHarmonicBeltrami.ofQuadratic R p hp q₂).val ξ)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q₁).val η) z ζ := by
  let b₁ : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q₁).val
  let b₂ : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q₂).val
  rw [bilinear_ofQuadratic_eq_pairing R hp b₁ q₂ ζ z,
    bilinear_ofQuadratic_eq_pairing R hp b₂ q₁ z ζ]
  congr 1
  calc
    _ = ∫ ξ : ℂ, hilbertH (innerInput (fun η => b₁ η) ζ) ξ *
        innerInput (fun η => b₂ η) z ξ :=
      (hilbertH_pairing_symm_L2 (innerInput_memLp_two b₁ ζ)
        (innerInput_memLp_two b₂ z)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => mul_comm _ _

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- Transposing both original points and their actual native harmonic
directions preserves the bilinear kernel, without a symmetry premise. -/
theorem nativeWeilPetersson_bilinear_transpose
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (ζ z : ℍ) :
    SourceKernel.bilinear
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF u)
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF v) ζ z =
      SourceKernel.bilinear
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF v)
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF u) z ζ := by
  let := C
  let bu := TH ν P F hF hsmooth ((K (β ν.val)).symm u)
  let bv := TH ν P F hF hsmooth ((K (β ν.val)).symm v)
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF bu.val).mp bu.property with ⟨q₁, hq₁⟩
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF bv.val).mp bv.property with ⟨q₂, hq₂⟩
  have h := SourceKernel.bilinear_ofQuadratic_transpose
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) q₁ q₂ ζ z
  rw [hq₁, hq₂] at h
  exact h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
