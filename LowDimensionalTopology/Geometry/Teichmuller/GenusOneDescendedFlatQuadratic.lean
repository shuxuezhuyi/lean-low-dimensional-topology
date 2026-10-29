module

public import LowDimensionalTopology.Unproved.Teichmuller.NormalizedTorusDzDescent
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusFlatArea
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Ring

/-!
# Conditional original-atlas quadratic tensors from the actual descended dz

The only independent premise is the explicitly named one-differential descent
obligation. Its actual (1,0) coefficient family is squared into the existing
native holomorphic quadratic differential space.
The flat cover density and its fundamental-domain integral are derived.
No native Riemannian volume identification or original T1 metric is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces
open LowDimensionalTopology.Unproved.Teichmuller

/-- Choose the actual one-differential only from the explicit descent premise. -/
def descendedDz (τ : ℍ) (h : NormalizedTorusDzDescent τ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    ↥(LiZhongQC.diffFamilySubmodule ComplexTorusCarrier 1 0) :=
  Classical.choose h

/-- Actual holomorphicity and literal cover pullback of the chosen one-differential. -/
theorem descendedDz_spec (τ : ℍ) (h : NormalizedTorusDzDescent τ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    (∀ x : ComplexTorusCarrier,
      DifferentiableOn ℂ ((descendedDz τ h).val x) (chartAt ℂ x).target) ∧
    ∀ (x : ComplexTorusCarrier) (z : ℂ),
      (normalizedTorusModel τ).projection z ∈ (chartAt ℂ x).source →
        (descendedDz τ h).val x ((chartAt ℂ x) ((normalizedTorusModel τ).projection z)) *
          deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z = 1 :=
  Classical.choose_spec h

/-- The actual holomorphic quadratic tensor c dz² in the original torus atlas.
Its quadratic gluing law is derived by squaring the actual one-form law. -/
def descendedFlatQuadratic (τ : ℍ) (h : NormalizedTorusDzDescent τ) (c : ℂ) :
    HolomorphicQuadraticDifferential (normalizedTorusModel τ).surface.toRiemannAtlas := by
  letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  let η := descendedDz τ h
  have hη : LiZhongQC.IsDiffFamily 1 0 η.val := η.property
  refine ⟨fun x z => c * (η.val x z) ^ 2, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x z hz
    simp only [hη.1 x z hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
  · intro x y z hz hsrc
    have ht := hη.2 x y z hz hsrc
    simp only [zpow_one, zpow_zero, mul_one] at ht
    change c * (η.val y z) ^ 2 = _
    rw [ht]
    simp only [zpow_ofNat, pow_zero, mul_one]
    ring
  · intro x
    exact (((descendedDz_spec τ h).1 x).pow 2).const_mul c

/-- The genuine quadratic tensor has constant plane-cover coefficient c.
The original chart derivative is retained and need not equal one. -/
theorem descendedFlatQuadratic_cover (τ : ℍ) (h : NormalizedTorusDzDescent τ) (c : ℂ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    ∀ (x : ComplexTorusCarrier) (z : ℂ),
      (normalizedTorusModel τ).projection z ∈ (chartAt ℂ x).source →
      (descendedFlatQuadratic τ h c : ComplexTorusCarrier → ℂ → ℂ) x
          ((chartAt ℂ x) ((normalizedTorusModel τ).projection z)) *
        deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z ^ 2 = c := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  intro x z hz
  have hdz := (descendedDz_spec τ h).2 x z hz
  change c * ((descendedDz τ h).val x
      ((chartAt ℂ x) ((normalizedTorusModel τ).projection z))) ^ 2 *
      deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z ^ 2 = c
  calc
    _ = c * ((descendedDz τ h).val x
        ((chartAt ℂ x) ((normalizedTorusModel τ).projection z)) *
      deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z) ^ 2 := by ring
    _ = c := by rw [hdz]; ring

/-- The norm of the actual quadratic pullback is its scalar cover density. -/
theorem descendedFlatQuadratic_cover_norm (τ : ℍ) (h : NormalizedTorusDzDescent τ) (c : ℂ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    ∀ (x : ComplexTorusCarrier) (z : ℂ),
      (normalizedTorusModel τ).projection z ∈ (chartAt ℂ x).source →
      ‖(descendedFlatQuadratic τ h c : ComplexTorusCarrier → ℂ → ℂ) x
          ((chartAt ℂ x) ((normalizedTorusModel τ).projection z))‖ *
        ‖deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z‖ ^ 2 = ‖c‖ := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  intro x z hz
  simpa only [norm_mul, norm_pow] using
    congrArg norm (descendedFlatQuadratic_cover τ h c x z hz)

/-- The normalized absolute quadratic metric pulls back to y⁻¹|dz|².
This is an equality of the actual original quadratic line element on the cover. -/
theorem descendedFlatQuadratic_unit_lineElement (τ : ℍ) (h : NormalizedTorusDzDescent τ) :
    letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
    ∀ (x : ComplexTorusCarrier) (z v : ℂ),
      (normalizedTorusModel τ).projection z ∈ (chartAt ℂ x).source →
      ‖(descendedFlatQuadratic τ h ((τ.im⁻¹ : ℝ) : ℂ) : ComplexTorusCarrier → ℂ → ℂ) x
          ((chartAt ℂ x) ((normalizedTorusModel τ).projection z))‖ *
        ‖deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z * v‖ ^ 2 =
          ‖v‖ ^ 2 / τ.im := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  intro x z v hz
  have hd : ‖(descendedFlatQuadratic τ h ((τ.im⁻¹ : ℝ) : ℂ) :
      ComplexTorusCarrier → ℂ → ℂ) x
      ((chartAt ℂ x) ((normalizedTorusModel τ).projection z))‖ *
      ‖deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z‖ ^ 2 = τ.im⁻¹ := by
    simpa only [Complex.norm_of_nonneg (inv_nonneg.mpr τ.im_pos.le)] using
      descendedFlatQuadratic_cover_norm τ h ((τ.im⁻¹ : ℝ) : ℂ) x z hz
  rw [norm_mul, mul_pow, ← mul_assoc, hd]
  ring

/-- The actual absolute quadratic cover density, using the original preferred
chart at the image point. Its independence and constant value are proved next. -/
def descendedFlatCoverDensity (τ : ℍ) (h : NormalizedTorusDzDescent τ) (z : ℂ) : ℝ :=
  letI := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  let x := (normalizedTorusModel τ).projection z
  ‖(descendedFlatQuadratic τ h ((τ.im⁻¹ : ℝ) : ℂ) : ComplexTorusCarrier → ℂ → ℂ) x
      ((chartAt ℂ x) x)‖ *
    ‖deriv ((chartAt ℂ x) ∘ (normalizedTorusModel τ).projection) z‖ ^ 2

theorem descendedFlatCoverDensity_eq (τ : ℍ) (h : NormalizedTorusDzDescent τ) (z : ℂ) :
    descendedFlatCoverDensity τ h z = τ.im⁻¹ := by
  let := (normalizedTorusModel τ).surface.toRiemannAtlas.toChartedSpace
  simpa only [descendedFlatCoverDensity,
    Complex.norm_of_nonneg (inv_nonneg.mpr τ.im_pos.le)] using
      descendedFlatQuadratic_cover_norm τ h ((τ.im⁻¹ : ℝ) : ℂ)
        ((normalizedTorusModel τ).projection z) z
        (mem_chart_source ℂ ((normalizedTorusModel τ).projection z))

/-- The literal integral of the actual pulled-back quadratic density over the
existing half-open period domain is one. No native metric-volume identity is assumed. -/
theorem integral_descendedFlatCoverDensity (τ : ℍ) (h : NormalizedTorusDzDescent τ) :
    (∫ z in normalizedTorusFlatDomain τ, descendedFlatCoverDensity τ h z
      ∂(volume : Measure ℂ)) = 1 := by
  have hf : descendedFlatCoverDensity τ h =
      fun _ : ℂ => normalizedTorusFlatDensity τ ^ 2 := by
    funext z
    rw [descendedFlatCoverDensity_eq, normalizedTorusFlatDensity_sq]
  rw [hf]
  exact integral_normalizedTorusFlatDensity_sq τ

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
