/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Conformal.InnerProduct
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Tactic.Abel


/-!
# Differentiability and conformal linear approximations

The normalized error formulation of differentiability is connected to positive
multiples of linear isometries. Determinants distinguish the two orientations,
and the complex derivative supplies the conformal factor for analytic maps.
-/

@[expose] public section

open scoped Topology

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

universe u


def euclideanDifferentiableAt {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Prop := DifferentiableAt ℝ f x


noncomputable def differentiabilityError {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖y - x‖⁻¹ • (f y - f x - A (y - x))


theorem differentiabilityError_reconstruct {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) :
    f y = f x + A (y - x) + ‖y - x‖ • differentiabilityError f A x y := by
  by_cases h : y = x
  · subst y
    simp [differentiabilityError]
  · unfold differentiabilityError
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)), one_smul]
    abel


theorem hasFDerivAt_iff_differentiabilityError {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt f A x ↔ Filter.Tendsto (differentiabilityError f A x) (𝓝 x) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [differentiabilityError, norm_smul, norm_inv, norm_norm] using
    (hasFDerivAt_iff_tendsto (f := f) (f' := A) (x := x))


theorem euclideanDifferentiableAt_iff_error {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanDifferentiableAt f x ↔
      ∃ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        Filter.Tendsto (differentiabilityError f A x) (𝓝 x) (𝓝 0) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, (hasFDerivAt_iff_differentiabilityError f A x).mp hA⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, (hasFDerivAt_iff_differentiabilityError f A x).mpr hA⟩

section PositiveFactor

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isConformalMap_iff_positive_isometry (A : E →L[ℝ] E) :
    IsConformalMap A ↔ ∃ μ : ℝ, 0 < μ ∧ ∃ O : E ≃ₗᵢ[ℝ] E,
      A = μ • (O : E →L[ℝ] E) := by
  constructor
  · rintro ⟨c, hc, li, hA⟩
    let e := li.toLinearIsometryEquiv rfl
    by_cases hp : 0 < c
    · refine ⟨c, hp, e, hA.trans ?_⟩
      congr 1
    · have hcneg : c < 0 := (lt_or_gt_of_ne hc).resolve_right hp
      refine ⟨-c, neg_pos.mpr hcneg, e.trans (LinearIsometryEquiv.neg ℝ), ?_⟩
      rw [hA]
      ext v
      simp [e]
  · rintro ⟨μ, hμ, O, rfl⟩
    exact ⟨μ, hμ.ne', O.toLinearIsometry, rfl⟩


theorem conformalAt_iff_positive_isometry {f : E → E} {x : E} :
    ConformalAt f x ↔ ∃ μ : ℝ, 0 < μ ∧ ∃ O : E ≃ₗᵢ[ℝ] E,
      HasFDerivAt f (μ • (O : E →L[ℝ] E)) x := by
  constructor
  · rintro ⟨A, hA, hconf⟩
    rcases (isConformalMap_iff_positive_isometry A).mp hconf with ⟨μ, hμ, O, rfl⟩
    exact ⟨μ, hμ, O, hA⟩
  · rintro ⟨μ, hμ, O, hA⟩
    exact ⟨μ • (O : E →L[ℝ] E), hA,
      (isConformalMap_iff_positive_isometry _).mpr ⟨μ, hμ, O, rfl⟩⟩


def directlyConformalAt (f : E → E) (x : E) : Prop :=
  ConformalAt f x ∧ 0 < LinearMap.det (fderiv ℝ f x).toLinearMap


def indirectlyConformalAt (f : E → E) (x : E) : Prop :=
  ConformalAt f x ∧ LinearMap.det (fderiv ℝ f x).toLinearMap < 0

omit [FiniteDimensional ℝ E] in
theorem det_positive_iff_positive_isometry_det {A : E →L[ℝ] E} {μ : ℝ}
    (hμ : 0 < μ) (O : E ≃ₗᵢ[ℝ] E) (hA : A = μ • (O : E →L[ℝ] E)) :
    0 < LinearMap.det A.toLinearMap ↔ 0 < LinearMap.det O.toLinearEquiv.toLinearMap := by
  rw [hA]
  change 0 < LinearMap.det (μ • O.toLinearEquiv.toLinearMap) ↔ _
  rw [LinearMap.det_smul, mul_pos_iff_of_pos_left (pow_pos hμ _)]

omit [FiniteDimensional ℝ E] in
theorem det_negative_iff_positive_isometry_det {A : E →L[ℝ] E} {μ : ℝ}
    (hμ : 0 < μ) (O : E ≃ₗᵢ[ℝ] E) (hA : A = μ • (O : E →L[ℝ] E)) :
    LinearMap.det A.toLinearMap < 0 ↔ LinearMap.det O.toLinearEquiv.toLinearMap < 0 := by
  rw [hA]
  change LinearMap.det (μ • O.toLinearEquiv.toLinearMap) < 0 ↔ _
  rw [LinearMap.det_smul]
  simpa only [mul_zero] using
    (mul_lt_mul_iff_of_pos_left (pow_pos hμ (Module.finrank ℝ E)) :
      μ ^ Module.finrank ℝ E * LinearMap.det O.toLinearEquiv.toLinearMap <
          μ ^ Module.finrank ℝ E * (0 : ℝ) ↔
        LinearMap.det O.toLinearEquiv.toLinearMap < 0)


theorem directlyConformalAt_iff_positive_isometry {f : E → E} {x : E} :
    directlyConformalAt f x ↔ ∃ μ : ℝ, 0 < μ ∧ ∃ O : E ≃ₗᵢ[ℝ] E,
      HasFDerivAt f (μ • (O : E →L[ℝ] E)) x ∧
        0 < LinearMap.det O.toLinearEquiv.toLinearMap := by
  constructor
  · rintro ⟨hc, hd⟩
    rcases conformalAt_iff_positive_isometry.mp hc with ⟨μ, hμ, O, hf⟩
    refine ⟨μ, hμ, O, hf, ?_⟩
    rw [hf.fderiv] at hd
    exact (det_positive_iff_positive_isometry_det hμ O rfl).mp hd
  · rintro ⟨μ, hμ, O, hf, hd⟩
    refine ⟨conformalAt_iff_positive_isometry.mpr ⟨μ, hμ, O, hf⟩, ?_⟩
    rw [hf.fderiv]
    exact (det_positive_iff_positive_isometry_det hμ O rfl).mpr hd


theorem indirectlyConformalAt_iff_positive_isometry {f : E → E} {x : E} :
    indirectlyConformalAt f x ↔ ∃ μ : ℝ, 0 < μ ∧ ∃ O : E ≃ₗᵢ[ℝ] E,
      HasFDerivAt f (μ • (O : E →L[ℝ] E)) x ∧
        LinearMap.det O.toLinearEquiv.toLinearMap < 0 := by
  constructor
  · rintro ⟨hc, hd⟩
    rcases conformalAt_iff_positive_isometry.mp hc with ⟨μ, hμ, O, hf⟩
    refine ⟨μ, hμ, O, hf, ?_⟩
    rw [hf.fderiv] at hd
    exact (det_negative_iff_positive_isometry_det hμ O rfl).mp hd
  · rintro ⟨μ, hμ, O, hf, hd⟩
    refine ⟨conformalAt_iff_positive_isometry.mpr ⟨μ, hμ, O, hf⟩, ?_⟩
    rw [hf.fderiv]
    exact (det_negative_iff_positive_isometry_det hμ O rfl).mpr hd

end PositiveFactor


def euclideanConformalAt {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Prop := ConformalAt f x


theorem euclideanConformalAt_iff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanConformalAt f x ↔ ∃ μ : ℝ, 0 < μ ∧
      ∃ O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
        HasFDerivAt f (μ • (O : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n))) x := conformalAt_iff_positive_isometry

/-- The open-mapping assertion includes the necessary nonconstancy hypothesis. -/
theorem analytic_open_mapping {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D)
    (hconn : IsConnected D) (hf : DifferentiableOn ℂ f D)
    (hnon : ¬ ∃ w : ℂ, ∀ z ∈ D, f z = w) :
    ∀ s ⊆ D, IsOpen s → IsOpen (f '' s) :=
  ((hf.analyticOnNhd hD).is_constant_or_isOpen hconn.isPreconnected).resolve_left hnon


theorem analytic_domain_image_open {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D)
    (hconn : IsConnected D) (hf : DifferentiableOn ℂ f D)
    (hnon : ¬ ∃ w : ℂ, ∀ z ∈ D, f z = w) : IsOpen (f '' D) :=
  analytic_open_mapping hD hconn hf hnon D Set.Subset.rfl hD


theorem complexDifferentiable_conformalAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hderiv : deriv f z ≠ 0) : ConformalAt f z :=
  hf.conformalAt hderiv

theorem complex_real_fderiv_det {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = Complex.normSq (deriv f z) := by
  have hfc : (fderiv ℂ f z).toLinearMap = (deriv f z) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := by
    ext
    exact fderiv_eq_deriv_mul
  rw [(hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change LinearMap.det ((fderiv ℂ f z).toLinearMap.restrictScalars ℝ) = _
  rw [LinearMap.det_restrictScalars, hfc]
  simp only [LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id,
    mul_one, Algebra.norm_complex_apply]


theorem complexDifferentiable_directlyConformalAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hderiv : deriv f z ≠ 0) : directlyConformalAt f z := by
  refine ⟨hf.conformalAt hderiv, ?_⟩
  rw [complex_real_fderiv_det hf]
  exact Complex.normSq_pos.mpr hderiv


theorem analytic_directlyConformalAt {D : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) {z : ℂ} (hz : z ∈ D) (hderiv : deriv f z ≠ 0) :
    directlyConformalAt f z :=
  complexDifferentiable_directlyConformalAt (hf z hz).differentiableAt hderiv


theorem conformal_norm_ratio_tendsto
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x : E} {μ : ℝ} (hμ : 0 < μ) (O : E ≃ₗᵢ[ℝ] E)
    (hf : HasFDerivAt f (μ • (O : E →L[ℝ] E)) x) :
    Filter.Tendsto (fun y => ‖f y - f x‖ / ‖y - x‖) (𝓝[≠] x) (𝓝 μ) := by
  have hrem : Filter.Tendsto
      (fun y => ‖y - x‖⁻¹ * ‖f y - f x - (μ • (O : E →L[ℝ] E)) (y - x)‖)
      (𝓝[≠] x) (𝓝 0) :=
    (hasFDerivAt_iff_tendsto.mp hf).mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ y in 𝓝[≠] x,
      ‖‖f y - f x‖ / ‖y - x‖ - μ‖ ≤
        ‖y - x‖⁻¹ * ‖f y - f x - (μ • (O : E →L[ℝ] E)) (y - x)‖ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hxy : y ≠ x := hy
    have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hscale : ‖(μ • (O : E →L[ℝ] E)) (y - x)‖ = μ * ‖y - x‖ := by
      change ‖μ • O (y - x)‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ, O.norm_map]
    calc
      ‖‖f y - f x‖ / ‖y - x‖ - μ‖ =
          |(‖f y - f x‖ - ‖(μ • (O : E →L[ℝ] E)) (y - x)‖) / ‖y - x‖| := by
        rw [Real.norm_eq_abs]
        congr 1
        rw [hscale]
        field_simp
      _ = |‖f y - f x‖ - ‖(μ • (O : E →L[ℝ] E)) (y - x)‖| / ‖y - x‖ := by
        rw [abs_div, abs_of_pos hn]
      _ ≤ ‖f y - f x - (μ • (O : E →L[ℝ] E)) (y - x)‖ / ‖y - x‖ :=
        (div_le_div_iff_of_pos_right hn).mpr (abs_norm_sub_norm_le _ _)
      _ = ‖y - x‖⁻¹ * ‖f y - f x - (μ • (O : E →L[ℝ] E)) (y - x)‖ :=
        div_eq_inv_mul _ _
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hrem)


theorem conformalAt_norm_ratio_exists
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} {x : E} (hf : ConformalAt f x) :
    ∃ μ : ℝ, 0 < μ ∧
      Filter.Tendsto (fun y => ‖f y - f x‖ / ‖y - x‖) (𝓝[≠] x) (𝓝 μ) := by
  rcases conformalAt_iff_positive_isometry.mp hf with ⟨μ, hμ, O, hderiv⟩
  exact ⟨μ, hμ, conformal_norm_ratio_tendsto hμ O hderiv⟩

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
