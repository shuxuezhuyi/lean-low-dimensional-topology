module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusModel
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Unit-area data from the actual normalized period torus

The fundamental domain belongs to the existing integer lattice of 1 and tau.
Its normalized flat measure is pushed through the existing genuine projection.
This does not yet package an intrinsic Riemannian metric on the torus bundle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Module MeasureTheory
open scoped UpperHalfPlane InnerProductSpace

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The genuine half-open period parallelogram for the existing normalized torus. -/
def normalizedTorusFlatDomain (τ : ℍ) : Set ℂ :=
  ZSpan.fundamentalDomain (normalizedTorusBasis τ)

theorem normalizedTorusFlatDomain_isFundamental (τ : ℍ) :
    IsAddFundamentalDomain (normalizedPeriodLattice τ) (normalizedTorusFlatDomain τ)
      (volume : Measure ℂ) := by
  rw [normalizedPeriodLattice, ← normalizedTorusBasis_span τ]
  exact ZSpan.isAddFundamentalDomain (normalizedTorusBasis τ) (volume : Measure ℂ)

theorem normalizedTorusBasis_det (τ : ℍ) :
    Complex.basisOneI.det (normalizedTorusBasis τ) = τ.im := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, Complex.coe_basisOneI_repr]

/-- The area is computed from the actual periods, not postulated to be Im tau. -/
theorem volume_normalizedTorusFlatDomain (τ : ℍ) :
    (volume : Measure ℂ) (normalizedTorusFlatDomain τ) = ENNReal.ofReal τ.im := by
  let b₀ := Complex.orthonormalBasisOneI.toBasis
  have hunit : (volume : Measure ℂ) (ZSpan.fundamentalDomain b₀) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ volume)]
    exact Complex.orthonormalBasisOneI.volume_parallelepiped
  have h := ZSpan.measure_fundamentalDomain (normalizedTorusBasis τ)
    (volume : Measure ℂ) b₀
  simp only [b₀, Complex.toBasis_orthonormalBasisOneI] at hunit
  simpa only [normalizedTorusFlatDomain, b₀, Complex.toBasis_orthonormalBasisOneI,
    normalizedTorusBasis_det, abs_of_pos τ.im_pos, hunit, mul_one] using h

/-- The source's positive constant length density on the actual plane cover. -/
def normalizedTorusFlatDensity (τ : ℍ) : ℝ := 1 / Real.sqrt τ.im

theorem normalizedTorusFlatDensity_pos (τ : ℍ) : 0 < normalizedTorusFlatDensity τ :=
  one_div_pos.mpr (Real.sqrt_pos.mpr τ.im_pos)

theorem normalizedTorusFlatDensity_sq (τ : ℍ) :
    normalizedTorusFlatDensity τ ^ 2 = τ.im⁻¹ := by
  rw [normalizedTorusFlatDensity, one_div, inv_pow, Real.sq_sqrt τ.im_pos.le]

/-- The constant flat real tensor on the original complex plane cover. -/
def normalizedTorusFlatCoverTensor (τ : ℍ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  τ.im⁻¹ • innerSL ℝ

theorem normalizedTorusFlatCoverTensor_self (τ : ℍ) (v : ℂ) :
    normalizedTorusFlatCoverTensor τ v v = ‖v‖ ^ 2 / τ.im := by
  change τ.im⁻¹ * inner ℝ v v = _
  rw [real_inner_self_eq_norm_sq]
  ring

/-- The actual Euclidean cover measure with the source's squared density. -/
def normalizedTorusFlatCoverArea (τ : ℍ) : Measure ℂ :=
  ENNReal.ofReal τ.im⁻¹ • volume

theorem normalizedTorusFlatCoverArea_domain (τ : ℍ) :
    normalizedTorusFlatCoverArea τ (normalizedTorusFlatDomain τ) = 1 := by
  rw [normalizedTorusFlatCoverArea, Measure.smul_apply, smul_eq_mul,
    volume_normalizedTorusFlatDomain,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr τ.im_pos.le),
    inv_mul_cancel₀ τ.im_ne_zero, ENNReal.ofReal_one]

/-- The literal unit-area normalization integral on a genuine period domain. -/
theorem integral_normalizedTorusFlatDensity_sq (τ : ℍ) :
    (∫ _ in normalizedTorusFlatDomain τ, normalizedTorusFlatDensity τ ^ 2
      ∂(volume : Measure ℂ)) = 1 := by
  rw [setIntegral_const, smul_eq_mul, measureReal_def,
    volume_normalizedTorusFlatDomain, ENNReal.toReal_ofReal τ.im_pos.le,
    normalizedTorusFlatDensity_sq, mul_inv_cancel₀ τ.im_ne_zero]

/-- The normalized flat area measure on the EXISTING actual torus carrier. -/
def normalizedTorusUnitAreaMeasure (τ : ℍ) : Measure ComplexTorusCarrier :=
  Measure.map (normalizedTorusModel τ).projection
    ((normalizedTorusFlatCoverArea τ).restrict (normalizedTorusFlatDomain τ))

/-- Its total area is derived from the original cover and actual fundamental domain. -/
theorem normalizedTorusUnitAreaMeasure_univ (τ : ℍ) :
    normalizedTorusUnitAreaMeasure τ univ = 1 := by
  rw [normalizedTorusUnitAreaMeasure,
    Measure.map_apply (normalizedTorusModel τ).covering.continuous.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, normalizedTorusFlatCoverArea_domain]

end LowDimensionalTopology.Geometry.Surfaces
