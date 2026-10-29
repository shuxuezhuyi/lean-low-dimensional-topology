module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistInfinitesimal
public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiVariation
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The normalized Cauchy integral of an angular-strip coefficient

The coefficient is the zero extension of the elementary infinitesimal
coefficient from the upper half-plane. Its three-pole normalized integrand
is absolutely integrable, without any compact-support or finite-Lp premise.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- Every point in the closed angular strip lies strictly in the upper half-plane. -/
theorem im_pos_of_arg_mem_interval (θ : Width) {z : ℂ}
    (hz : Complex.arg z ∈ interval θ) : 0 < z.im := by
  have hlo : 0 < Complex.arg z :=
    lt_of_lt_of_le (sub_pos.mpr θ.property.2) hz.1
  have hhi : Complex.arg z < Real.pi := by
    have h := hz.2
    have hθ := θ.property.2
    linarith
  have hne : z ≠ 0 := by
    intro h
    subst z
    simp at hlo
  rw [← Complex.norm_mul_sin_arg z]
  exact mul_pos (norm_pos_iff.mpr hne) (Real.sin_pos_of_pos_of_lt_pi hlo hhi)

open scoped Classical in
/-- The elementary infinitesimal coefficient extended by zero to the complex plane. -/
def infinitesimalZeroExtension (θ : Width) (z : ℂ) : ℂ :=
  if Complex.arg z ∈ interval θ then infinitesimalScale θ * (z / conj z) else 0

/-- Restricting the extension to the native upper half-plane recovers the coefficient. -/
@[simp] theorem infinitesimalZeroExtension_coe (θ : Width) (z : ℍ) :
    infinitesimalZeroExtension θ (z : ℂ) = infinitesimal θ z := rfl

/-- The extension vanishes on the closed lower half-plane, including its boundary. -/
theorem infinitesimalZeroExtension_eq_zero_of_im_nonpos (θ : Width) {z : ℂ}
    (hz : z.im ≤ 0) : infinitesimalZeroExtension θ z = 0 := by
  classical
  have hnot : Complex.arg z ∉ interval θ := fun h =>
    (im_pos_of_arg_mem_interval θ h).not_ge hz
  simp only [infinitesimalZeroExtension, ite_eq_right hnot]

/-- The full-plane expression is literally the zero extension of the native coefficient. -/
theorem infinitesimalZeroExtension_eq_piecewise (θ : Width) (z : ℂ) :
    infinitesimalZeroExtension θ z =
      if hz : 0 < z.im then infinitesimal θ ⟨z, hz⟩ else 0 := by
  classical
  by_cases hz : 0 < z.im
  · simp only [dite_eq_left hz]
    rfl
  · simp only [dite_eq_right hz]
    exact infinitesimalZeroExtension_eq_zero_of_im_nonpos θ (le_of_not_gt hz)

/-- The zero extension is measurable for actual planar Lebesgue measure. -/
theorem measurable_infinitesimalZeroExtension (θ : Width) :
    Measurable (infinitesimalZeroExtension θ) := by
  classical
  have hs : MeasurableSet {z : ℂ | Complex.arg z ∈ interval θ} :=
    measurableSet_Icc.preimage Complex.measurable_arg
  exact Measurable.ite hs
    (measurable_const.mul (measurable_id.div Complex.continuous_conj.measurable))
    measurable_const

/-- The extension satisfies the same uniform bound as the native coefficient. -/
theorem norm_infinitesimalZeroExtension_le (θ : Width) (z : ℂ) :
    ‖infinitesimalZeroExtension θ z‖ ≤ 1 / (4 * (θ : ℝ)) := by
  by_cases hz : 0 < z.im
  · exact norm_infinitesimal_le θ ⟨z, hz⟩
  · rw [infinitesimalZeroExtension_eq_zero_of_im_nonpos θ (le_of_not_gt hz), norm_zero]
    have hθ : 0 < (θ : ℝ) := θ.property.1
    positivity

/-- The actual three-pole normalized Cauchy integrand is absolutely integrable. -/
theorem integrable_infinitesimalZeroExtension_mul_firstVariationKernel
    (θ : Width) (z : ℂ) :
    Integrable (fun ζ : ℂ => infinitesimalZeroExtension θ ζ *
      Quasiconformal.firstVariationKernel z ζ) (volume : Measure ℂ) := by
  exact (LiZhongQC.ah_ker_integrable z).bdd_mul
    (measurable_infinitesimalZeroExtension θ).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_infinitesimalZeroExtension_le θ))

/-- The normalized Cauchy integral of this zero-extended coefficient. -/
def firstCauchyTerm (θ : Width) (z : ℂ) : ℂ :=
  LiZhongQC.ahVar (infinitesimalZeroExtension θ) z

/-- Its full-plane integral is exactly the area integral over the actual upper half-plane. -/
theorem firstCauchyTerm_eq_upperHalfPlane (θ : Width) (z : ℂ) :
    firstCauchyTerm θ z = -(1 / (Real.pi : ℂ)) *
      ∫ ζ in {ζ : ℂ | 0 < ζ.im}, infinitesimalZeroExtension θ ζ *
        Quasiconformal.firstVariationKernel z ζ := by
  unfold firstCauchyTerm LiZhongQC.ahVar
  apply congrArg (fun c : ℂ => -(1 / (Real.pi : ℂ)) * c)
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro ζ hζ
  have hζ' : ζ.im ≤ 0 := le_of_not_gt hζ
  rw [infinitesimalZeroExtension_eq_zero_of_im_nonpos θ hζ', zero_mul]

/-- The normalization at zero holds for the actual integral. -/
@[simp] theorem firstCauchyTerm_zero (θ : Width) : firstCauchyTerm θ 0 = 0 := by
  simp [firstCauchyTerm, LiZhongQC.ahVar, LiZhongQC.ahKer]

/-- The normalization at one holds for the actual integral. -/
@[simp] theorem firstCauchyTerm_one (θ : Width) : firstCauchyTerm θ 1 = 0 := by
  simp [firstCauchyTerm, LiZhongQC.ahVar, LiZhongQC.ahKer]

open scoped Classical in
/-- The real angular density with total mass one on the strip. -/
def angularDensity (θ : Width) (t : ℝ) : ℝ :=
  if t ∈ interval θ then 1 / (2 * (θ : ℝ)) else 0

/-- The oriented angular primitive from the positive real ray. -/
def angularPrimitive (θ : Width) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, angularDensity θ s

/-- The angular and complex-logarithmic expression for the normalized integral. -/
def firstCauchyClosedForm (θ : Width) (z : ℂ) : ℂ :=
  -z * ((angularPrimitive θ (Complex.arg z) : ℂ) +
    Complex.I / (2 * (Real.pi : ℂ)) * Complex.log z)

/-- The closed expression has its zero-valued extension at the origin. -/
@[simp] theorem firstCauchyClosedForm_zero (θ : Width) :
    firstCauchyClosedForm θ 0 = 0 := by
  simp [firstCauchyClosedForm]

/-- The same closed expression is normalized at one. -/
@[simp] theorem firstCauchyClosedForm_one (θ : Width) :
    firstCauchyClosedForm θ 1 = 0 := by
  simp [firstCauchyClosedForm, angularPrimitive]

/-- The actual integral agrees with the closed expression at zero. -/
theorem firstCauchyTerm_eq_closedForm_zero (θ : Width) :
    firstCauchyTerm θ 0 = firstCauchyClosedForm θ 0 := by
  simp

/-- The actual integral agrees with the closed expression at one. -/
theorem firstCauchyTerm_eq_closedForm_one (θ : Width) :
    firstCauchyTerm θ 1 = firstCauchyClosedForm θ 1 := by
  simp

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
