module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNormalizedCoefficientMap
public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpQuasiPullback
public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpBoundedMultipliers

/-!
# The literal bounded coefficient transport at an actual nonzero base coefficient

The source and target carry the same original hyperbolic L-infinity class norm.
The actual normalized quasiconformal map supplies its two null-set-preserving
changes of variables. Multiplication by the literal derivative weight gives
the book's coefficient transport; the explicit reciprocal weight gives its
bounded inverse. No transport operator or inverse is assumed as additional data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The original coefficient's literal positive denominator. -/
def coefficientDenominator (ν : Ball Γ) (z : ℍ) : ℂ :=
  1 - conj (ν.val.val z) * ν.val.val z

/-- The literal derivative weight before change of variables. -/
def derivativeWeight (ν : Ball Γ) (z : ℍ) : ℂ :=
  derivativePhase ν z / coefficientDenominator ν z

/-- The literal reciprocal weight for the inverse transport. -/
def inverseWeight (ν : Ball Γ) (z : ℍ) : ℂ :=
  coefficientDenominator ν z / derivativePhase ν z

/-- The quantitative derivative bound in the original essential norm. -/
def derivativeBound (ν : Ball Γ) : ℝ := (1 - ‖ν.val.val‖ ^ 2)⁻¹

/-- A finite bound for the actual inverse weight. -/
def inverseBound (ν : Ball Γ) : ℝ := 1 + ‖ν.val.val‖ ^ 2

theorem one_sub_norm_sq_pos (ν : Ball Γ) : 0 < 1 - ‖ν.val.val‖ ^ 2 := by
  have hk : ‖ν.val.val‖ < 1 := Ball.norm_lt_one ν
  nlinarith [norm_nonneg ν.val.val]

theorem derivativeBound_nonneg (ν : Ball Γ) : 0 ≤ derivativeBound ν :=
  inv_nonneg.mpr (one_sub_norm_sq_pos ν).le

theorem inverseBound_nonneg (ν : Ball Γ) : 0 ≤ inverseBound ν :=
  add_nonneg zero_le_one (sq_nonneg ‖ν.val.val‖)

theorem coefficientDenominator_aestronglyMeasurable (ν : Ball Γ) :
    AEStronglyMeasurable (coefficientDenominator ν) (volume : Measure ℍ) := by
  have hm := Lp.aestronglyMeasurable ν.val.val
  exact aestronglyMeasurable_const.sub
    ((Complex.continuous_conj.comp_aestronglyMeasurable hm).mul hm)

theorem derivativeWeight_aestronglyMeasurable (ν : Ball Γ) :
    AEStronglyMeasurable (derivativeWeight ν) (volume : Measure ℍ) :=
  (derivativePhase_aestronglyMeasurable ν).div₀
    (coefficientDenominator_aestronglyMeasurable ν)

theorem inverseWeight_aestronglyMeasurable (ν : Ball Γ) :
    AEStronglyMeasurable (inverseWeight ν) (volume : Measure ℍ) :=
  (coefficientDenominator_aestronglyMeasurable ν).div₀
    (derivativePhase_aestronglyMeasurable ν)

/-- The strict coefficient bound gives a uniform nonzero denominator a.e. -/
theorem coefficientDenominator_lower_ae (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, 1 - ‖ν.val.val‖ ^ 2 ≤ ‖coefficientDenominator ν z‖ := by
  filter_upwards [lpInfinity_norm_ae_le ν.val.val] with z hz
  have hm : ‖conj (ν.val.val z) * ν.val.val z‖ ≤ ‖ν.val.val‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, pow_two]
    exact mul_le_mul hz hz (norm_nonneg (ν.val.val z)) (norm_nonneg ν.val.val)
  have hs := norm_sub_norm_le (1 : ℂ) (conj (ν.val.val z) * ν.val.val z)
  rw [norm_one] at hs
  change 1 - ‖ν.val.val‖ ^ 2 ≤ ‖1 - conj (ν.val.val z) * ν.val.val z‖
  linarith

/-- The same literal denominator has an explicit finite upper bound a.e. -/
theorem coefficientDenominator_upper_ae (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, ‖coefficientDenominator ν z‖ ≤ inverseBound ν := by
  filter_upwards [lpInfinity_norm_ae_le ν.val.val] with z hz
  change ‖1 - conj (ν.val.val z) * ν.val.val z‖ ≤ 1 + ‖ν.val.val‖ ^ 2
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖conj (ν.val.val z) * ν.val.val z‖ := norm_sub_le _ _
    _ = 1 + ‖ν.val.val z‖ ^ 2 := by
      rw [norm_one, norm_mul, Complex.norm_conj, pow_two]
    _ ≤ 1 + ‖ν.val.val‖ ^ 2 :=
      add_le_add (le_refl (1 : ℝ)) (pow_le_pow_left₀ (norm_nonneg (ν.val.val z)) hz 2)

theorem norm_derivativeWeight_ae_le (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, ‖derivativeWeight ν z‖ ≤ derivativeBound ν := by
  filter_upwards [coefficientDenominator_lower_ae ν] with z hz
  rw [derivativeWeight, norm_div]
  calc
    _ ≤ 1 / ‖coefficientDenominator ν z‖ :=
      div_le_div_of_nonneg_right (norm_derivativePhase_le ν z)
        (norm_nonneg (coefficientDenominator ν z))
    _ ≤ 1 / (1 - ‖ν.val.val‖ ^ 2) :=
      div_le_div_of_nonneg_left zero_le_one (one_sub_norm_sq_pos ν) hz
    _ = derivativeBound ν := by rw [derivativeBound, one_div]

theorem norm_inverseWeight_ae_le (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, ‖inverseWeight ν z‖ ≤ inverseBound ν := by
  filter_upwards [norm_derivativePhase_ae ν, coefficientDenominator_upper_ae ν]
    with z hphase hdenom
  rw [inverseWeight, norm_div, hphase, div_one]
  exact hdenom

/-- Both concrete factors are nonzero outside the genuine null exceptional set. -/
theorem inverseWeight_mul_derivativeWeight_ae (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, inverseWeight ν z * derivativeWeight ν z = 1 := by
  filter_upwards [coefficientDenominator_lower_ae ν, norm_derivativePhase_ae ν]
    with z hdenom hphase
  have hd : coefficientDenominator ν z ≠ 0 :=
    norm_pos_iff.mp ((one_sub_norm_sq_pos ν).trans_le hdenom)
  have hp : derivativePhase ν z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hphase]
    exact one_ne_zero
  rw [inverseWeight, derivativeWeight, div_mul_div_comm,
    mul_comm (coefficientDenominator ν z) (derivativePhase ν z),
    div_self (mul_ne_zero hp hd)]

theorem derivativeWeight_mul_inverseWeight_ae (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, derivativeWeight ν z * inverseWeight ν z = 1 := by
  filter_upwards [inverseWeight_mul_derivativeWeight_ae ν] with z hz
  exact (mul_comm _ _).trans hz

/-- The literal linear derivative transport on the entire original ambient space. -/
def ambientDerivative (ν : Ball Γ) : Ambient →L[ℂ] Ambient :=
  (quasiPullback (normalizedUpperEquiv ν).symm
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν)).comp
    (boundedMultiply (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
      (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν))

/-- Its literal inverse before restriction to compatible subspaces. -/
def ambientInverse (ν : Ball Γ) : Ambient →L[ℂ] Ambient :=
  (boundedMultiply (inverseWeight ν) (inverseWeight_aestronglyMeasurable ν)
    (inverseBound_nonneg ν) (norm_inverseWeight_ae_le ν)).comp
    (quasiPullback (normalizedUpperEquiv ν)
      (normalizedUpperEquiv_quasiMeasurePreserving ν))

theorem ambientDerivative_weighted_coe_ae (ν : Ball Γ) (μ : Ambient) :
    ambientDerivative ν μ =ᵐ[volume] fun z =>
      derivativeWeight ν ((normalizedUpperEquiv ν).symm z) *
        μ ((normalizedUpperEquiv ν).symm z) := by
  filter_upwards [quasiPullback_coe_ae (normalizedUpperEquiv ν).symm
      (normalizedUpperEquiv_symm_quasiMeasurePreserving ν)
      (boundedMultiply (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ),
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae
      (boundedMultiply_coe_ae (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ)] with z hp hm
  exact hp.trans hm

/-- The value is exactly the book's coefficient formula with its actual inverse map. -/
theorem ambientDerivative_coe_ae (ν : Ball Γ) (μ : Ambient) :
    ambientDerivative ν μ =ᵐ[volume] fun z =>
      μ ((normalizedUpperEquiv ν).symm z) /
          (1 - conj (ν.val.val ((normalizedUpperEquiv ν).symm z)) *
            ν.val.val ((normalizedUpperEquiv ν).symm z)) *
        derivativePhase ν ((normalizedUpperEquiv ν).symm z) := by
  filter_upwards [ambientDerivative_weighted_coe_ae ν μ] with z hz
  rw [hz]
  simp only [derivativeWeight, coefficientDenominator, div_eq_mul_inv]
  ring

theorem ambientInverse_weighted_coe_ae (ν : Ball Γ) (μ : Ambient) :
    ambientInverse ν μ =ᵐ[volume] fun z =>
      inverseWeight ν z * μ (normalizedUpperEquiv ν z) := by
  filter_upwards [boundedMultiply_coe_ae (inverseWeight ν)
      (inverseWeight_aestronglyMeasurable ν) (inverseBound_nonneg ν)
      (norm_inverseWeight_ae_le ν)
      (quasiPullback (normalizedUpperEquiv ν)
        (normalizedUpperEquiv_quasiMeasurePreserving ν) μ),
    quasiPullback_coe_ae (normalizedUpperEquiv ν)
      (normalizedUpperEquiv_quasiMeasurePreserving ν) μ] with z hm hp
  exact hm.trans (congrArg (fun w : ℂ => inverseWeight ν z * w) hp)

theorem ambientInverse_coe_ae (ν : Ball Γ) (μ : Ambient) :
    ambientInverse ν μ =ᵐ[volume] fun z =>
      (1 - conj (ν.val.val z) * ν.val.val z) / derivativePhase ν z *
        μ (normalizedUpperEquiv ν z) := by
  filter_upwards [ambientInverse_weighted_coe_ae ν μ] with z hz
  exact hz

theorem norm_ambientDerivative_le (ν : Ball Γ) (μ : Ambient) :
    ‖ambientDerivative ν μ‖ ≤ derivativeBound ν * ‖μ‖ := by
  calc
    _ ≤ ‖boundedMultiply (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ‖ :=
      norm_quasiPullback_le (normalizedUpperEquiv ν).symm
        (normalizedUpperEquiv_symm_quasiMeasurePreserving ν) _
    _ ≤ derivativeBound ν * ‖μ‖ :=
      norm_boundedMultiply_le (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ

theorem norm_ambientInverse_le (ν : Ball Γ) (μ : Ambient) :
    ‖ambientInverse ν μ‖ ≤ inverseBound ν * ‖μ‖ := by
  calc
    _ ≤ inverseBound ν * ‖quasiPullback (normalizedUpperEquiv ν)
        (normalizedUpperEquiv_quasiMeasurePreserving ν) μ‖ :=
      norm_boundedMultiply_le (inverseWeight ν) (inverseWeight_aestronglyMeasurable ν)
        (inverseBound_nonneg ν) (norm_inverseWeight_ae_le ν) _
    _ ≤ inverseBound ν * ‖μ‖ :=
      mul_le_mul_of_nonneg_left (norm_quasiPullback_le (normalizedUpperEquiv ν)
        (normalizedUpperEquiv_quasiMeasurePreserving ν) μ) (inverseBound_nonneg ν)

/-- The explicit inverse cancels the actual derivative on every original coefficient. -/
theorem ambientInverse_ambientDerivative (ν : Ball Γ) (μ : Ambient) :
    ambientInverse ν (ambientDerivative ν μ) = μ := by
  apply Lp.ext
  filter_upwards [ambientInverse_weighted_coe_ae ν (ambientDerivative ν μ),
    (normalizedUpperEquiv_quasiMeasurePreserving ν).ae
      (ambientDerivative_weighted_coe_ae ν μ),
    inverseWeight_mul_derivativeWeight_ae ν] with z hi hd hw
  rw [hi, hd, Equiv.symm_apply_apply, ← mul_assoc, hw, one_mul]

/-- Cancellation in the other order uses the same actual normalized inverse. -/
theorem ambientDerivative_ambientInverse (ν : Ball Γ) (μ : Ambient) :
    ambientDerivative ν (ambientInverse ν μ) = μ := by
  apply Lp.ext
  filter_upwards [ambientDerivative_weighted_coe_ae ν (ambientInverse ν μ),
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae
      (ambientInverse_weighted_coe_ae ν μ),
    (normalizedUpperEquiv_symm_quasiMeasurePreserving ν).ae
      (derivativeWeight_mul_inverseWeight_ae ν)] with z hd hi hw
  rw [hd, hi, Equiv.apply_symm_apply, ← mul_assoc, hw, one_mul]

/-- The genuine bounded ambient transport equivalence in the unchanged essential norms. -/
def ambientEquiv (ν : Ball Γ) : Ambient ≃L[ℂ] Ambient where
  toLinearEquiv :=
    { (ambientDerivative ν).toLinearMap with
      invFun := ambientInverse ν
      left_inv := ambientInverse_ambientDerivative ν
      right_inv := ambientDerivative_ambientInverse ν }
  continuous_toFun := (ambientDerivative ν).continuous
  continuous_invFun := (ambientInverse ν).continuous

@[simp] theorem ambientEquiv_apply (ν : Ball Γ) (μ : Ambient) :
    ambientEquiv ν μ = ambientDerivative ν μ := rfl

@[simp] theorem ambientEquiv_symm_apply (ν : Ball Γ) (μ : Ambient) :
    (ambientEquiv ν).symm μ = ambientInverse ν μ := rfl

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
