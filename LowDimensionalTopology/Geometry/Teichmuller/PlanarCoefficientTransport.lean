module

public import LowDimensionalTopology.Geometry.Teichmuller.PlanarLpCoefficientOperators
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientTranslation

/-!
# Coefficient transport on the full planar measurable coefficient space

The fixed map is the actual normalized solution of the given planar coefficient
class. Both directions preserve null sets. Its literal derivative phase and
coefficient denominator give a bounded complex-linear equivalence on the full
planar L-infinity space, in its original essential norm.

The measure-class operator proofs reuse the existing coefficient-transport
proofs on the upper half plane, with every carrier and measure here explicitly
changed to the plane. No group compatibility condition is imposed. The actual
quasiconformal facts reuse Wu Xiaobin's LiZhongQC development; see
`THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport

/-- The actual full-plane normalized homeomorphism at the given base class. -/
abbrev normalizedMap (ν : MeasurableBeltramiBall) : ℂ ≃ₜ ℂ :=
  MeasurableBeltramiBall.normalizedSolution ν

/-- Its unchanged underlying equivalence of the full plane. -/
abbrev normalizedEquiv (ν : MeasurableBeltramiBall) : ℂ ≃ ℂ :=
  (normalizedMap ν).toEquiv

/-- The source inverse convention agrees with the actual homeomorphism inverse. -/
theorem invFunOn_normalizedMap (ν : MeasurableBeltramiBall) :
    Function.invFunOn (normalizedMap ν) univ = (normalizedMap ν).symm := by
  funext w
  apply (normalizedMap ν).injective
  exact (Function.invFunOn_eq
    ⟨(normalizedMap ν).symm w, mem_univ _, (normalizedMap ν).apply_symm_apply w⟩).trans
      ((normalizedMap ν).apply_symm_apply w).symm

/-- The actual normalized inverse preserves the planar measure class. -/
theorem normalizedEquiv_symm_quasiMeasurePreserving (ν : MeasurableBeltramiBall) :
    QuasiMeasurePreserving (normalizedEquiv ν).symm (volume : Measure ℂ) volume := by
  have h := LiZhongQC.ahT_qmp_inv
    (MeasurableBeltramiBall.normalizedSolution_spec ν).1.1
    (MeasurableBeltramiBall.normalizedSolution_spec ν).1.2.1
  rw [invFunOn_normalizedMap ν] at h
  exact h

/-- The same full-plane map preserves the measure class in the forward direction. -/
theorem normalizedEquiv_quasiMeasurePreserving (ν : MeasurableBeltramiBall) :
    QuasiMeasurePreserving (normalizedEquiv ν) (volume : Measure ℂ) volume := by
  have hK := (MeasurableBeltramiBall.normalizedSolution_spec ν).2.1
  have hI := LiZhongQC.thm7_2_inv hK
  rw [(MeasurableBeltramiBall.normalizedSolution_spec ν).1.2.1,
    invFunOn_normalizedMap ν] at hI
  refine ⟨(normalizedMap ν).continuous.measurable,
    Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  change (Measure.map (normalizedMap ν) volume) s = 0
  rw [Measure.map_apply (normalizedMap ν).continuous.measurable hs]
  have hsub : normalizedMap ν ⁻¹' s ⊆ (normalizedMap ν).symm '' s := by
    intro z hz
    exact ⟨normalizedMap ν z, hz, (normalizedMap ν).symm_apply_apply z⟩
  exact measure_mono_null hsub
    (LiZhongQC.thm9_6_cor1_null hI (subset_univ s) hs0)

/-- The phase of the derivative of the actual normalized plane map. -/
def derivativePhase (ν : MeasurableBeltramiBall) (z : ℂ) : ℂ :=
  LiZhongQC.dz (normalizedMap ν) z / conj (LiZhongQC.dz (normalizedMap ν) z)

theorem derivativePhase_aestronglyMeasurable (ν : MeasurableBeltramiBall) :
    AEStronglyMeasurable (derivativePhase ν) (volume : Measure ℂ) := by
  have hm : AEStronglyMeasurable (LiZhongQC.dz (normalizedMap ν)) (volume : Measure ℂ) :=
    (LiZhongQC.measurable_dz (normalizedMap ν)).aestronglyMeasurable
  exact hm.div₀ (Complex.continuous_conj.comp_aestronglyMeasurable hm)

theorem norm_derivativePhase_le (ν : MeasurableBeltramiBall) (z : ℂ) :
    ‖derivativePhase ν z‖ ≤ 1 := LiZhongQC.ahT_norm_div_conj_le _

/-- Genuine planar quasiconformality makes this phase a unit almost everywhere. -/
theorem norm_derivativePhase_ae (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume, ‖derivativePhase ν z‖ = 1 := by
  have hJ := LiZhongQC.thm9_6_cor2_jacobian_pos
    (MeasurableBeltramiBall.normalizedSolution_spec ν).2.1
  rw [Measure.restrict_univ] at hJ
  filter_upwards [hJ] with z hz
  have hd : LiZhongQC.dz (normalizedMap ν) z ≠ 0 := by
    intro he
    unfold LiZhongQC.jacobian at hz
    rw [he, norm_zero] at hz
    nlinarith [sq_nonneg ‖LiZhongQC.dzbar (normalizedMap ν) z‖]
  rw [derivativePhase, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hd)]

/-- The original coefficient's literal positive denominator. -/
def coefficientDenominator (ν : MeasurableBeltramiBall) (z : ℂ) : ℂ :=
  1 - conj (ν.val z) * ν.val z

/-- The literal derivative weight before change of variables. -/
def derivativeWeight (ν : MeasurableBeltramiBall) (z : ℂ) : ℂ :=
  derivativePhase ν z / coefficientDenominator ν z

/-- The literal reciprocal weight for the inverse transport. -/
def inverseWeight (ν : MeasurableBeltramiBall) (z : ℂ) : ℂ :=
  coefficientDenominator ν z / derivativePhase ν z

/-- The quantitative derivative bound in the original essential norm. -/
def derivativeBound (ν : MeasurableBeltramiBall) : ℝ := (1 - ‖ν.val‖ ^ 2)⁻¹

/-- A finite bound for the actual inverse weight. -/
def inverseBound (ν : MeasurableBeltramiBall) : ℝ := 1 + ‖ν.val‖ ^ 2

theorem one_sub_norm_sq_pos (ν : MeasurableBeltramiBall) : 0 < 1 - ‖ν.val‖ ^ 2 := by
  have hk : ‖ν.val‖ < 1 := MeasurableBeltramiBall.norm_lt_one ν
  nlinarith [norm_nonneg ν.val]

theorem derivativeBound_nonneg (ν : MeasurableBeltramiBall) : 0 ≤ derivativeBound ν :=
  inv_nonneg.mpr (one_sub_norm_sq_pos ν).le

theorem inverseBound_nonneg (ν : MeasurableBeltramiBall) : 0 ≤ inverseBound ν :=
  add_nonneg zero_le_one (sq_nonneg ‖ν.val‖)

theorem coefficientDenominator_aestronglyMeasurable (ν : MeasurableBeltramiBall) :
    AEStronglyMeasurable (coefficientDenominator ν) (volume : Measure ℂ) := by
  have hm := Lp.aestronglyMeasurable ν.val
  exact aestronglyMeasurable_const.sub
    ((Complex.continuous_conj.comp_aestronglyMeasurable hm).mul hm)

theorem derivativeWeight_aestronglyMeasurable (ν : MeasurableBeltramiBall) :
    AEStronglyMeasurable (derivativeWeight ν) (volume : Measure ℂ) :=
  (derivativePhase_aestronglyMeasurable ν).div₀
    (coefficientDenominator_aestronglyMeasurable ν)

theorem inverseWeight_aestronglyMeasurable (ν : MeasurableBeltramiBall) :
    AEStronglyMeasurable (inverseWeight ν) (volume : Measure ℂ) :=
  (coefficientDenominator_aestronglyMeasurable ν).div₀
    (derivativePhase_aestronglyMeasurable ν)

/-- The strict coefficient bound gives a uniform nonzero denominator a.e. -/
theorem coefficientDenominator_lower_ae (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume, 1 - ‖ν.val‖ ^ 2 ≤ ‖coefficientDenominator ν z‖ := by
  filter_upwards [lpInfinity_norm_ae_le ν.val] with z hz
  have hm : ‖conj (ν.val z) * ν.val z‖ ≤ ‖ν.val‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, pow_two]
    exact mul_le_mul hz hz (norm_nonneg (ν.val z)) (norm_nonneg ν.val)
  have hs := norm_sub_norm_le (1 : ℂ) (conj (ν.val z) * ν.val z)
  rw [norm_one] at hs
  change 1 - ‖ν.val‖ ^ 2 ≤ ‖1 - conj (ν.val z) * ν.val z‖
  linarith

/-- The same literal denominator has an explicit finite upper bound a.e. -/
theorem coefficientDenominator_upper_ae (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume, ‖coefficientDenominator ν z‖ ≤ inverseBound ν := by
  filter_upwards [lpInfinity_norm_ae_le ν.val] with z hz
  change ‖1 - conj (ν.val z) * ν.val z‖ ≤ 1 + ‖ν.val‖ ^ 2
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖conj (ν.val z) * ν.val z‖ := norm_sub_le _ _
    _ = 1 + ‖ν.val z‖ ^ 2 := by
      rw [norm_one, norm_mul, Complex.norm_conj, pow_two]
    _ ≤ 1 + ‖ν.val‖ ^ 2 :=
      add_le_add (le_refl (1 : ℝ)) (pow_le_pow_left₀ (norm_nonneg (ν.val z)) hz 2)

theorem norm_derivativeWeight_ae_le (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume, ‖derivativeWeight ν z‖ ≤ derivativeBound ν := by
  filter_upwards [coefficientDenominator_lower_ae ν] with z hz
  rw [derivativeWeight, norm_div]
  calc
    _ ≤ 1 / ‖coefficientDenominator ν z‖ :=
      div_le_div_of_nonneg_right (norm_derivativePhase_le ν z)
        (norm_nonneg (coefficientDenominator ν z))
    _ ≤ 1 / (1 - ‖ν.val‖ ^ 2) :=
      div_le_div_of_nonneg_left zero_le_one (one_sub_norm_sq_pos ν) hz
    _ = derivativeBound ν := by rw [derivativeBound, one_div]

theorem norm_inverseWeight_ae_le (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume, ‖inverseWeight ν z‖ ≤ inverseBound ν := by
  filter_upwards [norm_derivativePhase_ae ν, coefficientDenominator_upper_ae ν]
    with z hphase hdenom
  rw [inverseWeight, norm_div, hphase, div_one]
  exact hdenom

/-- Both concrete factors are nonzero outside the genuine null exceptional set. -/
theorem inverseWeight_mul_derivativeWeight_ae (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume, inverseWeight ν z * derivativeWeight ν z = 1 := by
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

theorem derivativeWeight_mul_inverseWeight_ae (ν : MeasurableBeltramiBall) :
    ∀ᵐ z : ℂ ∂volume, derivativeWeight ν z * inverseWeight ν z = 1 := by
  filter_upwards [inverseWeight_mul_derivativeWeight_ae ν] with z hz
  exact (mul_comm _ _).trans hz

/-- The literal linear derivative transport on the entire original ambient space. -/
def ambientDerivative (ν : MeasurableBeltramiBall) : Ambient →L[ℂ] Ambient :=
  (quasiPullback (normalizedEquiv ν).symm
    (normalizedEquiv_symm_quasiMeasurePreserving ν)).comp
    (boundedMultiply (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
      (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν))

/-- The literal inverse on the same full planar coefficient space. -/
def ambientInverse (ν : MeasurableBeltramiBall) : Ambient →L[ℂ] Ambient :=
  (boundedMultiply (inverseWeight ν) (inverseWeight_aestronglyMeasurable ν)
    (inverseBound_nonneg ν) (norm_inverseWeight_ae_le ν)).comp
    (quasiPullback (normalizedEquiv ν)
      (normalizedEquiv_quasiMeasurePreserving ν))

theorem ambientDerivative_weighted_coe_ae (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ambientDerivative ν μ =ᵐ[volume] fun z =>
      derivativeWeight ν ((normalizedEquiv ν).symm z) *
        μ ((normalizedEquiv ν).symm z) := by
  filter_upwards [quasiPullback_coe_ae (normalizedEquiv ν).symm
      (normalizedEquiv_symm_quasiMeasurePreserving ν)
      (boundedMultiply (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ),
    (normalizedEquiv_symm_quasiMeasurePreserving ν).ae
      (boundedMultiply_coe_ae (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ)] with z hp hm
  exact hp.trans hm

/-- The value is exactly the book's coefficient formula with its actual inverse map. -/
theorem ambientDerivative_coe_ae (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ambientDerivative ν μ =ᵐ[volume] fun z =>
      μ ((normalizedEquiv ν).symm z) /
          (1 - conj (ν.val ((normalizedEquiv ν).symm z)) *
            ν.val ((normalizedEquiv ν).symm z)) *
        derivativePhase ν ((normalizedEquiv ν).symm z) := by
  filter_upwards [ambientDerivative_weighted_coe_ae ν μ] with z hz
  rw [hz]
  simp only [derivativeWeight, coefficientDenominator, div_eq_mul_inv]
  ring

theorem ambientInverse_weighted_coe_ae (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ambientInverse ν μ =ᵐ[volume] fun z =>
      inverseWeight ν z * μ (normalizedEquiv ν z) := by
  filter_upwards [boundedMultiply_coe_ae (inverseWeight ν)
      (inverseWeight_aestronglyMeasurable ν) (inverseBound_nonneg ν)
      (norm_inverseWeight_ae_le ν)
      (quasiPullback (normalizedEquiv ν)
        (normalizedEquiv_quasiMeasurePreserving ν) μ),
    quasiPullback_coe_ae (normalizedEquiv ν)
      (normalizedEquiv_quasiMeasurePreserving ν) μ] with z hm hp
  exact hm.trans (congrArg (fun w : ℂ => inverseWeight ν z * w) hp)

theorem ambientInverse_coe_ae (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ambientInverse ν μ =ᵐ[volume] fun z =>
      (1 - conj (ν.val z) * ν.val z) / derivativePhase ν z *
        μ (normalizedEquiv ν z) := by
  filter_upwards [ambientInverse_weighted_coe_ae ν μ] with z hz
  exact hz

theorem norm_ambientDerivative_le (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ‖ambientDerivative ν μ‖ ≤ derivativeBound ν * ‖μ‖ := by
  calc
    _ ≤ ‖boundedMultiply (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ‖ :=
      norm_quasiPullback_le (normalizedEquiv ν).symm
        (normalizedEquiv_symm_quasiMeasurePreserving ν) _
    _ ≤ derivativeBound ν * ‖μ‖ :=
      norm_boundedMultiply_le (derivativeWeight ν) (derivativeWeight_aestronglyMeasurable ν)
        (derivativeBound_nonneg ν) (norm_derivativeWeight_ae_le ν) μ

theorem norm_ambientInverse_le (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ‖ambientInverse ν μ‖ ≤ inverseBound ν * ‖μ‖ := by
  calc
    _ ≤ inverseBound ν * ‖quasiPullback (normalizedEquiv ν)
        (normalizedEquiv_quasiMeasurePreserving ν) μ‖ :=
      norm_boundedMultiply_le (inverseWeight ν) (inverseWeight_aestronglyMeasurable ν)
        (inverseBound_nonneg ν) (norm_inverseWeight_ae_le ν) _
    _ ≤ inverseBound ν * ‖μ‖ :=
      mul_le_mul_of_nonneg_left (norm_quasiPullback_le (normalizedEquiv ν)
        (normalizedEquiv_quasiMeasurePreserving ν) μ) (inverseBound_nonneg ν)

/-- The explicit inverse cancels the actual derivative on every original coefficient. -/
theorem ambientInverse_ambientDerivative (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ambientInverse ν (ambientDerivative ν μ) = μ := by
  apply Lp.ext
  filter_upwards [ambientInverse_weighted_coe_ae ν (ambientDerivative ν μ),
    (normalizedEquiv_quasiMeasurePreserving ν).ae
      (ambientDerivative_weighted_coe_ae ν μ),
    inverseWeight_mul_derivativeWeight_ae ν] with z hi hd hw
  rw [hi, hd, Equiv.symm_apply_apply, ← mul_assoc, hw, one_mul]

/-- Cancellation in the other order uses the same actual normalized inverse. -/
theorem ambientDerivative_ambientInverse (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ambientDerivative ν (ambientInverse ν μ) = μ := by
  apply Lp.ext
  filter_upwards [ambientDerivative_weighted_coe_ae ν (ambientInverse ν μ),
    (normalizedEquiv_symm_quasiMeasurePreserving ν).ae
      (ambientInverse_weighted_coe_ae ν μ),
    (normalizedEquiv_symm_quasiMeasurePreserving ν).ae
      (derivativeWeight_mul_inverseWeight_ae ν)] with z hd hi hw
  rw [hd, hi, Equiv.apply_symm_apply, ← mul_assoc, hw, one_mul]

/-- The genuine bounded ambient transport equivalence in the unchanged essential norms. -/
def ambientEquiv (ν : MeasurableBeltramiBall) : Ambient ≃L[ℂ] Ambient where
  toLinearEquiv :=
    { (ambientDerivative ν).toLinearMap with
      invFun := ambientInverse ν
      left_inv := ambientInverse_ambientDerivative ν
      right_inv := ambientDerivative_ambientInverse ν }
  continuous_toFun := (ambientDerivative ν).continuous
  continuous_invFun := (ambientInverse ν).continuous

@[simp] theorem ambientEquiv_apply (ν : MeasurableBeltramiBall) (μ : Ambient) :
    ambientEquiv ν μ = ambientDerivative ν μ := rfl

@[simp] theorem ambientEquiv_symm_apply (ν : MeasurableBeltramiBall) (μ : Ambient) :
    (ambientEquiv ν).symm μ = ambientInverse ν μ := rfl

end LowDimensionalTopology.Geometry.Teichmuller.PlanarCoefficientTransport
