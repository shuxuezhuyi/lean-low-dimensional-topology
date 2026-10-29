module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyRay
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The angular and logarithmic formula for the normalized strip integral

The angular density has total mass one. Integrating its truncated mass
computes the logarithmic jump, with both normalization points treated
directly and the two boundary conventions on the negative real axis paired.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

private theorem angularDensity_eq_indicator (θ : Width) :
    angularDensity θ = (interval θ).indicator (fun _ : ℝ => 1 / (2 * (θ : ℝ))) := by
  classical
  rfl

/-- The actual angular density is globally integrable on the real line. -/
theorem integrable_angularDensity (θ : Width) :
    Integrable (angularDensity θ) (volume : Measure ℝ) := by
  rw [angularDensity_eq_indicator]
  have hi : IntegrableOn (fun _ : ℝ => 1 / (2 * (θ : ℝ))) (interval θ)
      (volume : Measure ℝ) :=
    integrableOn_const measure_Icc_lt_top.ne
  exact hi.integrable_indicator measurableSet_Icc

private theorem support_angularDensity_subset (θ : Width) :
    Function.support (angularDensity θ) ⊆ Ioc (0 : ℝ) Real.pi := by
  classical
  intro t ht
  have hs : t ∈ interval θ := by
    by_contra hnot
    exact ht (by simp only [angularDensity, ite_eq_right hnot])
  have hlo : 0 < Real.pi / 2 - (θ : ℝ) := sub_pos.mpr θ.property.2
  have hhi : Real.pi / 2 + (θ : ℝ) < Real.pi := by linarith [θ.property.2]
  exact ⟨hlo.trans_le hs.1, hs.2.trans hhi.le⟩

/-- The real angular density has total mass one. -/
theorem integral_angularDensity (θ : Width) :
    (∫ t : ℝ, angularDensity θ t) = 1 := by
  have hs : MeasurableSet (interval θ) := measurableSet_Icc
  rw [angularDensity_eq_indicator, integral_indicator_const _ hs]
  have hlen : (volume : Measure ℝ).real (interval θ) = 2 * (θ : ℝ) := by
    unfold interval
    rw [Real.volume_real_Icc_of_le (by linarith [θ.property.1])]
    ring
  rw [hlen, smul_eq_mul]
  field_simp [θ.property.1.ne']

/-- The oriented angular primitive vanishes at all nonpositive angles. -/
theorem angularPrimitive_eq_zero_of_nonpos (θ : Width) {a : ℝ} (ha : a ≤ 0) :
    angularPrimitive θ a = 0 := by
  classical
  unfold angularPrimitive
  apply intervalIntegral.integral_zero_ae
  filter_upwards with t ht
  rw [uIoc_of_ge ha] at ht
  have hnot : t ∉ interval θ := by
    intro h
    have hpos : 0 < t := lt_of_lt_of_le (sub_pos.mpr θ.property.2) h.1
    exact hpos.not_ge ht.2
  simp only [angularDensity, ite_eq_right hnot]

/-- The angular primitive reaches its full mass at the negative real ray. -/
theorem angularPrimitive_pi (θ : Width) : angularPrimitive θ Real.pi = 1 := by
  unfold angularPrimitive
  rw [intervalIntegral.integral_eq_integral_of_support_subset (support_angularDensity_subset θ)]
  exact integral_angularDensity θ

/-- The lower choice of argument at the same boundary ray has zero angular mass. -/
theorem angularPrimitive_neg_pi (θ : Width) : angularPrimitive θ (-Real.pi) = 0 :=
  angularPrimitive_eq_zero_of_nonpos θ (neg_nonpos.mpr Real.pi_pos.le)

/-- Truncating the angular density computes exactly its oriented primitive. -/
theorem integral_angularDensity_cut (θ : Width) {a : ℝ} (ha : a ≤ Real.pi) :
    (∫ t in Ioo (0 : ℝ) Real.pi, if t < a then angularDensity θ t else 0) =
      angularPrimitive θ a := by
  classical
  by_cases ha0 : 0 ≤ a
  · calc
      (∫ t in Ioo (0 : ℝ) Real.pi, if t < a then angularDensity θ t else 0) =
          ∫ t in (0 : ℝ)..Real.pi, (Iic a).indicator (angularDensity θ) t := by
        rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
        apply integral_congr_ae
        have hne : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ a := by
          simp [ae_iff, measure_singleton]
        filter_upwards [ae_restrict_of_ae hne] with t htne
        have hiff : t < a ↔ t ≤ a := ⟨le_of_lt, fun h => lt_of_le_of_ne h htne⟩
        simp only [Set.indicator_apply, mem_Iic, hiff]
      _ = angularPrimitive θ a :=
        intervalIntegral.integral_indicator (f := angularDensity θ) ⟨ha0, ha⟩
  · rw [angularPrimitive_eq_zero_of_nonpos θ (le_of_not_ge ha0)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hnot : ¬t < a := not_lt.mpr ((le_of_not_ge ha0).trans ht.1.le)
    simp only [ite_eq_right hnot, Pi.zero_apply]

private theorem integral_complex_angularDensity (θ : Width) :
    (∫ t in Ioo (0 : ℝ) Real.pi, (angularDensity θ t : ℂ)) = 1 := by
  have h : (∫ t in Ioo (0 : ℝ) Real.pi, angularDensity θ t) = 1 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    exact angularPrimitive_pi θ
  calc
    (∫ t in Ioo (0 : ℝ) Real.pi, (angularDensity θ t : ℂ)) =
        ((∫ t in Ioo (0 : ℝ) Real.pi, angularDensity θ t : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [h, Complex.ofReal_one]

private theorem integral_complex_angularDensity_cut (θ : Width) {a : ℝ} (ha : a ≤ Real.pi) :
    (∫ t in Ioo (0 : ℝ) Real.pi,
      if t < a then (angularDensity θ t : ℂ) else 0) = (angularPrimitive θ a : ℂ) := by
  classical
  calc
    (∫ t in Ioo (0 : ℝ) Real.pi, if t < a then (angularDensity θ t : ℂ) else 0) =
        ∫ t in Ioo (0 : ℝ) Real.pi,
          ((if t < a then angularDensity θ t else 0 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t < a
      · simp only [ite_eq_left ht]
      · simp only [ite_eq_right ht, Complex.ofReal_zero]
    _ = ((∫ t in Ioo (0 : ℝ) Real.pi,
        if t < a then angularDensity θ t else 0 : ℝ) : ℂ) := integral_ofReal
    _ = (angularPrimitive θ a : ℂ) :=
      congrArg Complex.ofReal (integral_angularDensity_cut θ ha)

private theorem integral_angularDensity_mul_jump_sub (θ : Width) {a : ℝ}
    (ha : a ≤ Real.pi) (L : ℂ) :
    (∫ t in Ioo (0 : ℝ) Real.pi, (angularDensity θ t : ℂ) *
      ((if t < a then (2 * (Real.pi : ℂ)) * Complex.I else 0) - L)) =
        (2 * (Real.pi : ℂ)) * Complex.I * (angularPrimitive θ a : ℂ) - L := by
  classical
  have hd : Integrable (fun t : ℝ => (angularDensity θ t : ℂ))
      (volume : Measure ℝ) := (integrable_angularDensity θ).ofReal
  have hcut : Integrable (fun t : ℝ => if t < a then (angularDensity θ t : ℂ) else 0)
      (volume : Measure ℝ) := by
    refine (hd.indicator (s := Iio a) measurableSet_Iio).congr ?_
    filter_upwards with t
    simp only [Set.indicator_apply, mem_Iio]
  have heq : (fun t : ℝ => (angularDensity θ t : ℂ) *
        ((if t < a then (2 * (Real.pi : ℂ)) * Complex.I else 0) - L)) =
      fun t : ℝ => (2 * (Real.pi : ℂ)) * Complex.I *
        (if t < a then (angularDensity θ t : ℂ) else 0) - (angularDensity θ t : ℂ) * L := by
    funext t
    by_cases ht : t < a
    · simp only [ite_eq_left ht]
      ring
    · simp only [ite_eq_right ht, mul_zero, zero_sub, mul_neg]
  rw [heq, integral_sub (hcut.const_mul _).integrableOn (hd.mul_const L).integrableOn,
    integral_const_mul, integral_mul_const,
    integral_complex_angularDensity_cut θ ha, integral_complex_angularDensity θ, one_mul]

/-- Changing both boundary choices of argument and logarithm leaves their paired expression unchanged. -/
theorem angular_log_branch_pair (θ : Width) (L : ℂ) :
    (angularPrimitive θ Real.pi : ℂ) + Complex.I / (2 * (Real.pi : ℂ)) * L =
      (angularPrimitive θ (-Real.pi) : ℂ) + Complex.I / (2 * (Real.pi : ℂ)) *
        (L - (2 * (Real.pi : ℂ)) * Complex.I) := by
  rw [angularPrimitive_pi, angularPrimitive_neg_pi]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ]
  ring_nf
  simp [Complex.I_sq]

/-- The two matched logarithm conventions agree at every point of the negative real axis. -/
theorem firstCauchyClosedForm_negative_real_branch (θ : Width) {z : ℂ}
    (hre : z.re < 0) (him : z.im = 0) :
    firstCauchyClosedForm θ z =
      -z * ((angularPrimitive θ (-Real.pi) : ℂ) + Complex.I / (2 * (Real.pi : ℂ)) *
        (Complex.log z - (2 * (Real.pi : ℂ)) * Complex.I)) := by
  unfold firstCauchyClosedForm
  rw [Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩, angular_log_branch_pair]

/-- The actual normalized area integral has the angular and logarithmic expression at every point. -/
theorem firstCauchyTerm_eq_closedForm (θ : Width) (z : ℂ) :
    firstCauchyTerm θ z = firstCauchyClosedForm θ z := by
  classical
  by_cases hz0 : z = 0
  · subst z
    exact firstCauchyTerm_eq_closedForm_zero θ
  by_cases hz1 : z = 1
  · subst z
    exact firstCauchyTerm_eq_closedForm_one θ
  rw [firstCauchyTerm_eq_polarIntegral,
    integral_congr_ae (ae_integral_firstCauchyPolarIntegrand_eq hz0 θ)]
  have heq : (fun t : ℝ => -(Complex.I * z / 2) * (angularDensity θ t : ℂ) *
        ((if t < Complex.arg z then (2 * (Real.pi : ℂ)) * Complex.I else 0) - Complex.log z)) =
      fun t : ℝ => -(Complex.I * z / 2) * ((angularDensity θ t : ℂ) *
        ((if t < Complex.arg z then (2 * (Real.pi : ℂ)) * Complex.I else 0) - Complex.log z)) := by
    funext t
    ring
  rw [heq, integral_const_mul,
    integral_angularDensity_mul_jump_sub θ (Complex.arg_le_pi z) (Complex.log z)]
  unfold firstCauchyClosedForm
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
