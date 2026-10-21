/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexReflections
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.Conformal
public import Mathlib.Analysis.Complex.OperatorNorm
/-!
# Isometric circles

The exact finite-distance identity proves Euclidean distance preservation on the isometric circle. Composing with its actual sphere reflection gives an explicit onto Euclidean isometry with real Jacobian determinant -1. The equality of extended actions includes the pole, center and infinity.
-/

@[expose] public section
noncomputable section
open scoped ComplexConjugate OnePoint
namespace LowDimensionalTopology.Geometry.Mobius

/-- The ordinary finite coordinate of the coefficient action. -/
def fractionalValue (a b c d z : ℂ) : ℂ := (a*z+b)/(c*z+d)

theorem fractionalValue_sub (a b c d z w : ℂ)
    (hz : c*z+d ≠ 0) (hw : c*w+d ≠ 0) :
    fractionalValue a b c d z - fractionalValue a b c d w =
      (a*d-b*c)*(z-w)/((c*z+d)*(c*w+d)) := by
  unfold fractionalValue
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

theorem fractionalValue_dist (a b c d z w : ℂ)
    (hz : c*z+d ≠ 0) (hw : c*w+d ≠ 0) :
    dist (fractionalValue a b c d z) (fractionalValue a b c d w) =
      ‖a*d-b*c‖ * dist z w / (‖c*z+d‖*‖c*w+d‖) := by
  rw [dist_eq_norm, fractionalValue_sub a b c d z w hz hw, norm_div, norm_mul,
    norm_mul, dist_eq_norm]

/-- The finite isometric circle for c≠0. -/
def isometricCircle (a b c d : ℂ) : Set ℂ :=
  Metric.sphere (-d/c) (Real.sqrt ‖a*d-b*c‖ / ‖c‖)

theorem mem_isometricCircle_iff (a b c d z : ℂ) (hc : c ≠ 0) :
    z ∈ isometricCircle a b c d ↔ ‖c*z+d‖ = Real.sqrt ‖a*d-b*c‖ := by
  have h : c*z+d = c*(z-(-d/c)) := by field_simp; ring
  rw [isometricCircle, Metric.mem_sphere, dist_eq_norm, eq_div_iff (norm_ne_zero_iff.mpr hc),
    h, norm_mul]
  simp only [mul_comm]

theorem isometricCircle_denominator_ne_zero (a b c d z : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (hz : z ∈ isometricCircle a b c d) :
    c*z+d ≠ 0 := by
  have hpos : 0 < Real.sqrt ‖a*d-b*c‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hdet)
  intro h
  have heq := (mem_isometricCircle_iff a b c d z hc).mp hz
  rw [h, norm_zero] at heq
  exact hpos.ne' heq.symm

theorem fractionalValue_preserves_circle_distance (a b c d z w : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0)
    (hz : z ∈ isometricCircle a b c d) (hw : w ∈ isometricCircle a b c d) :
    dist (fractionalValue a b c d z) (fractionalValue a b c d w) = dist z w := by
  rw [fractionalValue_dist a b c d z w
    (isometricCircle_denominator_ne_zero a b c d z hdet hc hz)
    (isometricCircle_denominator_ne_zero a b c d w hdet hc hw),
    (mem_isometricCircle_iff a b c d z hc).mp hz,
    (mem_isometricCircle_iff a b c d w hc).mp hw,
    ← pow_two, Real.sq_sqrt (norm_nonneg _)]
  exact mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hdet)

theorem fractionalLinearOfCoefficients_on_isometricCircle (a b c d z : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (hz : z ∈ isometricCircle a b c d) :
    fractionalLinearOfCoefficients a b c d hdet z = (fractionalValue a b c d z : ExtendedComplex) :=
  fractionalLinearOfCoefficients_finite a b c d z hdet
    (isometricCircle_denominator_ne_zero a b c d z hdet hc hz)
theorem fractionalValue_center_shift (a b c d u : ℂ) (hc : c ≠ 0) (hu : u ≠ 0) :
    fractionalValue a b c d (-d/c+u) = a/c - (a*d-b*c)/(c^2*u) := by
  have hden : c*(-d/c+u)+d = c*u := by field_simp; ring
  unfold fractionalValue
  rw [hden]
  field_simp [hc, hu]
  ring

def isometricCircleRadius (a b c d : ℂ) : ℝ := Real.sqrt ‖a*d-b*c‖/‖c‖

theorem isometricCircleRadius_pos (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) : 0 < isometricCircleRadius a b c d :=
  div_pos (Real.sqrt_pos.mpr (norm_pos_iff.mpr hdet)) (norm_pos_iff.mpr hc)

theorem isometricCircleRadius_sq (a b c d : ℂ) (hc : c ≠ 0) :
    ‖c‖^2 * (isometricCircleRadius a b c d)^2 = ‖a*d-b*c‖ := by
  unfold isometricCircleRadius
  rw [div_pow, Real.sq_sqrt (norm_nonneg _)]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
def isometricReflectionScale (a b c d : ℂ) : ℂ :=
  (a*d-b*c)/(c^2*(isometricCircleRadius a b c d : ℂ)^2)

theorem isometricReflectionScale_norm (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) : ‖isometricReflectionScale a b c d‖ = 1 := by
  have hr := isometricCircleRadius_pos a b c d hdet hc
  simp only [isometricReflectionScale, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [isometricCircleRadius_sq a b c d hc]
  exact div_self (norm_ne_zero_iff.mpr hdet)

def circleReflectedValue (a b c d z : ℂ) : ℂ :=
  a/c - isometricReflectionScale a b c d * (conj z-conj (-d/c))

theorem circleReflectedValue_isometry (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) : Isometry (circleReflectedValue a b c d) := by
  apply isometry_iff_dist_eq.mpr
  intro z w
  have hsub : circleReflectedValue a b c d z-circleReflectedValue a b c d w =
      -(isometricReflectionScale a b c d)*conj (z-w) := by
    unfold circleReflectedValue
    rw [map_sub]
    ring
  rw [dist_eq_norm, hsub, norm_mul, norm_neg, isometricReflectionScale_norm a b c d hdet hc,
    one_mul, Complex.norm_conj, dist_eq_norm]

theorem fractionalValue_sphereInversion (a b c d z : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (hz : z ≠ -d/c) :
    fractionalValue a b c d
      (Mobius.ReflectionBridge.e.symm (EuclideanGeometry.inversion (Mobius.ReflectionBridge.e (-d/c))
        (isometricCircleRadius a b c d) (Mobius.ReflectionBridge.e z))) =
      circleReflectedValue a b c d z := by
  have hr := (isometricCircleRadius_pos a b c d hdet hc).ne'
  have hR : (isometricCircleRadius a b c d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hz' : conj (z-(-d/c)) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hz)
  rw [Mobius.ReflectionBridge.inversion_complex_formula _ _ _ hz,
    fractionalValue_center_shift a b c d _ hc (div_ne_zero (pow_ne_zero 2 hR) hz')]
  unfold circleReflectedValue isometricReflectionScale
  rw [← map_sub]
  field_simp [hc, hR, hz']
def isometricCircleReflection (a b c d : ℂ) (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) :
    Equiv.Perm ExtendedComplex :=
  Mobius.ReflectionBridge.toComplex (Inversive.sphereInversionHomeomorph
    (Mobius.ReflectionBridge.e (-d/c)) (isometricCircleRadius a b c d)
    (isometricCircleRadius_pos a b c d hdet hc).ne')

theorem fractionalLinear_isometricCircleReflection (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (z : ExtendedComplex) :
    fractionalLinearOfCoefficients a b c d hdet
      (isometricCircleReflection a b c d hdet hc z) =
      OnePoint.map (circleReflectedValue a b c d) z := by
  have hr := (isometricCircleRadius_pos a b c d hdet hc).ne'
  induction z using OnePoint.rec with
  | infty =>
    change fractionalLinearOfCoefficients a b c d hdet
      (extendedComplexEuclideanHomeomorph.symm
        (Inversive.sphereInversionHomeomorph (Mobius.ReflectionBridge.e (-d/c))
          (isometricCircleRadius a b c d) hr ∞)) = ∞
    rw [Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_infty,
      Mobius.ReflectionBridge.coordinate_symm_coe, Mobius.ReflectionBridge.e.symm_apply_apply]
    exact fractionalLinearOfCoefficients_pole a b c d hdet hc
  | coe z =>
    change fractionalLinearOfCoefficients a b c d hdet
      (extendedComplexEuclideanHomeomorph.symm
        (Inversive.sphereInversionHomeomorph (Mobius.ReflectionBridge.e (-d/c))
          (isometricCircleRadius a b c d) hr (Mobius.ReflectionBridge.e z))) =
      (circleReflectedValue a b c d z : ExtendedComplex)
    rw [Inversive.sphereInversionHomeomorph_apply]
    by_cases hz : z = -d/c
    · subst z
      simp [Inversive.sphereInversion_center, fractionalLinearOfCoefficients_infty,
        hc, circleReflectedValue]
    · have he : Mobius.ReflectionBridge.e z ≠ Mobius.ReflectionBridge.e (-d/c) :=
        fun h => hz (Mobius.ReflectionBridge.e.injective h)
      rw [Inversive.sphereInversion_coe _ _ he, Mobius.ReflectionBridge.coordinate_symm_coe]
      have hz' : conj (z-(-d/c)) ≠ 0 :=
        (map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hz)
      have hR : (isometricCircleRadius a b c d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
      have hden : c*(Mobius.ReflectionBridge.e.symm (EuclideanGeometry.inversion
          (Mobius.ReflectionBridge.e (-d/c)) (isometricCircleRadius a b c d)
          (Mobius.ReflectionBridge.e z)))+d ≠ 0 := by
        rw [Mobius.ReflectionBridge.inversion_complex_formula _ _ _ hz]
        have hform : c*(-d/c+(isometricCircleRadius a b c d : ℂ)^2 / conj (z-(-d/c)))+d =
            c*((isometricCircleRadius a b c d : ℂ)^2 / conj (z-(-d/c))) := by
          field_simp
          ring
        rw [hform]
        exact mul_ne_zero hc (div_ne_zero (pow_ne_zero 2 hR) hz')
      rw [fractionalLinearOfCoefficients_finite _ _ _ _ _ _ hden]
      exact congrArg (fun w : ℂ => (w : ExtendedComplex))
        (fractionalValue_sphereInversion a b c d z hdet hc hz)
theorem isometricReflectionScale_ne_zero (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) : isometricReflectionScale a b c d ≠ 0 := by
  intro h
  have heq := isometricReflectionScale_norm a b c d hdet hc
  simp only [h, norm_zero, zero_ne_one] at heq

theorem circleReflectedValue_surjective (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) : Function.Surjective (circleReflectedValue a b c d) := by
  intro y
  let K := isometricReflectionScale a b c d
  have hK : K ≠ 0 := isometricReflectionScale_ne_zero a b c d hdet hc
  refine ⟨conj ((a/c-y)/K+conj (-d/c)), ?_⟩
  change a/c-K*(conj (conj ((a/c-y)/K+conj (-d/c)))-conj (-d/c))=y
  simp only [Complex.conj_conj, add_sub_cancel_right]
  field_simp
  ring

def circleReflectedEuclideanIsometry (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) : ℂ ≃ᵢ ℂ where
  toEquiv := Equiv.ofBijective (circleReflectedValue a b c d)
    ⟨(circleReflectedValue_isometry a b c d hdet hc).injective,
      circleReflectedValue_surjective a b c d hdet hc⟩
  isometry_toFun := circleReflectedValue_isometry a b c d hdet hc

theorem circleReflectedValue_fderiv_det (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (z : ℂ) :
    LinearMap.det (fderiv ℝ (circleReflectedValue a b c d) z).toLinearMap = -1 := by
  let K := isometricReflectionScale a b c d
  let F : ℂ → ℂ := fun w => a/c-K*(w-conj (-d/c))
  have hD : HasDerivAt F (-K) (conj z) := by
    convert (hasDerivAt_const (conj z) (a/c)).sub
      (((hasDerivAt_id (conj z)).sub_const (conj (-d/c))).const_mul K) using 1 <;> simp [F]
    funext w
    rfl
  have heq : circleReflectedValue a b c d = F ∘ conj := rfl
  rw [heq, fderiv_comp z (hD.differentiableAt.restrictScalars ℝ) Complex.conjCLE.differentiableAt]
  rw [show fderiv ℝ (conj : ℂ → ℂ) z = (Complex.conjCLE : ℂ →L[ℝ] ℂ) from
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.fderiv]
  change LinearMap.det ((fderiv ℝ F (conj z)).toLinearMap.comp Complex.conjCLE.toLinearMap) = -1
  rw [LinearMap.det_comp, Auxiliary.Analysis.complex_real_fderiv_det hD.differentiableAt,
    hD.deriv]
  have hconj : LinearMap.det Complex.conjCLE.toLinearMap = -1 := Complex.det_conjLIE
  rw [hconj]
  have hn : Complex.normSq (-K) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_neg, isometricReflectionScale_norm a b c d hdet hc]
    norm_num
  rw [hn, one_mul]
theorem circleReflectedEuclideanIsometry_apply (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (z : ℂ) :
    circleReflectedEuclideanIsometry a b c d hdet hc z = circleReflectedValue a b c d z := rfl

theorem circleReflectedValue_indirectlyConformalAt (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (z : ℂ) :
    Auxiliary.Analysis.indirectlyConformalAt (circleReflectedValue a b c d) z := by
  constructor
  · apply conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj.mpr
    constructor
    · right
      have hF : circleReflectedValue a b c d ∘ conj =
          fun w : ℂ => a/c-isometricReflectionScale a b c d*(w-conj (-d/c)) := by
        funext w
        simp [circleReflectedValue]
      rw [hF]
      fun_prop
    · intro hzero
      have hd := circleReflectedValue_fderiv_det a b c d hdet hc z
      rw [hzero] at hd
      norm_num at hd
  · rw [circleReflectedValue_fderiv_det a b c d hdet hc z]
    norm_num

theorem fractionalLinear_comp_isometricCircleReflection (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (hc : c ≠ 0) (z : ExtendedComplex) :
    fractionalLinearOfCoefficients a b c d hdet
      (isometricCircleReflection a b c d hdet hc z) =
      OnePoint.map (circleReflectedEuclideanIsometry a b c d hdet hc) z :=
  fractionalLinear_isometricCircleReflection a b c d hdet hc z
end LowDimensionalTopology.Geometry.Mobius
