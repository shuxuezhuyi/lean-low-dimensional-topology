/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.Tactic

/-!
# Hyperbolic discs and circles

Lengths are the previously defined integrals of the actual hyperbolic density.
Areas use the density-weighted Lebesgue measure, rather than a prescribed formula.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc ENNReal Topology MatrixGroups ComplexConjugate

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

instance unitDiscMeasurableSpace : MeasurableSpace 𝔻 := borel 𝔻

instance unitDiscBorelSpace : BorelSpace 𝔻 := ⟨rfl⟩

/-- The canonical once-around parametrization of a Euclidean circle inside the disc. -/
def discCirclePiece (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) : DiscC1CurvePiece where
  a := 0
  b := 2 * Real.pi
  ordered := (Real.two_pi_pos).le
  curve θ := Complex.UnitDisc.mk (circleMap 0 R θ)
    (by simpa only [norm_circleMap_zero, abs_of_nonneg hR] using hR1)
  velocity θ := circleMap 0 R θ * Complex.I
  continuous_curve := by
    apply Continuous.continuousOn
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    exact continuous_circleMap 0 R
  continuous_velocity := ((continuous_circleMap 0 R).mul continuous_const).continuousOn
  hasDerivWithin θ _ := by
    change HasDerivWithinAt (circleMap 0 R) _ _ _
    exact (hasDerivAt_circleMap 0 R θ).hasDerivWithinAt

theorem discCirclePiece_speed (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) (θ : ℝ) :
    discWeightedSpeed (discCirclePiece R hR hR1).curve (discCirclePiece R hR hR1).velocity θ =
      2 * R / (1 - R ^ 2) := by
  simp only [discWeightedSpeed, discCirclePiece, Complex.UnitDisc.coe_mk, norm_mul,
    Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_nonneg hR]

theorem discCirclePiece_length (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    (discCirclePiece R hR hR1).length = 4 * Real.pi * R / (1 - R ^ 2) := by
  unfold DiscC1CurvePiece.length
  simp only [discCirclePiece_speed]
  change (∫ _ : ℝ in (0 : ℝ)..(2 * Real.pi), 2 * R / (1 - R ^ 2)) = _
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem one_sub_tanh_sq (t : ℝ) :
    1 - Real.tanh t ^ 2 = 1 / Real.cosh t ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem tanh_half_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Real.tanh (r / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le

/-- The integral circumference formula at hyperbolic radius `r`. -/
theorem discCirclePiece_hyperbolic_length (r : ℝ) (hr : 0 ≤ r) :
    (discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).length =
      2 * Real.pi * Real.sinh r := by
  rw [discCirclePiece_length, one_sub_tanh_sq, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh (r / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hs := Real.sinh_two_mul (r / 2)
  rw [show 2 * (r / 2) = r by ring] at hs
  rw [hs]
  field_simp
  ring

/-- The Cayley formulas identify Euclidean norm with the hyperbolic radial coordinate. -/
theorem disc_norm_eq_tanh_half_distance (z : 𝔻) :
    ‖(z : ℂ)‖ = Real.tanh (discPathDist 0 z / 2) := by
  simpa only [Complex.UnitDisc.coe_zero, zero_mul, sub_zero, norm_one, zero_sub,
    norm_neg, div_one] using (disc_tanh_half_distance 0 z).symm

/-- The parametrization lies on the circle of the advertised hyperbolic radius. -/
theorem discCirclePiece_distance (r : ℝ) (hr : 0 ≤ r) (θ : ℝ) :
    discPathDist 0
      ((discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve θ) =
      r := by
  have h := disc_norm_eq_tanh_half_distance
    ((discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve θ)
  simp only [discCirclePiece, Complex.UnitDisc.coe_mk, norm_circleMap_zero,
    abs_of_nonneg (tanh_half_nonneg hr)] at h
  have h' := congrArg Real.artanh h
  rw [Real.artanh_tanh, Real.artanh_tanh] at h'
  change r / 2 = discPathDist 0
    ((discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve θ) / 2
    at h'
  linarith

/-- The planar area density prescribed. -/
def discAreaDensity (z : ℂ) : ℝ := 4 / (1 - ‖z‖ ^ 2) ^ 2

theorem discAreaDensity_nonneg (z : ℂ) : 0 ≤ discAreaDensity z := by
  exact div_nonneg (by norm_num) (sq_nonneg _)

/-- The genuine density-weighted Lebesgue measure, totalized outside the unit disc. -/
def discAreaMeasure : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (discAreaDensity z))

theorem discAreaDensity_continuousOn_closedBall (R : ℝ) (hR : R < 1) :
    ContinuousOn discAreaDensity (Metric.closedBall 0 R) := by
  apply continuousOn_const.div
    ((continuousOn_const.sub (continuous_norm.continuousOn.pow 2)).pow 2)
  intro z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hs : ‖z‖ ^ 2 < 1 := by nlinarith [hzR.trans_lt hR, norm_nonneg z]
  exact pow_ne_zero 2 (sub_pos.mpr hs).ne'

/-- On compact subdiscs, the measure is the stated ordinary area integral. -/
theorem discAreaMeasure_closedBall_integral (R : ℝ) (hR : R < 1) :
    discAreaMeasure (Metric.closedBall 0 R) =
      ENNReal.ofReal (∫ z in Metric.closedBall 0 R, discAreaDensity z) := by
  rw [discAreaMeasure, withDensity_apply _ measurableSet_closedBall]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (discAreaDensity_continuousOn_closedBall R hR).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)
  · exact ae_of_all _ discAreaDensity_nonneg

/-- Polar change of variables for the actual planar density integral. -/
theorem discAreaDensity_closedBall_polar (R : ℝ) (hR : 0 ≤ R) :
    (∫ z in Metric.closedBall 0 R, discAreaDensity z) =
      2 * Real.pi * (∫ t in (0 : ℝ)..R, 4 * t / (1 - t ^ 2) ^ 2) := by
  let f : ℂ → ℝ := (Metric.closedBall 0 R).indicator discAreaDensity
  have hp := Complex.integral_comp_polarCoord_symm f
  rw [integral_indicator measurableSet_closedBall] at hp
  rw [← hp, polarCoord_target]
  have heq : (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) =ᵐ[
      volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)]
      (fun p => ((Iic R).indicator (fun t => 4 * t / (1 - t ^ 2) ^ 2) p.1) * (1 : ℝ)) := by
    apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    have hr : 0 < p.1 := hp.1
    change p.1 * (Metric.closedBall (0 : ℂ) R).indicator discAreaDensity
      (Complex.polarCoord.symm p) =
      ((Iic R).indicator (fun t => 4 * t / (1 - t ^ 2) ^ 2) p.1) * 1
    have hm : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R ↔ p.1 ≤ R := by
      simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hr]
    by_cases hle : p.1 ≤ R
    · rw [Set.indicator_of_mem (hm.mpr hle), Set.indicator_of_mem (show p.1 ∈ Iic R from hle)]
      simp only [discAreaDensity, Complex.norm_polarCoord_symm, abs_of_pos hr, mul_one]
      ring
    · rw [Set.indicator_of_notMem (fun h => hle (hm.mp h)),
        Set.indicator_of_notMem (show p.1 ∉ Iic R from hle)]
      simp only [mul_zero, zero_mul]
  rw [integral_congr_ae heq]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul
    ((Iic R).indicator (fun t => 4 * t / (1 - t ^ 2) ^ 2)) (fun _ : ℝ => 1)]
  rw [setIntegral_indicator measurableSet_Iic]
  have hi : Ioi (0 : ℝ) ∩ Iic R = Ioc 0 R := by ext t; simp [and_comm]
  rw [hi, ← intervalIntegral.integral_of_le hR]
  have ha : (∫ _ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]),
      intervalIntegral.integral_const]
    simp
    ring
  rw [ha, mul_comm]

theorem discArea_radial_integral (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    (∫ t in (0 : ℝ)..R, 4 * t / (1 - t ^ 2) ^ 2) = 2 / (1 - R ^ 2) - 2 := by
  have hden (t : ℝ) (ht : t ∈ Icc 0 R) : 1 - t ^ 2 ≠ 0 := by
    have hlt : t < 1 := ht.2.trans_lt hR1
    nlinarith [ht.1]
  have hd (t : ℝ) (ht : t ∈ Icc 0 R) :
      HasDerivAt (fun s : ℝ => 2 / (1 - s ^ 2)) (4 * t / (1 - t ^ 2) ^ 2) t := by
    convert! (hasDerivAt_const t (2 : ℝ)).div
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)) (hden t ht) using 1
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  have hc : ContinuousOn (fun t : ℝ => 4 * t / (1 - t ^ 2) ^ 2) (Icc 0 R) :=
    (continuousOn_const.mul continuousOn_id).div
      ((continuousOn_const.sub (continuousOn_id.pow 2)).pow 2)
      (fun t ht => pow_ne_zero 2 (hden t ht))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hR] using ht))
    (hc.intervalIntegrable_of_Icc hR)
  simpa using hi

/-- The area of an actual Euclidean subdisc, computed from the prescribed density. -/
theorem discAreaMeasure_closedBall (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    discAreaMeasure (Metric.closedBall 0 R) = ENNReal.ofReal
      (4 * Real.pi * R ^ 2 / (1 - R ^ 2)) := by
  rw [discAreaMeasure_closedBall_integral R hR1, discAreaDensity_closedBall_polar R hR,
    discArea_radial_integral R hR hR1]
  congr 1
  have hd : 1 - R ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- The density measure gives the area at the origin. -/
theorem discAreaMeasure_hyperbolic_radius (r : ℝ) (hr : 0 ≤ r) :
    discAreaMeasure (Metric.closedBall 0 (Real.tanh (r / 2))) =
      ENNReal.ofReal (4 * Real.pi * Real.sinh (r / 2) ^ 2) := by
  rw [discAreaMeasure_closedBall _ (tanh_half_nonneg hr) (Real.tanh_lt_one _),
    one_sub_tanh_sq, Real.tanh_eq_sinh_div_cosh]
  congr 1
  have hc : Real.cosh (r / 2) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp

/-- The radial coordinate also identifies every hyperbolic closed ball as a Euclidean subdisc. -/
theorem disc_distance_zero_le_iff (z : 𝔻) (r : ℝ) :
    discPathDist 0 z ≤ r ↔ ‖(z : ℂ)‖ ≤ Real.tanh (r / 2) := by
  have hn : ‖(z : ℂ)‖ ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [norm_nonneg (z : ℂ)], z.norm_lt_one⟩
  have ht : Real.tanh (r / 2) ∈ Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  have hd : Real.artanh ‖(z : ℂ)‖ = discPathDist 0 z / 2 := by
    rw [disc_norm_eq_tanh_half_distance, Real.artanh_tanh]
  have h := Real.artanh_le_artanh_iff hn ht
  rw [hd, Real.artanh_tanh] at h
  constructor
  · intro hz
    exact h.mp (by linarith)
  · intro hz
    have h' := h.mpr hz
    linarith

theorem disc_closedBall_image (r : ℝ) :
    ((↑) : 𝔻 → ℂ) '' {z : 𝔻 | discPathDist 0 z ≤ r} =
      Metric.closedBall 0 (Real.tanh (r / 2)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (disc_distance_zero_le_iff w r).mp hw
  · intro hz
    have hn : ‖z‖ ≤ Real.tanh (r / 2) :=
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    let w := Complex.UnitDisc.mk z (hn.trans_lt (Real.tanh_lt_one _))
    exact ⟨w, (disc_distance_zero_le_iff w r).mpr hn, rfl⟩

/-- Area of a set in the disc model is its density-weighted planar Lebesgue area. -/
def discHyperbolicArea (s : Set 𝔻) : ℝ≥0∞ := discAreaMeasure (((↑) : 𝔻 → ℂ) '' s)

theorem discHyperbolicArea_closedBall_zero (r : ℝ) (hr : 0 ≤ r) :
    discHyperbolicArea {z : 𝔻 | discPathDist 0 z ≤ r} =
      ENNReal.ofReal (4 * Real.pi * Real.sinh (r / 2) ^ 2) := by
  rw [discHyperbolicArea, disc_closedBall_image, discAreaMeasure_hyperbolic_radius r hr]

/-- The real derivative used for the area change of variables. -/
def inverseCayleyRealFDeriv (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ ((2 * Complex.I) / (1 - z) ^ 2)).restrictScalars ℝ

theorem hasFDerivAt_inverseCayley_real (z : 𝔻) :
    HasFDerivAt inverseCayleyFormula (inverseCayleyRealFDeriv z) (z : ℂ) :=
  (hasDerivAt_inverseCayleyFormula z).hasFDerivAt.restrictScalars ℝ

theorem det_inverseCayleyRealFDeriv (z : ℂ) :
    (inverseCayleyRealFDeriv z).det = ‖(2 * Complex.I) / (1 - z) ^ 2‖ ^ 2 := by
  simp only [inverseCayleyRealFDeriv, ContinuousLinearMap.det,
    ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    ContinuousLinearMap.det_toSpanSingleton, Algebra.norm_complex_eq]
  change Complex.normSq _ = _
  exact Complex.normSq_eq_norm_sq _

/-- The actual Jacobian and the half-plane area density combine to the disc area density. -/
theorem inverseCayley_area_density (z : 𝔻) :
    |(inverseCayleyRealFDeriv z).det| * (1 / (inverseCayleyFormula z).im ^ 2) =
      discAreaDensity z := by
  rw [det_inverseCayleyRealFDeriv, abs_of_nonneg (sq_nonneg _)]
  have h := inverseCayley_weighted_tangent_norm z (1 : ℂ)
  simp only [mul_one, norm_one] at h
  have h' := congrArg (fun t : ℝ => t ^ 2) h
  simpa only [div_pow, discAreaDensity, mul_one, mul_one_div, show (2 : ℝ) ^ 2 = 4 by norm_num]
    using h'

theorem disc_isOpenEmbedding_coe : Topology.IsOpenEmbedding ((↑) : 𝔻 → ℂ) := by
  refine ⟨Complex.UnitDisc.isEmbedding_coe, ?_⟩
  have hr : Set.range ((↑) : 𝔻 → ℂ) = {z : ℂ | ‖z‖ < 1} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.norm_lt_one
    · intro hz
      exact ⟨Complex.UnitDisc.mk z hz, rfl⟩
  rw [hr]
  exact isOpen_lt continuous_norm continuous_const

theorem disc_measurableEmbedding_coe : MeasurableEmbedding ((↑) : 𝔻 → ℂ) :=
  disc_isOpenEmbedding_coe.measurableEmbedding

theorem halfPlane_area_weight (z : ℂ) :
    (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞) = ENNReal.ofReal (1 / z.im ^ 2) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs,
    div_pow, one_pow, sq_abs]

/-- The two density-defined area notions agree under the actual Cayley change of variables. -/
theorem discHyperbolicArea_eq_halfPlane_volume (s : Set 𝔻) (hs : MeasurableSet s) :
    discHyperbolicArea s = volume (discToHalfPlane '' s) := by
  have hsc : MeasurableSet (((↑) : 𝔻 → ℂ) '' s) := disc_measurableEmbedding_coe.measurableSet_image.mpr hs
  have hinj : Set.InjOn inverseCayleyFormula (((↑) : 𝔻 → ℂ) '' s) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ heq
    have hzw : discToHalfPlane z = discToHalfPlane w := by
      apply UpperHalfPlane.coe_injective
      exact heq
    exact congrArg ((↑) : 𝔻 → ℂ) (cayleyEquiv.symm.injective hzw)
  have hmain := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsc
    (f := inverseCayleyFormula) (f' := inverseCayleyRealFDeriv)
    (Set.forall_mem_image.mpr fun z _ =>
      (hasFDerivAt_inverseCayley_real z).hasFDerivWithinAt)
    hinj (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2))
  rw [discHyperbolicArea, discAreaMeasure, withDensity_apply _ hsc,
    UpperHalfPlane.volume_eq_lintegral]
  have him : ((↑) : ℍ → ℂ) '' (discToHalfPlane '' s) =
      inverseCayleyFormula '' (((↑) : 𝔻 → ℂ) '' s) := by
    simp only [Set.image_image, discToHalfPlane, UpperHalfPlane.coe_mk]
  rw [him]
  simp_rw [halfPlane_area_weight]
  rw [hmain]
  apply setLIntegral_congr_fun hsc
  rintro _ ⟨z, hz, rfl⟩
  change ENNReal.ofReal (discAreaDensity z) =
    ENNReal.ofReal |(inverseCayleyRealFDeriv z).det| *
      ENNReal.ofReal (1 / (inverseCayleyFormula z).im ^ 2)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), inverseCayley_area_density]

/-- The actual determinant-one action conjugated into the disc model. -/
def discSL2Equiv (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : 𝔻 ≃ 𝔻 where
  toFun z := halfPlaneToDisc (g • discToHalfPlane z)
  invFun z := halfPlaneToDisc (g⁻¹ • discToHalfPlane z)
  left_inv z := by
    change halfPlaneToDisc (g⁻¹ • discToHalfPlane (halfPlaneToDisc (g • discToHalfPlane z))) = z
    rw [discToHalfPlane_halfPlaneToDisc, inv_smul_smul, halfPlaneToDisc_discToHalfPlane]
  right_inv z := by
    change halfPlaneToDisc (g • discToHalfPlane (halfPlaneToDisc (g⁻¹ • discToHalfPlane z))) = z
    rw [discToHalfPlane_halfPlaneToDisc, smul_inv_smul, halfPlaneToDisc_discToHalfPlane]

theorem discSL2Equiv_distance (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z w : 𝔻) :
    discPathDist (discSL2Equiv g z) (discSL2Equiv g w) = discPathDist z w := by
  simp only [discPathDist_eq_halfPlane, discSL2Equiv, Equiv.coe_fn_mk,
    discToHalfPlane_halfPlaneToDisc, dist_smul]

def discSL2Homeomorph (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : 𝔻 ≃ₜ 𝔻 where
  toEquiv := discSL2Equiv g
  continuous_toFun := continuous_halfPlaneToDisc.comp
    ((continuous_const_smul g).comp continuous_discToHalfPlane)
  continuous_invFun := continuous_halfPlaneToDisc.comp
    ((continuous_const_smul g⁻¹).comp continuous_discToHalfPlane)

theorem discSL2Equiv_area (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s : Set 𝔻)
    (hs : MeasurableSet s) : discHyperbolicArea (discSL2Equiv g '' s) = discHyperbolicArea s := by
  have himg : MeasurableSet (discSL2Equiv g '' s) :=
    (discSL2Homeomorph g).measurableEmbedding.measurableSet_image.mpr hs
  rw [discHyperbolicArea_eq_halfPlane_volume _ himg,
    discHyperbolicArea_eq_halfPlane_volume s hs]
  have him : discToHalfPlane '' (discSL2Equiv g '' s) =
      (fun z : ℍ => g • z) '' (discToHalfPlane '' s) := by
    simp only [Set.image_image, discSL2Equiv, Equiv.coe_fn_mk, discToHalfPlane_halfPlaneToDisc]
  rw [him]
  have h := measure_smul (volume : Measure ℍ) (Matrix.SpecialLinearGroup.mapGL ℝ g)
    (discToHalfPlane '' s)
  change volume ((fun z : ℍ => g • z) '' (discToHalfPlane '' s)) =
    volume (discToHalfPlane '' s) at h
  exact h

theorem discToHalfPlane_zero : discToHalfPlane 0 = UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_injective
  simp [discToHalfPlane, inverseCayleyFormula]

theorem discSL2Equiv_center (q : 𝔻) :
    discSL2Equiv (discToHalfPlane q).toSL2R 0 = q := by
  change halfPlaneToDisc ((discToHalfPlane q).toSL2R • discToHalfPlane 0) = q
  rw [discToHalfPlane_zero, UpperHalfPlane.toSL2R_smul_I, halfPlaneToDisc_discToHalfPlane]

theorem continuous_discPathDist_left (q : 𝔻) : Continuous (discPathDist q) := by
  change Continuous (fun z : 𝔻 => discPathDist q z)
  simp only [discPathDist_eq_halfPlane]
  exact continuous_const.dist continuous_discToHalfPlane

theorem measurableSet_discClosedBall (q : 𝔻) (r : ℝ) :
    MeasurableSet {z : 𝔻 | discPathDist q z ≤ r} :=
  (isClosed_le (continuous_discPathDist_left q) continuous_const).measurableSet

theorem discSL2Equiv_image_closedBall (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (q : 𝔻) (r : ℝ) :
    discSL2Equiv g '' {z : 𝔻 | discPathDist q z ≤ r} =
      {z : 𝔻 | discPathDist (discSL2Equiv g q) z ≤ r} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Set.mem_ofPred_eq, discSL2Equiv_distance] using hw
  · intro hz
    refine ⟨(discSL2Equiv g).symm z, ?_, (discSL2Equiv g).apply_symm_apply z⟩
    have h := discSL2Equiv_distance g q ((discSL2Equiv g).symm z)
    rw [(discSL2Equiv g).apply_symm_apply] at h
    change discPathDist q ((discSL2Equiv g).symm z) ≤ r
    rw [← h]
    exact hz

/-- With arbitrary centre in the genuine disc area measure. -/
theorem discHyperbolicArea_closedBall (q : 𝔻) (r : ℝ) (hr : 0 ≤ r) :
    discHyperbolicArea {z : 𝔻 | discPathDist q z ≤ r} =
      ENNReal.ofReal (4 * Real.pi * Real.sinh (r / 2) ^ 2) := by
  have h := discSL2Equiv_area (discToHalfPlane q).toSL2R
    {z : 𝔻 | discPathDist 0 z ≤ r} (measurableSet_discClosedBall 0 r)
  rw [discSL2Equiv_image_closedBall, discSL2Equiv_center] at h
  exact h.trans (discHyperbolicArea_closedBall_zero r hr)

/-- Transport any actual disc C¹ piece by the proved model isometry. -/
def DiscC1CurvePiece.moveSL2 (c : DiscC1CurvePiece) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    DiscC1CurvePiece := (c.toHalfPlane.mapSL2 g).toDisc

theorem DiscC1CurvePiece.moveSL2_curve (c : DiscC1CurvePiece)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    (c.moveSL2 g).curve t = discSL2Equiv g (c.curve t) := rfl

theorem DiscC1CurvePiece.moveSL2_length (c : DiscC1CurvePiece)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : (c.moveSL2 g).length = c.length := by
  rw [DiscC1CurvePiece.moveSL2, C1CurvePiece.toDisc_length,
    C1CurvePiece.mapSL2_length, DiscC1CurvePiece.toHalfPlane_length]

/-- A circle with arbitrary centre is obtained by an actual density-preserving curve map. -/
def centeredDiscCirclePiece (q : 𝔻) (r : ℝ) (hr : 0 ≤ r) : DiscC1CurvePiece :=
  (discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).moveSL2
    (discToHalfPlane q).toSL2R

theorem centeredDiscCirclePiece_length (q : 𝔻) (r : ℝ) (hr : 0 ≤ r) :
    (centeredDiscCirclePiece q r hr).length = 2 * Real.pi * Real.sinh r := by
  rw [centeredDiscCirclePiece, DiscC1CurvePiece.moveSL2_length]
  exact discCirclePiece_hyperbolic_length r hr

theorem centeredDiscCirclePiece_distance (q : 𝔻) (r : ℝ) (hr : 0 ≤ r) (θ : ℝ) :
    discPathDist q ((centeredDiscCirclePiece q r hr).curve θ) = r := by
  rw [centeredDiscCirclePiece, DiscC1CurvePiece.moveSL2_curve]
  calc
    discPathDist q _ = discPathDist
        (discSL2Equiv (discToHalfPlane q).toSL2R 0)
        (discSL2Equiv (discToHalfPlane q).toSL2R
          ((discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve θ)) :=
      by rw [discSL2Equiv_center]
    _ = discPathDist 0 _ := discSL2Equiv_distance _ _ _
    _ = r := discCirclePiece_distance r hr θ

theorem disc_distance_zero_eq_iff (z : 𝔻) (r : ℝ) :
    discPathDist 0 z = r ↔ ‖(z : ℂ)‖ = Real.tanh (r / 2) := by
  constructor
  · intro h
    rw [disc_norm_eq_tanh_half_distance, h]
  · intro h
    rw [disc_norm_eq_tanh_half_distance] at h
    have h' := congrArg Real.artanh h
    rw [Real.artanh_tanh, Real.artanh_tanh] at h'
    linarith

theorem discCirclePiece_image_Icc (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    (discCirclePiece R hR hR1).curve '' Icc 0 (2 * Real.pi) =
      {z : 𝔻 | ‖(z : ℂ)‖ = R} := by
  ext z
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    simp only [Set.mem_ofPred_eq, discCirclePiece, Complex.UnitDisc.coe_mk,
      norm_circleMap_zero, abs_of_nonneg hR]
  · intro hz
    change ‖(z : ℂ)‖ = R at hz
    have hmem : (z : ℂ) ∈ Metric.sphere 0 |R| := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hR] using hz
    rw [← image_circleMap_Ioc] at hmem
    obtain ⟨θ, hθ, heq⟩ := hmem
    refine ⟨θ, ⟨hθ.1.le, hθ.2⟩, ?_⟩
    apply Complex.UnitDisc.coe_injective
    exact heq

theorem discCirclePiece_sphere_image (r : ℝ) (hr : 0 ≤ r) :
    (discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve ''
        Icc 0 (2 * Real.pi) = {z : 𝔻 | discPathDist 0 z = r} := by
  rw [discCirclePiece_image_Icc]
  ext z
  exact (disc_distance_zero_eq_iff z r).symm

theorem discSL2Equiv_image_sphere (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (q : 𝔻) (r : ℝ) :
    discSL2Equiv g '' {z : 𝔻 | discPathDist q z = r} =
      {z : 𝔻 | discPathDist (discSL2Equiv g q) z = r} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Set.mem_ofPred_eq, discSL2Equiv_distance] using hw
  · intro hz
    refine ⟨(discSL2Equiv g).symm z, ?_, (discSL2Equiv g).apply_symm_apply z⟩
    have h := discSL2Equiv_distance g q ((discSL2Equiv g).symm z)
    rw [(discSL2Equiv g).apply_symm_apply] at h
    exact h.symm.trans hz

/-- The actual integrated parametrization covers the complete circle, with arbitrary centre. -/
theorem centeredDiscCirclePiece_image_Icc (q : 𝔻) (r : ℝ) (hr : 0 ≤ r) :
    (centeredDiscCirclePiece q r hr).curve '' Icc 0 (2 * Real.pi) =
      {z : 𝔻 | discPathDist q z = r} := by
  have heq : (centeredDiscCirclePiece q r hr).curve =
      discSL2Equiv (discToHalfPlane q).toSL2R ∘
        (discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve := rfl
  rw [heq]
  change (fun θ => discSL2Equiv (discToHalfPlane q).toSL2R
      ((discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve θ)) ''
        Icc 0 (2 * Real.pi) = _
  rw [← Set.image_image (discSL2Equiv (discToHalfPlane q).toSL2R)
      (discCirclePiece (Real.tanh (r / 2)) (tanh_half_nonneg hr) (Real.tanh_lt_one _)).curve,
    discCirclePiece_sphere_image r hr, discSL2Equiv_image_sphere, discSL2Equiv_center]

theorem discCirclePiece_closed (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    (discCirclePiece R hR hR1).curve 0 = (discCirclePiece R hR hR1).curve (2 * Real.pi) := by
  apply Complex.UnitDisc.coe_injective
  change circleMap 0 R 0 = circleMap 0 R (2 * Real.pi)
  simpa only [zero_add] using ((periodic_circleMap 0 R) 0).symm

theorem discCirclePiece_injOn_Ioc (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    Set.InjOn (discCirclePiece R hR.le hR1).curve (Ioc 0 (2 * Real.pi)) := by
  intro θ hθ φ hφ heq
  have hc := congrArg ((↑) : 𝔻 → ℂ) heq
  apply eq_of_circleMap_eq hR.ne' _ hc
  rw [abs_lt]
  constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]

theorem centeredDiscCirclePiece_closed (q : 𝔻) (r : ℝ) (hr : 0 ≤ r) :
    (centeredDiscCirclePiece q r hr).curve 0 =
      (centeredDiscCirclePiece q r hr).curve (2 * Real.pi) := by
  simp only [centeredDiscCirclePiece, DiscC1CurvePiece.moveSL2_curve]
  rw [discCirclePiece_closed]

theorem centeredDiscCirclePiece_injOn_Ioc (q : 𝔻) (r : ℝ) (hr : 0 < r) :
    Set.InjOn (centeredDiscCirclePiece q r hr.le).curve (Ioc 0 (2 * Real.pi)) := by
  have ht : 0 < Real.tanh (r / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  intro θ hθ φ hφ heq
  have h' := (discSL2Equiv (discToHalfPlane q).toSL2R).injective
    (show discSL2Equiv (discToHalfPlane q).toSL2R _ =
      discSL2Equiv (discToHalfPlane q).toSL2R _ from heq)
  exact discCirclePiece_injOn_Ioc _ ht (Real.tanh_lt_one _) hθ hφ h'

theorem discToHalfPlane_image_closedBall (q : 𝔻) (r : ℝ) :
    discToHalfPlane '' {z : 𝔻 | discPathDist q z ≤ r} =
      {z : ℍ | dist (discToHalfPlane q) z ≤ r} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Set.mem_ofPred_eq, discPathDist_eq_halfPlane] using hw
  · intro hz
    refine ⟨halfPlaneToDisc z, ?_, discToHalfPlane_halfPlaneToDisc z⟩
    simpa only [Set.mem_ofPred_eq, discPathDist_eq_halfPlane,
      discToHalfPlane_halfPlaneToDisc] using hz

/-- The same area formula in Mathlib's density-defined upper-half-plane volume. -/
theorem halfPlane_volume_closedBall (q : ℍ) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall q r) = ENNReal.ofReal (4 * Real.pi * Real.sinh (r / 2) ^ 2) := by
  have h := discHyperbolicArea_eq_halfPlane_volume
    {z : 𝔻 | discPathDist (halfPlaneToDisc q) z ≤ r}
    (measurableSet_discClosedBall _ _)
  rw [discToHalfPlane_image_closedBall, discToHalfPlane_halfPlaneToDisc] at h
  have hs : {z : ℍ | dist q z ≤ r} = Metric.closedBall q r := by
    ext z
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_comm]
  rw [hs] at h
  exact h.symm.trans (discHyperbolicArea_closedBall (halfPlaneToDisc q) r hr)

/-- The canonical full-circle parametrization in the upper-half-plane model. -/
def halfPlaneCirclePiece (q : ℍ) (r : ℝ) (hr : 0 ≤ r) : C1CurvePiece :=
  (centeredDiscCirclePiece (halfPlaneToDisc q) r hr).toHalfPlane

theorem halfPlaneCirclePiece_length (q : ℍ) (r : ℝ) (hr : 0 ≤ r) :
    (halfPlaneCirclePiece q r hr).length = 2 * Real.pi * Real.sinh r := by
  rw [halfPlaneCirclePiece, DiscC1CurvePiece.toHalfPlane_length,
    centeredDiscCirclePiece_length]

theorem halfPlaneCirclePiece_distance (q : ℍ) (r : ℝ) (hr : 0 ≤ r) (θ : ℝ) :
    dist q ((halfPlaneCirclePiece q r hr).curve θ) = r := by
  have h := centeredDiscCirclePiece_distance (halfPlaneToDisc q) r hr θ
  rw [discPathDist_eq_halfPlane, discToHalfPlane_halfPlaneToDisc] at h
  exact h

/-- Both conclusions, with an actual closed once-around circle and its density integral. -/
theorem hyperbolic_disc_area_and_circle_length (q : 𝔻) (r : ℝ) (hr : 0 ≤ r) :
    discHyperbolicArea {z : 𝔻 | discPathDist q z ≤ r} =
        ENNReal.ofReal (4 * Real.pi * Real.sinh (r / 2) ^ 2) ∧
    (centeredDiscCirclePiece q r hr).length = 2 * Real.pi * Real.sinh r ∧
    (centeredDiscCirclePiece q r hr).curve '' Icc 0 (2 * Real.pi) =
        {z : 𝔻 | discPathDist q z = r} ∧
    (centeredDiscCirclePiece q r hr).curve 0 =
        (centeredDiscCirclePiece q r hr).curve (2 * Real.pi) ∧
    (0 < r → Set.InjOn (centeredDiscCirclePiece q r hr).curve (Ioc 0 (2 * Real.pi))) := by
  refine ⟨discHyperbolicArea_closedBall q r hr, centeredDiscCirclePiece_length q r hr,
    centeredDiscCirclePiece_image_Icc q r hr, centeredDiscCirclePiece_closed q r hr, ?_⟩
  intro hrpos
  exact centeredDiscCirclePiece_injOn_Ioc q r hrpos

end

end LowDimensionalTopology.Geometry.Hyperbolic
