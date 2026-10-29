module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinateProjection
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticRamifiedDevelopment
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The original quadratic coefficient and its two ordinary normalizers

The projected coordinate has derivative square equal to the coefficient of the
same original differential. The ordinary normalizer with coefficient `c²` and
its rescaling with coefficient one give the same flat primitive and radius.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

private theorem slitExponential_symm_apply (w : ℂ) :
    quadraticSlitExponential.symm w = Complex.log (-w) + (Real.pi : ℂ) * Complex.I := by
  change -(-((Real.pi : ℂ) * Complex.I)) + Complex.log ((-1 : ℂ)⁻¹ * w) = _
  simp only [neg_neg, inv_neg, inv_one, neg_one_mul]
  exact add_comm _ _

private theorem slitExponential_mem_target (w : ℂ) :
    w ∈ quadraticSlitExponential.target ↔ -w ∈ Complex.slitPlane := by
  change (((-1 : ℂ)⁻¹ * w ∈ Complex.slitPlane) ∧
    Complex.log ((-1 : ℂ)⁻¹ * w) ∈ (univ : Set ℂ)) ↔ _
  simp only [inv_neg, inv_one, neg_one_mul, mem_univ, and_true]

private def slitFlatBranch (m : ℕ) (w : ℂ) : ℂ :=
  Complex.exp (quadraticZeroExponent m * quadraticSlitExponential.symm w)

private theorem slitFlatBranch_data (m : ℕ) {w : ℂ}
    (hw : w ∈ quadraticSlitExponential.target) :
    AnalyticAt ℂ (slitFlatBranch m) w ∧
      deriv (slitFlatBranch m) w ^ 2 = quadraticZeroExponent m ^ 2 * w ^ m := by
  have analytic (s : ℂ) (hs : s ∈ quadraticSlitExponential.target) :
      AnalyticAt ℂ (slitFlatBranch m) s := by
    have hlog := analyticAt_id.neg.clog ((slitExponential_mem_target s).1 hs)
    change AnalyticAt ℂ
      (fun ξ => Complex.exp (quadraticZeroExponent m * quadraticSlitExponential.symm ξ)) s
    simp only [slitExponential_symm_apply]
    exact (analyticAt_const.mul (hlog.add analyticAt_const)).cexp'
  have square (s : ℂ) (hs : s ∈ quadraticSlitExponential.target) :
      slitFlatBranch m s ^ 2 = s ^ (m + 2) := by
    have he : Complex.exp (quadraticSlitExponential.symm s) = s :=
      (quadraticSlitExponential_apply _).symm.trans (quadraticSlitExponential.right_inv hs)
    calc
      slitFlatBranch m s ^ 2 =
          Complex.exp (2 * (quadraticZeroExponent m * quadraticSlitExponential.symm s)) :=
        (Complex.exp_nat_mul _ 2).symm
      _ = Complex.exp (((m + 2 : ℕ) : ℂ) * quadraticSlitExponential.symm s) := by
        congr 1
        dsimp [quadraticZeroExponent]
        ring
      _ = Complex.exp (quadraticSlitExponential.symm s) ^ (m + 2) :=
        Complex.exp_nat_mul _ _
      _ = s ^ (m + 2) := by rw [he]
  have hwne : w ≠ 0 :=
    neg_ne_zero.mp (Complex.slitPlane_ne_zero ((slitExponential_mem_target w).1 hw))
  have hsq : ∀ᶠ ξ in 𝓝 w, slitFlatBranch m ξ ^ 2 = ξ ^ (m + 2) := by
    filter_upwards [quadraticSlitExponential.open_target.mem_nhds hw] with ξ hξ
    exact square ξ hξ
  refine ⟨analytic w hw, ?_⟩
  simpa only [quadraticZeroExponent, Nat.cast_add, Nat.cast_ofNat] using
    (LiZhongQC.s26d_a_deriv_sq hwne (analytic w hw) hsq).self_of_nhds

namespace QuadraticNaturalCoordinateData

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {p : X}
    (D : QuadraticNaturalCoordinateData R q p)

private theorem ordinary_source (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    x ∈ D.ordinaryNeighborhood.source ↔
      x ∈ (chartAt ℂ p).source ∧ chartAt ℂ p x ∈ D.ordinaryChart.source ∧
        D.ordinaryChart (chartAt ℂ p x) ∈ Metric.ball (0 : ℂ) D.radius := by
  let := R.toRiemannAtlas.toChartedSpace
  change (((x ∈ (chartAt ℂ p).source ∧ chartAt ℂ p x ∈ D.ordinaryChart.source) ∧
    D.ordinaryChart (chartAt ℂ p x) ∈ interior (Metric.ball (0 : ℂ) D.radius))) ↔ _
  rw [Metric.isOpen_ball.interior_eq]
  exact and_assoc

private theorem projected_chart_eventually :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ w ∈ (chartAt ℂ p).target,
      (fun ξ => D.projectedCoordinate ((chartAt ℂ p).symm ξ)) =ᶠ[𝓝 w]
        (if D.order = 0 then (D.ordinaryChart : ℂ → ℂ)
          else fun ξ => slitFlatBranch D.order (D.ordinaryChart ξ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  intro w hw
  filter_upwards [(chartAt ℂ p).open_target.mem_nhds hw] with ξ hξ
  by_cases hm : D.order = 0
  · simp only [projectedCoordinate, targetProjection, retainedCoordinate, ite_eq_left hm]
    change D.ordinaryChart (chartAt ℂ p ((chartAt ℂ p).symm ξ)) = D.ordinaryChart ξ
    rw [(chartAt ℂ p).right_inv hξ]
  · simp only [projectedCoordinate, targetProjection, retainedCoordinate, ite_eq_right hm]
    change Complex.exp ((((D.order + 2 : ℕ) : ℂ) / 2) *
      quadraticSlitExponential.symm (D.ordinaryChart (chartAt ℂ p ((chartAt ℂ p).symm ξ)))) = _
    rw [(chartAt ℂ p).right_inv hξ]
    rfl

/-- The projected coordinate is a conformal primitive of the given original
quadratic coefficient at every point of its actual coordinate source. -/
theorem projectedCoordinate_natural :
    letI := R.toRiemannAtlas.toChartedSpace
    let F : ℂ → ℂ := fun w => D.projectedCoordinate ((chartAt ℂ p).symm w)
    ∀ x ∈ D.retainedCoordinate.source,
      AnalyticAt ℂ F (chartAt ℂ p x) ∧
        deriv F (chartAt ℂ p x) ^ 2 = (q : X → ℂ → ℂ) p (chartAt ℂ p x) ∧
        deriv F (chartAt ℂ p x) ≠ 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let F : ℂ → ℂ := fun w => D.projectedCoordinate ((chartAt ℂ p).symm w)
  dsimp only
  intro x hx
  let z := chartAt ℂ p x
  change AnalyticAt ℂ F z ∧ deriv F z ^ 2 = (q : X → ℂ → ℂ) p z ∧ deriv F z ≠ 0
  have hxA : x ∈ D.ordinaryNeighborhood.source := by
    by_cases hm : D.order = 0
    · simpa only [retainedCoordinate, ite_eq_left hm] using hx
    · rw [retainedCoordinate, ite_eq_right hm] at hx
      exact hx.1
  obtain ⟨hxchart, hz, -⟩ := (ordinary_source D x).1 hxA
  have hztarget : z ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hxchart
  have hη := D.normal.analytic z hz
  have hφ := D.normal.identity z hz
  have hFeq := projected_chart_eventually D z hztarget
  by_cases hm : D.order = 0
  · rw [ite_eq_left hm] at hFeq
    have hF := hη.differentiableAt.hasDerivAt.congr_of_eventuallyEq hFeq
    have hsq : deriv F z ^ 2 = (q : X → ℂ → ℂ) p z := by
      rw [hF.deriv]
      simpa only [hm, Nat.cast_zero, zero_add, div_self (two_ne_zero : (2 : ℂ) ≠ 0),
        one_pow, pow_zero, one_mul] using hφ.symm
    have hqne : (q : X → ℂ → ℂ) p z ≠ 0 := by
      by_cases hz0 : z = chartAt ℂ p p
      · rw [hz0]
        exact D.normal.regular_iff.mpr hm
      · exact D.normal.ne_zero z hz hz0
    refine ⟨hη.congr hFeq.symm, hsq, ?_⟩
    intro hf0
    apply hqne
    rw [← hsq, hf0, zero_pow two_ne_zero]
  · rw [ite_eq_right hm] at hFeq
    have hcut : D.ordinaryChart z ∈ quadraticSlitExponential.target := by
      rw [retainedCoordinate, ite_eq_right hm] at hx
      exact hx.2
    obtain ⟨hG, hGsq⟩ := slitFlatBranch_data D.order hcut
    have hcomp := hG.differentiableAt.hasDerivAt.comp z hη.differentiableAt.hasDerivAt
    have hF := hcomp.congr_of_eventuallyEq hFeq
    have hsq : deriv F z ^ 2 = (q : X → ℂ → ℂ) p z := by
      rw [hF.deriv, mul_pow, hGsq]
      simpa only [quadraticZeroExponent, Nat.cast_add, Nat.cast_ofNat] using hφ.symm
    have hz0 : z ≠ chartAt ℂ p p := by
      intro hz0
      have hη0 : D.ordinaryChart z = 0 := by
        rw [hz0]
        exact D.normal.natural.2.1
      have hn := Complex.slitPlane_ne_zero ((slitExponential_mem_target _).1 hcut)
      exact hn (by rw [hη0, neg_zero])
    refine ⟨(hG.comp hη).congr hFeq.symm, hsq, ?_⟩
    intro hf0
    apply D.normal.ne_zero z hz hz0
    rw [← hsq, hf0, zero_pow two_ne_zero]

/-- A fixed nonzero rescaling of the original ordinary normalizer gives the
coefficient-one normal form for the same original quadratic coefficient. -/
theorem coefficientOneNormalizer_data :
    letI := R.toRiemannAtlas.toChartedSpace
    let z : ℂ → ℂ := fun w => quadraticZeroScaling D.order * D.ordinaryChart w
    AnalyticAt ℂ z (chartAt ℂ p p) ∧ z (chartAt ℂ p p) = 0 ∧
      deriv z (chartAt ℂ p p) ≠ 0 ∧
      ∀ w ∈ D.ordinaryChart.source,
        (q : X → ℂ → ℂ) p w = z w ^ D.order * deriv z w ^ 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  let a := quadraticZeroScaling D.order
  let z : ℂ → ℂ := fun w => a * D.ordinaryChart w
  have ha : a ≠ 0 := quadraticZeroScaling_ne_zero D.order
  have hη := D.normal.natural.1
  have hd : deriv z (chartAt ℂ p p) = a * deriv D.ordinaryChart (chartAt ℂ p p) :=
    (hη.differentiableAt.hasDerivAt.const_mul a).deriv
  refine ⟨analyticAt_const.mul hη, ?_, ?_, ?_⟩
  · change a * D.ordinaryChart (chartAt ℂ p p) = 0
    rw [D.normal.natural.2.1, mul_zero]
  · rw [hd]
    exact mul_ne_zero ha D.normal.natural.2.2.1
  · intro w hw
    have hwη := D.normal.analytic w hw
    have hdw : deriv z w = a * deriv D.ordinaryChart w :=
      (hwη.differentiableAt.hasDerivAt.const_mul a).deriv
    have hpower : a ^ (D.order + 2) = quadraticZeroExponent D.order ^ 2 :=
      quadraticZeroScaling_pow D.order
    have hφ : (q : X → ℂ → ℂ) p w =
        quadraticZeroExponent D.order ^ 2 * D.ordinaryChart w ^ D.order *
          deriv D.ordinaryChart w ^ 2 := by
      simpa only [quadraticZeroExponent, Nat.cast_add, Nat.cast_ofNat] using D.normal.identity w hw
    rw [hφ, hdw, ← hpower]
    change a ^ (D.order + 2) * D.ordinaryChart w ^ D.order * deriv D.ordinaryChart w ^ 2 =
      (a * D.ordinaryChart w) ^ D.order * (a * deriv D.ordinaryChart w) ^ 2
    rw [pow_add, mul_pow, mul_pow]
    ring

/-- The two ordinary normalizations give the same flat value at the actual
original points, with the corresponding literal change of ordinary radius. -/
theorem zeroSector_standard_formula (hm : 0 < D.order) :
    letI := R.toRiemannAtlas.toChartedSpace
    let c := quadraticZeroExponent D.order
    let a := quadraticZeroScaling D.order
    a = (Real.exp (Real.log D.exponent / D.exponent) : ℂ) ∧
      Real.rpow (‖a‖ * D.radius) D.exponent / D.exponent =
        Real.rpow D.radius D.exponent ∧
      ∀ u : D.sourceLogStrip,
        a * D.ordinaryChart (chartAt ℂ p (D.sourceLogProjection u)) =
            Complex.exp ((u : ℂ) + Complex.log c / c) ∧
          D.projectedCoordinate (D.sourceLogProjection u) =
            quadraticZeroDevelopment D.order ((u : ℂ) + Complex.log c / c) := by
  let := R.toRiemannAtlas.toChartedSpace
  let c := quadraticZeroExponent D.order
  let a := quadraticZeroScaling D.order
  have hpos : 0 < D.exponent := by dsimp [exponent]; positivity
  have hcast : c = (D.exponent : ℂ) := by
    simp only [c, quadraticZeroExponent, exponent, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have ha : a = (Real.exp (Real.log D.exponent / D.exponent) : ℂ) := by
    change Complex.exp (Complex.log c / c) = _
    rw [hcast, ← Complex.ofReal_log hpos.le, ← Complex.ofReal_div, ← Complex.ofReal_exp]
  have hnorm : ‖a‖ = Real.exp (Real.log D.exponent / D.exponent) := by
    rw [ha, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hpower : Real.rpow ‖a‖ D.exponent = D.exponent := by
    rw [Real.rpow_eq_pow, hnorm, ← Real.exp_mul,
      div_mul_cancel₀ _ hpos.ne', Real.exp_log hpos]
  have hmul : Real.rpow (‖a‖ * D.radius) D.exponent =
      Real.rpow ‖a‖ D.exponent * Real.rpow D.radius D.exponent := by
    simpa only [Real.rpow_eq_pow] using
      (Real.mul_rpow (z := D.exponent) (norm_nonneg a) D.radius_pos.le)
  refine ⟨ha, ?_, ?_⟩
  · change Real.rpow (‖a‖ * D.radius) D.exponent / D.exponent =
      Real.rpow D.radius D.exponent
    rw [hmul, hpower]
    calc
      (D.exponent * Real.rpow D.radius D.exponent) / D.exponent =
          Real.rpow D.radius D.exponent * (D.exponent / D.exponent) := by ring
      _ = Real.rpow D.radius D.exponent := by rw [div_self hpos.ne', mul_one]
  · intro u
    have hwball : Complex.exp (u : ℂ) ∈ Metric.ball (0 : ℂ) D.radius := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      calc
        Real.exp (u : ℂ).re < Real.exp (Real.log D.radius) := Real.exp_lt_exp.mpr u.property.1
        _ = D.radius := Real.exp_log D.radius_pos
    have hwZ := D.disk_target hwball
    have hwchart := D.normal.source_sub (D.ordinaryChart.map_target hwZ)
    have hη : D.ordinaryChart (chartAt ℂ p (D.sourceLogProjection u)) = Complex.exp (u : ℂ) := by
      change D.ordinaryChart (chartAt ℂ p
        ((chartAt ℂ p).symm (D.ordinaryChart.symm (Complex.exp (u : ℂ))))) = _
      rw [(chartAt ℂ p).right_inv hwchart, D.ordinaryChart.right_inv hwZ]
    constructor
    · rw [hη]
      change Complex.exp (Complex.log c / c) * Complex.exp (u : ℂ) = _
      rw [Complex.exp_add]
      exact mul_comm _ _
    · calc
        D.projectedCoordinate (D.sourceLogProjection u) =
            Complex.exp ((D.exponent : ℂ) * (u : ℂ)) :=
          ((zeroSector_coordinates D hm).2 u).2.2
        _ = Complex.exp (c * (u : ℂ)) := by rw [hcast]
        _ = quadraticZeroDevelopment D.order ((u : ℂ) + Complex.log c / c) :=
          (quadraticZeroDevelopment_rescaled D.order u).symm

end QuadraticNaturalCoordinateData
end LowDimensionalTopology.Geometry.Teichmuller
