module

public import LowDimensionalTopology.Geometry.Teichmuller.AhlforsWeillRealAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicBiparameterFamily
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The actual asymmetric harmonic Ahlfors-Weill formula

The normalized holomorphic pair in the existing construction gives a
rational expression using only the same map and its lower derivatives.
Normalized uniqueness identifies it with the actual two-parameter family
on the asymmetric axis. No dependence of the auxiliary pair on a parameter
is needed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami QuadraticBergman LiZhongQC

private theorem normalized_pair_rational_formula
    {H v₁ v₂ : ℂ → ℂ} {d : ℂ} (hd : d ≠ 0)
    (hv₁ : DifferentiableOn ℂ v₁ lowerHalf)
    (hv₂ : DifferentiableOn ℂ v₂ lowerHalf)
    (hW : ∀ w ∈ lowerHalf, v₁ w * deriv v₂ w - v₂ w * deriv v₁ w = d)
    (hL : ∀ w ∈ lowerHalf, v₂ w ≠ 0 ∧ H w = v₁ w / v₂ w)
    (hU : ∀ z ∈ upperHalf,
      v₂ (conj z) + (z - conj z) * deriv v₂ (conj z) ≠ 0 ∧
      H z = (v₁ (conj z) + (z - conj z) * deriv v₁ (conj z)) /
        (v₂ (conj z) + (z - conj z) * deriv v₂ (conj z))) :
    ∀ z ∈ upperHalf,
      2 * deriv H (conj z) - (z - conj z) * deriv (deriv H) (conj z) ≠ 0 ∧
      H z = H (conj z) + 2 * (z - conj z) * deriv H (conj z) ^ 2 /
        (2 * deriv H (conj z) - (z - conj z) * deriv (deriv H) (conj z)) := by
  have hfirst (w : ℂ) (hw : w ∈ lowerHalf) :
      deriv H w = -d / v₂ w ^ 2 := by
    have hlocal : H =ᶠ[𝓝 w] fun v => v₁ v / v₂ v :=
      Filter.mem_of_superset (isOpen_lowerHalf.mem_nhds hw) fun v hv => (hL v hv).2
    have hquot := ((hv₁.differentiableAt (isOpen_lowerHalf.mem_nhds hw)).hasDerivAt).div
      ((hv₂.differentiableAt (isOpen_lowerHalf.mem_nhds hw)).hasDerivAt) (hL w hw).1
    have hnum : deriv v₁ w * v₂ w - v₁ w * deriv v₂ w = -d := by
      linear_combination -(hW w hw)
    rw [hnum] at hquot
    exact hlocal.deriv_eq.trans hquot.deriv
  have hsecond (w : ℂ) (hw : w ∈ lowerHalf) :
      deriv (deriv H) w = 2 * d * deriv v₂ w / v₂ w ^ 3 := by
    have hlocal : deriv H =ᶠ[𝓝 w] fun v => -d / v₂ v ^ 2 :=
      Filter.mem_of_superset (isOpen_lowerHalf.mem_nhds hw) fun v hv => hfirst v hv
    have hquot := (hasDerivAt_const w (-d)).div
      (((hv₂.differentiableAt (isOpen_lowerHalf.mem_nhds hw)).hasDerivAt).fun_pow 2)
      (pow_ne_zero 2 (hL w hw).1)
    rw [(hquot.congr_of_eventuallyEq hlocal).deriv]
    field_simp [(hL w hw).1]
    ring
  intro z hz
  have hzL : conj z ∈ lowerHalf := by
    change (conj z).im < 0
    simpa only [Complex.conj_im] using neg_lt_zero.mpr hz
  have hne := (hL (conj z) hzL).1
  have hu := (hU z hz).1
  have hden : 2 * deriv H (conj z) - (z - conj z) * deriv (deriv H) (conj z) =
      -2 * d * (v₂ (conj z) + (z - conj z) * deriv v₂ (conj z)) / v₂ (conj z) ^ 3 := by
    rw [hfirst (conj z) hzL, hsecond (conj z) hzL]
    field_simp [hne]
    ring
  have hdenne : 2 * deriv H (conj z) -
      (z - conj z) * deriv (deriv H) (conj z) ≠ 0 := by
    rw [hden]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) hd) hu)
      (pow_ne_zero 3 hne)
  refine ⟨hdenne, ?_⟩
  have hv₁' : deriv v₁ (conj z) =
      (v₁ (conj z) * deriv v₂ (conj z) - d) / v₂ (conj z) := by
    apply (eq_div_iff hne).2
    linear_combination -(hW (conj z) hzL)
  rw [hden, hfirst (conj z) hzL, (hL (conj z) hzL).2, (hU z hz).2, hv₁']
  field_simp [hne, hu, hd]
  ring

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

/-- The same asymmetric normalized family has the exact Ahlfors-Weill
expression in its own lower-half-plane derivatives, with nonzero denominator. -/
theorem canonicalBiparameterFamily_asymmetric_ahlforsWeill
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, ‖s‖ < ε →
      let A := canonicalBiparameterFamily R p q s 0
      DifferentiableOn ℂ A lowerHalf ∧ AnalyticOnNhd ℝ A upperHalf ∧
      ∀ z ∈ upperHalf,
        2 * deriv A (conj z) - (z - conj z) * deriv (deriv A) (conj z) ≠ 0 ∧
        A z = A (conj z) + 2 * (z - conj z) * deriv A (conj z) ^ 2 /
          (2 * deriv A (conj z) - (z - conj z) * deriv (deriv A) (conj z)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨δ, hδ, hspec, _, _⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  obtain ⟨M, hM, hbound⟩ := uniformizedQuadratic_weightedBound R p hp q
  have hM1 : 0 < M + 1 := by linarith
  let ε : ℝ := min δ (1 / (M + 1))
  have hε : 0 < ε := lt_min hδ (by positivity)
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hsδ : ‖s‖ < δ := hs.trans_le (min_le_left _ _)
  have hsM1 : ‖s‖ * (M + 1) < 1 :=
    (lt_div_iff₀ hM1).mp (hs.trans_le (min_le_right _ _))
  have hsM : ‖s‖ * M < 1 := by nlinarith [norm_nonneg s]
  let φ : ℂ → ℂ := fun w => -(s / 2) * conj (uniformizedQuadratic R p q (conj w))
  have hQ : DifferentiableOn ℂ (uniformizedQuadratic R p q) upperHalf :=
    utm_liftQD_differentiableOn q.property hp
  have hφd : DifferentiableOn ℂ φ lowerHalf := by
    intro w hw
    have hwH : conj w ∈ upperHalf := by
      change 0 < (conj w).im
      simpa only [Complex.conj_im] using neg_pos.mpr hw
    have hq : DifferentiableAt ℂ
        (fun v => conj (uniformizedQuadratic R p q (conj v))) w := by
      simpa only [Function.comp_def, Complex.conj_conj] using
        (hQ.differentiableAt (isOpen_upperHalf.mem_nhds hwH)).conj_conj
    exact (hq.const_mul (-(s / 2))).differentiableWithinAt
  have hφb : ∀ w ∈ lowerHalf, ‖φ w‖ * w.im ^ 2 ≤ ‖s‖ * M / 2 := by
    intro w hw
    have hwH : conj w ∈ upperHalf := by
      change 0 < (conj w).im
      simpa only [Complex.conj_im] using neg_pos.mpr hw
    calc
      ‖φ w‖ * w.im ^ 2 =
          (‖s‖ / 2) * (‖uniformizedQuadratic R p q (conj w)‖ * (conj w).im ^ 2) := by
        dsimp only [φ]
        rw [norm_mul, norm_neg, norm_div, Complex.norm_ofNat, Complex.norm_conj,
          Complex.conj_im, neg_sq]
        ring
      _ ≤ (‖s‖ / 2) * M := mul_le_mul_of_nonneg_left (hbound (conj w) hwH) (by positivity)
      _ = ‖s‖ * M / 2 := by ring
  obtain ⟨H, Q, hHQ, hHs, hH0, hH1, hHd, _, hHμ, hHa, v₁, v₂, d,
      hd, hv₁, hv₂, hODE, hL, hU⟩ :=
    ahlforsWeill_core_normalizedPair (by positivity : 0 ≤ ‖s‖ * M / 2)
      (by linarith : ‖s‖ * M / 2 < 1 / 2) hφd hφb
  have hsol := (hspec s 0 hsδ (by simpa only [norm_zero] using hδ)).2
  have heq : canonicalBiparameterFamily R p q s 0 = H := by
    refine thm13_5_uniqueness_plane hsol.1 ⟨Q, hHQ⟩ hsol.2.1 hHs ?_
      hsol.2.2.1 hsol.2.2.2.1 hH0 hH1
    have hnull : ∀ᵐ w : ℂ, w ∉ {v : ℂ | v.im = 0} :=
      measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
    filter_upwards [hsol.2.2.2.2, hnull] with w hw hne
    rw [hw]
    rcases lt_or_gt_of_ne (hne : w.im ≠ 0) with hwL | hwH
    · have hbar : dzbar H w = 0 :=
        (cauchyRiemann_iff.1 (hHd.differentiableAt (isOpen_lowerHalf.mem_nhds hwL))).2
      simp only [harmonicBiparameterCoefficient, ite_eq_left hwL, zero_mul,
        complexDilatation, hbar, zero_div]
    · rw [harmonicBiparameterCoefficient, ite_eq_right (not_lt.mpr hwH.le), hHμ w hwH]
      dsimp only [φ, harmonicPlane]
      rw [Complex.conj_conj]
      ring
  dsimp only
  rw [heq]
  exact ⟨hHd, hHa, normalized_pair_rational_formula hd hv₁ hv₂
    (fun w hw => (hODE w hw).2.2) hL hU⟩

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
