module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRegularity
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The real Hilbert estimate on planar horizontal slices

The planar estimate is obtained by applying the specified real-line bound
on every horizontal slice and then using Tonelli's theorem. The functions
and measure remain the original complex plane and planar Lebesgue measure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

private theorem realHilbertTruncation_translate (ψ : ℝ → ℂ) (ξ ε : ℝ) :
    realHilbertTruncation (fun x => ψ (x + ξ)) 0 ε =
      realHilbertTruncation ψ ξ ε := by
  have hs : MeasurableSet {x : ℝ | ε < |x - ξ|} := by measurability
  have hs0 : MeasurableSet {x : ℝ | ε < |x|} := by measurability
  simp only [realHilbertTruncation, sub_zero]
  congr 1
  rw [← integral_indicator hs0, ← integral_indicator hs]
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, add_sub_cancel_right] using
    integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => {x : ℝ | ε < |x - ξ|}.indicator
        (fun x => ψ x / ((x - ξ : ℝ) : ℂ)) x) ξ

private theorem realHilbertTransform_translate (ψ : ℝ → ℂ) (ξ : ℝ) :
    realHilbertTransform (fun x => ψ (x + ξ)) 0 = realHilbertTransform ψ ξ := by
  unfold realHilbertTransform
  congr 1
  funext ε
  exact realHilbertTruncation_translate ψ ξ ε

private theorem directional_zero_eq_slice (φ : ℂ → ℂ) (z : ℂ) :
    directionalHilbertTransform φ 0 z =
      realHilbertTransform (fun x : ℝ => φ ((x : ℂ) + (z.im : ℂ) * I)) z.re := by
  simp only [directionalHilbertTransform, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one]
  have hfun : (fun x : ℝ => φ ((x : ℂ) + z)) =
      (fun x : ℝ => φ (((x + z.re : ℝ) : ℂ) + (z.im : ℂ) * I)) := by
    funext x
    rw [Complex.ofReal_add, add_assoc, Complex.re_add_im]
  rw [hfun]
  exact realHilbertTransform_translate
    (fun x : ℝ => φ ((x : ℂ) + (z.im : ℂ) * I)) z.re

private theorem planar_lintegral_slices {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z : ℂ, f z = ∫⁻ y : ℝ, ∫⁻ x : ℝ, f ((x : ℂ) + (y : ℂ) * I) := by
  rw [← Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp hf]
  change (∫⁻ a : ℝ × ℝ, f (Complex.measurableEquivRealProd.symm a)
    ∂(volume : Measure ℝ).prod (volume : Measure ℝ)) = _
  rw [lintegral_prod_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun a : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm a))
    (hf.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro x
  congr 1
  exact Complex.ext (by simp) (by simp)

private theorem realHilbert_lintegral_rpow_bound {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    ∫⁻ x, ‖realHilbertTransform ψ x‖ₑ ^ p ≤
      (ENNReal.ofReal (A p)) ^ p * ∫⁻ x, ‖ψ x‖ₑ ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hm : MemLp ψ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    hψ.continuous.memLp_of_hasCompactSupport hc
  obtain ⟨-, hHm, hbound⟩ := hA.2.2 p hp ψ hψ hc
  have hbound' : eLpNorm (realHilbertTransform ψ) (ENNReal.ofReal p)
      (volume : Measure ℝ) ≤ ENNReal.ofReal (A p) *
        eLpNorm ψ (ENNReal.ofReal p) (volume : Measure ℝ) := by
    have hb := ENNReal.ofReal_le_ofReal hbound
    rwa [ENNReal.ofReal_mul (RealHilbertEstimate.nonneg hA hp),
      ENNReal.ofReal_toReal hHm.eLpNorm_ne_top,
      ENNReal.ofReal_toReal hm.eLpNorm_ne_top] at hb
  have hpow := ENNReal.rpow_le_rpow hbound' hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hHm.aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0] at hpow
  exact hpow

/-- The horizontal extension of the real Hilbert transform satisfies its
same literal Riesz bound on the whole planar Lp space of smooth tests. -/
theorem directionalHilbertTransform_zero_bound {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    MemLp (directionalHilbertTransform φ 0) (ENNReal.ofReal p)
        (volume : Measure ℂ) ∧
      eLpNorm (directionalHilbertTransform φ 0) (ENNReal.ofReal p)
          (volume : Measure ℂ) ≤
        ENNReal.ofReal (A p) * eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  let D : ℂ → ℂ := directionalHilbertTransform φ 0
  have hpair : Measurable (fun ζ : ℂ => ((0 : ℝ), ζ)) :=
    measurable_const.prodMk measurable_id
  have hJoint : StronglyMeasurable
      (fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) :=
    stronglyMeasurable_directionalHilbertTransform hA hp hφ hc
  have hComp : StronglyMeasurable
      ((fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) ∘
        (fun ζ : ℂ => ((0 : ℝ), ζ))) :=
    hJoint.comp_measurable hpair
  have hcomp_eq :
      ((fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) ∘
        (fun ζ : ℂ => ((0 : ℝ), ζ))) = D := by
    funext ζ
    rfl
  have hD : StronglyMeasurable D := by
    rw [← hcomp_eq]
    exact hComp
  have hm : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  have hDpower : (eLpNorm D (ENNReal.ofReal p) (volume : Measure ℂ)) ^ p =
      ∫⁻ ζ : ℂ, ‖D ζ‖ₑ ^ p := by
    rw [eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hD.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := D)
      (μ := (volume : Measure ℂ)) hp0).symm
  have hφpower : (eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ)) ^ p =
      ∫⁻ ζ : ℂ, ‖φ ζ‖ₑ ^ p := by
    rw [eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := φ)
      (μ := (volume : Measure ℂ)) hp0).symm
  have hslice (x y : ℝ) : D ((x : ℂ) + (y : ℂ) * I) =
      realHilbertTransform (fun t : ℝ => φ ((t : ℂ) + (y : ℂ) * I)) x := by
    dsimp only [D]
    simpa using directional_zero_eq_slice φ ((x : ℂ) + (y : ℂ) * I)
  have hIntegral : (∫⁻ ζ : ℂ, ‖D ζ‖ₑ ^ p) ≤
      (ENNReal.ofReal (A p)) ^ p * ∫⁻ ζ : ℂ, ‖φ ζ‖ₑ ^ p := by
    rw [planar_lintegral_slices (hD.enorm.pow_const p),
      planar_lintegral_slices (hφ.continuous.measurable.enorm.pow_const p)]
    simp_rw [hslice]
    calc
      _ ≤ ∫⁻ y : ℝ, (ENNReal.ofReal (A p)) ^ p *
          ∫⁻ x : ℝ, ‖φ ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ p := by
        apply lintegral_mono
        intro y
        have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : ℝ => φ ((x : ℂ) + (y : ℂ) * I)) := by
          simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] using
            contDiff_affineLine hφ 0 ((y : ℂ) * I)
        have hψc : HasCompactSupport (fun x : ℝ => φ ((x : ℂ) + (y : ℂ) * I)) := by
          simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] using
            hasCompactSupport_affineLine hc 0 ((y : ℂ) * I)
        exact realHilbert_lintegral_rpow_bound hA hp hψ hψc
      _ = _ := lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
  have hpow : (eLpNorm D (ENNReal.ofReal p) (volume : Measure ℂ)) ^ p ≤
      (ENNReal.ofReal (A p) * eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ)) ^ p := by
    rw [hDpower, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hφpower]
    exact hIntegral
  have hbound := (ENNReal.rpow_le_rpow_iff hp0).mp hpow
  refine ⟨?_, hbound⟩
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm.eLpNorm_lt_top)

end LowDimensionalTopology.Geometry.Quasiconformal
