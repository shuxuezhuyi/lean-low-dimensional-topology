module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertSlices
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Rotation and the finite angular-average estimate

The angular measure is the literal restriction of real Lebesgue measure
to the source interval, whose mass is pi. No different planar singular
operator is used in the estimate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

private theorem directionalHilbertTransform_rotation (φ : ℂ → ℂ) (θ : ℝ) (ζ : ℂ) :
    directionalHilbertTransform φ θ ζ =
      directionalHilbertTransform (φ ∘ rotation (Circle.exp θ)) 0
        ((rotation (Circle.exp θ)).symm ζ) := by
  simp only [directionalHilbertTransform, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one]
  congr 1
  funext x
  simp only [Function.comp_apply, map_add,
    (rotation (Circle.exp θ)).apply_symm_apply, rotation_apply, Circle.coe_exp]
  rw [mul_comm (Complex.exp ((θ : ℂ) * I)) (x : ℂ)]

/-- Every actual direction has the same planar Riesz bound, by a
measure-preserving rotation of the horizontal slice estimate. -/
theorem directionalHilbertTransform_bound {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) (θ : ℝ) :
    MemLp (directionalHilbertTransform φ θ) (ENNReal.ofReal p)
        (volume : Measure ℂ) ∧
      eLpNorm (directionalHilbertTransform φ θ) (ENNReal.ofReal p)
          (volume : Measure ℂ) ≤
        ENNReal.ofReal (A p) * eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ) := by
  let r := rotation (Circle.exp θ)
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ ∘ r) :=
    hφ.comp r.toContinuousLinearEquiv.contDiff
  have hψc : HasCompactSupport (φ ∘ r) :=
    hc.comp_isClosedEmbedding r.toHomeomorph.isClosedEmbedding
  obtain ⟨hm, hb⟩ := directionalHilbertTransform_zero_bound hA hp hψ hψc
  have heq : directionalHilbertTransform φ θ =
      directionalHilbertTransform (φ ∘ r) 0 ∘ r.symm := by
    funext ζ
    exact directionalHilbertTransform_rotation φ θ ζ
  rw [heq]
  refine ⟨hm.comp_measurePreserving r.symm.measurePreserving, ?_⟩
  rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable r.symm.measurePreserving]
  simpa only [eLpNorm_comp_measurePreserving hφ.continuous.aestronglyMeasurable
    r.measurePreserving] using hb

private theorem angularAverage_lintegral_rpow_bound {p : ℝ} (hp : 2 ≤ p)
    {f : ℝ → ℂ} (hf : StronglyMeasurable f) :
    ‖(1 / 2 : ℂ) * ∫ θ in (0 : ℝ)..Real.pi, f θ‖ₑ ^ p ≤
      (ENNReal.ofReal (1 / 2 : ℝ)) ^ p * (ENNReal.ofReal Real.pi) ^ (p - 1) *
        ∫⁻ θ in Ioc (0 : ℝ) Real.pi, ‖f θ‖ₑ ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hmass : (volume : Measure ℝ).restrict (Ioc 0 Real.pi) univ =
      ENNReal.ofReal Real.pi := by simp
  have hscalar : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [← ofReal_norm]
    norm_num
  have hi : ‖∫ θ in Ioc (0 : ℝ) Real.pi, f θ‖ₑ ≤
      eLpNorm' f p ((volume : Measure ℝ).restrict (Ioc 0 Real.pi)) *
        (ENNReal.ofReal Real.pi) ^ (1 - 1 / p) := by
    have he := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
      (f := f) (μ := (volume : Measure ℝ).restrict (Ioc 0 Real.pi))
      zero_lt_one (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)
      hf.aestronglyMeasurable
    simp only [eLpNorm', one_div_one, ENNReal.rpow_one, hmass] at he
    exact (enorm_integral_le_lintegral_enorm _).trans he
  have hi' := ENNReal.rpow_le_rpow
    (mul_le_mul' (le_rfl : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal (1 / 2 : ℝ))
      hi) hp0.le
  have hexp : (1 - 1 / p) * p = p - 1 := by
    rw [sub_mul, one_mul, div_mul_cancel₀ 1 hp0.ne']
  have hmasspower : ((ENNReal.ofReal Real.pi) ^ (1 - 1 / p)) ^ p =
      (ENNReal.ofReal Real.pi) ^ (p - 1) := by
    rw [← ENNReal.rpow_mul, hexp]
  have hfpower : (eLpNorm' f p ((volume : Measure ℝ).restrict (Ioc 0 Real.pi))) ^ p =
      ∫⁻ θ in Ioc (0 : ℝ) Real.pi, ‖f θ‖ₑ ^ p :=
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f)
      (μ := (volume : Measure ℝ).restrict (Ioc 0 Real.pi)) hp0).symm
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at hi'
  rw [hmasspower, hfpower] at hi'
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le, enorm_mul,
    hscalar, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, mul_assoc, mul_comm, mul_left_comm]
    using hi'

private theorem directionalHilbert_lintegral_rpow_bound {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) (θ : ℝ) :
    ∫⁻ ζ : ℂ, ‖directionalHilbertTransform φ θ ζ‖ₑ ^ p ≤
      (ENNReal.ofReal (A p)) ^ p * ∫⁻ ζ : ℂ, ‖φ ζ‖ₑ ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  obtain ⟨hm, hb⟩ := directionalHilbertTransform_bound hA hp hφ hc θ
  have hφm : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  have hpow := ENNReal.rpow_le_rpow hb hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hφm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0] at hpow
  exact hpow

private theorem jointDirectional_lintegral_rpow_bound {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ∫⁻ ζ : ℂ, ∫⁻ θ in Ioc (0 : ℝ) Real.pi,
      ‖directionalHilbertTransform φ θ ζ‖ₑ ^ p ≤
        ENNReal.ofReal Real.pi * (ENNReal.ofReal (A p)) ^ p *
          ∫⁻ ζ : ℂ, ‖φ ζ‖ₑ ^ p := by
  have hd := stronglyMeasurable_directionalHilbertTransform hA hp hφ hc
  have hswapComp : Measurable
      ((fun w : ℝ × ℂ => ‖directionalHilbertTransform φ w.1 w.2‖ₑ ^ p) ∘
        (Prod.swap : ℂ × ℝ → ℝ × ℂ)) :=
    (hd.enorm.pow_const p).comp measurable_swap
  have hswap_eq :
      ((fun w : ℝ × ℂ => ‖directionalHilbertTransform φ w.1 w.2‖ₑ ^ p) ∘
        (Prod.swap : ℂ × ℝ → ℝ × ℂ)) =
      (fun w : ℂ × ℝ => ‖directionalHilbertTransform φ w.2 w.1‖ₑ ^ p) := by
    funext w
    rcases w with ⟨ζ, θ⟩
    rfl
  have hswap : Measurable (fun w : ℂ × ℝ =>
      ‖directionalHilbertTransform φ w.2 w.1‖ₑ ^ p) := by
    rw [← hswap_eq]
    exact hswapComp
  rw [lintegral_lintegral_swap (μ := (volume : Measure ℂ))
    (ν := (volume : Measure ℝ).restrict (Ioc 0 Real.pi))
    (f := fun ζ : ℂ => fun θ : ℝ => ‖directionalHilbertTransform φ θ ζ‖ₑ ^ p)
    hswap.aemeasurable]
  calc
    _ ≤ ∫⁻ θ in Ioc (0 : ℝ) Real.pi,
        (ENNReal.ofReal (A p)) ^ p * ∫⁻ ζ : ℂ, ‖φ ζ‖ₑ ^ p :=
      lintegral_mono fun θ => directionalHilbert_lintegral_rpow_bound hA hp hφ hc θ
    _ = _ := by simp [mul_assoc, mul_comm]

private theorem angularWeight_enorm (θ : ℝ) :
    ‖Complex.exp (-((θ : ℂ) * I))‖ₑ = 1 := by
  simpa only [Circle.coe_exp, Complex.ofReal_neg, neg_mul] using
    Circle.enorm_coe (Circle.exp (-θ))

/-- The actual directional angular integrand is integrable for almost every
planar point. This follows from the slice bounds and finite angular measure. -/
theorem ae_integrable_circularHilbertIntegrand {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ∀ᵐ ζ : ℂ ∂volume,
      IntegrableOn (fun θ : ℝ => directionalHilbertTransform φ θ ζ *
        Complex.exp (-((θ : ℂ) * I))) (Ioc 0 Real.pi) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)
  have hφm : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  have hφfin : (∫⁻ ζ : ℂ, ‖φ ζ‖ₑ ^ p) < (∞ : ℝ≥0∞) := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hpp0 ENNReal.ofReal_ne_top hφm
  have hd := stronglyMeasurable_directionalHilbertTransform hA hp hφ hc
  have hfin : (∫⁻ ζ : ℂ, ∫⁻ θ in Ioc (0 : ℝ) Real.pi,
      ‖directionalHilbertTransform φ θ ζ‖ₑ ^ p) < (∞ : ℝ≥0∞) :=
    (jointDirectional_lintegral_rpow_bound hA hp hφ hc).trans_lt
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)) hφfin)
  have hae := ae_lt_top ((hd.enorm.pow_const p).lintegral_prod_left'
    (μ := (volume : Measure ℝ).restrict (Ioc 0 Real.pi))) hfin.ne
  filter_upwards [hae] with ζ hζ
  have hpair : Measurable (fun θ : ℝ => (θ, ζ)) :=
    measurable_id.prodMk measurable_const
  have hComp : StronglyMeasurable
      ((fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) ∘
        (fun θ : ℝ => (θ, ζ))) := hd.comp_measurable hpair
  have hcomp_eq :
      ((fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) ∘
        (fun θ : ℝ => (θ, ζ))) =
      (fun θ : ℝ => directionalHilbertTransform φ θ ζ) := by
    funext θ
    rfl
  have hθ : StronglyMeasurable (fun θ : ℝ => directionalHilbertTransform φ θ ζ) := by
    rw [← hcomp_eq]
    exact hComp
  have hmθ : MemLp (fun θ => directionalHilbertTransform φ θ ζ)
      (ENNReal.ofReal p) ((volume : Measure ℝ).restrict (Ioc 0 Real.pi)) := by
    rw [memLp_iff]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpp0 ENNReal.ofReal_ne_top
      hθ.aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofReal hp0.le] using hζ
  have hi := memLp_one_iff_integrable.mp (hmθ.mono_exponent hp1)
  apply hi.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with θ
    simp [Complex.norm_exp]

/-- The literal circular Hilbert transform of every smooth compact planar
test belongs to the same Lp space and has the source bound pi times A_p / 2. -/
theorem circularHilbertTransform_test_bound {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    MemLp (circularHilbertTransform φ) (ENNReal.ofReal p) (volume : Measure ℂ) ∧
      (eLpNorm (circularHilbertTransform φ) (ENNReal.ofReal p)
        (volume : Measure ℂ)).toReal ≤
          (Real.pi / 2 * A p) *
            (eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ)).toReal := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hAnon : 0 ≤ A p := RealHilbertEstimate.nonneg hA hp
  have hCnon : 0 ≤ Real.pi / 2 * A p := mul_nonneg (by positivity) hAnon
  have hSm := stronglyMeasurable_circularHilbertTransform hA hp hφ hc
  have hφm : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  let c : ℝ≥0∞ := (ENNReal.ofReal (1 / 2 : ℝ)) ^ p *
    (ENNReal.ofReal Real.pi) ^ (p - 1)
  have hcfin : c ≠ (∞ : ℝ≥0∞) := by
    dsimp only [c]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (x := ENNReal.ofReal (1 / 2 : ℝ))
        (y := p) hp0.le ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (x := ENNReal.ofReal Real.pi)
        (y := p - 1) (by linarith : 0 ≤ p - 1) ENNReal.ofReal_ne_top)
  have hd := stronglyMeasurable_directionalHilbertTransform hA hp hφ hc
  have hmasspow : (ENNReal.ofReal Real.pi) ^ (p - 1) * ENNReal.ofReal Real.pi =
      (ENNReal.ofReal Real.pi) ^ p := by
    calc
      _ = (ENNReal.ofReal Real.pi) ^ (p - 1) *
          (ENNReal.ofReal Real.pi) ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = (ENNReal.ofReal Real.pi) ^ ((p - 1) + 1) :=
        (ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'
          ENNReal.ofReal_ne_top).symm
      _ = _ := by congr 1; ring
  have hscalar : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal Real.pi *
      ENNReal.ofReal (A p) = ENNReal.ofReal (Real.pi / 2 * A p) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 2 * Real.pi)]
    congr 1
    ring
  have hpow : (eLpNorm (circularHilbertTransform φ) (ENNReal.ofReal p)
      (volume : Measure ℂ)) ^ p ≤
      (ENNReal.ofReal (Real.pi / 2 * A p) *
        eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ)) ^ p := by
    rw [eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hSm.aestronglyMeasurable,
      eLpNorm_eq_eLpNorm' hpp0 ENNReal.ofReal_ne_top hφm.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0]
    calc
      _ ≤ ∫⁻ ζ : ℂ, c * ∫⁻ θ in Ioc (0 : ℝ) Real.pi,
          ‖directionalHilbertTransform φ θ ζ‖ₑ ^ p := by
        apply lintegral_mono
        intro ζ
        have hf : StronglyMeasurable (fun θ : ℝ => directionalHilbertTransform φ θ ζ *
            Complex.exp (-((θ : ℂ) * I))) := by
          have hpair : Measurable (fun θ : ℝ => (θ, ζ)) :=
            measurable_id.prodMk measurable_const
          have hComp : StronglyMeasurable
              ((fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) ∘
                (fun θ : ℝ => (θ, ζ))) := hd.comp_measurable hpair
          have hcomp_eq :
              ((fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) ∘
                (fun θ : ℝ => (θ, ζ))) =
              (fun θ : ℝ => directionalHilbertTransform φ θ ζ) := by
            funext θ
            rfl
          have hdir : StronglyMeasurable (fun θ : ℝ => directionalHilbertTransform φ θ ζ) := by
            rw [← hcomp_eq]
            exact hComp
          have hweight : StronglyMeasurable
              (fun θ : ℝ => Complex.exp (-((θ : ℂ) * I))) := by
            apply Continuous.stronglyMeasurable
            fun_prop
          simpa only [Pi.mul_def] using
            hdir.mul hweight
        simpa only [circularHilbertTransform, enorm_mul, angularWeight_enorm, mul_one]
          using angularAverage_lintegral_rpow_bound hp hf
      _ = c * ∫⁻ ζ : ℂ, ∫⁻ θ in Ioc (0 : ℝ) Real.pi,
          ‖directionalHilbertTransform φ θ ζ‖ₑ ^ p := lintegral_const_mul' c _ hcfin
      _ ≤ c * (ENNReal.ofReal Real.pi * (ENNReal.ofReal (A p)) ^ p *
          ∫⁻ ζ : ℂ, ‖φ ζ‖ₑ ^ p) :=
        mul_le_mul' (le_rfl : c ≤ c) (jointDirectional_lintegral_rpow_bound hA hp hφ hc)
      _ = (ENNReal.ofReal (1 / 2 : ℝ)) ^ p * (ENNReal.ofReal Real.pi) ^ p *
          (ENNReal.ofReal (A p)) ^ p * (eLpNorm' φ p (volume : Measure ℂ)) ^ p := by
        rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0]
        dsimp only [c]
        calc
          _ = (ENNReal.ofReal (1 / 2 : ℝ)) ^ p *
              ((ENNReal.ofReal Real.pi) ^ (p - 1) * ENNReal.ofReal Real.pi) *
              (ENNReal.ofReal (A p)) ^ p * (eLpNorm' φ p volume) ^ p := by ring
          _ = _ := by rw [hmasspow]
      _ = _ := by
        rw [← hscalar]
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, mul_assoc]
  have hb := (ENNReal.rpow_le_rpow_iff hp0).mp hpow
  have hm : MemLp (circularHilbertTransform φ) (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφm.eLpNorm_lt_top)
  refine ⟨hm, ?_⟩
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφm.eLpNorm_ne_top) hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCnon] using hreal

end LowDimensionalTopology.Geometry.Quasiconformal
