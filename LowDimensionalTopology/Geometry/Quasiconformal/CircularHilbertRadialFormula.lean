module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertAngularPairing
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPolarPairing
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.GreenPolar

/-!
# The radial truncations as genuine paired polar integrals

Polar change of variables is applied only after proving absolute
integrability. Opposite angular halves then combine into the paired rays,
with the original positive normalization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem integrableOn_fullPolar {f : ℂ → ℂ}
    (hm : Measurable f) (hi : Integrable f volume) :
    IntegrableOn (fun v : ℝ × ℝ => (v.1 : ℂ) * f (Complex.polarCoord.symm v))
      _root_.polarCoord.target (volume : Measure (ℝ × ℝ)) := by
  have hc : Continuous (fun v : ℝ × ℝ => Complex.polarCoord.symm v) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  refine ⟨((Complex.continuous_ofReal.comp continuous_fst).measurable.mul
    (hm.comp hc.measurable)).aestronglyMeasurable.restrict, ?_⟩
  have heq :
      (∫⁻ v in _root_.polarCoord.target,
        ‖(v.1 : ℂ) * f (Complex.polarCoord.symm v)‖ₑ) = ∫⁻ z : ℂ, ‖f z‖ₑ := by
    rw [← Complex.lintegral_comp_polarCoord_symm (fun z => ‖f z‖ₑ)]
    apply setLIntegral_congr_fun _root_.polarCoord.open_target.measurableSet
    intro v hv
    change ‖(v.1 : ℂ) * f (Complex.polarCoord.symm v)‖ₑ =
      ENNReal.ofReal v.1 * ‖f (Complex.polarCoord.symm v)‖ₑ
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm (v.1 : ℂ), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hv.1]
  rw [hasFiniteIntegral_iff_enorm, heq]
  exact hi.hasFiniteIntegral

private theorem integral_fullPolar {f : ℂ → ℂ}
    (hm : Measurable f) (hi : Integrable f volume) :
    (∫ z : ℂ, f z) =
      ∫ r in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi,
        (r : ℂ) * f (circleMap 0 r θ) := by
  let F : ℝ × ℝ → ℂ := fun v => (v.1 : ℂ) * f (Complex.polarCoord.symm v)
  have hint : IntegrableOn F
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    convert! integrableOn_fullPolar hm hi using 1
  have hval : (∫ v in _root_.polarCoord.target, F v) = ∫ z : ℂ, f z := by
    simpa only [F, Complex.real_smul] using Complex.integral_comp_polarCoord_symm f
  rw [← hval]
  change (∫ v in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, F v) = _
  rw [Measure.volume_eq_prod ℝ ℝ, setIntegral_prod F hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  change (∫ θ in Ioo (-Real.pi) Real.pi, F (r, θ)) =
    ∫ θ in (0 : ℝ)..2 * Real.pi, (r : ℂ) * f (circleMap 0 r θ)
  have heq : (fun θ : ℝ => F (r, θ)) =
      fun θ : ℝ => (r : ℂ) * f (circleMap 0 r θ) := by
    funext θ
    dsimp [F]
    rw [show Complex.polarCoord.symm (r, θ) = circleMap 0 r θ by
      simpa only [add_zero] using LiZhongQC.polarCoord_symm_add_eq_circleMap 0 r θ]
  rw [heq]
  have hper : Function.Periodic (fun θ : ℝ => (r : ℂ) * f (circleMap 0 r θ))
      (2 * Real.pi) := by
    intro θ
    change (r : ℂ) * f (circleMap 0 r (θ + 2 * Real.pi)) =
      (r : ℂ) * f (circleMap 0 r θ)
    rw [periodic_circleMap 0 r θ]
  rw [← LiZhongQC.intervalIntegral_shift_period hper,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo]

/-- Every positive radial truncation is the exact paired polar integral. -/
theorem circularHilbertTruncation_eq_paired_integral {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (ζ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    circularHilbertTruncation φ ζ ε = (1 / (2 * (Real.pi : ℂ))) *
      ∫ θ in (0 : ℝ)..Real.pi, ∫ r in Ioi ε, circularPairedKernel φ ζ (θ, r) := by
  let g : ℂ → ℂ := fun z => φ (z + ζ) / (z * (‖z‖ : ℂ))
  let s : Set ℂ := {z | ε < ‖z‖}
  let f : ℂ → ℂ := s.indicator g
  have hs : MeasurableSet s := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hgm : Measurable g :=
    (hφ.continuous.measurable.comp (measurable_id.add_const ζ)).div
      (measurable_id.mul (Complex.continuous_ofReal.measurable.comp measurable_norm))
  have hfm : Measurable f := hgm.indicator hs
  have hfi : Integrable f volume :=
    (integrable_indicator_iff hs).2 (integrableOn_circularHilbertRadialKernel
      hφ.continuous hc ζ hε)
  have hinner (r : ℝ) (hr : 0 < r) :
      (∫ θ in (0 : ℝ)..2 * Real.pi, (r : ℂ) * f (circleMap 0 r θ)) =
        if ε < r then
          ∫ θ in (0 : ℝ)..Real.pi, circularPairedKernel φ ζ (θ, r)
        else 0 := by
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hn (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
      rw [norm_circleMap_zero, abs_of_pos hr]
    have hv (θ : ℝ) : circleMap 0 r θ =
        (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by simp [circleMap]
    by_cases her : ε < r
    · rw [ite_eq_left her]
      have heq (θ : ℝ) : (r : ℂ) * f (circleMap 0 r θ) =
          (r : ℂ)⁻¹ *
            (φ ((r : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ) *
              Complex.exp (-((θ : ℂ) * I))) := by
        have hmem : circleMap 0 r θ ∈ s := by
          change ε < ‖circleMap 0 r θ‖
          rwa [hn]
        dsimp [f]
        rw [Set.indicator_of_mem hmem]
        dsimp [g]
        rw [hn, hv, Complex.exp_neg]
        field_simp [hrC, Complex.exp_ne_zero]
      simp_rw [heq]
      rw [intervalIntegral.integral_const_mul,
        circular_angular_integral_eq_paired hφ.continuous ζ r,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [circularPairedKernel]
      ring
    · rw [ite_eq_right her]
      have heq : (fun θ : ℝ => (r : ℂ) * f (circleMap 0 r θ)) = 0 := by
        funext θ
        have hnot : circleMap 0 r θ ∉ s := by
          change ¬ ε < ‖circleMap 0 r θ‖
          rwa [hn]
        simp [f, Set.indicator_of_notMem hnot]
      rw [heq]
      change (∫ _θ in (0 : ℝ)..2 * Real.pi, (0 : ℂ)) = 0
      exact intervalIntegral.integral_zero
  have hradial :
      (∫ r in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi,
        (r : ℂ) * f (circleMap 0 r θ)) =
          ∫ r in Ioi ε, ∫ θ in (0 : ℝ)..Real.pi,
            circularPairedKernel φ ζ (θ, r) := by
    have heq :
        (fun r : ℝ => if ε < r then
          ∫ θ in (0 : ℝ)..Real.pi, circularPairedKernel φ ζ (θ, r) else 0) =
        (Ioi ε).indicator (fun r : ℝ =>
          ∫ θ in (0 : ℝ)..Real.pi, circularPairedKernel φ ζ (θ, r)) := rfl
    calc
      _ = ∫ r in Ioi (0 : ℝ), if ε < r then
          ∫ θ in (0 : ℝ)..Real.pi, circularPairedKernel φ ζ (θ, r) else 0 := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact hinner r hr
      _ = _ := by
        rw [heq, setIntegral_indicator measurableSet_Ioi,
          inter_eq_self_of_subset_right (Ioi_subset_Ioi hε.le)]
  have hprod := (integrableOn_circularPairedKernel hφ hc ζ).mono_set
    (Set.prod_mono (Subset.refl _) (Ioi_subset_Ioi hε.le))
  have hprod' : Integrable
      (Function.uncurry (fun θ r : ℝ => circularPairedKernel φ ζ (θ, r)))
      ((volume.restrict (Ioc (0 : ℝ) Real.pi)).prod (volume.restrict (Ioi ε))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hprod0 := hprod
    unfold IntegrableOn at hprod0
    have hfun :
        Function.uncurry (fun θ r : ℝ => circularPairedKernel φ ζ (θ, r)) =
          circularPairedKernel φ ζ := by
      funext v
      rfl
    rw [hfun]
    exact hprod0
  have hswap :
      (∫ r in Ioi ε, ∫ θ in (0 : ℝ)..Real.pi, circularPairedKernel φ ζ (θ, r)) =
        ∫ θ in (0 : ℝ)..Real.pi, ∫ r in Ioi ε, circularPairedKernel φ ζ (θ, r) := by
    simp only [intervalIntegral.integral_of_le Real.pi_pos.le]
    exact (integral_integral_swap hprod').symm
  rw [circularHilbertTruncation]
  change (1 / (2 * (Real.pi : ℂ))) * (∫ z in s, g z) = _
  rw [← integral_indicator hs, integral_fullPolar hfm hfi, hradial, hswap]

end LowDimensionalTopology.Geometry.Quasiconformal
