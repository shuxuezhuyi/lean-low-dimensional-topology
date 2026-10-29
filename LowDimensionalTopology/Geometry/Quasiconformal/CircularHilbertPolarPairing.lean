module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPairedBounds
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRegularity
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Absolutely integrable paired polar rays

The opposite-ray quotient has a uniform cancellation bound and finite
radial support, so its angular/radial product integral is genuine. Its
iterated integral is the original directional circular Hilbert transform.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff NNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The actual opposite-ray quotient with its angular weight. Its value at
radius zero is immaterial for the positive-radius integral. -/
def circularPairedKernel (φ : ℂ → ℂ) (ζ : ℂ) (v : ℝ × ℝ) : ℂ :=
  (v.2 : ℂ)⁻¹ *
    (φ ((v.2 : ℂ) * Complex.exp ((v.1 : ℂ) * I) + ζ) -
      φ (((-v.2 : ℝ) : ℂ) * Complex.exp ((v.1 : ℂ) * I) + ζ)) *
        Complex.exp (-((v.1 : ℂ) * I))

theorem circularPairedKernel_eq_paired (φ : ℂ → ℂ) (ζ : ℂ) (θ : ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    circularPairedKernel φ ζ (θ, r) =
      realHilbertPairedKernel
        (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) 0 r *
          Complex.exp (-((θ : ℂ) * I)) := by
  rw [realHilbertPairedKernel_of_ne _ 0 hr]
  simp [circularPairedKernel, Complex.real_smul]

theorem measurable_circularPairedKernel {φ : ℂ → ℂ}
    (hφ : Continuous φ) (ζ : ℂ) : Measurable (circularPairedKernel φ ζ) := by
  unfold circularPairedKernel
  fun_prop

/-- The cancellation bound includes every direction and every radius. -/
theorem norm_circularPairedKernel_le {φ : ℂ → ℂ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (ζ : ℂ) (v : ℝ × ℝ) :
    ‖circularPairedKernel φ ζ v‖ ≤ 2 * L := by
  rcases v with ⟨θ, r⟩
  by_cases hr : r = 0
  · simp [hr, circularPairedKernel]
  · rw [circularPairedKernel_eq_paired _ _ _ hr, norm_mul]
    have hu : ‖Complex.exp (-((θ : ℂ) * I))‖ = 1 := by simp [Complex.norm_exp]
    rw [hu, mul_one]
    exact norm_realHilbertPairedKernel_affineLine_le hL θ ζ hr

/-- Joint absolute integrability follows from the actual uniform radial
support and cancellation bound, before any order of integration is exchanged. -/
theorem integrableOn_circularPairedKernel {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (ζ : ℂ) :
    IntegrableOn (circularPairedKernel φ ζ)
      (Ioc (0 : ℝ) Real.pi ×ˢ Ioi (0 : ℝ)) (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by simp)
  obtain ⟨R, hR, hsupport⟩ := exists_uniform_affineLine_paired_support hc ζ
  let s : Set (ℝ × ℝ) := Ioc (0 : ℝ) Real.pi ×ˢ Ioi (0 : ℝ)
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) Real.pi ×ˢ Icc (0 : ℝ) R
  have hs : MeasurableSet s := measurableSet_Ioc.prod measurableSet_Ioi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hm : AEStronglyMeasurable (circularPairedKernel φ ζ)
      (volume : Measure (ℝ × ℝ)) :=
    (measurable_circularPairedKernel hφ.continuous ζ).aestronglyMeasurable
  have hintK : IntegrableOn (circularPairedKernel φ ζ) K := by
    exact (integrableOn_const (C := (2 : ℝ) * L) hK.measure_ne_top).mono'
      hm.restrict (Eventually.of_forall fun v => norm_circularPairedKernel_le hL ζ v)
  have heq : s.indicator (circularPairedKernel φ ζ) =
      (s ∩ K).indicator (circularPairedKernel φ ζ) := by
    funext v
    by_cases hvs : v ∈ s
    · by_cases hvK : v ∈ K
      · simp [Set.indicator_of_mem, hvs, hvK]
      · have hvθ : v.1 ∈ Icc (0 : ℝ) Real.pi := ⟨hvs.1.1.le, hvs.1.2⟩
        have hvr : 0 < v.2 := hvs.2
        have hgt : R < v.2 := lt_of_not_ge fun hle => hvK ⟨hvθ, ⟨hvr.le, hle⟩⟩
        have hzero : circularPairedKernel φ ζ v = 0 := by
          rw [show v = (v.1, v.2) from rfl,
            circularPairedKernel_eq_paired _ _ _ (ne_of_gt hvr),
            hsupport v.1 v.2 (by simpa only [abs_of_pos hvr] using hgt.le), zero_mul]
        simp [hvs, hvK, hzero]
    · simp [hvs]
  change IntegrableOn (circularPairedKernel φ ζ) s
  rw [← integrable_indicator_iff hs, heq]
  exact (integrable_indicator_iff (hs.inter hK.measurableSet)).2
    (hintK.mono_set inter_subset_right)

/-- The literal circular average is the paired positive-ray integral, with
its original factor `1 / (2π)`. -/
theorem circularHilbertTransform_eq_paired_integral {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (ζ : ℂ) :
    circularHilbertTransform φ ζ = (1 / (2 * (Real.pi : ℂ))) *
      ∫ θ in (0 : ℝ)..Real.pi, ∫ r in Ioi (0 : ℝ), circularPairedKernel φ ζ (θ, r) := by
  have hθ (θ : ℝ) : directionalHilbertTransform φ θ ζ =
      (1 / (Real.pi : ℂ)) * ∫ r in Ioi (0 : ℝ),
        realHilbertPairedKernel
          (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) 0 r := by
    exact (realHilbert_principalValue_and_eq_paired
      ((contDiff_affineLine hφ θ ζ).of_le (by simp))
      (hasCompactSupport_affineLine hc θ ζ) 0).2
  have hinner (θ : ℝ) :
      (∫ r in Ioi (0 : ℝ), circularPairedKernel φ ζ (θ, r)) =
        (∫ r in Ioi (0 : ℝ), realHilbertPairedKernel
          (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) 0 r) *
            Complex.exp (-((θ : ℂ) * I)) := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact circularPairedKernel_eq_paired _ _ _ (ne_of_gt hr)
  have heq :
      (fun θ : ℝ => directionalHilbertTransform φ θ ζ * Complex.exp (-((θ : ℂ) * I))) =
        fun θ : ℝ => (1 / (Real.pi : ℂ)) *
          ∫ r in Ioi (0 : ℝ), circularPairedKernel φ ζ (θ, r) := by
    funext θ
    rw [hθ, hinner]
    ring
  rw [circularHilbertTransform, heq, intervalIntegral.integral_const_mul]
  have hcoeff : (1 / 2 : ℂ) * (1 / (Real.pi : ℂ)) = 1 / (2 * (Real.pi : ℂ)) := by
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [← mul_assoc, hcoeff]

end LowDimensionalTopology.Geometry.Quasiconformal
