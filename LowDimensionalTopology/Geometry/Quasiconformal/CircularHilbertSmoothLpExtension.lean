module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertSmoothLpPrincipalValue
public import LowDimensionalTopology.Unproved.Quasiconformal.RealDirectionalHilbert
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The actual bounded circular extension on smooth noncompact Lp functions

Compact smooth cutoffs converge in the original Lp and their circular
transforms converge pointwise to the genuine radial principal value.
An almost-everywhere convergent subsequence identifies the given bounded
extension with that value, without presuming a directional integral on
the noncompact function.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Every given bounded extension acts on a smooth noncompact Lp input as
its genuine radial principal value in the same plane and the same exponent. -/
theorem isCircularHilbertLpExtension_eq_radial_smoothLp {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    {S : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)}
    (hS : LowDimensionalTopology.Unproved.Quasiconformal.IsCircularHilbertLpExtension p S)
    {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hmem : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    (S (hmem.toLp φ) : ℂ → ℂ) =ᵐ[volume] radialCircularHilbertTransform φ := by
  let a : ℕ → ℂ → ℂ := circularSmoothLpCutoffApprox φ
  have hacd (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a n) :=
    contDiff_circularSmoothLpCutoffApprox hφ n
  have hacs (n : ℕ) : HasCompactSupport (a n) :=
    hasCompactSupport_circularSmoothLpCutoffApprox φ n
  have hamem (n : ℕ) : MemLp (a n) (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (hacd n).continuous.memLp_of_hasCompactSupport (hacs n)
  have haLp : Tendsto (fun n : ℕ => (hamem n).toLp (a n)) atTop
      (𝓝 (hmem.toLp φ)) :=
    circularSmoothLpCutoffApprox_tendsto (by linarith) hφ hmem
  have hsLp := (S.continuous.tendsto (hmem.toLp φ)).comp haLp
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hsLp).exists_seq_tendsto_ae'
  have heq : ∀ᵐ z : ℂ, ∀ n : ℕ,
      (S ((hamem n).toLp (a n)) : ℂ → ℂ) z = circularHilbertTransform (a n) z :=
    ae_all_iff.mpr fun n => hS (a n) (hacd n) (hacs n)
  filter_upwards [hae, heq] with z hz hzeq
  apply tendsto_nhds_unique hz
  have hpoint := (circularHilbertTransform_cutoffApprox_tendsto hp hφ hmem z).comp hns
  exact hpoint.congr' (Eventually.of_forall fun n => (hzeq (ns n)).symm)

end LowDimensionalTopology.Geometry.Quasiconformal
