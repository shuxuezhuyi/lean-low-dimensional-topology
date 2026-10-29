module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPotentialFormula
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertSmoothLpPrincipalValue
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPotentialTailWirtinger

/-!
# The radial potential formula on the smooth noncompact input

A compact smooth local representative accounts for the singularity. Its
complement vanishes on a closed neighborhood of the evaluation point and
has the ordinary differentiable tail already established. Actual value
integrability at each point permits addition of the original potentials.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The genuine radial principal value equals the Wirtinger derivative of
the original renormalized potential on a smooth planar Lp input whose
value integrals are genuinely integrable. -/
theorem radialCircularHilbertTransform_eq_dz_renormalizedInverseNormPotential
    {p : ℝ} (hp : 1 < p) {g : ℂ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hmem : MemLp g (ENNReal.ofReal p) (volume : Measure ℂ))
    (hint : ∀ x : ℂ, Integrable (fun t : ℂ => g t * renormalizedInverseNormKernel t x)
      (volume : Measure ℂ)) (z : ℂ) :
    radialCircularHilbertTransform g z =
      (1 / (Real.pi : ℂ)) * LiZhongQC.dz (renormalizedInverseNormPotential g) z := by
  let χ : ContDiffBump z := ⟨1, 2, by norm_num, by norm_num⟩
  let ψ : ℂ → ℂ := fun t => χ t • g t
  let d : ℂ → ℂ := fun t => g t - ψ t
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := χ.contDiff.smul hg
  have hcψ : HasCompactSupport ψ := χ.hasCompactSupport.smul_right
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hψmem : MemLp ψ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hψ.continuous.memLp_of_hasCompactSupport hcψ
  have hdmem : MemLp d (ENNReal.ofReal p) (volume : Measure ℂ) := hmem.sub hψmem
  have hlocal (t : ℂ) (ht : ‖t - z‖ ≤ 1) : g t = ψ t := by
    have hχ : χ t = 1 := χ.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_eq_norm] using ht)
    simp only [ψ, hχ, one_smul]
  have hzero (t : ℂ) (ht : ‖t - z‖ ≤ 1) : d t = 0 := by
    simp only [d, hlocal t ht, sub_self]
  have hψint (x : ℂ) :
      Integrable (fun t : ℂ => ψ t * renormalizedInverseNormKernel t x)
        (volume : Measure ℂ) := by
    have h0 := integrable_inverseNormPotential hψ.continuous hcψ (0 : ℂ)
    simp only [sub_zero] at h0
    have hi := (integrable_inverseNormPotential hψ.continuous hcψ x).sub h0
    apply hi.congr
    apply Eventually.of_forall
    intro t
    simp only [Pi.sub_apply, renormalizedInverseNormKernel, mul_sub]
  have hdint (x : ℂ) :
      Integrable (fun t : ℂ => d t * renormalizedInverseNormKernel t x)
        (volume : Measure ℂ) := by
    apply ((hint x).sub (hψint x)).congr
    apply Eventually.of_forall
    intro t
    simp only [Pi.sub_apply]
    dsimp only [d]
    ring
  have hPsum : renormalizedInverseNormPotential g =
      fun x => renormalizedInverseNormPotential ψ x + renormalizedInverseNormPotential d x := by
    funext x
    unfold renormalizedInverseNormPotential
    rw [← integral_add (hψint x) (hdint x)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    dsimp only [d]
    ring
  have hPψdiff : DifferentiableAt ℝ (renormalizedInverseNormPotential ψ) z := by
    have heq : renormalizedInverseNormPotential ψ =
        fun x => inverseNormPotential ψ x - inverseNormPotential ψ 0 :=
      funext (renormalizedInverseNormPotential_eq_sub hψ.continuous hcψ)
    rw [heq]
    exact ((contDiff_inverseNormPotential hψ1 hcψ).differentiable one_ne_zero z).sub
      (differentiableAt_const (inverseNormPotential ψ 0))
  have hPddiff : DifferentiableAt ℝ (renormalizedInverseNormPotential d) z :=
    (hasFDerivAt_renormalizedInverseNormPotential_of_vanishing hp hdmem z
      (by norm_num : (0 : ℝ) < 1) hzero (hdint z)).differentiableAt
  have hdzsum : LiZhongQC.dz (renormalizedInverseNormPotential g) z =
      LiZhongQC.dz (renormalizedInverseNormPotential ψ) z +
        LiZhongQC.dz (renormalizedInverseNormPotential d) z := by
    rw [hPsum]
    have hfd := (hPψdiff.hasFDerivAt.add hPddiff.hasFDerivAt).fderiv
    have hsumfun : renormalizedInverseNormPotential ψ + renormalizedInverseNormPotential d =
        fun x : ℂ => renormalizedInverseNormPotential ψ x +
          renormalizedInverseNormPotential d x := by
      funext x
      simp only [Pi.add_apply]
    rw [hsumfun] at hfd
    simp only [LiZhongQC.dz, hfd, add_apply]
    ring
  have hfull :
      (∫ t in {t : ℂ | 1 < ‖t - z‖}, d t / ((t - z) * (‖t - z‖ : ℂ))) =
        ∫ t : ℂ, d t / ((t - z) * (‖t - z‖ : ℂ)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [hzero t (le_of_not_gt ht), zero_div]
  have hlim := tendsto_circularHilbertTruncation_of_local_compact hp hmem hψ hcψ z
    (by norm_num : (0 : ℝ) < 1) hlocal
  have hvalue := hlim.limUnder_eq
  change radialCircularHilbertTransform g z = circularHilbertTransform ψ z +
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ t in {t : ℂ | 1 < ‖t - z‖}, d t / ((t - z) * (‖t - z‖ : ℂ)) at hvalue
  rw [hfull] at hvalue
  have htail := dz_renormalizedInverseNormPotential_of_vanishing hp hdmem z
    (by norm_num : (0 : ℝ) < 1) hzero (hdint z)
  rw [hvalue, hdzsum, circularHilbertTransform_eq_dz_renormalizedInverseNormPotential hψ hcψ,
    htail]
  have hcoeff : (1 / 2 : ℂ) * (1 / (Real.pi : ℂ)) = 1 / (2 * (Real.pi : ℂ)) := by
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [← hcoeff]
  ring

end LowDimensionalTopology.Geometry.Quasiconformal
