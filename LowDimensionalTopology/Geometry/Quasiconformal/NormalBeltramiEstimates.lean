/-
The singular-transform and normalized-potential estimates used below are due to
Wu Xiaobin, Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Their Apache-2.0 attribution is
retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiSolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.Linarith

/-!
# Quantitative bounds for actual normal Beltrami solutions

The antiholomorphic weak derivative has the exact contraction bound at the
given exponent. The same normalized-potential constant, chosen before the
coefficient or its bound, gives the global Hölder estimate for the actual
function. Both estimates apply to every genuine weak derivative witness of
the same continuous normal solution.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

private theorem fixedPoint_lp_bound {μ ω : ℂ → ℂ} {k p : ℝ}
    (hk : 0 ≤ k) (hp : 2 < p) (hμ : IsBeltramiCoeff μ univ k)
    (hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ))
    (hfixed : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z)
    (hsmall : k * smoothHilbertNorm p < 1) :
    (eLpNorm ω (ENNReal.ofReal p) volume).toReal ≤
      (eLpNorm μ (ENNReal.ofReal p) volume).toReal / (1 - k * smoothHilbertNorm p) := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp1.le
  have hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ) := by
    simpa only [Measure.restrict_univ] using hμ.1
  have hμbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    simpa only [Measure.restrict_univ] using hμ.2
  have hμTop : MemLp μ ⊤ volume := memLp_top_of_bound hμmeas k hμbound
  have hHω := hilbertH_memLp hp1 hω
  have hprod : MemLp (fun z => μ z * hilbertH ω z)
      (ENNReal.ofReal p) (volume : Measure ℂ) := hμTop.fun_mul hHω
  have hprodBound : eLpNorm (fun z => μ z * hilbertH ω z)
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal k * eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume := by
    calc
      _ ≤ eLpNorm ((k : ℝ) • hilbertH ω) (ENNReal.ofReal p) volume := by
        apply eLpNorm_mono_ae hprod.aestronglyMeasurable
        filter_upwards [hμbound] with z hz
        simp only [Pi.smul_apply, Complex.real_smul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hk]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = _ := by
        rw [eLpNorm_const_smul]
        congr 1
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hk]
  have hprodReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHω.eLpNorm_ne_top) hprodBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk] at hprodReal
  have htriangle := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hprod.eLpNorm_ne_top, hμLp.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (f := fun z => μ z * hilbertH ω z) (g := μ)
      (μ := (volume : Measure ℂ)) hp1e)
  rw [ENNReal.toReal_add hprod.eLpNorm_ne_top hμLp.eLpNorm_ne_top] at htriangle
  have hsum : (eLpNorm ω (ENNReal.ofReal p) volume).toReal ≤
      k * (smoothHilbertNorm p * (eLpNorm ω (ENNReal.ofReal p) volume).toReal) +
        (eLpNorm μ (ENNReal.ofReal p) volume).toReal := by
    calc
      _ = (eLpNorm ((fun z => μ z * hilbertH ω z) + μ)
          (ENNReal.ofReal p) volume).toReal := by
        apply congrArg ENNReal.toReal
        apply eLpNorm_congr_ae
        filter_upwards [hfixed] with z hz
        simpa only [Pi.add_apply] using hz
      _ ≤ (eLpNorm (fun z => μ z * hilbertH ω z) (ENNReal.ofReal p) volume).toReal +
          (eLpNorm μ (ENNReal.ofReal p) volume).toReal := htriangle
      _ ≤ k * (eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume).toReal +
          (eLpNorm μ (ENNReal.ofReal p) volume).toReal := add_le_add hprodReal le_rfl
      _ ≤ _ := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_left _ hk
        simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using eq11_16 hp1 hω
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  nlinarith [hsum]

private theorem normal_weak_derivative_eq_potential_input
    {f g h ω : ℂ → ℂ} {p : ℝ} (hp : 2 < p)
    (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ))
    (hw : HasDistributionalWirtingerDerivatives f g h univ)
    (hrepr : f = fun z => z + normalizedCauchyPotential ω z) : h =ᵐ[volume] ω := by
  have hpot := normalizedCauchyPotential_distributional hp hω
  have hdiff : HasDistributionalWirtingerDerivatives
      (fun z => f z - normalizedCauchyPotential ω z)
      (fun z => g z - hilbertH ω z) (fun z => h z - ω z) univ := hw.sub_univ hpot
  have hidentity : (fun z => f z - normalizedCauchyPotential ω z) = fun z => z := by
    funext z
    rw [hrepr]
    dsimp only
    exact add_sub_cancel_right z _
  rw [hidentity] at hdiff
  have hid := c1_hasDistributionalWirtingerDerivatives_univ
    (f := fun z : ℂ => z) contDiff_id
  have heq := (distributionalWirtinger_derivatives_unique_univ hdiff hid).2
  filter_upwards [heq] with z hz
  have hidbar : dzbar (fun z : ℂ => z) z = 0 :=
    (cauchyRiemann_iff.mp (hasDerivAt_id' z).differentiableAt).2
  exact sub_eq_zero.mp (hz.trans hidbar)

/-- Every actual antiholomorphic weak derivative of a normal solution belongs
to the specified Lp and satisfies the sharp contraction denominator bound. -/
theorem normalLpSolution_antiholomorphic_lp_bound {μ f g h : ℂ → ℂ} {k p : ℝ}
    (hk : 0 ≤ k) (hp : 2 < p) (hμ : IsBeltramiCoeff μ univ k)
    (hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hsmall : k * smoothHilbertNorm p < 1) (hf : IsNormalLpSolution μ f p)
    (hw : HasDistributionalWirtingerDerivatives f g h univ) :
    MemLp h (ENNReal.ofReal p) (volume : Measure ℂ) ∧
      (eLpNorm h (ENNReal.ofReal p) volume).toReal ≤
        (eLpNorm μ (ENNReal.ofReal p) volume).toReal / (1 - k * smoothHilbertNorm p) := by
  obtain ⟨ω, hω, hfixed, hrepr⟩ := normalLpSolution_representation hp hμ hμLp hf
  have heq := normal_weak_derivative_eq_potential_input hp hω hw hrepr
  refine ⟨MemLp.ae_eq heq.symm hω, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact fixedPoint_lp_bound hk hp hμ hμLp hω hfixed hsmall

/-- A single potential constant depending only on p gives both estimates for
every actual normal solution, with arbitrary genuine weak derivative data.
The coefficient is an L-infinity class with compact essential support. -/
theorem exists_normalLpSolution_estimate_constant {p : ℝ} (hp : 2 < p) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧
      (∀ v : ℂ → ℂ, MemLp v (ENNReal.ofReal p) (volume : Measure ℂ) → ∀ z₁ z₂ : ℂ,
        ‖normalizedCauchyPotential v z₁ - normalizedCauchyPotential v z₂‖ ≤
          Kp * (eLpNorm v (ENNReal.ofReal p) volume).toReal * ‖z₁ - z₂‖ ^ (1 - 2 / p)) ∧
      ∀ (μ : MeasurableBeltramiSpace) (k : ℝ) (f g h : ℂ → ℂ), k ∈ Ico (0 : ℝ) 1 →
        ‖μ‖ ≤ k → HasCompactEssentialSupport (μ : ℂ → ℂ) →
        k * smoothHilbertNorm p < 1 → IsNormalLpSolution (μ : ℂ → ℂ) f p →
        HasDistributionalWirtingerDerivatives f g h univ →
        MemLp h (ENNReal.ofReal p) (volume : Measure ℂ) ∧
          (eLpNorm h (ENNReal.ofReal p) volume).toReal ≤
            (eLpNorm (μ : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal /
              (1 - k * smoothHilbertNorm p) ∧
          ∀ z₁ z₂ : ℂ, ‖f z₁ - f z₂‖ ≤
            Kp / (1 - k * smoothHilbertNorm p) *
              (eLpNorm (μ : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal *
                ‖z₁ - z₂‖ ^ (1 - 2 / p) + ‖z₁ - z₂‖ := by
  obtain ⟨Kp, hKp, hpotential⟩ := normalizedCauchyPotential_holder_bound hp
  have hexponent : (p - 2) / p = 1 - 2 / p := by
    rw [sub_div, div_self (ne_of_gt (lt_trans zero_lt_two hp))]
  have hpotential' : ∀ v : ℂ → ℂ,
      MemLp v (ENNReal.ofReal p) (volume : Measure ℂ) → ∀ z₁ z₂ : ℂ,
      ‖normalizedCauchyPotential v z₁ - normalizedCauchyPotential v z₂‖ ≤
        Kp * (eLpNorm v (ENNReal.ofReal p) volume).toReal * ‖z₁ - z₂‖ ^ (1 - 2 / p) := by
    simpa only [hexponent] using hpotential
  refine ⟨Kp, hKp, hpotential', ?_⟩
  intro μ k f g h hk hμk hcomp hsmall hf hw
  have hμ : IsBeltramiCoeff (μ : ℂ → ℂ) univ k := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff μ).1, ?_⟩
    filter_upwards [(MeasurableBeltramiSpace.isBeltramiCoeff μ).2] with z hz
    exact hz.trans hμk
  have hμLp := measurableBeltrami_memLp_of_compactEssentialSupport μ hcomp (ENNReal.ofReal p)
  obtain ⟨hm, hb⟩ := normalLpSolution_antiholomorphic_lp_bound hk.1 hp hμ hμLp hsmall hf hw
  refine ⟨hm, hb, ?_⟩
  obtain ⟨ω, hω, hfixed, hrepr⟩ := normalLpSolution_representation hp hμ hμLp hf
  have hωbound := fixedPoint_lp_bound hk.1 hp hμ hμLp hω hfixed hsmall
  intro z₁ z₂
  have hdiff : f z₁ - f z₂ =
      (normalizedCauchyPotential ω z₁ - normalizedCauchyPotential ω z₂) + (z₁ - z₂) := by
    rw [hrepr]
    dsimp only
    ring
  calc
    _ = ‖(normalizedCauchyPotential ω z₁ - normalizedCauchyPotential ω z₂) + (z₁ - z₂)‖ :=
      congrArg norm hdiff
    _ ≤ ‖normalizedCauchyPotential ω z₁ - normalizedCauchyPotential ω z₂‖ + ‖z₁ - z₂‖ :=
      norm_add_le _ _
    _ ≤ Kp * (eLpNorm ω (ENNReal.ofReal p) volume).toReal *
        ‖z₁ - z₂‖ ^ (1 - 2 / p) + ‖z₁ - z₂‖ :=
      add_le_add (hpotential' ω hω z₁ z₂) le_rfl
    _ ≤ Kp * ((eLpNorm (μ : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal /
        (1 - k * smoothHilbertNorm p)) * ‖z₁ - z₂‖ ^ (1 - 2 / p) + ‖z₁ - z₂‖ := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      exact mul_le_mul_of_nonneg_left hωbound hKp
    _ = _ := by ring

end LowDimensionalTopology.Geometry.Quasiconformal
