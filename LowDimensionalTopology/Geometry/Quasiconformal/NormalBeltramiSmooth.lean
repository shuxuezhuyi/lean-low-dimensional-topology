/-
The same-exponent smooth fixed-point theorem is due to Wu Xiaobin,
Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Its Apache-2.0 attribution is
retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiQuasiconformal
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic.Ring

/-!
# Regularity of the actual normal solution for smooth compact coefficients

The actual smooth coefficient is kept as a function. Its given a.e. bound
extends pointwise by continuity. The same-exponent smooth fixed-point theorem
and the actual normalized integral representation prove that every given normal
solution is C1. Its homeomorphism and geometric quasiconformality refer to this
same original function. The sequence theorem applies this result to every
original smooth approximating coefficient and its own original normal solution.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Metric MeasureTheory Filter Topology
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- Every actual normal solution for a smooth compactly supported coefficient
is C1 and is a quasiconformal homeomorphism of the entire plane. The coefficient
bound remains an a.e. bound, and the exponent is the originally given one. -/
theorem normalLpSolution_smooth {μ f : ℂ → ℂ} {k p : ℝ}
    (hk : k ∈ Ico (0 : ℝ) 1) (hp : 2 < p)
    (hsmall : k * smoothHilbertNorm p < 1) (hμ : IsBeltramiCoeff μ univ k)
    (hμs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ) (hμc : HasCompactSupport μ)
    (hf : IsNormalLpSolution μ f p) :
    ContDiff ℝ 1 f ∧ (∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ) = f) ∧
      IsKQC f univ ((1 + k) / (1 - k)) := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hkp : k * hilbertNorm p < 1 := by
    simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using hsmall
  have hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    simpa only [Measure.restrict_univ] using hμ.2
  have hclosed : IsClosed {z : ℂ | ‖μ z‖ ≤ k} :=
    isClosed_le hμs.continuous.norm continuous_const
  have hdense : Dense {z : ℂ | ‖μ z‖ ≤ k} := Measure.dense_of_ae hbound
  have hpoint : ∀ z : ℂ, ‖μ z‖ ≤ k :=
    eq_univ_iff_forall.mp (hclosed.closure_eq.symm.trans hdense.closure_eq)
  have hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hμs.continuous.memLp_of_hasCompactSupport hμc
  obtain ⟨ω, hω, hfixed, hrepr⟩ := normalLpSolution_representation hp hμ hμLp hf
  obtain ⟨a, hrawC1, -, -, -⟩ := thm12_1_smooth_case hk.2 hμs hμc hpoint hp hkp hω hfixed
  obtain ⟨R, -, hR⟩ := hμc.isCompact.isBounded.exists_pos_norm_le
  have hsupp : ∀ z, R < ‖z‖ → μ z = 0 := by
    intro z hz
    exact image_eq_zero_of_notMem_tsupport (fun hzS => (not_le_of_gt hz) (hR z hzS))
  have hP := normalizedCauchyPotential_eq_cauchyT_sub_of_fixedPoint hp hω hsupp hfixed
  have hfeq : f = fun z => (z + cauchyT ω z + a) - (a + cauchyT ω 0) := by
    rw [hrepr, hP]
    funext z
    dsimp only
    ring
  have hC1 : ContDiff ℝ 1 f := by
    rw [hfeq]
    exact hrawC1.sub contDiff_const
  have hess : HasCompactEssentialSupport μ :=
    ⟨tsupport μ, hμc.isCompact,
      Eventually.of_forall fun _ hz => image_eq_zero_of_notMem_tsupport hz⟩
  let ν : MeasurableBeltramiSpace := (MeasurableBeltramiBall.coefficientMemLp hμ).toLp μ
  have hν : (ν : ℂ → ℂ) =ᵐ[volume] μ :=
    (MeasurableBeltramiBall.coefficientMemLp hμ).coeFn_toLp
  have hνk : ‖ν‖ ≤ k := by
    apply lpInfinity_norm_le_of_ae_bound ν hk.1
    filter_upwards [hν, hbound] with z hz hzb
    rw [hz]
    exact hzb
  have hνcomp : HasCompactEssentialSupport (ν : ℂ → ℂ) :=
    (hasCompactEssentialSupport_congr_ae hν).mpr hess
  have hνnormal : IsNormalLpSolution (ν : ℂ → ℂ) f p :=
    (isNormalLpSolution_congr_coefficient_ae hν).mpr hf
  obtain ⟨hQC, hhomeo, -⟩ := normalLpSolution_quasiconformal ν hk hνk hνcomp hp hsmall hνnormal
  exact ⟨hC1, hhomeo, hQC⟩

/-- Every member of the original smooth approximating sequence has its own
original normal solution C1 and a quasiconformal homeomorphism of the plane. -/
theorem normalLpSolution_smooth_sequence {μn fn : ℕ → ℂ → ℂ} {k p : ℝ}
    (hk : k ∈ Ico (0 : ℝ) 1) (hp : 2 < p) (hsmall : k * smoothHilbertNorm p < 1)
    (hμ : ∀ n, IsBeltramiCoeff (μn n) univ k)
    (hμs : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n))
    (hμc : ∀ n, HasCompactSupport (μn n))
    (hfn : ∀ n, IsNormalLpSolution (μn n) (fn n) p) :
    ∀ n, ContDiff ℝ 1 (fn n) ∧ (∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ) = fn n) ∧
      IsKQC (fn n) univ ((1 + k) / (1 - k)) :=
  fun n => normalLpSolution_smooth hk hp hsmall (hμ n) (hμs n) (hμc n) (hfn n)

end LowDimensionalTopology.Geometry.Quasiconformal
