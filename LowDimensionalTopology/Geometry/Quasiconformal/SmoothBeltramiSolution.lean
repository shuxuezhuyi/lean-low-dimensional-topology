/-
The singular-integral existence and C1 solution theorem used here are due to
Wu Xiaobin, Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Its Apache-2.0 attribution is
retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Unproved.Quasiconformal.SmoothBeltramiRegularity
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S12_Existence
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# A smooth plane Beltrami homeomorphism from explicit elliptic regularity

The actual smooth compact coefficient first produces an actual C1 solution,
its everywhere pointwise equation, positive Jacobian and global homeomorphism
by the existing integral construction. The named regularity hypothesis upgrades
this very same function to real C∞. The actual invertible real derivatives and
Mathlib's smooth inverse theorem then prove real C∞ of its original inverse.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A smooth compact coefficient with a strict pointwise uniform bound has an
actual plane homeomorphism satisfying its original equation everywhere, with
positive Jacobian and real C∞ maps in both directions. Elliptic regularity is
an explicit hypothesis; existence and inverse smoothness are proved here. -/
theorem exists_smooth_beltrami_homeomorph_of_regularity
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    {μ : ℂ → ℂ} {k : ℝ} (hk : k < 1)
    (hμs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ)
    (hμc : HasCompactSupport μ) (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ e : ℂ ≃ₜ ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : ℂ → ℂ) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e.symm : ℂ → ℂ) ∧
      (∀ z, dzbar (e : ℂ → ℂ) z = μ z * dz (e : ℂ → ℂ) z) ∧
      ∀ z, 0 < jacobian (e : ℂ → ℂ) z := by
  have hk0 : 0 ≤ k := (norm_nonneg (μ 0)).trans (hbound 0)
  obtain ⟨p, hp, _hp3, hkp⟩ :=
    eq12_1_exists_exponent hk (show (2 : ℝ) < 3 by norm_num)
  have hμB : IsBeltramiCoeff μ univ k :=
    ⟨hμs.continuous.aestronglyMeasurable, Eventually.of_forall hbound⟩
  have hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hμs.continuous.memLp_of_hasCompactSupport hμc
  obtain ⟨ω, hω, hfixed, _hunique⟩ := eq12_1_solution hk0 hμB hp hkp hμLp
  obtain ⟨a, hwC1, hPDE, hJ, e, he⟩ :=
    thm12_1_smooth_case hk hμs hμc hbound hp hkp hω hfixed
  have hw : ContDiff ℝ 1 (fun z => z + cauchyT ω z) := by
    have hconst : ContDiff ℝ 1 (fun _ : ℂ => a) := contDiff_const
    simpa using hwC1.sub hconst
  have hwSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => z + cauchyT ω z) :=
    hreg μ (fun z => z + cauchyT ω z) k hk hμs hμc hbound hw hPDE
  have heC1 : ContDiff ℝ 1 (e : ℂ → ℂ) := by
    simpa only [he] using hw
  have heSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : ℂ → ℂ) := by
    simpa only [he] using hwSmooth
  have hePDE : ∀ z, dzbar (e : ℂ → ℂ) z = μ z * dz (e : ℂ → ℂ) z := by
    simpa only [he] using hPDE
  have heJac : ∀ z, 0 < jacobian (e : ℂ → ℂ) z := by
    simpa only [he] using hJ
  have hdiff : ∀ z, DifferentiableAt ℝ (e : ℂ → ℂ) z :=
    fun z => heC1.differentiable one_ne_zero z
  have hker : ∀ z, LinearMap.ker (fderiv ℝ (e : ℂ → ℂ) z : ℂ →ₗ[ℝ] ℂ) = ⊥ := by
    intro z
    by_contra hne
    have hdet0 : LinearMap.det (fderiv ℝ (e : ℂ → ℂ) z : ℂ →ₗ[ℝ] ℂ) = 0 :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.2 hne
    rw [det_fderiv_eq_jacobian (hdiff z)] at hdet0
    exact (heJac z).ne' hdet0
  have hrange : ∀ z, LinearMap.range (fderiv ℝ (e : ℂ → ℂ) z : ℂ →ₗ[ℝ] ℂ) = ⊤ :=
    fun z => LinearMap.ker_eq_bot_iff_range_eq_top.1 (hker z)
  let D : ℂ → ℂ ≃L[ℝ] ℂ := fun z =>
    ContinuousLinearEquiv.ofBijective (fderiv ℝ (e : ℂ → ℂ) z) (hker z) (hrange z)
  have hD (z : ℂ) : (D z : ℂ →L[ℝ] ℂ) = fderiv ℝ (e : ℂ → ℂ) z := by
    exact ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hDeriv (z : ℂ) : HasFDerivAt (e : ℂ → ℂ) (D z : ℂ →L[ℝ] ℂ) z := by
    rw [hD z]
    exact (hdiff z).hasFDerivAt
  refine ⟨e, heSmooth, ?_, hePDE, heJac⟩
  exact Homeomorph.contDiff_symm e (f₀' := D) hDeriv heSmooth

end LowDimensionalTopology.Geometry.Quasiconformal
