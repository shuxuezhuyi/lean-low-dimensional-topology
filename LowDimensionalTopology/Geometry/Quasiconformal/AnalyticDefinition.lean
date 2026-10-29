/-
The ACL and homeomorphism regularity results used here retain Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.AbsoluteContinuityOnLines
public import LowDimensionalTopology.Geometry.Quasiconformal.QuasiconformalDistributional
public import LowDimensionalTopology.Geometry.Quasiconformal.MaximalDilatation

/-!
# The linewise analytic definition and genuine weak definition

The linewise definition retains the orientation-preserving homeomorphism, bare
ACL on compact rectangles and the inequality for actual coordinate-line partials.
Total real differentiability is proved a.e. from the homeomorphism and ACL data;
it is not an additional field. The same distortion constants and their infimum
are preserved when passing to the existing analytic and genuine weak interfaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Complex
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The holomorphic partial formed from the actual ordinary coordinate-line
partial derivatives, without presupposing a total real derivative. -/
def coordinateDz (f : ℂ → ℂ) (z : ℂ) : ℂ := genDz (partialX f) (partialY f) z

/-- The antiholomorphic partial formed from the actual ordinary coordinate-line
partial derivatives, without presupposing a total real derivative. -/
def coordinateDzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := genDzbar (partialX f) (partialY f) z

/-- Fixed-K analytic quasiconformality with literal bare ACL and the ordinary
coordinate-line Wirtinger inequality. Orientation and homeomorphism are explicit. -/
def IsLinewiseKQuasiconformal (f : ℂ → ℂ) (U : Set ℂ) (K : ℝ) : Prop :=
  IsOpen U ∧ 1 ≤ K ∧ IsHomeomorphOnto f U (f '' U) ∧ IsSensePreserving f U ∧
    IsAbsolutelyContinuousOnLines f U ∧
      ∀ᵐ z ∂(volume.restrict U),
        ‖coordinateDz f z‖ + ‖coordinateDzbar f z‖ ≤
          K * (‖coordinateDz f z‖ - ‖coordinateDzbar f z‖)

/-- Analytic quasiconformality using actual coordinate partials: bare ACL and one
constant 0≤k<1 with the a.e. Beltrami norm inequality, on an oriented homeomorphism. -/
def IsLinewiseQuasiconformal (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ IsHomeomorphOnto f U (f '' U) ∧ IsSensePreserving f U ∧
    IsAbsolutelyContinuousOnLines f U ∧ ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ᵐ z ∂(volume.restrict U), ‖coordinateDzbar f z‖ ≤ k * ‖coordinateDz f z‖

/-- Homeomorphism and bare ACL imply that the coordinate-line and actual
fderiv-based Wirtinger derivatives agree a.e. Menchoff supplies total
real differentiability from the proved coordinate partial existence. -/
theorem homeomorph_coordinate_wirtinger_eq_ae {f : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hf : IsHomeomorphOnto f U V)
    (hline : IsAbsolutelyContinuousOnLines f U) :
    ∀ᵐ z ∂(volume.restrict U),
      coordinateDz f z = dz f z ∧ coordinateDzbar f z = dzbar f z := by
  have hacl : IsACL f U := source_isACL_iff_continuousOn_and_lines.2 ⟨hf.1, hline⟩
  have hdiff := differentiable_ae_of_partials hU hf (isACL_coordinate_differentiable_ae hU hacl)
  filter_upwards [hdiff] with z hz
  exact ⟨by simp only [coordinateDz, genDz, dz,
      partialX_eq_of_differentiableAt hz, partialY_eq_of_differentiableAt hz],
    by simp only [coordinateDzbar, genDzbar, dzbar,
      partialX_eq_of_differentiableAt hz, partialY_eq_of_differentiableAt hz]⟩

/-- The literal linewise definition and the existing analytic definition
have exactly the same admissible fixed distortion constants. -/
theorem linewise_iff_analytic {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} :
    IsLinewiseKQuasiconformal f U K ↔ IsAnalyticallyKQuasiconformal f U K := by
  constructor
  · rintro ⟨hU, hK, hhomeo, -, hline, hbound⟩
    have hacl : IsACL f U := source_isACL_iff_continuousOn_and_lines.2 ⟨hhomeo.1, hline⟩
    refine ⟨hU, hK, hhomeo, hacl, ?_⟩
    filter_upwards [homeomorph_coordinate_wirtinger_eq_ae hU hhomeo hline, hbound]
      with z hz hboundz
    simpa only [hz.1, hz.2] using hboundz
  · intro hf
    have horient := (geometric_iff_analytic.2 hf).isSensePreserving
    rcases hf with ⟨hU, hK, hhomeo, hacl, hbound⟩
    have hline := (source_isACL_iff_continuousOn_and_lines.1 hacl).2
    refine ⟨hU, hK, hhomeo, horient, hline, ?_⟩
    filter_upwards [homeomorph_coordinate_wirtinger_eq_ae hU hhomeo hline, hbound]
      with z hz hboundz
    simpa only [hz.1, hz.2] using hboundz

/-- The ordinary-coordinate ACL and genuine local-L1 weak definitions agree
with the same K, without assuming either ACL or total differentiability in the
weak definition. -/
theorem linewise_iff_distributional_K {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} :
    IsLinewiseKQuasiconformal f U K ↔ IsDistributionallyKQuasiconformal f U K :=
  linewise_iff_analytic.trans analytic_iff_distributional

/-- The exact conversion K=(1+k)/(1-k), k=(K-1)/(K+1) relates the literal
linewise k-form and its fixed-K form. -/
theorem linewise_iff_exists_K {f : ℂ → ℂ} {U : Set ℂ} :
    IsLinewiseQuasiconformal f U ↔ ∃ K : ℝ, IsLinewiseKQuasiconformal f U K := by
  constructor
  · rintro ⟨hU, hhomeo, horient, hline, k, hk0, hk1, hbound⟩
    have hkpos : 0 < 1 - k := by linarith only [hk1]
    have hK : 1 ≤ (1 + k) / (1 - k) := by
      rw [le_div_iff₀ hkpos]
      linarith only [hk0]
    refine ⟨(1 + k) / (1 - k), hU, hK, hhomeo, horient, hline, ?_⟩
    filter_upwards [hbound] with z hz
    rw [div_mul_eq_mul_div, le_div_iff₀ hkpos]
    nlinarith only [hz]
  · rintro ⟨K, hU, hK, hhomeo, horient, hline, hbound⟩
    have hKpos : 0 < K + 1 := by linarith only [hK]
    have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (sub_nonneg.mpr hK) hKpos.le
    have hk1 : (K - 1) / (K + 1) < 1 := by
      rw [div_lt_iff₀ hKpos]
      linarith only []
    refine ⟨hU, hhomeo, horient, hline, (K - 1) / (K + 1), hk0, hk1, ?_⟩
    exact hbound.mono fun z hz => (wirtinger_inequality_iff hK).1 hz

/-- The two full analytic definitions agree, with the literal ordinary partials
on the ACL side and genuinely locally integrable weak derivatives on the other. -/
theorem linewise_iff_distributional {f : ℂ → ℂ} {U : Set ℂ} :
    IsLinewiseQuasiconformal f U ↔ IsDistributionallyQuasiconformal f U := by
  rw [linewise_iff_exists_K, distributional_iff_exists_K]
  exact exists_congr fun K => linewise_iff_distributional_K

/-- Maximal dilatation is literally the infimum of all admissible constants
in the ordinary-coordinate ACL definition. The entire admissible set is preserved. -/
theorem infimalDilatation_eq_linewise_inf (f : ℂ → ℂ) (U : Set ℂ) :
    infimalDilatation f U = sInf {K : ℝ | IsLinewiseKQuasiconformal f U K} := by
  rw [infimalDilatation_eq_analytic_inf]
  apply congrArg sInf
  ext K
  exact linewise_iff_analytic.symm

end LowDimensionalTopology.Geometry.Quasiconformal
