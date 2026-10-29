module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGramSmooth
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGramProportional
public import LowDimensionalTopology.Geometry.Quasiconformal.SmoothLocalBeltramiSolution
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Positive smooth local densities for the same arbitrary raw metric

The original metric and its original tangent vectors are retained. The actual
local Beltrami solution supplies its real differential, and equality of the
literal coefficients gives a positive scalar identity on every vector pair.
The scalar is the actual original E entry divided by the squared norm of the
differential on 1. This proves its smoothness without a chosen smooth frame.
No compatibility of the metric with the old atlas or a new atlas is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
open LowDimensionalTopology.Geometry.Quasiconformal
universe u
variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

/-- The explicit local density in the original chart plane. Only valid chart
points are used for positivity or smoothness. The function w is unchanged. -/
def rawMetricIsothermalDensity (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (w : ℂ → ℂ) (z : ℂ) : ℝ :=
  metricGramInChart g e (e.val.symm z) 1 1 / ‖fderiv ℝ w z 1‖ ^ 2

private theorem metric_chart_coefficient_contDiffOn
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => metricBeltramiInChart g e (e.val.symm z)) e.val.target := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have hi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.val.symm e.val.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)
  have hc := (metricBeltramiInChart_contMDiffOn g e).comp hi
    (fun z hz => e.val.map_target hz)
  exact contMDiffOn_iff_contDiffOn.1 hc

private theorem metric_chart_coefficient_norm_lt_one
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    {z : ℂ} (hz : z ∈ e.val.target) :
    ‖metricBeltramiInChart g e (e.val.symm z)‖ < 1 := by
  rw [metricBeltramiInChart_eq g e _ (e.val.map_target hz)]
  exact metricBeltramiInOriginalChart_norm_lt_one g e _ (e.val.map_target hz)

private theorem plane_fderiv_injective_of_jacobian_pos
    {w : ℂ → ℂ} {z : ℂ} (hw : DifferentiableAt ℝ w z)
    (hJ : 0 < LiZhongQC.jacobian w z) : Function.Injective (fderiv ℝ w z) := by
  have hker : LinearMap.ker (fderiv ℝ w z : ℂ →ₗ[ℝ] ℂ) = ⊥ := by
    by_contra hne
    have hd : LinearMap.det (fderiv ℝ w z : ℂ →ₗ[ℝ] ℂ) = 0 :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.2 hne
    rw [LiZhongQC.det_fderiv_eq_jacobian hw] at hd
    exact hJ.ne' hd
  exact LinearMap.ker_eq_bot.mp hker

private theorem plane_fderiv_one_norm_sq_pos
    {w : ℂ → ℂ} {z : ℂ} (hw : DifferentiableAt ℝ w z)
    (hJ : 0 < LiZhongQC.jacobian w z) : 0 < ‖fderiv ℝ w z 1‖ ^ 2 := by
  have hi := plane_fderiv_injective_of_jacobian_pos hw hJ
  have hn : fderiv ℝ w z 1 ≠ 0 := by
    intro hz
    exact one_ne_zero (hi (hz.trans (map_zero _).symm))
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hn)

private theorem rawMetricIsothermalDensity_contDiffOn
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) {w : ℂ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hJ : ∀ z, 0 < LiZhongQC.jacobian w z) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (rawMetricIsothermalDensity g e w) e.val.target := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have hE : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun x => metricGramInChart g e x 1 1) e.val.source :=
    ((metricGramInChart_contMDiffOn g e).clm_apply
      contMDiffOn_const).clm_apply contMDiffOn_const
  have hi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.val.symm e.val.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)
  have hEp : ContDiffOn ℝ ∞
      (fun z => metricGramInChart g e (e.val.symm z) 1 1) e.val.target :=
    contMDiffOn_iff_contDiffOn.1 (hE.comp hi (fun z hz => e.val.map_target hz))
  have hD : ContDiff ℝ ∞ (fderiv ℝ w) := (contDiff_infty_iff_fderiv.1 hw).2
  have hD1 : ContDiff ℝ ∞ (fun z => fderiv ℝ w z 1) :=
    hD.clm_apply contDiff_const
  have hN : ContDiff ℝ ∞ (fun z => ‖fderiv ℝ w z 1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp hD1
  exact hEp.div hN.contDiffOn fun z _ =>
    (plane_fderiv_one_norm_sq_pos (hw.differentiable (by simp) z) (hJ z)).ne'

private theorem rawMetricIsothermalDensity_pos
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) {w : ℂ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hJ : ∀ z, 0 < LiZhongQC.jacobian w z) {z : ℂ} (hz : z ∈ e.val.target) :
    0 < rawMetricIsothermalDensity g e w z := by
  have hE : 0 < metricGramInChart g e (e.val.symm z) 1 1 := by
    rw [metricGramInChart_eq g e _ (e.val.map_target hz)]
    exact (metricGram_positive g e _ (e.val.map_target hz)).1
  exact div_pos hE
    (plane_fderiv_one_norm_sq_pos (hw.differentiable (by simp) z) (hJ z))

private theorem rawMetricIsothermalDensity_inner_coord
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) (w : ℂ → ℂ)
    (x : X) (hx : x ∈ e.val.source) (hw : DifferentiableAt ℝ w (e.val x))
    (hPDE : LiZhongQC.dzbar w (e.val x) =
      metricBeltramiInChart g e x * LiZhongQC.dz w (e.val x))
    (hJ : 0 < LiZhongQC.jacobian w (e.val x)) (v t : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    g.inner x v t = rawMetricIsothermalDensity g e w (e.val x) *
      ⟪fderiv ℝ w (e.val x) (originalChartDifferential R e x v),
        fderiv ℝ w (e.val x) (originalChartDifferential R e x t)⟫_ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let L := fderiv ℝ w (e.val x)
  let G := metricGramForm g e x hx
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := (innerSL ℝ (E := ℂ)).bilinearComp L L
  have hG (a b : ℂ) : G a b = g.inner x (D.symm a) (D.symm b) := rfl
  have hQ (a b : ℂ) : Q a b = ⟪L a, L b⟫_ℝ := by
    simp only [Q, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
  have hGs (a b : ℂ) : G a b = G b a := by
    rw [hG a b, hG b a]
    exact g.symm x _ _
  have hQs (a b : ℂ) : Q a b = Q b a := by
    rw [hQ a b, hQ b a]
    exact real_inner_comm _ _
  have hGp (a : ℂ) (ha : a ≠ 0) : 0 < G a a := by
    rw [hG a a]
    exact g.pos x _ (D.symm.toLinearEquiv.map_ne_zero_iff.mpr ha)
  have hLi : Function.Injective L := plane_fderiv_injective_of_jacobian_pos hw hJ
  have hQp (a : ℂ) (ha : a ≠ 0) : 0 < Q a a := by
    rw [hQ a a]
    apply real_inner_self_pos.mpr
    intro hz
    exact ha (hLi (hz.trans (map_zero L).symm))
  let a := LiZhongQC.dz w (e.val x)
  let b := LiZhongQC.dzbar w (e.val x)
  have hba : ‖b‖ < ‖a‖ := by
    have hj : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2 := hJ
    nlinarith [norm_nonneg a, norm_nonneg b]
  have ha : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg b).trans_lt hba)
  have hL1 : L 1 = a + b := by
    simpa only [L, a, b, map_one, mul_one] using
      LiZhongQC.fderiv_eq_dz_dzbar hw (1 : ℂ)
  have hLI : L Complex.I = a * Complex.I - b * Complex.I := by
    simpa only [L, a, b, Complex.conj_I, mul_neg, sub_eq_add_neg] using
      LiZhongQC.fderiv_eq_dz_dzbar hw Complex.I
  have hQμ : metricBeltramiFromGram (Q 1 1) (Q 1 Complex.I)
      (Q Complex.I Complex.I) = b / a := by
    rw [hQ 1 1, hQ 1 Complex.I, hQ Complex.I Complex.I, hL1, hLI]
    simp only [real_inner_self_eq_norm_sq]
    simpa only [one_mul] using
      metricBeltramiFromGram_of_wirtinger 1 a b zero_lt_one hba
  have hratio : b / a = metricBeltramiInChart g e x := (div_eq_iff ha).2 hPDE
  have hμ : metricBeltramiFromGram (Q 1 1) (Q 1 Complex.I) (Q Complex.I Complex.I) =
      metricBeltramiFromGram (G 1 1) (G 1 Complex.I) (G Complex.I Complex.I) := by
    rw [hQμ]
    simpa only [metricBeltramiInChart, metricGramInChart_eq g e x hx, G] using hratio
  obtain ⟨c, _hc, hform⟩ :=
    complexGram_proportional_of_metricBeltrami_eq Q G hQs hGs hQp hGp hμ
  have hden : 0 < ‖L 1‖ ^ 2 := plane_fderiv_one_norm_sq_pos hw hJ
  have h11 : metricGramInChart g e x 1 1 = c * ‖L 1‖ ^ 2 := by
    rw [metricGramInChart_eq g e x hx]
    change G 1 1 = c * ‖L 1‖ ^ 2
    simpa only [hQ 1 1, real_inner_self_eq_norm_sq] using hform 1 1
  have hρ : rawMetricIsothermalDensity g e w (e.val x) = c := by
    change metricGramInChart g e (e.val.symm (e.val x)) 1 1 /
      ‖fderiv ℝ w (e.val x) 1‖ ^ 2 = c
    rw [e.val.left_inv hx]
    exact (div_eq_iff hden.ne').2 h11
  have hvt := hform (D v) (D t)
  rw [hG (D v) (D t), hQ (D v) (D t)] at hvt
  rw [hρ]
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hvt
  simpa only [L, D, SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using hvt

private theorem originalChart_comp_mvfderiv
    (e : OriginalComplexChart R) (w : ℂ → ℂ) (x : X) (hx : x ∈ e.val.source)
    (hw : DifferentiableAt ℝ w (e.val x)) (v : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    mvfderiv 𝓘(ℝ, ℂ) (w ∘ (e.val : X → ℂ)) x v =
      fderiv ℝ w (e.val x) (originalChartDifferential R e x v) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have he := mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) e.property hx
  calc
    mvfderiv 𝓘(ℝ, ℂ) (w ∘ (e.val : X → ℂ)) x v =
        mvfderiv 𝓘(ℝ, ℂ) w (e.val x)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (e.val : X → ℂ) x v) :=
      congrArg (fun L : RealSurfaceTangent R x →L[ℝ] ℂ => L v)
        (mvfderiv_comp x hw.mdifferentiableAt he)
    _ = fderiv ℝ w (e.val x) (originalChartDifferential R e x v) := by
      rw [mvfderiv_eq_fderiv]
      rfl

/-- Every original raw metric has a positive smooth local density for the
actual coordinate supplied by the local Beltrami solution. Elliptic regularity
is explicit. The identity acts on all original tangent vectors and uses the
actual derivative of the actual composite, without assuming a new atlas. -/
theorem exists_rawMetric_local_isothermal_density_of_regularity
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) (x₀ : X)
    (hx₀ : x₀ ∈ e.val.source) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∃ (V : Set ℂ) (w : ℂ ≃ₜ ℂ),
      IsOpen V ∧ e.val x₀ ∈ V ∧ V ⊆ e.val.target ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w : ℂ → ℂ) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w.symm : ℂ → ℂ) ∧
      (∀ z ∈ V, LiZhongQC.dzbar (w : ℂ → ℂ) z =
        metricBeltramiInChart g e (e.val.symm z) * LiZhongQC.dz (w : ℂ → ℂ) z) ∧
      (∀ z, 0 < LiZhongQC.jacobian (w : ℂ → ℂ) z) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (rawMetricIsothermalDensity g e (w : ℂ → ℂ)) V ∧
      (∀ z ∈ V, 0 < rawMetricIsothermalDensity g e (w : ℂ → ℂ) z) ∧
      IsOpen (e.val.source ∩ e.val ⁻¹' V) ∧ x₀ ∈ e.val.source ∩ e.val ⁻¹' V ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
        (fun x => rawMetricIsothermalDensity g e (w : ℂ → ℂ) (e.val x))
        (e.val.source ∩ e.val ⁻¹' V) ∧
      ∀ (x : X), x ∈ e.val.source ∩ e.val ⁻¹' V →
        ∀ v t : RealSurfaceTangent R x,
          g.inner x v t = rawMetricIsothermalDensity g e (w : ℂ → ℂ) (e.val x) *
            ⟪mvfderiv 𝓘(ℝ, ℂ) ((w : ℂ → ℂ) ∘ (e.val : X → ℂ)) x v,
              mvfderiv 𝓘(ℝ, ℂ) ((w : ℂ → ℂ) ∘ (e.val : X → ℂ)) x t⟫_ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  obtain ⟨V, w, hV, hzV, hVU, hw, hwi, hPDE, hJ⟩ :=
    exists_smooth_local_beltrami_homeomorph_of_regularity hreg e.val.open_target
        (e.val.map_source hx₀) (metric_chart_coefficient_contDiffOn g e)
        (metric_chart_coefficient_norm_lt_one g e (e.val.map_source hx₀))
  have hρ : ContDiffOn ℝ ∞ (rawMetricIsothermalDensity g e (w : ℂ → ℂ)) V :=
    (rawMetricIsothermalDensity_contDiffOn g e hw hJ).mono hVU
  have hρpos (z : ℂ) (hz : z ∈ V) :
      0 < rawMetricIsothermalDensity g e (w : ℂ → ℂ) z :=
    rawMetricIsothermalDensity_pos g e hw hJ (hVU hz)
  have heNative : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (e.val : X → ℂ) e.val.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)
  have hρNative : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun x => rawMetricIsothermalDensity g e (w : ℂ → ℂ) (e.val x))
      (e.val.source ∩ e.val ⁻¹' V) :=
    (contMDiffOn_iff_contDiffOn.2 hρ).comp (heNative.mono inter_subset_left)
      (fun x hx => hx.2)
  refine ⟨V, w, hV, hzV, hVU, hw, hwi, hPDE, hJ, hρ, hρpos,
    e.val.isOpen_inter_preimage hV, ⟨hx₀, hzV⟩, hρNative, ?_⟩
  intro x hx v t
  have hd : DifferentiableAt ℝ (w : ℂ → ℂ) (e.val x) :=
    hw.differentiable (by simp) (e.val x)
  have hp : LiZhongQC.dzbar (w : ℂ → ℂ) (e.val x) =
      metricBeltramiInChart g e x * LiZhongQC.dz (w : ℂ → ℂ) (e.val x) := by
    simpa only [e.val.left_inv hx.1] using hPDE (e.val x) hx.2
  rw [originalChart_comp_mvfderiv e (w : ℂ → ℂ) x hx.1 hd v,
    originalChart_comp_mvfderiv e (w : ℂ → ℂ) x hx.1 hd t]
  exact rawMetricIsothermalDensity_inner_coord g e (w : ℂ → ℂ) x hx.1 hd hp
    (hJ (e.val x)) v t

end LowDimensionalTopology.Geometry.Teichmuller
