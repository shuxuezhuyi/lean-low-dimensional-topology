module

public import LowDimensionalTopology.Geometry.Teichmuller.RiemannianConformality
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Positive chart forms and their conformal transition factors

Every form below acts on the original real tangent bundle. The flat form of
one original complex chart is a positive multiple of the flat form of any
other original chart on their actual overlap. The transition factor is
strictly positive and infinitely smooth on that overlap. These are the local
forms used in a partition-of-unity construction of a compatible metric.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

namespace AtlasMetricConstruction

universe u
variable {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)

/-- Continuous bilinear forms on the unchanged real tangent fiber. -/
abbrev TangentForm (x : X) :=
  RealSurfaceTangent R x →L[ℝ] RealSurfaceTangent R x →L[ℝ] ℝ

/-- Pull back the ordinary real inner product by the actual chart differential.
Outside the chart source the expression is merely totalized; only values on
its source are used for positivity or transition identities. -/
def chartForm (e : OriginalComplexChart R) (x : X) : TangentForm R x := by
  let := R.toRiemannAtlas.toChartedSpace
  letI : IsNormableSpace ℝ (RealSurfaceTangent R x) := by
    let c : OriginalComplexChart R := ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
    exact (SmoothSurfaceEquiv.originalChartDifferentialEquiv c x
      (mem_chart_source ℂ x)).isNormableSpace
  exact (innerSL ℝ (E := ℂ)).bilinearComp
    (originalChartDifferential R e x) (originalChartDifferential R e x)

@[simp]
theorem chartForm_apply (e : OriginalComplexChart R) (x : X)
    (v w : RealSurfaceTangent R x) :
    chartForm R e x v w =
      ⟪originalChartDifferential R e x v, originalChartDifferential R e x w⟫_ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let : IsNormableSpace ℝ (RealSurfaceTangent R x) := by
    let c : OriginalComplexChart R := ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
    exact (SmoothSurfaceEquiv.originalChartDifferentialEquiv c x
      (mem_chart_source ℂ x)).isNormableSpace
  simp only [chartForm, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]

theorem chartForm_symm (e : OriginalComplexChart R) (x : X)
    (v w : RealSurfaceTangent R x) :
    chartForm R e x v w = chartForm R e x w v := by
  rw [chartForm_apply, chartForm_apply]
  exact real_inner_comm _ _

theorem chartForm_self_nonneg (e : OriginalComplexChart R) (x : X)
    (v : RealSurfaceTangent R x) : 0 ≤ chartForm R e x v v := by
  rw [chartForm_apply]
  exact real_inner_self_nonneg

theorem chartForm_self_pos (e : OriginalComplexChart R) (x : X)
    (hx : x ∈ e.val.source) (v : RealSurfaceTangent R x) (hv : v ≠ 0) :
    0 < chartForm R e x v v := by
  rw [chartForm_apply]
  apply real_inner_self_pos.mpr
  exact (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx).toLinearEquiv.map_ne_zero_iff.mpr hv

/-- The scalar relating the two actual coordinate inner products. -/
def transitionScale (e f : OriginalComplexChart R) (x : X) : ℝ :=
  ‖fderiv ℝ (riemannChartMap e.val (Homeomorph.refl X) f.val) (e.val x) 1‖ ^ 2

private theorem identity_surfaceDifferential (x : X) (v : RealSurfaceTangent R x) :
    surfaceDifferential R R (SmoothSurfaceEquiv.refl R) x v = v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : X → X) x) v = v
  rw [mfderiv_id]
  rfl

theorem transitionScale_pos (e f : OriginalComplexChart R) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    0 < transitionScale R e f x := by
  have hz : e.val x ∈ riemannChartMapDomain e.val (Homeomorph.refl X) f.val := by
    refine ⟨e.val.map_source he, ?_⟩
    change e.val.symm (e.val x) ∈ f.val.source
    rw [e.val.left_inv he]
    exact hf
  have han : RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas
      (SmoothSurfaceEquiv.refl R).toHomeomorph := RiemannAnalyticMap.id _
  have hL := (SmoothSurfaceEquiv.refl R).chartMap_isConformalMap_of_analytic han e f hz
  apply sq_pos_of_ne_zero
  apply norm_ne_zero_iff.mpr
  intro hzero
  exact one_ne_zero (hL.injective (hzero.trans (map_zero _).symm))

/-- The transition identity uses the actual coordinate differential, including
its positive conformal scale; no identification of distinct tangent fibers is used. -/
theorem chartForm_change (e f : OriginalComplexChart R) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source)
    (v w : RealSurfaceTangent R x) :
    chartForm R f x v w = transitionScale R e f x * chartForm R e x v w := by
  have hz : e.val x ∈ riemannChartMapDomain e.val (Homeomorph.refl X) f.val := by
    refine ⟨e.val.map_source he, ?_⟩
    change e.val.symm (e.val x) ∈ f.val.source
    rw [e.val.left_inv he]
    exact hf
  have han : RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas
      (SmoothSurfaceEquiv.refl R).toHomeomorph := RiemannAnalyticMap.id _
  have hL := (SmoothSurfaceEquiv.refl R).chartMap_isConformalMap_of_analytic han e f hz
  have hv := (SmoothSurfaceEquiv.refl R).chartDifferential_intertwines e f x he hf v
  have hw := (SmoothSurfaceEquiv.refl R).chartDifferential_intertwines e f x he hf w
  rw [identity_surfaceDifferential R x v] at hv
  rw [identity_surfaceDifferential R x w] at hw
  simp only [SmoothSurfaceEquiv.refl_toHomeomorph, Homeomorph.refl_apply] at hv hw hL
  change fderiv ℝ (riemannChartMap e.val (id : X → X) f.val) (e.val x)
      (originalChartDifferential R e x v) = originalChartDifferential R f x v at hv
  change fderiv ℝ (riemannChartMap e.val (id : X → X) f.val) (e.val x)
      (originalChartDifferential R e x w) = originalChartDifferential R f x w at hw
  rw [chartForm_apply, chartForm_apply, ← hv, ← hw]
  exact conformal_inner_eq_norm_apply_one_sq hL _ _

/-- The transition scale is genuinely infinitely smooth on the original chart overlap. -/
theorem transitionScale_contMDiffOn (e f : OriginalComplexChart R) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (transitionScale R e f)
      (e.val.source ∩ f.val.source) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (transitionScale R e f)
    (e.val.source ∩ f.val.source)
  intro x hx
  let F := riemannChartMap e.val (Homeomorph.refl X) f.val
  let D := riemannChartMapDomain e.val (Homeomorph.refl X) f.val
  have hD : IsOpen D :=
    riemannChartMapDomain_isOpen _ _ _ (Homeomorph.refl X).continuous
  have hz : e.val x ∈ D := by
    refine ⟨e.val.map_source hx.1, ?_⟩
    change e.val.symm (e.val x) ∈ f.val.source
    rw [e.val.left_inv hx.1]
    exact hx.2
  have hFD : ContDiffOn ℝ ∞ (fderiv ℝ F) D :=
    ((SmoothSurfaceEquiv.refl R).chartMap_contDiffOn_real_infty e f).fderiv_of_isOpen hD
      (by simp)
  have hFone : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z 1) D :=
    hFD.clm_apply contDiffOn_const
  have hnorm : ContDiffAt ℝ ∞ (fun z => ‖fderiv ℝ F z 1‖ ^ 2) (e.val x) :=
    (contDiff_norm_sq ℝ).contDiffAt.comp (e.val x)
      (hFone.contDiffAt (hD.mem_nhds hz))
  have heSmooth : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.val x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hx.1
  exact (hnorm.comp_contMDiffAt heSmooth).contMDiffWithinAt

end AtlasMetricConstruction

end LowDimensionalTopology.Geometry.Teichmuller
