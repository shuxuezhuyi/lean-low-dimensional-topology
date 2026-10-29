module

public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverPoincareOverlap
public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMetricLocalSections
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The smooth Poincaré metric on the original surface

Choose an actual sheet of the given disk cover at each point. Genuine sheet
independence makes the resulting form agree with every fixed local sheet.
The positive smooth local disk densities therefore give a native smooth metric
on the unchanged tangent bundle, inducing every original complex chart.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Bundle Set Filter Topology Bornology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Hyperbolic AtlasMetricConstruction

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

namespace DiscCoverMetricConstruction

theorem chosenChart_mem (x : X) : x ∈ (chosenChart R x).val.source := by
  let := R.toRiemannAtlas.toChartedSpace
  exact mem_chart_source ℂ x

theorem exists_sheet (M : HyperbolicSurfaceModel R) (x : X) :
    ∃ l : OpenPartialHomeomorph extendedUnitDisc X,
      M.discCover = (l : extendedUnitDisc → X) ∧ x ∈ l.target := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨l, hl, hx, _hs, _hp⟩ :=
    exists_discCoverSheetDensity M (chosenChart R x) x (chosenChart_mem x)
  exact ⟨l, hl, hx.2⟩

/-- An actual covering sheet whose target contains the specified original point. -/
def chosenSheet (M : HyperbolicSurfaceModel R) (x : X) :
    OpenPartialHomeomorph extendedUnitDisc X :=
  (exists_sheet M x).choose

theorem chosenSheet_eq (M : HyperbolicSurfaceModel R) (x : X) :
    M.discCover = (chosenSheet M x : extendedUnitDisc → X) :=
  (exists_sheet M x).choose_spec.1

theorem chosenSheet_mem (M : HyperbolicSurfaceModel R) (x : X) :
    x ∈ (chosenSheet M x).target :=
  (exists_sheet M x).choose_spec.2

/-- The derived local density evaluated through the selected actual sheet. -/
def density (M : HyperbolicSurfaceModel R) (e : OriginalComplexChart R) (x : X) : ℝ :=
  discCoverSheetDensity e (chosenSheet M x) x

theorem density_eq_sheet (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (x : X) (hx : x ∈ e.val.source ∩ l.target) :
    density M e x = discCoverSheetDensity e l x := by
  exact discCoverSheetDensity_independent M e (chosenSheet M x) l
    (chosenSheet_eq M x) hl x ⟨⟨hx.1, chosenSheet_mem M x⟩, hx.2⟩

theorem density_pos (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source) :
    0 < density M e x :=
  (discCoverSheetDensity_smooth_pos M e (chosenSheet M x)
    (chosenSheet_eq M x)).2 x ⟨hx, chosenSheet_mem M x⟩

theorem density_contMDiffOn (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (density M e) e.val.source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (density M e) e.val.source
  intro x hx
  let l := chosenSheet M x
  have hxl : x ∈ l.target := chosenSheet_mem M x
  have hU : e.val.source ∩ l.target ∈ 𝓝 x :=
    (e.val.open_source.inter l.open_target).mem_nhds ⟨hx, hxl⟩
  have hd : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (discCoverSheetDensity e l) x :=
    ((discCoverSheetDensity_smooth_pos M e l (chosenSheet_eq M x)).1
      x ⟨hx, hxl⟩).contMDiffAt hU
  apply ContMDiffAt.contMDiffWithinAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [hU] with y hy
  exact density_eq_sheet M e l (chosenSheet_eq M x) y hy

/-- The selected local form acts on the unchanged real tangent fiber. -/
def form (M : HyperbolicSurfaceModel R) (x : X) : TangentForm R x := by
  let := R.toRiemannAtlas.toChartedSpace
  exact density M (chosenChart R x) x • chartForm R (chosenChart R x) x

theorem form_apply (M : HyperbolicSurfaceModel R) (x : X)
    (v w : RealSurfaceTangent R x) :
    form M x v w = density M (chosenChart R x) x *
      chartForm R (chosenChart R x) x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  simp only [form, smul_apply, smul_eq_mul]

/-- The selected form agrees with the density in every original chart. -/
theorem form_eq_density (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source)
    (v w : RealSurfaceTangent R x) :
    form M x v w = density M e x * chartForm R e x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  rw [form_apply]
  exact discCoverSheetDensity_mul_chartForm_eq M (chosenChart R x) e
    (chosenSheet M x) (chosenSheet M x) (chosenSheet_eq M x) (chosenSheet_eq M x)
    x ⟨chosenChart_mem x, chosenSheet_mem M x⟩ ⟨hx, chosenSheet_mem M x⟩ v w

/-- This equality removes the varying sheet choice on each genuine local sheet. -/
theorem form_eq_sheet (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (x : X) (hx : x ∈ e.val.source ∩ l.target)
    (v w : RealSurfaceTangent R x) :
    form M x v w = discCoverSheetDensity e l x * chartForm R e x v w := by
  rw [form_eq_density M e x hx.1, density_eq_sheet M e l hl x hx]

theorem form_eq_smul_localForm (M : HyperbolicSurfaceModel R)
    (j : X) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (x : X) (hx : x ∈ (chosenChart R j).val.source ∩ l.target) :
    form M x = discCoverSheetDensity (chosenChart R j) l x • localForm R j x := by
  let := R.toRiemannAtlas.toChartedSpace
  ext v w
  rw [form_eq_sheet M (chosenChart R j) l hl x hx v w,
    localForm_eq_chartForm R j x hx.1]
  simp only [smul_apply, smul_eq_mul]

theorem form_symm (M : HyperbolicSurfaceModel R) (x : X)
    (v w : RealSurfaceTangent R x) : form M x v w = form M x w v := by
  rw [form_apply, form_apply, chartForm_symm]

theorem form_pos (M : HyperbolicSurfaceModel R) (x : X)
    (v : RealSurfaceTangent R x) (hv : v ≠ 0) : 0 < form M x v v := by
  rw [form_apply]
  exact mul_pos (density_pos M (chosenChart R x) x (chosenChart_mem x))
    (chartForm_self_pos R (chosenChart R x) x (chosenChart_mem x) v hv)

theorem form_isVonNBounded (M : HyperbolicSurfaceModel R) (x : X) :
    IsVonNBounded ℝ {v : RealSurfaceTangent R x | form M x v v < 1} := by
  let := R.toRiemannAtlas.toChartedSpace
  let a := density M (chosenChart R x) x
  have ha : 0 < a := density_pos M (chosenChart R x) x (chosenChart_mem x)
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv
    (chosenChart R x) x (chosenChart_mem x)
  have hball : IsVonNBounded ℝ
      (D.symm.toContinuousLinearMap '' Metric.ball (0 : ℂ) (Real.sqrt (1 / a))) :=
    (NormedSpace.isVonNBounded_ball ℝ ℂ (Real.sqrt (1 / a))).image
      D.symm.toContinuousLinearMap
  apply hball.subset
  intro v hv
  change form M x v v < 1 at hv
  refine ⟨D v, ?_, D.symm_apply_apply v⟩
  rw [Metric.mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg (D v))]
  apply (lt_div_iff₀ ha).mpr
  have hq : a * ‖D v‖ ^ 2 < 1 := by
    simpa only [form_apply, chartForm_apply, real_inner_self_eq_norm_sq,
      a, D, SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using hv
  simpa only [mul_comm] using hq

/-- Smoothness is local equality with a smooth density times an existing local section. -/
theorem form_contMDiff (M : HyperbolicSurfaceModel R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
      (fun x => TotalSpace.mk' (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) FormModel x (form M x)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
    (fun x => TotalSpace.mk' (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
      TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) FormModel x (form M x))
  intro x
  let e := chosenChart R x
  let l := chosenSheet M x
  have he : x ∈ e.val.source := chosenChart_mem x
  have hl : x ∈ l.target := chosenSheet_mem M x
  have hU : e.val.source ∩ l.target ∈ 𝓝 x :=
    (e.val.open_source.inter l.open_target).mem_nhds ⟨he, hl⟩
  have hd : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (discCoverSheetDensity e l) x :=
    ((discCoverSheetDensity_smooth_pos M e l (chosenSheet_eq M x)).1
      x ⟨he, hl⟩).contMDiffAt hU
  have hq : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
      (fun y => TotalSpace.mk' (E := fun z : X => TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] ℝ) FormModel y (localForm R x y)) x :=
    (localForm_contMDiffOn R x x he).contMDiffAt (e.val.open_source.mem_nhds he)
  apply (hd.smul_section hq).congr_of_eventuallyEq
  filter_upwards [hU] with y hy
  exact congrArg (TotalSpace.mk' (E := fun z : X => TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ]
    TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] ℝ) FormModel y)
      (form_eq_smul_localForm M x l (chosenSheet_eq M x) y hy)

/-- The actual native smooth positive metric assembled from the disk cover. -/
def metric (M : HyperbolicSurfaceModel R) : SmoothSurfaceMetric R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact
    { inner := form M
      symm := form_symm M
      pos := form_pos M
      isVonNBounded := form_isVonNBounded M
      contMDiff := form_contMDiff M }

end DiscCoverMetricConstruction

/-- The original disk cover produces a native smooth positive metric inducing
the original complex atlas. -/
def discCoverAtlasInducedMetric (M : HyperbolicSurfaceModel R) : AtlasInducedMetric R where
  metric := DiscCoverMetricConstruction.metric M
  density := DiscCoverMetricConstruction.density M
  density_smooth := DiscCoverMetricConstruction.density_contMDiffOn M
  density_pos := DiscCoverMetricConstruction.density_pos M
  inner_eq e x hx v w := by
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    change DiscCoverMetricConstruction.form M x v w =
      DiscCoverMetricConstruction.density M e x *
        ⟪originalChartDifferential R e x v, originalChartDifferential R e x w⟫_ℝ
    rw [← chartForm_apply]
    exact DiscCoverMetricConstruction.form_eq_density M e x hx v w

/-- Every actual local covering sheet gives the full metric in every original chart. -/
theorem discCoverAtlasInducedMetric_inner_eq_density (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (x : X) (hx : x ∈ e.val.source ∩ l.target)
    (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (discCoverAtlasInducedMetric M).metric.inner x v w =
      discCoverSheetDensity e l x * chartForm R e x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact DiscCoverMetricConstruction.form_eq_sheet M e l hl x hx v w

/-- The global metric is the actual inverse-sheet pullback of the disk tensor. -/
theorem discCoverAtlasInducedMetric_inner_eq_sheet_tensor (M : HyperbolicSurfaceModel R)
    (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (x : X) (hx : x ∈ l.target) (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    let s := l.symm.trans discFiniteChart
    (discCoverAtlasInducedMetric M).metric.inner x v w =
      discPoincareTensor (s x)
        (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x v)
        (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x w) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e := chosenChart R x
  have he : x ∈ e.val.source := DiscCoverMetricConstruction.chosenChart_mem x
  rw [discCoverAtlasInducedMetric_inner_eq_density M e l hl x ⟨he, hx⟩ v w]
  exact (discCoverSheetDensity_tensor M e l hl x ⟨he, hx⟩ v w).symm

end LowDimensionalTopology.Geometry.Teichmuller
