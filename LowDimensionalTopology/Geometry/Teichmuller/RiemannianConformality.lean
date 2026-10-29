module

public import LowDimensionalTopology.Geometry.Teichmuller.ConformalSmooth
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smooth Riemannian conformality in inducing complex atlases

A native smooth Riemannian metric is represented by a positive smooth density
in every original complex chart. An orientation-preserving smooth equivalence
between two such surfaces is metric conformal exactly when it is biholomorphic.
The global smooth exponent is constructed from local coordinate formulas for
a pointwise metric ratio.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

/-- The actual tangent space of the real manifold induced by the complex atlas. -/
abbrev RealSurfaceTangent {X : Type u} [TopologicalSpace X]
    (R : RiemannSurface X) (x : X) :=
  let := R.toRiemannAtlas.toChartedSpace
  TangentSpace 𝓘(ℝ, ℂ) x

/-- Mathlib's genuine smooth positive definite metric on the actual tangent bundle. -/
abbrev SmoothSurfaceMetric {X : Type u} [TopologicalSpace X]
    (R : RiemannSurface X) :=
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℂ) ∞ ℂ
    (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x)

/-- An original chart, without restricting to the charts selected by `chartAt`. -/
abbrev OriginalComplexChart {X : Type u} [TopologicalSpace X]
    (R : RiemannSurface X) := {e : OpenPartialHomeomorph X ℂ // e ∈ R.charts}

/-- The actual differential of an original chart, in the coordinate vector space. -/
def originalChartDifferential {X : Type u} [TopologicalSpace X]
    (R : RiemannSurface X) (e : OriginalComplexChart R) (x : X) :
    RealSurfaceTangent R x →L[ℝ] ℂ := by
  let := R.toRiemannAtlas.toChartedSpace
  exact mvfderiv 𝓘(ℝ, ℂ) (e.val : X → ℂ) x

/-- The actual differential of the given smooth surface map. -/
def surfaceDifferential {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (R : RiemannSurface X) (S : RiemannSurface Y)
    (f : SmoothSurfaceEquiv R S) (x : X) :
    RealSurfaceTangent R x →L[ℝ] RealSurfaceTangent S (f.toHomeomorph x) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  exact mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f.toHomeomorph x

/-- A native smooth metric with positive smooth isothermal densities in every
original complex chart. -/
structure AtlasInducedMetric {X : Type u} [TopologicalSpace X]
    (R : RiemannSurface X) where
  metric : SmoothSurfaceMetric R
  density : OriginalComplexChart R → X → ℝ
  density_smooth (e : OriginalComplexChart R) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (density e) e.val.source
  density_pos (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source) :
    0 < density e x
  inner_eq (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source)
      (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    metric.inner x v w = density e x *
      ⟪originalChartDifferential R e x v, originalChartDifferential R e x w⟫_ℝ

/-- Pullback conformality on actual tangent vectors, with a globally smooth real exponent. -/
def IsMetricConformal {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S) : Prop :=
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  ∃ φ : X → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ ∧
    ∀ (x : X) (v w : RealSurfaceTangent R x),
      h.metric.inner (f.toHomeomorph x)
          (surfaceDifferential R S f x v) (surfaceDifferential R S f x w) =
        Real.exp (φ x) * g.metric.inner x v w

/-- In the complex plane, the scale of a conformal differential is determined
by its value on the coordinate vector `1`. -/
theorem conformal_inner_eq_norm_apply_one_sq {L : ℂ →L[ℝ] ℂ}
    (hL : IsConformalMap L) (a b : ℂ) :
    ⟪L a, L b⟫_ℝ = ‖L 1‖ ^ 2 * ⟪a, b⟫_ℝ := by
  obtain ⟨c, hc, hinner⟩ := (isConformalMap_iff L).mp hL
  have hcval : ‖L 1‖ ^ 2 = c := by
    simpa only [real_inner_self_eq_norm_sq, norm_one, one_pow, mul_one]
      using hinner 1 1
  rw [hcval]
  exact hinner a b

/-- Orientation preservation excludes the conjugate-linear branch of Mathlib's
classification of conformal real linear maps on the complex plane. -/
theorem complexDifferentiableAt_of_inner_scaling
    {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (hJ : 0 < realJacobian F z)
    (hscale : ∃ c : ℝ, 0 < c ∧ ∀ a b : ℂ,
      ⟪fderiv ℝ F z a, fderiv ℝ F z b⟫_ℝ = c * ⟪a, b⟫_ℝ) :
    DifferentiableAt ℂ F z := by
  have hL : IsConformalMap (fderiv ℝ F z) :=
    (isConformalMap_iff _).mpr hscale
  rcases hL.is_complex_or_conj_linear with ⟨L, hL⟩ | ⟨L, hL⟩
  · exact (differentiableAt_iff_restrictScalars ℝ hF).mpr ⟨L, hL⟩
  · have hconj : (fderiv ℝ F z) =
        (L.restrictScalars ℝ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
      ext a
      have hh := congrArg (fun A : ℂ →L[ℝ] ℂ => A (conj a)) hL
      simpa using hh.symm
    have hdetConj :
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ).det = -1 := by
      change Complex.conjAe.toLinearEquiv.toLinearMap.det = -1
      exact Complex.det_conjAe
    have hnonneg : 0 ≤ ((L.restrictScalars ℝ) : ℂ →ₗ[ℝ] ℂ).det := by
      simp only [ContinuousLinearMap.coe_restrictScalars,
        LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
      exact Complex.normSq_nonneg _
    have hdet : realJacobian F z =
        ((L.restrictScalars ℝ) : ℂ →ₗ[ℝ] ℂ).det * (-1) := by
      unfold realJacobian
      rw [hconj]
      change (((L.restrictScalars ℝ) : ℂ →ₗ[ℝ] ℂ).comp
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)).det = _
      rw [LinearMap.det_comp, hdetConj]
    rw [hdet] at hJ
    linarith

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {R : RiemannSurface X} {S : RiemannSurface Y}

/-- The existing all-original-chart C¹ argument works at infinite smoothness. -/
theorem chartMap_contDiffOn_real_infty (f : SmoothSurfaceEquiv R S)
    (e : OriginalComplexChart R) (c : OriginalComplexChart S) :
    ContDiffOn ℝ ∞ (riemannChartMap e.val f.toHomeomorph c.val)
      (riemannChartMapDomain e.val f.toHomeomorph c.val) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  have heMax : e.val ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.subset_maximalAtlas e.property
  have hcMax : c.val ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ Y :=
    IsManifold.subset_maximalAtlas c.property
  intro z hz
  have hreal : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f.toHomeomorph :=
    f.contMDiff_toFun
  have hh := ((contMDiffAt_iff_of_mem_maximalAtlas heMax hcMax
    (e.val.map_target hz.1) hz.2).1
      (hreal.contMDiffAt (x := e.val.symm z))).2
  have hh' : ContDiffAt ℝ ∞ (riemannChartMap e.val f.toHomeomorph c.val) z := by
    simpa only [OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      Set.range_id, contDiffWithinAt_univ, riemannChartMap,
      e.val.right_inv hz.1] using hh
  exact hh'.contDiffWithinAt

/-- The genuine chart differential is an equivalence whenever the chart is valid. -/
def originalChartDifferentialEquiv (e : OriginalComplexChart R) (x : X)
    (hx : x ∈ e.val.source) : RealSurfaceTangent R x ≃L[ℝ] ℂ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact ((mdifferentiable_of_mem_atlas (I := 𝓘(ℝ, ℂ)) e.property).mfderiv hx).trans
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (e.val x))

@[simp]
theorem originalChartDifferentialEquiv_apply (e : OriginalComplexChart R) (x : X)
    (hx : x ∈ e.val.source) (v : RealSurfaceTangent R x) :
    originalChartDifferentialEquiv e x hx v = originalChartDifferential R e x v := rfl

/-- The native manifold derivative intertwines with every original coordinate map. -/
theorem chartDifferential_intertwines (f : SmoothSurfaceEquiv R S)
    (e : OriginalComplexChart R) (c : OriginalComplexChart S)
    (x : X) (he : x ∈ e.val.source) (hc : f.toHomeomorph x ∈ c.val.source)
    (v : RealSurfaceTangent R x) :
    fderiv ℝ (riemannChartMap e.val f.toHomeomorph c.val) (e.val x)
        (originalChartDifferential R e x v) =
      originalChartDifferential S c (f.toHomeomorph x)
        (surfaceDifferential R S f x v) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  let F := riemannChartMap e.val f.toHomeomorph c.val
  have hz : e.val x ∈ riemannChartMapDomain e.val f.toHomeomorph c.val := by
    refine ⟨e.val.map_source he, ?_⟩
    change f.toHomeomorph (e.val.symm (e.val x)) ∈ c.val.source
    simpa only [e.val.left_inv he] using hc
  have hdF : DifferentiableAt ℝ F (e.val x) :=
    ((f.chartMap_contDiffOn_real_infty e c).differentiableOn (by simp)).differentiableAt
      ((riemannChartMapDomain_isOpen e.val f.toHomeomorph c.val
        f.toHomeomorph.continuous).mem_nhds hz)
  have hde := mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) e.property he
  have hdc := mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) c.property hc
  have hdf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f.toHomeomorph x :=
    f.contMDiff_toFun.mdifferentiableAt (by simp)
  have hnear : F ∘ e.val =ᶠ[𝓝 x] c.val ∘ f.toHomeomorph := by
    filter_upwards [e.val.open_source.mem_nhds he] with y hy
    change c.val (f.toHomeomorph (e.val.symm (e.val y))) = c.val (f.toHomeomorph y)
    rw [e.val.left_inv hy]
  have hh := congrArg (fun A => A v)
    (hnear.mfderiv_eq (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)))
  rw [mfderiv_comp x hdF.mdifferentiableAt hde,
    mfderiv_comp x hdc hdf, mfderiv_eq_fderiv] at hh
  exact hh

/-- A local holomorphic homeomorphism has an actual conformal real differential. -/
theorem chartMap_isConformalMap_of_analytic (f : SmoothSurfaceEquiv R S)
    (han : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : OriginalComplexChart R) (c : OriginalComplexChart S)
    {z : ℂ} (hz : z ∈ riemannChartMapDomain e.val f.toHomeomorph c.val) :
    IsConformalMap (fderiv ℝ (riemannChartMap e.val f.toHomeomorph c.val) z) := by
  let F := riemannHomeomorphChart e.val f.toHomeomorph c.val
  have hF : AnalyticOnNhd ℂ F F.source := by
    rw [show F.source = riemannChartMapDomain e.val f.toHomeomorph c.val
      from riemannHomeomorphChart_source e.val f.toHomeomorph c.val]
    exact han.2 e.val e.property c.val c.property
  have hzF : z ∈ F.source := by
    rwa [show F.source = riemannChartMapDomain e.val f.toHomeomorph c.val
      from riemannHomeomorphChart_source e.val f.toHomeomorph c.val]
  exact (conformalAt_iff_isConformalMap_fderiv).mp
    ((hF z hzF).differentiableAt.conformalAt
      (openPartialHomeomorph_analytic_forward_deriv_ne_zero F hF z hzF))

end SmoothSurfaceEquiv

namespace AtlasInducedMetric

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {R : RiemannSurface X} {S : RiemannSurface Y}

/-- The explicit scale in a fixed pair of original isothermal charts. -/
def localScale (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S) (e : OriginalComplexChart R)
    (c : OriginalComplexChart S) (x : X) : ℝ :=
  h.density c (f.toHomeomorph x) *
      ‖fderiv ℝ (riemannChartMap e.val f.toHomeomorph c.val) (e.val x) 1‖ ^ 2 /
    g.density e x

theorem localScale_pos (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (han : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : OriginalComplexChart R) (c : OriginalComplexChart S)
    (x : X) (he : x ∈ e.val.source) (hc : f.toHomeomorph x ∈ c.val.source) :
    0 < localScale g h f e c x := by
  have hz : e.val x ∈ riemannChartMapDomain e.val f.toHomeomorph c.val := by
    refine ⟨e.val.map_source he, ?_⟩
    change f.toHomeomorph (e.val.symm (e.val x)) ∈ c.val.source
    simpa only [e.val.left_inv he] using hc
  have hL := f.chartMap_isConformalMap_of_analytic han e c hz
  have hn : fderiv ℝ (riemannChartMap e.val f.toHomeomorph c.val) (e.val x) 1 ≠ 0 := by
    intro hh
    exact one_ne_zero (hL.injective (hh.trans (map_zero _).symm))
  exact div_pos (mul_pos (h.density_pos c _ hc)
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hn))) (g.density_pos e x he)

/-- The pointwise metric identity in a fixed chart pair is proved from the
actual analytic coordinate differential. -/
theorem pullback_inner_eq_localScale (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (han : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : OriginalComplexChart R) (c : OriginalComplexChart S)
    (x : X) (he : x ∈ e.val.source) (hc : f.toHomeomorph x ∈ c.val.source)
    (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    let := S.toRiemannAtlas.isRealManifold
    h.metric.inner (f.toHomeomorph x)
        (surfaceDifferential R S f x v) (surfaceDifferential R S f x w) =
      localScale g h f e c x * g.metric.inner x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  change h.metric.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x v) (surfaceDifferential R S f x w) =
    localScale g h f e c x * g.metric.inner x v w
  have hz : e.val x ∈ riemannChartMapDomain e.val f.toHomeomorph c.val := by
    refine ⟨e.val.map_source he, ?_⟩
    change f.toHomeomorph (e.val.symm (e.val x)) ∈ c.val.source
    simpa only [e.val.left_inv he] using hc
  rw [h.inner_eq c _ hc, g.inner_eq e x he]
  rw [← f.chartDifferential_intertwines e c x he hc v,
    ← f.chartDifferential_intertwines e c x he hc w,
    conformal_inner_eq_norm_apply_one_sq (f.chartMap_isConformalMap_of_analytic han e c hz)]
  unfold localScale
  field_simp [(g.density_pos e x he).ne']

/-- A pointwise choice of a nonzero tangent vector through one actual chart. -/
def chosenFrame (R : RiemannSurface X) (x : X) : RealSurfaceTangent R x :=
  let e : OriginalComplexChart R := ⟨(R.cover x).choose, (R.cover x).choose_spec.1⟩
  (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (R.cover x).choose_spec.2).symm 1

theorem chosenFrame_ne_zero (R : RiemannSurface X) (x : X) : chosenFrame R x ≠ 0 := by
  let e : OriginalComplexChart R := ⟨(R.cover x).choose, (R.cover x).choose_spec.1⟩
  let T := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
    (R.cover x).choose_spec.2
  intro hz
  have hz' : T.symm 1 = 0 := hz
  apply (one_ne_zero : (1 : ℂ) ≠ 0)
  calc
    (1 : ℂ) = T (T.symm 1) := (T.apply_symm_apply 1).symm
    _ = T 0 := congrArg T hz'
    _ = 0 := map_zero T

/-- The pointwise ratio is defined independently of an analyticity proof. Its
chosen frame is not claimed to be a smooth global vector field. -/
def pullbackScale (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S) (x : X) : ℝ :=
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  h.metric.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x (chosenFrame R x))
      (surfaceDifferential R S f x (chosenFrame R x)) /
    g.metric.inner x (chosenFrame R x) (chosenFrame R x)

/-- Uniqueness on a nonzero tangent vector identifies the chosen-frame ratio
with the formula in every fixed original chart pair. -/
theorem pullbackScale_eq_localScale (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (han : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : OriginalComplexChart R) (c : OriginalComplexChart S)
    (x : X) (he : x ∈ e.val.source) (hc : f.toHomeomorph x ∈ c.val.source) :
    pullbackScale g h f x = localScale g h f e c x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  change h.metric.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x (chosenFrame R x))
      (surfaceDifferential R S f x (chosenFrame R x)) /
    g.metric.inner x (chosenFrame R x) (chosenFrame R x) = localScale g h f e c x
  rw [pullback_inner_eq_localScale g h f han e c x he hc]
  exact mul_div_cancel_right₀ _ (g.metric.pos x _ (chosenFrame_ne_zero R x)).ne'

theorem pullbackScale_pos (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (han : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (x : X) : 0 < pullbackScale g h f x := by
  obtain ⟨e, he, hxe⟩ := R.cover x
  obtain ⟨c, hc, hxc⟩ := S.cover (f.toHomeomorph x)
  rw [pullbackScale_eq_localScale g h f han ⟨e, he⟩ ⟨c, hc⟩ x hxe hxc]
  exact localScale_pos g h f han ⟨e, he⟩ ⟨c, hc⟩ x hxe hxc

/-- Each fixed-chart expression is smooth at every point where both charts are valid. -/
theorem localScale_contMDiffAt (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S) (e : OriginalComplexChart R)
    (c : OriginalComplexChart S) (x : X)
    (he : x ∈ e.val.source) (hc : f.toHomeomorph x ∈ c.val.source) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (localScale g h f e c) x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (localScale g h f e c) x
  let F := riemannChartMap e.val f.toHomeomorph c.val
  let D := riemannChartMapDomain e.val f.toHomeomorph c.val
  have hD : IsOpen D :=
    riemannChartMapDomain_isOpen e.val f.toHomeomorph c.val f.toHomeomorph.continuous
  have hz : e.val x ∈ D := by
    refine ⟨e.val.map_source he, ?_⟩
    change f.toHomeomorph (e.val.symm (e.val x)) ∈ c.val.source
    simpa only [e.val.left_inv he] using hc
  have hFD : ContDiffOn ℝ ∞ (fderiv ℝ F) D :=
    (f.chartMap_contDiffOn_real_infty e c).fderiv_of_isOpen hD (by simp)
  have hFone : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z 1) D :=
    hFD.clm_apply contDiffOn_const
  have hNorm : ContDiffAt ℝ ∞ (fun z => ‖fderiv ℝ F z 1‖ ^ 2) (e.val x) :=
    (contDiff_norm_sq ℝ).contDiffAt.comp (e.val x)
      (hFone.contDiffAt (hD.mem_nhds hz))
  have heSmooth : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.val x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) he
  have hNormNative := hNorm.comp_contMDiffAt heSmooth
  have hgρ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (g.density e) x :=
    (g.density_smooth e).contMDiffAt (e.val.open_source.mem_nhds he)
  have hhρ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (h.density c ∘ f.toHomeomorph) x :=
    ((h.density_smooth c).contMDiffAt (c.val.open_source.mem_nhds hc)).comp x
      f.contMDiff_toFun.contMDiffAt
  exact (hhρ.mul hNormNative).div₀ hgρ (g.density_pos e x he).ne'

/-- Local equality with fixed original chart formulas proves global smoothness;
there is no smoothness premise on the pointwise chosen frame. -/
theorem pullbackScale_contMDiff (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (han : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (pullbackScale g h f) := by
  let := R.toRiemannAtlas.toChartedSpace
  change ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (pullbackScale g h f)
  intro x
  obtain ⟨e, he, hxe⟩ := R.cover x
  obtain ⟨c, hc, hxc⟩ := S.cover (f.toHomeomorph x)
  have hnear : pullbackScale g h f =ᶠ[𝓝 x]
      localScale g h f ⟨e, he⟩ ⟨c, hc⟩ := by
    filter_upwards [e.open_source.mem_nhds hxe,
      (c.open_source.preimage f.toHomeomorph.continuous).mem_nhds hxc] with y hye hyc
    exact pullbackScale_eq_localScale g h f han ⟨e, he⟩ ⟨c, hc⟩ y hye hyc
  exact (localScale_contMDiffAt g h f ⟨e, he⟩ ⟨c, hc⟩ x hxe hxc).congr_of_eventuallyEq hnear

theorem metricConformal_of_analytic (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (han : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) :
    IsMetricConformal g h f := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  change ∃ φ : X → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ ∧
    ∀ (x : X) (v w : RealSurfaceTangent R x),
      h.metric.inner (f.toHomeomorph x)
          (surfaceDifferential R S f x v) (surfaceDifferential R S f x w) =
        Real.exp (φ x) * g.metric.inner x v w
  refine ⟨Real.log ∘ pullbackScale g h f, ?_, ?_⟩
  · intro x
    exact (Real.contDiffAt_log.mpr (pullbackScale_pos g h f han x).ne').comp_contMDiffAt
      (pullbackScale_contMDiff g h f han x)
  · intro x v w
    change _ = Real.exp (Real.log (pullbackScale g h f x)) * _
    rw [Real.exp_log (pullbackScale_pos g h f han x)]
    obtain ⟨e, he, hxe⟩ := R.cover x
    obtain ⟨c, hc, hxc⟩ := S.cover (f.toHomeomorph x)
    rw [pullbackScale_eq_localScale g h f han ⟨e, he⟩ ⟨c, hc⟩ x hxe hxc]
    exact pullback_inner_eq_localScale g h f han ⟨e, he⟩ ⟨c, hc⟩ x hxe hxc v w

theorem analytic_of_metricConformal (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (hor : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hconf : IsMetricConformal g h f) :
    RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  obtain ⟨φ, hφ, hpull⟩ := hconf
  refine ⟨f.toHomeomorph.continuous, ?_⟩
  intro e he c hc
  let E : OriginalComplexChart R := ⟨e, he⟩
  let C : OriginalComplexChart S := ⟨c, hc⟩
  let F := riemannChartMap e f.toHomeomorph c
  let D := riemannChartMapDomain e f.toHomeomorph c
  have hD : IsOpen D := riemannChartMapDomain_isOpen e f.toHomeomorph c f.toHomeomorph.continuous
  have hd : DifferentiableOn ℂ F D := by
    intro z hz
    let x := e.symm z
    have hxe : x ∈ e.source := e.map_target hz.1
    have hxc : f.toHomeomorph x ∈ c.source := hz.2
    have hex : e x = z := e.right_inv hz.1
    have hdR : DifferentiableAt ℝ F z :=
      ((f.chartMap_contDiffOn_real_infty E C).differentiableOn (by simp)).differentiableAt
        (hD.mem_nhds hz)
    apply (complexDifferentiableAt_of_inner_scaling hdR (hor e he c hc z hz) ?_).differentiableWithinAt
    refine ⟨Real.exp (φ x) * g.density E x / h.density C (f.toHomeomorph x),
      div_pos (mul_pos (Real.exp_pos _) (g.density_pos E x hxe)) (h.density_pos C _ hxc), ?_⟩
    intro a b
    let T := SmoothSurfaceEquiv.originalChartDifferentialEquiv E x hxe
    let v : RealSurfaceTangent R x := T.symm a
    let w : RealSurfaceTangent R x := T.symm b
    have hva : originalChartDifferential R E x v = a := T.apply_symm_apply a
    have hwb : originalChartDifferential R E x w = b := T.apply_symm_apply b
    have hlocal := hpull x v w
    rw [h.inner_eq C _ hxc, g.inner_eq E x hxe,
      ← f.chartDifferential_intertwines E C x hxe hxc v,
      ← f.chartDifferential_intertwines E C x hxe hxc w,
      hva, hwb, hex] at hlocal
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (h.density_pos C _ hxc).ne').mpr
    nlinarith [hlocal]
  exact hd.analyticOnNhd hD

/-- Metric conformality for the inducing complex atlases is equivalent to
biholomorphicity of the actual smooth equivalence. -/
theorem metricConformal_iff_biholomorphic
    (g : AtlasInducedMetric R) (h : AtlasInducedMetric S)
    (f : SmoothSurfaceEquiv R S)
    (hor : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) :
    IsMetricConformal g h f ↔
      (RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph ∧
        RiemannAnalyticMap S.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph.symm) := by
  constructor
  · intro hf
    have han := analytic_of_metricConformal g h f hor hf
    exact ⟨han, riemannAnalyticMap_homeomorph_symm f.toHomeomorph han⟩
  · intro hf
    exact metricConformal_of_analytic g h f hf.1

end AtlasInducedMetric

end LowDimensionalTopology.Geometry.Teichmuller
