module

public import LowDimensionalTopology.Geometry.Teichmuller.MetricBeltramiGram
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricPullback
public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMetricExistence
public import LowDimensionalTopology.Geometry.Teichmuller.MappingClassGroup
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The actual metric corresponding to an original smooth marking

Choose a compatible metric on the given marked target and pull it back by the
very same marking. Its coefficient is computed from its actual Gram matrix in
every original source chart, and equals the marking's actual Wirtinger ratio.
The output is a full smooth metric, not a metric compatible with the original
reference complex structure. No isothermal-realization result for arbitrary
metrics or metric-quotient classification is asserted here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v

/-- Compute the literal coefficient of an arbitrary smooth metric from its
real E,F,G entries in a valid original complex chart. -/
def metricBeltramiInOriginalChart
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) : ℂ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  exact metricBeltramiFromGram
    (g.inner x (D.symm 1) (D.symm 1))
    (g.inner x (D.symm 1) (D.symm Complex.I))
    (g.inner x (D.symm Complex.I) (D.symm Complex.I))

/-- The actual pullback metric has, in EVERY original source chart, precisely
the coefficient of the SAME original orientation-preserving smooth marking. -/
theorem pullback_metricBeltrami_eq_marking
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (h : AtlasInducedMetric S) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) :
    metricBeltramiInOriginalChart (SmoothSurfaceMetric.pullback f h.metric) e x hx =
      f.rawBeltramiCoefficient e (e.val x) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  obtain ⟨c, hc, hfc⟩ := S.cover (f.toHomeomorph x)
  let C : OriginalComplexChart S := ⟨c, hc⟩
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let F : ℂ → ℂ := riemannChartMap e.val f.toHomeomorph C.val
  let p : ℂ := LiZhongQC.dz F (e.val x)
  let q : ℂ := LiZhongQC.dzbar F (e.val x)
  have hdom : e.val x ∈ riemannChartMapDomain e.val f.toHomeomorph C.val := by
    refine ⟨e.val.map_source hx, ?_⟩
    change f.toHomeomorph (e.val.symm (e.val x)) ∈ C.val.source
    simpa only [e.val.left_inv hx] using hfc
  have hfd : DifferentiableAt ℝ F (e.val x) :=
    ((f.chartMap_contDiffOn_real_infty e C).differentiableOn (by simp)).differentiableAt
      ((riemannChartMapDomain_isOpen e.val f.toHomeomorph C.val
        f.toHomeomorph.continuous).mem_nhds hdom)
  have hD (a : ℂ) : originalChartDifferential R e x (D.symm a) = a :=
    D.apply_symm_apply a
  have himage (a : ℂ) : originalChartDifferential S C (f.toHomeomorph x)
      (surfaceDifferential R S f x (D.symm a)) = fderiv ℝ F (e.val x) a := by
    have hi := f.chartDifferential_intertwines e C x hx hfc (D.symm a)
    rw [hD a] at hi
    exact hi.symm
  have hGram (a b : ℂ) : (SmoothSurfaceMetric.pullback f h.metric).inner x
      (D.symm a) (D.symm b) = h.density C (f.toHomeomorph x) *
        ⟪fderiv ℝ F (e.val x) a, fderiv ℝ F (e.val x) b⟫_ℝ := by
    rw [SmoothSurfaceMetric.pullback_inner,
      h.inner_eq C (f.toHomeomorph x) hfc, himage a, himage b]
  have hu : fderiv ℝ F (e.val x) 1 = p + q := by
    simpa only [p, q, map_one, mul_one] using
      LiZhongQC.fderiv_eq_dz_dzbar hfd (1 : ℂ)
  have hv : fderiv ℝ F (e.val x) Complex.I = p * Complex.I - q * Complex.I := by
    simpa only [p, q, Complex.conj_I, mul_neg, sub_eq_add_neg] using
      LiZhongQC.fderiv_eq_dz_dzbar hfd Complex.I
  have hqp : ‖q‖ < ‖p‖ := f.chartMap_wirtinger_lt hf
    e.val e.property C.val C.property hdom
  change metricBeltramiFromGram
    ((SmoothSurfaceMetric.pullback f h.metric).inner x (D.symm 1) (D.symm 1))
    ((SmoothSurfaceMetric.pullback f h.metric).inner x (D.symm 1) (D.symm Complex.I))
    ((SmoothSurfaceMetric.pullback f h.metric).inner x
      (D.symm Complex.I) (D.symm Complex.I)) = _
  rw [hGram 1 1, hGram 1 Complex.I, hGram Complex.I Complex.I, hu, hv]
  simp only [real_inner_self_eq_norm_sq]
  rw [metricBeltramiFromGram_of_wirtinger _ p q (h.density_pos C _ hfc) hqp]
  rw [f.rawBeltramiCoefficient_eq_chartDilatation e (e.val.map_source hx)
    C.val C.property (by simpa only [e.val.left_inv hx] using hfc)]
  rfl

/-- The identity has the genuine identity differential on the original tangent
bundle. No choice of tangent coordinates or tangent topology is changed. -/
theorem surfaceDifferential_refl_apply
    {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)
    (x : X) (v : RealSurfaceTangent R x) :
    surfaceDifferential R R (SmoothSurfaceEquiv.refl R) x v = v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : X → X) x) v = v
  rw [mfderiv_id]
  rfl

/-- Changing the compatible metric on the SAME target changes the two actual
pullbacks by one globally smooth positive conformal factor on the original R. -/
theorem pullback_compatible_metrics_identity_scale
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (f : SmoothSurfaceEquiv R S) (h k : AtlasInducedMetric S) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∃ φ : X → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ ∧
      ∀ (x : X) (v w : RealSurfaceTangent R x),
        (SmoothSurfaceMetric.pullback f k.metric).inner x v w =
          Real.exp (φ x) * (SmoothSurfaceMetric.pullback f h.metric).inner x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  have han : RiemannAnalyticMap S.toRiemannAtlas S.toRiemannAtlas
      (SmoothSurfaceEquiv.refl S).toHomeomorph := by
    change RiemannAnalyticMap S.toRiemannAtlas S.toRiemannAtlas (id : Y → Y)
    exact RiemannAnalyticMap.id _
  obtain ⟨ψ, hψ, hscale⟩ :=
    AtlasInducedMetric.metricConformal_of_analytic h k (SmoothSurfaceEquiv.refl S) han
  refine ⟨ψ ∘ f.toHomeomorph, hψ.comp f.contMDiff_toFun, ?_⟩
  intro x v w
  rw [SmoothSurfaceMetric.pullback_inner, SmoothSurfaceMetric.pullback_inner]
  have hh := hscale (f.toHomeomorph x)
    (surfaceDifferential R S f x v) (surfaceDifferential R S f x w)
  change k.metric.inner (f.toHomeomorph x)
      (surfaceDifferential S S (SmoothSurfaceEquiv.refl S) (f.toHomeomorph x)
        (surfaceDifferential R S f x v))
      (surfaceDifferential S S (SmoothSurfaceEquiv.refl S) (f.toHomeomorph x)
        (surfaceDifferential R S f x w)) =
    Real.exp (ψ (f.toHomeomorph x)) * h.metric.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x v) (surfaceDifferential R S f x w) at hh
  rw [surfaceDifferential_refl_apply S (f.toHomeomorph x) (surfaceDifferential R S f x v),
    surfaceDifferential_refl_apply S (f.toHomeomorph x) (surfaceDifferential R S f x w)] at hh
  simpa only [Function.comp_apply] using hh

/-- The conformal change is witnessed by an ACTUAL reference automorphism in
Diff₀: the identity itself. This is the full strong-equivalence witness for the
two raw smooth pullback metrics, without a metric-quotient assumption. -/
theorem pullback_compatible_metrics_strong_witness
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) {S : RiemannSurface Y}
    (f : SmoothSurfaceEquiv R.toRiemannSurface S) (h k : AtlasInducedMetric S) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∃ a : OrientedSurfaceAut R,
      a ∈ OrientedSurfaceAut.homotopyIdentitySubgroup R ∧
      ∃ φ : X → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ ∧
        ∀ (x : X) (v w : RealSurfaceTangent R.toRiemannSurface x),
          (SmoothSurfaceMetric.pullback f k.metric).inner (a.toHomeomorph x)
              (surfaceDifferential R.toRiemannSurface R.toRiemannSurface a.smooth x v)
              (surfaceDifferential R.toRiemannSurface R.toRiemannSurface a.smooth x w) =
            Real.exp (φ x) * (SmoothSurfaceMetric.pullback f h.metric).inner x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  obtain ⟨φ, hφ, hscale⟩ := pullback_compatible_metrics_identity_scale f h k
  refine ⟨1, (OrientedSurfaceAut.homotopyIdentitySubgroup R).one_mem, φ, hφ, ?_⟩
  intro x v w
  change (SmoothSurfaceMetric.pullback f k.metric).inner x
    (surfaceDifferential R.toRiemannSurface R.toRiemannSurface
      (SmoothSurfaceEquiv.refl R.toRiemannSurface) x v)
    (surfaceDifferential R.toRiemannSurface R.toRiemannSurface
      (SmoothSurfaceEquiv.refl R.toRiemannSurface) x w) = _
  simpa only [surfaceDifferential_refl_apply] using hscale x v w

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- A compatible metric is selected on the actual marked target itself. Its
existence follows from the original target surface alone. -/
def compatibleTargetMetric (M : MarkedRiemannSurface.{u, v} R) :
    AtlasInducedMetric M.surface.toRiemannSurface :=
  Classical.choice (exists_atlasInducedMetric M.surface.toRiemannSurface)

/-- The actual original marking pulls the selected target metric back to the
full smooth metric space of the SAME original reference surface. -/
def correspondingMetric (M : MarkedRiemannSurface.{u, v} R) :
    SmoothSurfaceMetric R.toRiemannSurface :=
  SmoothSurfaceMetric.pullback M.marking M.compatibleTargetMetric.metric

/-- All original chart coefficients agree pointwise with the original marking;
no prescribed pullback, coordinate realization or isothermal premise is used. -/
theorem correspondingMetric_beltrami
    (M : MarkedRiemannSurface.{u, v} R) (e : OriginalComplexChart R.toRiemannSurface)
    (x : X) (hx : x ∈ e.val.source) :
    metricBeltramiInOriginalChart M.correspondingMetric e x hx =
      M.marking.rawBeltramiCoefficient e (e.val x) :=
  pullback_metricBeltrami_eq_marking M.marking M.orientation_preserving
    M.compatibleTargetMetric e x hx

end MarkedRiemannSurface

end LowDimensionalTopology.Geometry.Teichmuller
