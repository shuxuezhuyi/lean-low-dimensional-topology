module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricGaussianCurvatureScaleTwo
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricConformality

/-!
# The finite comparison of the two original curvature slices

The half metric stays on the same original tangent bundle. Doubling and
halving are inverse and commute with the actual smooth pullback. The same
realization covariance identifies the curvature of that pullback, so the
existing homotopy-identity automorphisms preserve both Gaussian level sets.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The inherited scalar action on this same native symmetric section space. -/
local instance canonicalCurvatureSliceTensorSMul : SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

private def halfOriginalMetric (g : SmoothSurfaceMetric R.toRiemannSurface) :
    SmoothSurfaceMetric R.toRiemannSurface := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let s : SmoothSymmetricTwoTensor R :=
    (1 / 2 : ℝ) • SmoothSurfaceMetric.toSymmetricTwoTensor R g
  refine
    { inner := s.val.toFun
      symm := ?_
      pos := ?_
      isVonNBounded := ?_
      contMDiff := s.val.contMDiff_toFun }
  · intro x v w
    change (1 / 2 : ℝ) * g.inner x v w = (1 / 2 : ℝ) * g.inner x w v
    rw [g.symm x v w]
  · intro x v hv
    change 0 < (1 / 2 : ℝ) * g.inner x v v
    exact mul_pos (by norm_num) (g.pos x v hv)
  · intro x
    let D : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x :=
      (2 : ℝ) • ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℂ) x)
    apply ((g.isVonNBounded x).image D).subset
    intro v hv
    change (1 / 2 : ℝ) * g.inner x v v < 1 at hv
    refine ⟨(1 / 2 : ℝ) • v, ?_, ?_⟩
    · change g.inner x ((1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v) < 1
      have hq : g.inner x ((1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v) =
          (1 / 4 : ℝ) * g.inner x v v := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      rw [hq]
      linarith only [hv]
    · change (2 : ℝ) • ((1 / 2 : ℝ) • v) = v
      rw [smul_smul]
      norm_num

private theorem halfOriginalMetric_inner
    (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X)
    (v w : RealSurfaceTangent R.toRiemannSurface x) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    (halfOriginalMetric R g).inner x v w = (1 / 2 : ℝ) * g.inner x v w := by
  rfl

/-- Public decomposition of the metric structure leaves only its inner data. -/
private theorem sameOriginalMetric_ext
    (g h : SmoothSurfaceMetric R.toRiemannSurface)
    (hinner :
      letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isRealManifold
      ∀ (x : X) (v w : RealSurfaceTangent R.toRiemannSurface x),
        g.inner x v w = h.inner x v w) : g = h := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have heq : g.inner = h.inner := by
    funext x
    ext v w
    exact hinner x v w
  cases g
  cases h
  cases heq
  rfl

/-- Read the pulled-back metric in g's actual isothermal realization,
using the actual composed marking and the same target density. -/
private theorem metricGaussianCurvature_pullback_same
    (hreg : Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (hcurv : Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature.{u})
    (hcov : Unproved.Teichmuller.OriginalMetricGaussianCurvatureCovariance.{u})
    (f : OrientedSurfaceAut R) (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X) :
    metricGaussianCurvature R hreg hcurv (SmoothSurfaceMetric.pullback f.smooth g) x =
      metricGaussianCurvature R hreg hcurv g (f.smooth.toHomeomorph x) := by
  let S : RiemannSurface (ULift.{0} X) :=
    rawMetricIsothermalSurface R.toRiemannSurface hreg g
  let m : SmoothSurfaceEquiv R.toRiemannSurface S :=
    rawMetricIsothermalMarking R.toRiemannSurface hreg g
  let G : AtlasInducedMetric S :=
    rawMetricIsothermalTargetMetric R.toRiemannSurface hreg g
  let F : SmoothSurfaceEquiv R.toRiemannSurface S := SmoothSurfaceEquiv.trans f.smooth m
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.isRealManifold
  have hrealization (p : X) (v w : RealSurfaceTangent R.toRiemannSurface p) :
      G.metric.inner (F.toHomeomorph p)
          (surfaceDifferential R.toRiemannSurface S F p v)
          (surfaceDifferential R.toRiemannSurface S F p w) =
        (SmoothSurfaceMetric.pullback f.smooth g).inner p v w := by
    change (SmoothSurfaceMetric.pullback (SmoothSurfaceEquiv.trans f.smooth m)
      G.metric).inner p v w = _
    rw [SmoothSurfaceMetric.pullback_trans_inner]
    change (SmoothSurfaceMetric.pullback m G.metric).inner (f.smooth.toHomeomorph p)
        (surfaceDifferential R.toRiemannSurface R.toRiemannSurface f.smooth p v)
        (surfaceDifferential R.toRiemannSurface R.toRiemannSurface f.smooth p w) =
      g.inner (f.smooth.toHomeomorph p)
        (surfaceDifferential R.toRiemannSurface R.toRiemannSurface f.smooth p v)
        (surfaceDifferential R.toRiemannSurface R.toRiemannSurface f.smooth p w)
    exact rawMetricIsothermalTargetMetric_pullback_inner R.toRiemannSurface hreg g
      (f.smooth.toHomeomorph p) _ _
  let Kp : X → ℝ :=
    metricGaussianCurvature R hreg hcurv (SmoothSurfaceMetric.pullback f.smooth g)
  let Kg : X → ℝ := metricGaussianCurvature R hreg hcurv g
  have hKp := (metricGaussianCurvature_spec R hreg hcurv
    (SmoothSurfaceMetric.pullback f.smooth g)).2
  have hKg := (metricGaussianCurvature_spec R hreg hcurv g).2
  have hcovp := hcov X R hreg (SmoothSurfaceMetric.pullback f.smooth g)
    Kp hKp S F G hrealization
  let y := m.toHomeomorph (f.smooth.toHomeomorph x)
  let e : OriginalComplexChart S := ⟨chartAt ℂ y, chart_mem_atlas ℂ y⟩
  have hy : y ∈ e.val.source := mem_chart_source ℂ y
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  have hxF : (SmoothSurfaceEquiv.symm F).toHomeomorph
      (e.val.symm (e.val y)) = x := by
    rw [e.val.left_inv hy]
    change F.toHomeomorph.symm (F.toHomeomorph x) = x
    exact F.toHomeomorph.symm_apply_apply x
  have hxm : (SmoothSurfaceEquiv.symm m).toHomeomorph
      (e.val.symm (e.val y)) = f.smooth.toHomeomorph x := by
    rw [e.val.left_inv hy]
    exact m.toHomeomorph.symm_apply_apply (f.smooth.toHomeomorph x)
  have hc := hcovp e (e.val y) hz
  have hg := hKg e (e.val y) hz
  have heq : Kp ((SmoothSurfaceEquiv.symm F).toHomeomorph (e.val.symm (e.val y))) =
      Kg ((SmoothSurfaceEquiv.symm m).toHomeomorph (e.val.symm (e.val y))) :=
    hc.trans hg.symm
  simpa only [hxF, hxm] using heq

/-- The literal double/half curvature-slice bijection and its compatibility
with the same actual pullback of homotopy-identity automorphisms. -/
theorem exists_original_curvature_slice_scaleTwo_equiv
    (hreg : Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (hcurv : Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature.{u})
    (hcov : Unproved.Teichmuller.OriginalMetricGaussianCurvatureCovariance.{u}) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ∃ H : SmoothSurfaceMetric R.toRiemannSurface →
        SmoothSurfaceMetric R.toRiemannSurface,
      (∀ (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X)
          (v w : RealSurfaceTangent R.toRiemannSurface x),
        (H g).inner x v w = (1 / 2 : ℝ) * g.inner x v w) ∧
      (∀ g, scaleTwoOriginalMetric R (H g) = g) ∧
      (∀ g, H (scaleTwoOriginalMetric R g) = g) ∧
      (∀ (f : OrientedSurfaceAut R) (g : SmoothSurfaceMetric R.toRiemannSurface),
        scaleTwoOriginalMetric R (SmoothSurfaceMetric.pullback f.smooth g) =
            SmoothSurfaceMetric.pullback f.smooth (scaleTwoOriginalMetric R g) ∧
          H (SmoothSurfaceMetric.pullback f.smooth g) =
            SmoothSurfaceMetric.pullback f.smooth (H g)) ∧
      (∀ (f : OrientedSurfaceAut.homotopyIdentitySubgroup R)
          (g : SmoothSurfaceMetric R.toRiemannSurface),
        g ∈ curvatureMinusOneMetrics R hreg hcurv →
          SmoothSurfaceMetric.pullback f.val.smooth g ∈
            curvatureMinusOneMetrics R hreg hcurv) ∧
      (∀ (f : OrientedSurfaceAut.homotopyIdentitySubgroup R)
          (g : SmoothSurfaceMetric R.toRiemannSurface),
        g ∈ gaussianCurvatureMinusHalfMetrics R hreg hcurv →
          SmoothSurfaceMetric.pullback f.val.smooth g ∈
            gaussianCurvatureMinusHalfMetrics R hreg hcurv) ∧
      ∃ E : ↥(curvatureMinusOneMetrics R hreg hcurv) ≃
          ↥(gaussianCurvatureMinusHalfMetrics R hreg hcurv),
        (∀ g, (E g).val = scaleTwoOriginalMetric R g.val) ∧
        (∀ g, (E.symm g).val = H g.val) ∧
        ∀ (f : OrientedSurfaceAut.homotopyIdentitySubgroup R)
          (g : ↥(curvatureMinusOneMetrics R hreg hcurv))
          (hp : SmoothSurfaceMetric.pullback f.val.smooth g.val ∈
            curvatureMinusOneMetrics R hreg hcurv),
          (E ⟨SmoothSurfaceMetric.pullback f.val.smooth g.val, hp⟩).val =
            SmoothSurfaceMetric.pullback f.val.smooth (E g).val := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have hdoubleHalf (g : SmoothSurfaceMetric R.toRiemannSurface) :
      scaleTwoOriginalMetric R (halfOriginalMetric R g) = g := by
    apply sameOriginalMetric_ext R
    intro x v w
    rw [scaleTwoOriginalMetric_inner, halfOriginalMetric_inner]
    ring
  have hhalfDouble (g : SmoothSurfaceMetric R.toRiemannSurface) :
      halfOriginalMetric R (scaleTwoOriginalMetric R g) = g := by
    apply sameOriginalMetric_ext R
    intro x v w
    rw [halfOriginalMetric_inner, scaleTwoOriginalMetric_inner]
    ring
  have hcommute (f : OrientedSurfaceAut R) (g : SmoothSurfaceMetric R.toRiemannSurface) :
      scaleTwoOriginalMetric R (SmoothSurfaceMetric.pullback f.smooth g) =
          SmoothSurfaceMetric.pullback f.smooth (scaleTwoOriginalMetric R g) ∧
        halfOriginalMetric R (SmoothSurfaceMetric.pullback f.smooth g) =
          SmoothSurfaceMetric.pullback f.smooth (halfOriginalMetric R g) := by
    constructor
    · apply sameOriginalMetric_ext R
      intro x v w
      rfl
    · apply sameOriginalMetric_ext R
      intro x v w
      rfl
  have hforward (g : SmoothSurfaceMetric R.toRiemannSurface)
      (hg : g ∈ curvatureMinusOneMetrics R hreg hcurv) :
      scaleTwoOriginalMetric R g ∈ gaussianCurvatureMinusHalfMetrics R hreg hcurv := by
    intro x
    change metricGaussianCurvature R hreg hcurv (scaleTwoOriginalMetric R g) x = -(1 / 2 : ℝ)
    rw [metricGaussianCurvature_scaleTwo R hreg hcurv hcov g x, hg x]
    norm_num
  have hbackward (g : SmoothSurfaceMetric R.toRiemannSurface)
      (hg : g ∈ gaussianCurvatureMinusHalfMetrics R hreg hcurv) :
      halfOriginalMetric R g ∈ curvatureMinusOneMetrics R hreg hcurv := by
    intro x
    have hs := metricGaussianCurvature_scaleTwo R hreg hcurv hcov (halfOriginalMetric R g) x
    rw [hdoubleHalf g] at hs
    have hlevel := hg x
    change metricGaussianCurvature R hreg hcurv (halfOriginalMetric R g) x = -1
    linarith only [hs, hlevel]
  have hminusOne (f : OrientedSurfaceAut.homotopyIdentitySubgroup R)
      (g : SmoothSurfaceMetric R.toRiemannSurface)
      (hg : g ∈ curvatureMinusOneMetrics R hreg hcurv) :
      SmoothSurfaceMetric.pullback f.val.smooth g ∈ curvatureMinusOneMetrics R hreg hcurv := by
    intro x
    rw [metricGaussianCurvature_pullback_same R hreg hcurv hcov f.val g x]
    exact hg (f.val.smooth.toHomeomorph x)
  have hminusHalf (f : OrientedSurfaceAut.homotopyIdentitySubgroup R)
      (g : SmoothSurfaceMetric R.toRiemannSurface)
      (hg : g ∈ gaussianCurvatureMinusHalfMetrics R hreg hcurv) :
      SmoothSurfaceMetric.pullback f.val.smooth g ∈
        gaussianCurvatureMinusHalfMetrics R hreg hcurv := by
    intro x
    rw [metricGaussianCurvature_pullback_same R hreg hcurv hcov f.val g x]
    exact hg (f.val.smooth.toHomeomorph x)
  let E : ↥(curvatureMinusOneMetrics R hreg hcurv) ≃
      ↥(gaussianCurvatureMinusHalfMetrics R hreg hcurv) :=
    { toFun := fun g => ⟨scaleTwoOriginalMetric R g.val, hforward g.val g.property⟩
      invFun := fun g => ⟨halfOriginalMetric R g.val, hbackward g.val g.property⟩
      left_inv := by
        intro g
        apply Subtype.ext
        exact hhalfDouble g.val
      right_inv := by
        intro g
        apply Subtype.ext
        exact hdoubleHalf g.val }
  refine ⟨halfOriginalMetric R, ?_, hdoubleHalf, hhalfDouble, hcommute,
    hminusOne, hminusHalf, E, ?_, ?_, ?_⟩
  · intro g x v w
    exact halfOriginalMetric_inner R g x v w
  · intro g
    rfl
  · intro g
    rfl
  · intro f g hp
    change scaleTwoOriginalMetric R (SmoothSurfaceMetric.pullback f.val.smooth g.val) =
      SmoothSurfaceMetric.pullback f.val.smooth (scaleTwoOriginalMetric R g.val)
    exact (hcommute f.val g.val).1

end LowDimensionalTopology.Geometry.Teichmuller
