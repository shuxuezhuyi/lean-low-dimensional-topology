module

public import LowDimensionalTopology.Geometry.Teichmuller.MetricBeltramiPullback
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Conformal pullback equations for arbitrary original smooth metrics

Every metric here is a full smooth positive definite metric on its original
real tangent bundle. The pullback equation composes and inverts along the
actual given smooth equivalences. Orientation is imposed on the reference
automorphisms in `RawMetricEquivalence`, where these equations are consumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v w

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {R : RiemannSurface X} {S : RiemannSurface Y} {T : RiemannSurface Z}

/-- The derivative of the actual composite is the composite of the actual
original-tangent derivatives. -/
theorem surfaceDifferential_trans_apply
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv S T)
    (x : X) (a : RealSurfaceTangent R x) :
    surfaceDifferential R T (trans f g) x a =
      surfaceDifferential S T g (f.toHomeomorph x)
        (surfaceDifferential R S f x a) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := T.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  let := T.toRiemannAtlas.isRealManifold
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g.toHomeomorph ∘ f.toHomeomorph) x a = _
  exact mfderiv_comp_apply x
    (g.contMDiff_toFun.mdifferentiable (by simp) (f.toHomeomorph x))
    (f.contMDiff_toFun.mdifferentiable (by simp) x) a

end SmoothSurfaceEquiv

namespace SmoothSurfaceMetric

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {R : RiemannSurface X} {S : RiemannSurface Y} {T : RiemannSurface Z}

/-- Metric pullback composes on every original tangent pair, with no equality
of unrelated tangent-space presentations. -/
theorem pullback_trans_inner
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv S T)
    (h : SmoothSurfaceMetric T) (x : X) (a b : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (pullback (SmoothSurfaceEquiv.trans f g) h).inner x a b =
      (pullback f (pullback g h)).inner x a b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := T.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  let := T.toRiemannAtlas.isRealManifold
  rw [pullback_inner, pullback_inner, pullback_inner]
  rw [SmoothSurfaceEquiv.surfaceDifferential_trans_apply,
    SmoothSurfaceEquiv.surfaceDifferential_trans_apply]
  rfl

/-- Pulling back by the actual identity preserves each original metric entry. -/
theorem pullback_refl_inner (g : SmoothSurfaceMetric R)
    (x : X) (a b : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (pullback (SmoothSurfaceEquiv.refl R) g).inner x a b = g.inner x a b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  rw [pullback_inner]
  change g.inner x (surfaceDifferential R R (SmoothSurfaceEquiv.refl R) x a)
    (surfaceDifferential R R (SmoothSurfaceEquiv.refl R) x b) = g.inner x a b
  rw [surfaceDifferential_refl_apply R x a, surfaceDifferential_refl_apply R x b]

end SmoothSurfaceMetric

/-- A globally smooth exponential pullback equation for two arbitrary original
metrics along a given actual smooth surface equivalence. -/
def IsRawMetricConformal
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (g : SmoothSurfaceMetric R) (h : SmoothSurfaceMetric S)
    (f : SmoothSurfaceEquiv R S) : Prop :=
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  ∃ φ : X → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ ∧
    ∀ (x : X) (a b : RealSurfaceTangent R x),
      h.inner (f.toHomeomorph x)
          (surfaceDifferential R S f x a) (surfaceDifferential R S f x b) =
        Real.exp (φ x) * g.inner x a b

namespace IsRawMetricConformal

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {R : RiemannSurface X} {S : RiemannSurface Y} {T : RiemannSurface Z}

/-- A metric is conformal to itself by the actual identity. -/
theorem refl (g : SmoothSurfaceMetric R) :
    IsRawMetricConformal g g (SmoothSurfaceEquiv.refl R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  refine ⟨fun _ => 0, contMDiff_const, ?_⟩
  intro x a b
  change g.inner x (surfaceDifferential R R (SmoothSurfaceEquiv.refl R) x a)
    (surfaceDifferential R R (SmoothSurfaceEquiv.refl R) x b) = Real.exp 0 * g.inner x a b
  rw [surfaceDifferential_refl_apply R x a, surfaceDifferential_refl_apply R x b,
    Real.exp_zero, one_mul]

/-- The original marking is an isometry from its actual pullback metric. -/
theorem pullback (f : SmoothSurfaceEquiv R S) (h : SmoothSurfaceMetric S) :
    IsRawMetricConformal (SmoothSurfaceMetric.pullback f h) h f := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  refine ⟨fun _ => 0, contMDiff_const, ?_⟩
  intro x a b
  simpa only [Real.exp_zero, one_mul] using
    (SmoothSurfaceMetric.pullback_inner f h x a b).symm

/-- Conformal pullback composes with the sum of the two actual smooth
exponents, the second composed with the first given map. -/
theorem trans {g : SmoothSurfaceMetric R} {h : SmoothSurfaceMetric S}
    {k : SmoothSurfaceMetric T} {f : SmoothSurfaceEquiv R S}
    {j : SmoothSurfaceEquiv S T} (hf : IsRawMetricConformal g h f)
    (hj : IsRawMetricConformal h k j) :
    IsRawMetricConformal g k (SmoothSurfaceEquiv.trans f j) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := T.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  let := T.toRiemannAtlas.isRealManifold
  obtain ⟨φ, hφ, hscale⟩ := hf
  obtain ⟨ψ, hψ, jscale⟩ := hj
  refine ⟨fun x => φ x + ψ (f.toHomeomorph x), hφ.add (hψ.comp f.contMDiff_toFun), ?_⟩
  intro x a b
  rw [SmoothSurfaceEquiv.surfaceDifferential_trans_apply,
    SmoothSurfaceEquiv.surfaceDifferential_trans_apply]
  change k.inner (j.toHomeomorph (f.toHomeomorph x)) _ _ = _
  rw [jscale, hscale, Real.exp_add]
  ring

/-- The actual inverse is conformal with the negative pulled-back exponent.
The inverse identity is proved using genuine derivative pullback composition. -/
theorem symm {g : SmoothSurfaceMetric R} {h : SmoothSurfaceMetric S}
    {f : SmoothSurfaceEquiv R S} (hf : IsRawMetricConformal g h f) :
    IsRawMetricConformal h g (SmoothSurfaceEquiv.symm f) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  obtain ⟨φ, hφ, hscale⟩ := hf
  let j := SmoothSurfaceEquiv.symm f
  refine ⟨fun y => -φ (j.toHomeomorph y), (hφ.comp j.contMDiff_toFun).neg, ?_⟩
  intro y a b
  have hj : SmoothSurfaceEquiv.trans j f = SmoothSurfaceEquiv.refl S :=
    Diffeomorph.symm_trans_self f
  have hs := hscale (j.toHomeomorph y)
    (surfaceDifferential S R j y a) (surfaceDifferential S R j y b)
  change (SmoothSurfaceMetric.pullback j (SmoothSurfaceMetric.pullback f h)).inner y a b =
    Real.exp (φ (j.toHomeomorph y)) *
      (SmoothSurfaceMetric.pullback j g).inner y a b at hs
  rw [← SmoothSurfaceMetric.pullback_trans_inner, hj,
    SmoothSurfaceMetric.pullback_refl_inner] at hs
  change (SmoothSurfaceMetric.pullback j g).inner y a b =
    Real.exp (-φ (j.toHomeomorph y)) * h.inner y a b
  rw [hs, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end IsRawMetricConformal

/-- The existing conformal equation for compatible metrics is exactly the
same full original-tangent equation after forgetting atlas compatibility. -/
theorem IsMetricConformal.raw
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    {g : AtlasInducedMetric R} {h : AtlasInducedMetric S}
    {f : SmoothSurfaceEquiv R S} (hf : IsMetricConformal g h f) :
    IsRawMetricConformal g.metric h.metric f := hf

end LowDimensionalTopology.Geometry.Teichmuller
