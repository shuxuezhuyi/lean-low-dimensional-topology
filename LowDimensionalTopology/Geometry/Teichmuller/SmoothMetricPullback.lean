module

public import LowDimensionalTopology.Geometry.Teichmuller.RiemannianConformality
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Pull back an actual smooth metric by the actual smooth surface marking

The pullback uses the derivative of the given map on the original tangent
bundles. Its smoothness is proved in nested Hom coordinates, and bounded unit
sublevels follow by the actual inverse derivative. No new tangent topology or
compatible-atlas restriction is placed on the resulting metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Bundle Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}

/-- The derivative of the actual diffeomorphism is a genuine equivalence on the
original tangent spaces; its inverse is the derivative of the actual inverse. -/
def differentialEquiv (f : SmoothSurfaceEquiv R S) (x : X) :
    RealSurfaceTangent R x ≃L[ℝ] RealSurfaceTangent S (f.toHomeomorph x) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  exact (f.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv (by simp)

/-- The equivalence has exactly the original manifold derivative as its map. -/
theorem differentialEquiv_apply (f : SmoothSurfaceEquiv R S) (x : X)
    (a : RealSurfaceTangent R x) :
    f.differentialEquiv x a = surfaceDifferential R S f x a := rfl

end SmoothSurfaceEquiv

namespace SmoothSurfaceMetric

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}

/-- The literal pullback form on the original tangent space at each point. -/
def pullbackForm (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceMetric S) (x : X) :
    RealSurfaceTangent R x →L[ℝ] RealSurfaceTangent R x →L[ℝ] ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  letI : IsNormableSpace ℝ (RealSurfaceTangent R x) := by
    let e : OriginalComplexChart R := ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
    exact (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
      (mem_chart_source ℂ x)).isNormableSpace
  letI : IsNormableSpace ℝ (RealSurfaceTangent S (f.toHomeomorph x)) := by
    let e : OriginalComplexChart S :=
      ⟨chartAt ℂ (f.toHomeomorph x), chart_mem_atlas ℂ (f.toHomeomorph x)⟩
    exact (SmoothSurfaceEquiv.originalChartDifferentialEquiv e (f.toHomeomorph x)
      (mem_chart_source ℂ (f.toHomeomorph x))).isNormableSpace
  exact (g.inner (f.toHomeomorph x)).bilinearComp
    (surfaceDifferential R S f x) (surfaceDifferential R S f x)

/-- The literal derivative pullback is smooth in the original nested Hom bundle. -/
theorem pullbackForm_contMDiff (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceMetric S) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
        (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
          TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) x (pullbackForm f g x)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  change ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) ∞
    (fun x => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
        (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
          TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) x (pullbackForm f g x))
  intro x₀
  apply (contMDiffAt_section x₀).mpr
  let D : X → ℂ →L[ℝ] ℂ := inTangentCoordinates 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
    id f.toHomeomorph (surfaceDifferential R S f) x₀
  let B : X → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fun x =>
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
      (ℂ →L[ℝ] ℝ) (fun y : Y => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ)
      (f.toHomeomorph x₀) (f.toHomeomorph x)
      (f.toHomeomorph x₀) (f.toHomeomorph x) (g.inner (f.toHomeomorph x))
  have hD : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞ D x₀ := by
    exact (f.contMDiff_toFun.contMDiffAt).mfderiv_const (by simp)
  have hB : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ B x₀ := by
    have hg := (g.contMDiff (f.toHomeomorph x₀)).comp x₀
      (f.contMDiff_toFun.contMDiffAt)
    simp only [contMDiffAt_hom_bundle] at hg
    exact hg.2
  let : NormedAddCommGroup (ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℝ)
  let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)
  let flipForm : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ ℂ ℂ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hflip : ContMDiff 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ flipForm :=
    ContinuousLinearMap.contMDiff (𝕜 := ℝ)
      (E := ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (F := ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (n := ∞) flipForm
  have hQ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun x => (B x).bilinearComp (D x) (D x)) x₀ := by
    change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun x => flipForm ((flipForm ((B x).comp (D x))).comp (D x))) x₀
    exact hflip.contMDiffAt.comp x₀
      ((hflip.contMDiffAt.comp x₀ (hB.clm_comp hD)).clm_comp hD)
  apply hQ.congr_of_eventuallyEq
  let tR := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) x₀
  let tS := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) (f.toHomeomorph x₀)
  have hxR : x₀ ∈ tR.baseSet := mem_baseSet_trivializationAt _ _ _
  have hxS : f.toHomeomorph x₀ ∈ tS.baseSet := mem_baseSet_trivializationAt _ _ _
  filter_upwards [tR.open_baseSet.mem_nhds hxR,
    f.toHomeomorph.continuous.continuousAt (tS.open_baseSet.mem_nhds hxS)] with x hx hy
  ext a b
  change ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
      (ℂ →L[ℝ] ℝ) (fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ)
      x₀ x x₀ x (pullbackForm f g x) a b =
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
      (ℂ →L[ℝ] ℝ) (fun y : Y => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ)
      (f.toHomeomorph x₀) (f.toHomeomorph x)
      (f.toHomeomorph x₀) (f.toHomeomorph x) (g.inner (f.toHomeomorph x))
        (D x a) (D x b)
  rw [inCoordinates_apply_eq₂ hx hx (Set.mem_univ x),
    inCoordinates_apply_eq₂ hy hy (Set.mem_univ (f.toHomeomorph x))]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  have hDx (a : ℂ) : tS.symm (f.toHomeomorph x) (D x a) =
      surfaceDifferential R S f x (tR.symm x a) := by
    rw [← tS.symmL_apply (R := ℝ) (F := ℂ)
      (E := fun y : Y => TangentSpace 𝓘(ℝ, ℂ) y) hy,
      ← tR.symmL_apply (R := ℝ) (F := ℂ)
        (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y) hx]
    change tS.symmL ℝ (f.toHomeomorph x)
      (tS.continuousLinearMapAt ℝ (f.toHomeomorph x)
        (surfaceDifferential R S f x (tR.symmL ℝ x a))) = _
    exact tS.symmL_continuousLinearMapAt (R := ℝ) (F := ℂ)
      (E := fun y : Y => TangentSpace 𝓘(ℝ, ℂ) y) hy _
  rw [hDx a, hDx b]
  rfl

/-- Pull back a genuine smooth metric along the given actual diffeomorphism.
The resulting metric need not induce the original reference complex structure. -/
def pullback (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceMetric S) :
    SmoothSurfaceMetric R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  refine
    { inner := pullbackForm f g
      symm := ?_
      pos := ?_
      isVonNBounded := ?_
      contMDiff := pullbackForm_contMDiff f g }
  · intro x a b
    change g.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x a) (surfaceDifferential R S f x b) =
      g.inner (f.toHomeomorph x)
        (surfaceDifferential R S f x b) (surfaceDifferential R S f x a)
    exact g.symm (f.toHomeomorph x) _ _
  · intro x a ha
    change 0 < g.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x a) (surfaceDifferential R S f x a)
    apply g.pos (f.toHomeomorph x)
    change f.differentialEquiv x a ≠ 0
    exact (f.differentialEquiv x).toLinearEquiv.map_ne_zero_iff.mpr ha
  · intro x
    let D := f.differentialEquiv x
    apply ((g.isVonNBounded (f.toHomeomorph x)).image
      D.symm.toContinuousLinearMap).subset
    intro a ha
    refine ⟨D a, ?_, D.symm_apply_apply a⟩
    change g.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x a) (surfaceDifferential R S f x a) < 1
    change g.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x a) (surfaceDifferential R S f x a) < 1 at ha
    exact ha

/-- The new metric is the actual metric pullback on every pair of original tangent vectors. -/
theorem pullback_inner (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceMetric S)
    (x : X) (a b : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    let := S.toRiemannAtlas.isRealManifold
    (pullback f g).inner x a b = g.inner (f.toHomeomorph x)
      (surfaceDifferential R S f x a) (surfaceDifferential R S f x b) := rfl

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
