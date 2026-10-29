module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricPullbackFamily
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The actual pullback time derivative in a fixed original tensor chart

The time derivative in the point-centered chart is carried into any fixed
original nested Hom chart by its actual linear fibre coordinate change.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
namespace SmoothSurfaceMetric

variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

set_option maxHeartbeats 800000 in
/-- The derivative of the literal fixed-chart pullback is the actual linear
coordinate change of the time partial in the point-centered chart. -/
theorem pullbackFormInChart_timeDerivative_inFixedChart
    (Phi : ℝ → SmoothSurfaceEquiv R R) (g : SmoothSurfaceMetric R)
    (x₀ x : X) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    let B := ℂ →L[ℝ] ℂ →L[ℝ] ℝ
    let E : X → Type := fun y =>
      TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ
    let : NormedAddCommGroup (ℂ →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℝ)
    let : NormedAddCommGroup B :=
      ContinuousLinearMap.toNormedAddCommGroup
        (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)
    letI : ∀ y : X, IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) :=
      fun y => ContinuousLinearMap.isTopologicalAddGroup
        (E := TangentSpace 𝓘(ℝ, ℂ) y) (F := ℝ) (σ := RingHom.id ℝ)
    letI : ∀ y : X, ContinuousAdd (TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) :=
      fun y => (ContinuousLinearMap.isTopologicalAddGroup
        (E := TangentSpace 𝓘(ℝ, ℂ) y) (F := ℝ) (σ := RingHom.id ℝ)).toContinuousAdd
    let e₀ := trivializationAt B E x₀
    let eₓ := trivializationAt B E x
    x ∈ e₀.baseSet →
    ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x) →
    HasDerivAt
      (fun t : ℝ => pullbackFormInChart Phi g x₀ (t, x))
      (e₀.continuousLinearMapAt ℝ x
        (eₓ.symmL ℝ x
          (deriv (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) 0))) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hx₀ hPhi
  let B := ℂ →L[ℝ] ℂ →L[ℝ] ℝ
  let E : X → Type := fun y =>
    TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ
  let : NormedAddCommGroup (ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℝ)
  let : NormedAddCommGroup B :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)
  let : ∀ y : X, IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) :=
    fun y => ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) y) (F := ℝ) (σ := RingHom.id ℝ)
  let : ∀ y : X, ContinuousAdd (TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) :=
    fun y => (ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) y) (F := ℝ) (σ := RingHom.id ℝ)).toContinuousAdd
  let e₀ := trivializationAt B E x₀
  let eₓ := trivializationAt B E x
  let C : B →L[ℝ] B := (e₀.continuousLinearMapAt ℝ x).comp (eₓ.symmL ℝ x)
  have hx : x ∈ eₓ.baseSet := mem_baseSet_trivializationAt B E x
  have hcoord (a : X) (ha : x ∈ (trivializationAt B E a).baseSet) (t : ℝ) :
      (trivializationAt B E a).continuousLinearMapAt ℝ x (pullbackForm (Phi t) g x) =
        pullbackFormInChart Phi g a (t, x) := by
    rw [(trivializationAt B E a).continuousLinearMapAt_apply_of_mem ℝ ha]
    exact congrArg Prod.snd (hom_trivializationAt_apply (RingHom.id ℝ) a
      (⟨x, pullbackForm (Phi t) g x⟩ : TotalSpace B E))
  have hchange : C ∘ (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) =
      (fun t : ℝ => pullbackFormInChart Phi g x₀ (t, x)) := by
    funext t
    change e₀.continuousLinearMapAt ℝ x
      (eₓ.symmL ℝ x (pullbackFormInChart Phi g x (t, x))) = _
    rw [← hcoord x hx t, eₓ.symmL_continuousLinearMapAt hx]
    exact hcoord x₀ hx₀ t
  have hcenter : HasDerivAt
      (fun t : ℝ => pullbackFormInChart Phi g x (t, x))
      (deriv (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) 0) (0 : ℝ) :=
    (pullbackFormInChart_timeDerivative Phi g x hPhi).2
  have h : HasDerivAt
      (C ∘ (fun t : ℝ => pullbackFormInChart Phi g x (t, x)))
      (C (deriv (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) 0)) (0 : ℝ) := by
    apply hasDerivAt_iff_hasFDerivAt.mpr
    apply HasFDerivAt.of_isLittleOTVS
    simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
      map_sub, map_smul] using
      C.isBigOTVS_comp.trans_isLittleOTVS hcenter.hasFDerivAt.isLittleOTVS
  rw [hchange] at h
  exact h

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
