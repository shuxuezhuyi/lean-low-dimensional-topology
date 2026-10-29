module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricPullbackFixedChart
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSymmetricTensors

/-!
# The native symmetric tensor of a given pullback variation

The point-centered time derivatives define a genuine smooth section of the
original nested Hom bundle. Evaluation on every pair of original tangent
vectors is the scalar derivative of the literal pullback metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
namespace SmoothSurfaceMetric

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- A jointly smooth family has an actual smooth symmetric first variation,
with unchanged original tangent slots and actual scalar derivatives. -/
theorem exists_pullbackTimeDerivativeTensor
    (Phi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x : X, ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x)) →
    ∃ L : SmoothSymmetricTwoTensor R,
      ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
        HasDerivAt (fun t : ℝ => (pullback (Phi t) g).inner x a b)
          (L.val x a b) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi
  let B := ℂ →L[ℝ] ℂ →L[ℝ] ℝ
  let E : X → Type := fun x =>
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ
  let : NormedAddCommGroup (ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℝ)
  let : NormedAddCommGroup B :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)
  let : ∀ x : X, IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) :=
    fun x => ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) x) (F := ℝ) (σ := RingHom.id ℝ)
  let : ∀ x : X, ContinuousAdd (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) :=
    fun x => (ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) x) (F := ℝ) (σ := RingHom.id ℝ)).toContinuousAdd
  let A : ∀ x : X, E x := fun x =>
    (trivializationAt B E x).symmL ℝ x
      (deriv (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) 0)
  have hfixed (x₀ x : X) (hx₀ : x ∈ (trivializationAt B E x₀).baseSet) :
      HasDerivAt (fun t : ℝ => pullbackFormInChart Phi g x₀ (t, x))
        ((trivializationAt B E x₀).continuousLinearMapAt ℝ x (A x)) 0 :=
    pullbackFormInChart_timeDerivative_inFixedChart Phi g x₀ x hx₀ (hPhi x)
  have hsection : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, B)) ∞
      (fun x => TotalSpace.mk' B (E := E) x (A x)) := by
    intro x₀
    apply (contMDiffAt_section x₀).mpr
    have hs := (pullbackFormInChart_timeDerivative Phi g x₀ (hPhi x₀)).1
    apply hs.congr_of_eventuallyEq
    let e₀ := trivializationAt B E x₀
    have hx₀ : x₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt B E x₀
    filter_upwards [e₀.open_baseSet.mem_nhds hx₀] with x hx
    rw [← e₀.continuousLinearMapAt_apply_of_mem ℝ hx]
    have hderiv := (hfixed x₀ x hx).hasFDerivAt.fderiv
    have hvalue := congrArg (fun L : ℝ →L[ℝ] B => L 1) hderiv
    simpa only [deriv, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hvalue.symm
  have hscalar (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x) :
      HasDerivAt (fun t : ℝ => pullbackForm (Phi t) g x a b) (A x a b) 0 := by
    let eₓ := trivializationAt B E x
    have hx : x ∈ eₓ.baseSet := mem_baseSet_trivializationAt B E x
    let ev : E x →L[ℝ] ℝ :=
      { toLinearMap :=
          { toFun := fun L => L a b
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        cont := (continuous_eval_const b).comp (continuous_eval_const a) }
    let C : B →L[ℝ] ℝ := ev.comp (eₓ.symmL ℝ x)
    have hcoord (t : ℝ) :
        eₓ.continuousLinearMapAt ℝ x (pullbackForm (Phi t) g x) =
          pullbackFormInChart Phi g x (t, x) := by
      rw [eₓ.continuousLinearMapAt_apply_of_mem ℝ hx]
      exact congrArg Prod.snd (hom_trivializationAt_apply (RingHom.id ℝ) x
        (⟨x, pullbackForm (Phi t) g x⟩ : TotalSpace B E))
    have hcurve : C ∘ (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) =
        (fun t : ℝ => pullbackForm (Phi t) g x a b) := by
      funext t
      change eₓ.symmL ℝ x (pullbackFormInChart Phi g x (t, x)) a b = _
      rw [← hcoord t, eₓ.symmL_continuousLinearMapAt hx]
    have hcenter : HasDerivAt
        (fun t : ℝ => pullbackFormInChart Phi g x (t, x))
        (deriv (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) 0) (0 : ℝ) :=
      (pullbackFormInChart_timeDerivative Phi g x (hPhi x)).2
    have h : HasDerivAt
        (C ∘ (fun t : ℝ => pullbackFormInChart Phi g x (t, x)))
        (C (deriv (fun t : ℝ => pullbackFormInChart Phi g x (t, x)) 0)) (0 : ℝ) := by
      apply hasDerivAt_iff_hasFDerivAt.mpr
      apply HasFDerivAt.of_isLittleOTVS
      simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
        map_sub, map_smul] using
        C.isBigOTVS_comp.trans_isLittleOTVS hcenter.hasFDerivAt.isLittleOTVS
    rw [hcurve] at h
    exact h
  have hsymm : ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
      A x a b = A x b a := by
    intro x a b
    have hswap : (fun t : ℝ => pullbackForm (Phi t) g x a b) =
        (fun t : ℝ => pullbackForm (Phi t) g x b a) := by
      funext t
      exact (pullback (Phi t) g).symm x a b
    have h := hscalar x a b
    rw [hswap] at h
    exact h.unique (hscalar x b a)
  have hmem : (⟨A, hsection⟩ : SmoothSurfaceTwoTensor R) ∈
      symmetricTwoTensorSubmodule R := by
    simp only [symmetricTwoTensorSubmodule]
    exact hsymm
  refine ⟨⟨⟨A, hsection⟩, hmem⟩, ?_⟩
  intro x a b
  exact hscalar x a b

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
