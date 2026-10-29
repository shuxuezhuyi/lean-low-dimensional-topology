module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricPullback
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# A given pullback metric family in a fixed original bundle chart

The coordinates use the actual nested Hom bundle of the original tangent
spaces. Joint smoothness of the given diffeomorphism family controls its
spatial differential and the time partial derivative of the literal pullback.
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

variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

/-- Read the actual pullback in the fixed original nested Hom chart at `x₀`. -/
def pullbackFormInChart
    (Phi : ℝ → SmoothSurfaceEquiv R R) (g : SmoothSurfaceMetric R)
    (x₀ : X) (p : ℝ × X) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
    (ℂ →L[ℝ] ℝ) (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ)
    x₀ p.2 x₀ p.2 (pullbackForm (Phi p.1) g p.2)

/-- Joint smoothness of the family gives joint smoothness of its actual
pullback form in the fixed original chart around the time-zero basepoint. -/
theorem pullbackFormInChart_contMDiffAt
    (Phi : ℝ → SmoothSurfaceEquiv R R) (g : SmoothSurfaceMetric R) (x₀ : X) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x₀) →
    ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ (pullbackFormInChart Phi g x₀) (0, x₀) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi
  let F : (ℝ × X) → X → X := fun p x => (Phi p.1).toHomeomorph x
  let f : ℝ × X → X := fun p => F p p.2
  let D : ℝ × X → ℂ →L[ℝ] ℂ :=
    inTangentCoordinates 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Prod.snd f
      (fun p => surfaceDifferential R R (Phi p.1) p.2) (0, x₀)
  let B : ℝ × X → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fun p =>
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
      (ℂ →L[ℝ] ℝ) (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ)
      (f (0, x₀)) (f p) (f (0, x₀)) (f p) (g.inner (f p))
  have hF : ContMDiffAt ((𝓘(ℝ).prod 𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, ℂ) ∞ (Function.uncurry F) ((0, x₀), x₀) := by
    exact hPhi.comp ((0, x₀), x₀)
      ((contMDiffAt_fst (I := 𝓘(ℝ).prod 𝓘(ℝ, ℂ))
        (J := 𝓘(ℝ, ℂ))).fst.prodMk contMDiffAt_snd)
  have hD : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞ D (0, x₀) := by
    exact hF.mfderiv F Prod.snd contMDiffAt_snd (by simp)
  have hB : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ B (0, x₀) := by
    have hg := (g.contMDiff (f (0, x₀))).comp (0, x₀) hPhi
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
  have hQ : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun p => (B p).bilinearComp (D p) (D p)) (0, x₀) := by
    change ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun p => flipForm ((flipForm ((B p).comp (D p))).comp (D p))) (0, x₀)
    exact hflip.contMDiffAt.comp (0, x₀)
      ((hflip.contMDiffAt.comp (0, x₀) (hB.clm_comp hD)).clm_comp hD)
  apply hQ.congr_of_eventuallyEq
  let tR := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) x₀
  let tS := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) (f (0, x₀))
  have hxR : x₀ ∈ tR.baseSet := mem_baseSet_trivializationAt _ _ _
  have hxS : f (0, x₀) ∈ tS.baseSet := mem_baseSet_trivializationAt _ _ _
  have hpr : ContinuousAt (fun p : ℝ × X => p.2) (0, x₀) :=
    continuous_snd.continuousAt
  filter_upwards [hpr (tR.open_baseSet.mem_nhds hxR),
    hPhi.continuousAt (tS.open_baseSet.mem_nhds hxS)] with p hx hy
  ext a b
  change ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
      (ℂ →L[ℝ] ℝ) (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ)
      x₀ p.2 x₀ p.2 (pullbackForm (Phi p.1) g p.2) a b =
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
      (ℂ →L[ℝ] ℝ) (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ)
      (f (0, x₀)) (f p) (f (0, x₀)) (f p) (g.inner (f p)) (D p a) (D p b)
  rw [inCoordinates_apply_eq₂ hx hx (Set.mem_univ p.2),
    inCoordinates_apply_eq₂ hy hy (Set.mem_univ (f p))]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  have hDp (a : ℂ) : tS.symm (f p) (D p a) =
      surfaceDifferential R R (Phi p.1) p.2 (tR.symm p.2 a) := by
    rw [← tS.symmL_apply (R := ℝ) (F := ℂ)
      (E := fun x : X => TangentSpace 𝓘(ℝ, ℂ) x) hy,
      ← tR.symmL_apply (R := ℝ) (F := ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℝ, ℂ) x) hx]
    change tS.symmL ℝ (f p)
      (tS.continuousLinearMapAt ℝ (f p)
        (surfaceDifferential R R (Phi p.1) p.2 (tR.symmL ℝ p.2 a))) = _
    exact tS.symmL_continuousLinearMapAt (R := ℝ) (F := ℂ)
      (E := fun x : X => TangentSpace 𝓘(ℝ, ℂ) x) hy _
  rw [hDp a, hDp b]
  rfl

/-- The actual time partial derivative in one fixed chart is smooth in the
basepoint, and at its center it is the derivative of the literal pullback. -/
theorem pullbackFormInChart_timeDerivative
    (Phi : ℝ → SmoothSurfaceEquiv R R) (g : SmoothSurfaceMetric R) (x₀ : X) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x₀) →
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
        (fun x => deriv (fun t => pullbackFormInChart Phi g x₀ (t, x)) 0) x₀ ∧
      HasDerivAt (fun t => pullbackFormInChart Phi g x₀ (t, x₀))
        (deriv (fun t => pullbackFormInChart Phi g x₀ (t, x₀)) 0) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi
  let : NormedAddCommGroup (ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℝ)
  let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)
  have hQ := pullbackFormInChart_contMDiffAt Phi g x₀ hPhi
  let F : X → ℝ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    fun x t => pullbackFormInChart Phi g x₀ (t, x)
  have hF : ContMDiffAt (𝓘(ℝ, ℂ).prod 𝓘(ℝ))
      𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ (Function.uncurry F) (x₀, 0) := by
    exact hQ.comp (x₀, 0) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  let Dtime : X → ℝ →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    inTangentCoordinates 𝓘(ℝ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      (fun _ : X => (0 : ℝ)) (fun x => F x 0)
      (fun x => mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (F x) 0) x₀
  have hS : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun x => Dtime x 1) x₀ := by
    exact hF.mfderiv_apply (m := ∞) F (fun _ : X => (0 : ℝ)) id
      (fun _ : X => (1 : ℝ)) contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
  have hderiv (x : X) : Dtime x 1 = deriv (F x) 0 := by
    dsimp only [Dtime]
    rw [inTangentCoordinates_eq (I := 𝓘(ℝ))
      (I' := 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ))
      (fun _ : X => (0 : ℝ)) (fun y => F y 0)
      (fun y => mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (F y) 0)
      (by simp) (by simp)]
    simp only [tangentBundleCore_coordChange_model_space,
      ContinuousLinearMap.id_comp]
    exact congrArg (fun A : ℝ →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℝ => A 1)
      (mfderiv_eq_fderiv (𝕜 := ℝ) (f := F x) (x := (0 : ℝ)))
  have hs : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun x => deriv (F x) 0) x₀ := by
    simpa only [hderiv] using hS
  refine ⟨hs, ?_⟩
  have ht : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ (F x₀) 0 :=
    hQ.comp 0 (contMDiffAt_id.prodMk contMDiffAt_const)
  exact (ht.contDiffAt.differentiableAt (by simp)).hasDerivAt

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
