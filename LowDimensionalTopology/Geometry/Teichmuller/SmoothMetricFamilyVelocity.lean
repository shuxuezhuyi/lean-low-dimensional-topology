module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricPullbackLieCoordinates
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The native velocity of a given smooth diffeomorphism family

The actual time differential applied to the canonical time tangent vector
is a smooth tangent section. Its basepoint is transported only by the given
time-zero identity. Every original chart reads the same actual derivative.
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

/-- A given family through the identity has an actual smooth native velocity,
with the genuine derivative in every valid original chart. -/
theorem exists_nativeVelocity_of_smoothFamily
    (Phi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hzero : ∀ x : X, (Phi 0).toHomeomorph x = x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x : X, ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x)) →
    ∃ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      ∀ (e : OriginalComplexChart R.toRiemannSurface)
          (x : X) (hx : x ∈ e.val.source),
        HasDerivAt (fun t : ℝ => e.val ((Phi t).toHomeomorph x))
          (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi
  let v₀ : TangentSpace 𝓘(ℝ) (0 : ℝ) :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1
  let u : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) ((Phi 0).toHomeomorph x) := fun x =>
    mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (fun t : ℝ => (Phi t).toHomeomorph x) 0 v₀
  let A : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x := fun x =>
    cast (congrArg (TangentSpace 𝓘(ℝ, ℂ)) (hzero x)) (u x)
  have hsection : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (A x)) := by
    intro x₀
    let F : X → ℝ → X := fun x t => (Phi t).toHomeomorph x
    have hF : ContMDiffAt (𝓘(ℝ, ℂ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞
        (Function.uncurry F) (x₀, 0) :=
      (hPhi x₀).comp (x₀, 0) (contMDiffAt_snd.prodMk contMDiffAt_fst)
    have hD := hF.mfderiv (m := ∞) F (fun _ : X => (0 : ℝ))
      contMDiffAt_const (by simp)
    have hv : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
        (fun _ : X => (TotalSpace.mk' ℝ (0 : ℝ) v₀ : TangentBundle 𝓘(ℝ) ℝ)) x₀ :=
      contMDiffAt_const
    have hb : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x : X => F x 0) x₀ := by
      have hbase : (fun x : X => F x 0) = id := funext hzero
      rw [hbase]
      exact contMDiffAt_id
    have hs := hD.clm_apply_of_inCoordinates hv hb
    apply hs.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => TotalSpace.mk_cast (hzero x) (u x)
  let V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X) := ⟨A, hsection⟩
  refine ⟨V, ?_⟩
  intro e x hx
  have he : e.val ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.subset_maximalAtlas e.property
  have hcurve : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (Phi t).toHomeomorph x) 0 :=
    (hPhi x).comp 0 (contMDiffAt_id.prodMk contMDiffAt_const)
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      e.val ((Phi 0).toHomeomorph x) := by
    rw [hzero]
    exact contMDiffAt_of_mem_maximalAtlas he hx
  have hscalar : DifferentiableAt ℝ
      (fun t : ℝ => e.val ((Phi t).toHomeomorph x)) 0 :=
    (hchart.comp 0 hcurve).contDiffAt.differentiableAt (by simp)
  apply hscalar.hasDerivAt.congr_deriv
  have hchain := mvfderiv_comp_apply 0
    (hchart.mdifferentiableAt (by simp)) (hcurve.mdifferentiableAt (by simp)) v₀
  have hactual : deriv (fun t : ℝ => e.val ((Phi t).toHomeomorph x)) 0 =
      mvfderiv 𝓘(ℝ, ℂ) (e.val : X → ℂ) ((Phi 0).toHomeomorph x) (u x) := by
    simpa only [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, v₀, u,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      fderiv_apply_one_eq_deriv, Function.comp_def] using hchain
  have hcast := congrArg
    (fun p : TangentBundle 𝓘(ℝ, ℂ) X =>
      mvfderiv 𝓘(ℝ, ℂ) (e.val : X → ℂ) p.proj p.snd)
    (TotalSpace.mk_cast (F := ℂ) (hzero x) (u x))
  exact hactual.trans hcast.symm

/-- The same given family supplies both native fields and the full original
metric Lie-coordinate formula, without a supplied velocity or tensor. -/
theorem exists_nativeMetricLie_of_smoothFamily
    (Phi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hzero : ∀ x : X, (Phi 0).toHomeomorph x = x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x : X, ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x)) →
    ∃ (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X))
        (L : SmoothSymmetricTwoTensor R),
      (∀ (e : OriginalComplexChart R.toRiemannSurface)
          (x : X) (hx : x ∈ e.val.source),
        HasDerivAt (fun t : ℝ => e.val ((Phi t).toHomeomorph x))
          (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0) ∧
      (∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
        HasDerivAt (fun t : ℝ => (pullback (Phi t) g).inner x a b)
          (L.val x a b) 0) ∧ HasOriginalMetricLieCoordinates R g V L := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi
  rcases exists_nativeVelocity_of_smoothFamily R Phi hzero hPhi with ⟨V, hV⟩
  rcases exists_metricLieTensor_of_smoothFamily R Phi g hzero hPhi V hV with ⟨L, hL, hcoord⟩
  exact ⟨V, L, hV, hL, hcoord⟩

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
