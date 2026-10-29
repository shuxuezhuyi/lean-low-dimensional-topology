module

public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverPoincareDensity
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.PoincareLineElement

/-!
# The local Poincaré tensor on the original tangent fiber

The actual inverse covering sheet pulls the disk tensor back to its derived
positive smooth density times the original chart form. The proof uses the
manifold chain rule for that same sheet and its actual analytic coordinate map.
No global descended metric or covering-branch independence is assumed here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Hyperbolic

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

/-- The actual inverse sheet pulls back both disk tensor slots to the derived
Poincaré density times the original chart form, on the original tangent fiber. -/
theorem discCoverSheetDensity_tensor (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (x : X) (hx : x ∈ e.val.source ∩ l.target)
    (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let s := l.symm.trans discFiniteChart
    discPoincareTensor (s x)
        (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x v)
        (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x w) =
      discCoverSheetDensity e l x * AtlasMetricConstruction.chartForm R e x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let s := l.symm.trans discFiniteChart
  let F := discCoverSheetCoordinate e l
  have hF : AnalyticOnNhd ℂ F F.source := discCoverSheetCoordinate_analytic M e l hl
  have hxF : e.val x ∈ F.source := by
    change (e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ l.target) ∧
      l.symm (e.val.symm (e.val x)) ∈ discFiniteChart.source
    rw [e.val.left_inv hx.1, discFiniteChart_source]
    exact ⟨⟨e.val.map_source hx.1, hx.2⟩, mem_univ _⟩
  have hdF : DifferentiableAt ℂ F (e.val x) := (hF (e.val x) hxF).differentiableAt
  have hdR : DifferentiableAt ℝ F (e.val x) := hdF.restrictScalars ℝ
  have he := mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) e.property hx.1
  have hnear : (s : X → ℂ) =ᶠ[𝓝 x] (F : ℂ → ℂ) ∘ (e.val : X → ℂ) := by
    filter_upwards [e.val.open_source.mem_nhds hx.1] with y hy
    change discFiniteChart (l.symm y) = discFiniteChart (l.symm (e.val.symm (e.val y)))
    rw [e.val.left_inv hy]
  have hval : F (e.val x) = s x := by
    change discFiniteChart (l.symm (e.val.symm (e.val x))) = discFiniteChart (l.symm x)
    rw [e.val.left_inv hx.1]
  have hComp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      ((F : ℂ → ℂ) ∘ (e.val : X → ℂ)) x := hdR.mdifferentiableAt.comp x he
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (s : X → ℂ) x =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((F : ℂ → ℂ) ∘ (e.val : X → ℂ)) x :=
    (hComp.hasMFDerivAt.congr_of_eventuallyEq_abuse hnear).mfderiv
  have hmv : mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x =
      mvfderiv 𝓘(ℝ, ℂ) ((F : ℂ → ℂ) ∘ (e.val : X → ℂ)) x := by
    unfold mvfderiv
    rw [hmf]
    ext a
    rfl
  have hchain (a : RealSurfaceTangent R x) :
      mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x a =
        fderiv ℝ F (e.val x) (originalChartDifferential R e x a) := by
    rw [hmv]
    calc
      mvfderiv 𝓘(ℝ, ℂ) ((F : ℂ → ℂ) ∘ (e.val : X → ℂ)) x a =
          mvfderiv 𝓘(ℝ, ℂ) (F : ℂ → ℂ) (e.val x)
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (e.val : X → ℂ) x a) :=
        congrArg (fun L : RealSurfaceTangent R x →L[ℝ] ℂ => L a)
          (mvfderiv_comp x hdR.mdifferentiableAt he)
      _ = fderiv ℝ F (e.val x) (originalChartDifferential R e x a) := by
        rw [mvfderiv_eq_fderiv]
        rfl
  have hL : IsConformalMap (fderiv ℝ F (e.val x)) :=
    (conformalAt_iff_isConformalMap_fderiv).mp
      (hdF.conformalAt (openPartialHomeomorph_analytic_forward_deriv_ne_zero F hF (e.val x) hxF))
  have hOne : fderiv ℝ F (e.val x) 1 = deriv F (e.val x) := by
    rw [hdF.fderiv_restrictScalars ℝ]
    rfl
  change discPoincareTensor (s x)
      (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x v)
      (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x w) =
    discCoverSheetDensity e l x * AtlasMetricConstruction.chartForm R e x v w
  rw [discPoincareTensor_apply, poincareDensityDisc_eq_poincareLengthDensity,
    hchain v, hchain w, conformal_inner_eq_norm_apply_one_sq hL,
    hOne, AtlasMetricConstruction.chartForm_apply]
  change poincareLengthDensity (s x) ^ 2 *
      (‖deriv F (e.val x)‖ ^ 2 *
        ⟪originalChartDifferential R e x v, originalChartDifferential R e x w⟫_ℝ) =
    (poincareLengthDensity (F (e.val x)) ^ 2 * ‖deriv F (e.val x)‖ ^ 2) *
      ⟪originalChartDifferential R e x v, originalChartDifferential R e x w⟫_ℝ
  rw [hval]
  ring

end LowDimensionalTopology.Geometry.Teichmuller
