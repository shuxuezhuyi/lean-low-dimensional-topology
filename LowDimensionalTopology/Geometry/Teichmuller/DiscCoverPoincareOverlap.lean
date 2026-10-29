module

public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverSheetTransition
public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverPoincareTensor
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.PoincareTensorCovariance

/-!
# Independence of the actual local Poincaré form

The normalized transition between two inverse covering sheets identifies their
literal densities in each original chart. Consequently every original chart
and every actual sheet give the same bilinear form on the original tangent fiber.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Hyperbolic Auxiliary.Analysis

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

/-- The prescribed density in one original chart is independent of the actual
inverse sheet of the same disk covering. -/
theorem discCoverSheetDensity_independent (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (l k : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (hk : M.discCover = (k : extendedUnitDisc → X))
    (x : X) (hx : x ∈ e.val.source ∩ l.target ∩ k.target) :
    discCoverSheetDensity e l x = discCoverSheetDensity e k x := by
  let F := discCoverSheetCoordinate e l
  let G := discCoverSheetCoordinate e k
  have hxF : e.val x ∈ F.source := by
    change (e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ l.target) ∧
      l.symm (e.val.symm (e.val x)) ∈ discFiniteChart.source
    rw [e.val.left_inv hx.1.1, discFiniteChart_source]
    exact ⟨⟨e.val.map_source hx.1.1, hx.1.2⟩, mem_univ _⟩
  have hdF : DifferentiableAt ℂ F (e.val x) :=
    (discCoverSheetCoordinate_analytic M e l hl (e.val x) hxF).differentiableAt
  obtain ⟨a, c, hdet, hrel⟩ :=
    discCoverSheets_eventually_related_normalized M l k hl hk x hx.1.2 hx.2
  have heinv : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := e.val.tendsto_symm hx.1.1
  have hnear : (G : ℂ → ℂ) =ᶠ[𝓝 (e.val x)]
      discFractionalMap a c ∘ (F : ℂ → ℂ) := by
    exact heinv.eventually hrel
  have hpoint : G (e.val x) = discFractionalMap a c (F (e.val x)) :=
    hnear.eq_of_nhds
  let z : Complex.UnitDisc := discFiniteHomeomorph (l.symm x)
  have hFval : F (e.val x) = (z : ℂ) := by
    change discFiniteChart (l.symm (e.val.symm (e.val x))) = discFiniteChart (l.symm x)
    rw [e.val.left_inv hx.1.1]
  have hGval : G (e.val x) = (discFractionalHomeomorph a c hdet z : ℂ) := by
    change G (e.val x) = discFractionalMap a c (z : ℂ)
    rw [hpoint, hFval]
  have hdMap : DifferentiableAt ℂ (discFractionalMap a c) (F (e.val x)) := by
    rw [hFval]
    exact (normalizedDisc_analyticAt a c hdet z).differentiableAt
  have hderiv : deriv G (e.val x) =
      deriv (discFractionalMap a c) (F (e.val x)) * deriv F (e.val x) := by
    calc
      deriv G (e.val x) = deriv (discFractionalMap a c ∘ (F : ℂ → ℂ)) (e.val x) :=
        hnear.deriv_eq
      _ = deriv (discFractionalMap a c) (F (e.val x)) * deriv F (e.val x) :=
        deriv_comp (e.val x) hdMap hdF
  have hcov : discPoincareTensor (G (e.val x)) (deriv G (e.val x)) (deriv G (e.val x)) =
      discPoincareTensor (F (e.val x)) (deriv F (e.val x)) (deriv F (e.val x)) := by
    simpa only [hGval, hderiv, hFval] using
      normalizedDisc_discPoincareTensor_pullback a c hdet z
        (deriv F (e.val x)) (deriv F (e.val x))
  simp only [discPoincareTensor_apply, poincareDensityDisc_eq_poincareLengthDensity,
    real_inner_self_eq_norm_sq] at hcov
  change poincareLengthDensity (F (e.val x)) ^ 2 * ‖deriv F (e.val x)‖ ^ 2 =
    poincareLengthDensity (G (e.val x)) ^ 2 * ‖deriv G (e.val x)‖ ^ 2
  exact hcov.symm

/-- Any two original charts and any two actual inverse sheets give the same
full bilinear form on the original tangent fiber. -/
theorem discCoverSheetDensity_mul_chartForm_eq (M : HyperbolicSurfaceModel R)
    (e f : OriginalComplexChart R) (l k : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (hk : M.discCover = (k : extendedUnitDisc → X))
    (x : X) (hx : x ∈ e.val.source ∩ l.target) (hy : x ∈ f.val.source ∩ k.target)
    (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    discCoverSheetDensity e l x * AtlasMetricConstruction.chartForm R e x v w =
      discCoverSheetDensity f k x * AtlasMetricConstruction.chartForm R f x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  rw [discCoverSheetDensity_independent M e l k hl hk x ⟨hx, hy.2⟩]
  exact (discCoverSheetDensity_tensor M e k hk x ⟨hx.1, hy.2⟩ v w).symm.trans
    (discCoverSheetDensity_tensor M f k hk x hy v w)

end LowDimensionalTopology.Geometry.Teichmuller
