module

public import LowDimensionalTopology.Geometry.Teichmuller.TerminalDifferentialUniqueness

/-! Every centered initial natural parameter has a compatible terminal parameter
for the same Teichmüller map and terminal quadratic differential. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open LiZhongQC
universe u v

section Raw
variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Every supplied centered initial natural parameter has a matching terminal
natural parameter for the same map, differentials, and stretch constant. -/
theorem teichmullerMap_anyInitialNaturalParameter
    {f : X ≃ₜ Y} {q : X → ℂ → ℂ} {r : Y → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q r k) (p : X) (hp : IsRegularPoint q p)
    {ζ : ℂ → ℂ} (hζ : IsNaturalParameterAt q p ζ) :
    ∃ η : ℂ → ℂ, IsNaturalParameterAt r (f p) η ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p),
        η (localMapExpr f p z) =
          (ζ z + (k : ℂ) * conj (ζ z)) / (1 - (k : ℂ)) := by
  obtain ⟨_, A, B, hA, hB, hrel⟩ := hf.regular p hp
  rcases eq25_3_natural_parameter_unique hA.1 hζ.1 hA.2.1 hζ.2.1
    hA.2.2.2 hζ.2.2.2 hp with hsign | hsign
  · refine ⟨B, hB, ?_⟩
    filter_upwards [hrel, hsign] with z hz hs
    simpa only [hs, teichStretch] using hz
  · have hBn : IsNaturalParameterAt r (f p) (-B) := by
      refine ⟨hB.1.neg, ?_, ?_, ?_⟩
      · simp only [Pi.neg_apply, hB.2.1, neg_zero]
      · rw [deriv.neg]
        exact neg_ne_zero.mpr hB.2.2.1
      · filter_upwards [hB.2.2.2] with w hw
        rw [deriv.neg, neg_sq, hw]
    refine ⟨-B, hBn, ?_⟩
    filter_upwards [hrel, hsign] with z hz hs
    change -B (localMapExpr f p z) = teichStretch k (ζ z)
    rw [hs] at hz
    have hn : teichStretch k (-ζ z) = -teichStretch k (ζ z) := by
      simp only [teichStretch, map_neg]
      ring
    rw [hn] at hz
    simpa only [neg_neg] using congrArg (fun w : ℂ => -w) hz

end Raw

/-- On the unchanged original surfaces the same terminal witness preserves
all finite zero orders and satisfies the affine formula for every supplied natural parameter. -/
theorem bookTeichmuller_zeroOrders_and_anyInitialNaturalParameter
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : Surfaces.ClosedRiemannSurface X) (S : Surfaces.ClosedRiemannSurface Y)
    (φ : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (ψ : Surfaces.HolomorphicQuadraticDifferential S.toRiemannAtlas)
    (f : X ≃ₜ Y) (k : ℝ)
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      IsTeichmullerMap f φ ψ k) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    (∀ (p : X) (m : ℕ), IsZeroOfOrder φ p m → IsZeroOfOrder ψ (f p) m) ∧
      ∀ (p : X), IsRegularPoint φ p →
        ∀ ζ : ℂ → ℂ, IsNaturalParameterAt φ p ζ →
          ∃ η : ℂ → ℂ, IsNaturalParameterAt ψ (f p) η ∧
            ∀ᶠ z in 𝓝 (chartAt ℂ p p),
              η (localMapExpr f p z) =
                (ζ z + (k : ℂ) * conj (ζ z)) / (1 - (k : ℂ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  refine ⟨hf.zero, ?_⟩
  intro p hp ζ hζ
  exact teichmullerMap_anyInitialNaturalParameter hf p hp hζ

end LowDimensionalTopology.Geometry.Teichmuller
