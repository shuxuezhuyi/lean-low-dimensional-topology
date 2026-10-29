module

public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableEncoding

/-!
# Actual preferred-atlas consumption of the full measurable tensor space

The native space quantifies over every original chart. Restricting those genuine
L-infinity classes to the atlas's actual preferred charts gives precisely the
measurable Beltrami differential predicate of the quasiconformal surface library.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableBeltrami

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (A : RiemannAtlas X)

/-- The actual preferred chart, regarded as a member of the original atlas. -/
def preferredChart (x : X) : Chart A := by
  let := A.toChartedSpace
  exact ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩

/-- The actual chosen measurable representative in each preferred chart. -/
def preferredCoefficient (μ : Space A) (x : X) : ℂ → ℂ := coeff μ (preferredChart A x)

/-- The full original-atlas tensor law specializes to the actual preferred-atlas AE law. -/
theorem preferred_isDiffFamilyAE (μ : Space A) :
    let := A.toChartedSpace
    LiZhongQC.IsDiffFamilyAE (-1) 1 (preferredCoefficient A μ) := by
  dsimp only
  let := A.toChartedSpace
  intro x y
  have h := compatible μ (preferredChart A y) (preferredChart A x)
  change ∀ᵐ z ∂(volume.restrict
      ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source)),
    preferredCoefficient A μ y z =
      preferredCoefficient A μ x (LiZhongQC.chartTransition x y z) *
        (conj (deriv (LiZhongQC.chartTransition x y) z) /
          deriv (LiZhongQC.chartTransition x y) z) at h
  filter_upwards [h] with z hz
  rw [hz, zpow_neg_one, zpow_one, div_eq_mul_inv]
  ring

/-- Every genuine common essential bound is retained by the actual source tensor predicate. -/
theorem preferred_isBeltramiDifferential (μ : Space A) {k : ℝ}
    (hk : 0 ≤ k) (hμ : ‖μ‖ ≤ k) :
    let := A.toChartedSpace
    LiZhongQC.IsBeltramiDifferential (preferredCoefficient A μ) k := by
  dsimp only
  let := A.toChartedSpace
  refine ⟨preferred_isDiffFamilyAE A μ, fun x => ?_⟩
  exact ⟨Lp.aestronglyMeasurable (coeff μ (preferredChart A x)),
    (norm_le_iff μ hk).1 hμ (preferredChart A x)⟩

end LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableBeltrami
