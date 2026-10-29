module

public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMetricPartition

/-!
# A compatible smooth metric on every original Riemann surface

The metric is the actual locally finite weighted sum of original chart forms.
Its coordinate densities are derived from the same sum and the true
holomorphic transition factors. Hausdorffness, second countability and sigma
compactness are supplied by the original surface, with no compactness premise.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
namespace AtlasMetricConstruction

universe u
variable {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)

/-- The density of the constructed metric in any original complex chart. -/
def partitionDensity (ρ : Partition R) (e : OriginalComplexChart R) (x : X) : ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  exact ∑ j ∈ ρ.finsupport x, ρ j x * transitionScale R e (chosenChart R j) x

/-- The whole metric, not only its diagonal, has the derived conformal density. -/
theorem partitionForm_eq_density (ρ : Partition R) (hρ : Subordinate R ρ)
    (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source)
    (v w : RealSurfaceTangent R x) :
    partitionForm R ρ x v w = partitionDensity R ρ e x * chartForm R e x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  rw [partitionForm_apply]
  unfold partitionDensity
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : ρ j x ≠ 0 := by simpa only [ρ.mem_finsupport, Function.mem_support] using hj
  have hxj : x ∈ (chosenChart R j).val.source := hρ j (subset_tsupport _ hj')
  rw [localForm_eq_chartForm R j x hxj, chartForm_change R e (chosenChart R j) x hx hxj]
  ring

/-- Positive definiteness of the actual sum makes every original-chart density positive. -/
theorem partitionDensity_pos (ρ : Partition R) (hρ : Subordinate R ρ)
    (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source) :
    0 < partitionDensity R ρ e x := by
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let v : RealSurfaceTangent R x := D.symm 1
  have hv : v ≠ 0 := D.symm.toLinearEquiv.map_ne_zero_iff.mpr one_ne_zero
  have hDv : originalChartDifferential R e x v = 1 := D.apply_symm_apply 1
  have hpos := partitionForm_self_pos R ρ hρ x v hv
  rw [partitionForm_eq_density R ρ hρ e x hx v v, chartForm_apply, hDv] at hpos
  simpa only [real_inner_self_eq_norm_sq, norm_one, one_pow, mul_one] using hpos

/-- Only the true overlaps enter the smooth density calculation. Outside a
chosen chart, its partition weight vanishes on a neighborhood. -/
theorem partitionDensity_contMDiffOn (ρ : Partition R) (hρ : Subordinate R ρ)
    (e : OriginalComplexChart R) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (partitionDensity R ρ e) e.val.source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (partitionDensity R ρ e) e.val.source
  have hEq (x : X) : partitionDensity R ρ e x =
      ∑ᶠ j, ρ j x * transitionScale R e (chosenChart R j) x := by
    simpa only [partitionDensity, smul_eq_mul] using
      ρ.sum_finsupport_smul_eq_finsum x
        (fun j y => transitionScale R e (chosenChart R j) y)
  have hfun : partitionDensity R ρ e =
      (fun x => ∑ᶠ j, ρ j x • transitionScale R e (chosenChart R j) x) := by
    funext x
    simpa only [smul_eq_mul] using hEq x
  rw [hfun]
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply ρ.contMDiffAt_finsum
  intro j hj
  have hxj : x ∈ (chosenChart R j).val.source := hρ j hj
  exact (transitionScale_contMDiffOn R e (chosenChart R j) x ⟨hx, hxj⟩).contMDiffAt
    ((e.val.open_source.inter (chosenChart R j).val.open_source).mem_nhds ⟨hx, hxj⟩)

/-- The constructed metric and its derived densities induce the original complex atlas. -/
def metricOfPartitionCompatible (ρ : Partition R) (hρ : Subordinate R ρ) :
    AtlasInducedMetric R where
  metric := metricOfPartition R ρ hρ
  density := partitionDensity R ρ
  density_smooth := partitionDensity_contMDiffOn R ρ hρ
  density_pos := partitionDensity_pos R ρ hρ
  inner_eq e x hx v w := by
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    exact partitionForm_eq_density R ρ hρ e x hx v w

end AtlasMetricConstruction

/-- Every original Riemann surface admits an actual infinitely smooth positive
metric inducing its original complex structure in all original charts. -/
theorem exists_atlasInducedMetric {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) : Nonempty (AtlasInducedMetric R) := by
  obtain ⟨ρ, hρ⟩ := AtlasMetricConstruction.exists_partition R
  exact ⟨AtlasMetricConstruction.metricOfPartitionCompatible R ρ hρ⟩

end LowDimensionalTopology.Geometry.Teichmuller
