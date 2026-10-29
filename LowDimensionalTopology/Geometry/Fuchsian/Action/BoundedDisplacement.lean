module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceUniverse
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Finitely many deck transformations have bounded displacement on a compact set

The action and hyperbolic distance are those of the actual upper half-plane.
Compact thickening reduces bounded displacement to proper discontinuity.
The original-surface covering theorem uses Wu Xiaobin's Li-Zhong-QC APIs,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

public section
noncomputable section
open Set Metric
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Only finitely many actual group elements move some point of a given compact
set by a bounded distance. No cocompactness or torsion assumption is needed. -/
theorem finite_bounded_displacement
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {K : Set ℍ} (hK : IsCompact K) (R : ℝ) :
    {g | g ∈ Γ ∧ ∃ z ∈ K, dist z (g • z) ≤ R}.Finite := by
  apply (hΓ (cthickening R K) hK.cthickening).subset
  rintro g ⟨hg, z, hz, hd⟩
  refine ⟨hg, g • z, ⟨z, self_subset_cthickening K hz, rfl⟩, ?_⟩
  exact mem_cthickening_of_dist_le (g • z) z R K hz (by simpa only [dist_comm] using hd)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

/-- A given holomorphic uniformization of an original closed surface has only
finitely many actual deck matrices with bounded displacement on a compact set. -/
theorem finite_bounded_deck_displacement
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {K : Set ℍ} (hK : IsCompact K) (L : ℝ) :
    {g | g ∈ Γ ∧ ∃ z ∈ K, dist z (g • z) ≤ L}.Finite := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  exact Fuchsian.finite_bounded_displacement (LiZhongQC.utm_x2_isFuchsian hp) hK L

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface
