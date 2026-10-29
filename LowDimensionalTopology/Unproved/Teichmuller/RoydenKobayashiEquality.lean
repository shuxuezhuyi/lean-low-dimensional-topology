module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillNeighborhood
public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiExtendedCore

/-!
# Royden's distance equality on the original group Teichmuller space

The original group quotient carries its proved QC metric and Bers complex atlas.
The imported Teichmuller distance has the half-log normalization, so its double
is the full-log distance compared with the literal Kobayashi chain infimum.
The extended-value equality also states finiteness, without converting infinity
to a real zero. This file defines an unproved classical proposition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

/-- The literal Kobayashi distance is the full-log Teichmuller distance on the
same original group quotient with its actual Bers complex structure. -/
def RoydenKobayashiEquality
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  letI := R.t2Space
  letI := R.connectedSpace
  letI := R.compactSpace
  letI := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  letI := gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  letI := gammaBers_isManifold R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  ∀ a b : LiZhongQC.TeichGamma Γ,
    KobayashiCore.kobayashiEDist (d := 3 * g - 3) a b =
      ENNReal.ofReal (2 * LiZhongQC.teichDistanceGamma a b)

end LowDimensionalTopology.Unproved.Teichmuller
