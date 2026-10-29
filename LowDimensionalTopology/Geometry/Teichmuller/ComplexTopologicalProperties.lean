module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexCanonicalAtlas
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Topology of the actual marked-surface space through Bers coordinates

The actual connected open Bers image gives path connectedness for the actual
QC metric. The canonical realized-coefficient quotient has these topological
properties under the explicit global quasiconformal smoothing statement.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

include hg hgenus hPresentation hΓ hfree hp

/-- Actual QC-metric path connectedness requires no smoothing assumption. -/
theorem pathConnected_fromQCMetric :
    let m : MetricSpace (TeichmullerSpace.{u, u} R) :=
      fromQCMetricSpace R hg hgenus hPresentation
    @PathConnectedSpace (TeichmullerSpace.{u, u} R)
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) :=
    fromQCMetricSpace R hg hgenus hPresentation
  have hpath :=
    (isOpen_range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp).isConnected_iff_isPathConnected.mp
      (isConnected_range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp)
  let : PathConnectedSpace
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) :=
    isPathConnected_iff_pathConnectedSpace.mp hpath
  let tQC : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    (fromQCMetricSpace R hg hgenus hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let tB : TopologicalSpace
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) := inferInstance
  let H : @Homeomorph (TeichmullerSpace.{u, u} R)
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) tQC tB :=
    fromQCBersCoordinateHomeomorph R hg hgenus hPresentation hΓ hfree hp
  exact @Homeomorph.pathConnectedSpace
    (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp))
    (TeichmullerSpace.{u, u} R) tB tQC inferInstance
    (@Homeomorph.symm (TeichmullerSpace.{u, u} R)
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) tQC tB H)

/-- The original coefficient quotient is path connected under actual QC smoothing. -/
theorem canonical_pathConnected_of_smoothing
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u}) :
    PathConnectedSpace (TeichmullerSpace.{u, u} R) := by
  have hpath :=
    (isOpen_range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp).isConnected_iff_isPathConnected.mp
      (isConnected_range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp)
  let : PathConnectedSpace
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) :=
    isPathConnected_iff_pathConnectedSpace.mp hpath
  exact
    (canonicalBersCoordinateHomeomorph R hg hgenus
      hPresentation hΓ hfree hp hsmooth).symm.pathConnectedSpace

/-- Hausdorff separation concerns the actual canonical coefficient quotient topology. -/
theorem canonical_t2Space_of_smoothing
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u}) :
    T2Space (TeichmullerSpace.{u, u} R) :=
  (canonicalBersCoordinateHomeomorph R hg hgenus
    hPresentation hΓ hfree hp hsmooth).symm.t2Space

/-- The actual finite-dimensional Bers embedding supplies a countable basis. -/
theorem canonical_secondCountable_of_smoothing
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u}) :
    SecondCountableTopology (TeichmullerSpace.{u, u} R) :=
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    hPresentation hΓ hfree hp hsmooth).isEmbedding.secondCountableTopology

/-- Local compactness comes from the actual finite-dimensional open Bers image. -/
theorem canonical_locallyCompact_of_smoothing
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u}) :
    LocallyCompactSpace (TeichmullerSpace.{u, u} R) :=
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    hPresentation hΓ hfree hp hsmooth).locallyCompactSpace

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
