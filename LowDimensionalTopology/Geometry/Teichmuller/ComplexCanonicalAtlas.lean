module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersMetric
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexQuotientTopology

/-!
# A complex atlas on the actual coefficient quotient topology

The coordinate map is the actual Bers map of the corresponding marked-surface
class. Its metric comparison is proved independently. Quantitative global QC
smoothing is the explicit analytic input needed to compare the realized
coefficient quotient topology with that metric topology.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped ContDiff Manifold

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
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- The canonical coefficient quotient has the actual bounded open Bers image. -/
def canonicalBersCoordinateHomeomorph : TeichmullerSpace.{u, u} R ≃ₜ
    range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
  let tQC : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    (fromQCMetricSpace R hg hgenus hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let tB : TopologicalSpace
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) := inferInstance
  let H : @Homeomorph (TeichmullerSpace.{u, u} R)
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) tQC tB :=
    fromQCBersCoordinateHomeomorph R hg hgenus hPresentation hΓ hfree hp
  let E : TeichmullerSpace.{u, u} R ≃
      range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) :=
    @Homeomorph.toEquiv (TeichmullerSpace.{u, u} R)
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) tQC tB H
  refine @Homeomorph.mk (TeichmullerSpace.{u, u} R)
    (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp))
    (beltramiTopology R) tB E ?_ ?_
  · change @Continuous (TeichmullerSpace.{u, u} R)
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp))
      (beltramiTopology R) tB E
    rw [beltramiTopology_eq_fromQC_of_smoothing R hg hgenus hPresentation hsmooth]
    exact @Homeomorph.continuous_toFun (TeichmullerSpace.{u, u} R)
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) tQC tB H
  · change @Continuous
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp))
      (TeichmullerSpace.{u, u} R) tB (beltramiTopology R) E.symm
    rw [beltramiTopology_eq_fromQC_of_smoothing R hg hgenus hPresentation hsmooth]
    exact @Homeomorph.continuous_invFun (TeichmullerSpace.{u, u} R)
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) tQC tB H

include hsmooth

/-- The actual Bers coordinates are an open embedding for the canonical topology. -/
theorem canonicalBersCoordinates_isOpenEmbedding : Topology.IsOpenEmbedding
    (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
  have he : Topology.IsEmbedding
      (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
    change Topology.IsEmbedding (Subtype.val ∘
      canonicalBersCoordinateHomeomorph R hg hgenus hPresentation hΓ hfree hp hsmooth)
    exact Topology.IsEmbedding.subtypeVal.comp
      (canonicalBersCoordinateHomeomorph R hg hgenus hPresentation hΓ hfree hp hsmooth).isEmbedding
  exact ⟨he, isOpen_range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp⟩

/-- An explicit complex atlas on the already defined native quotient topology. -/
@[instance_reducible]
def canonicalComplexChartedSpace :
    ChartedSpace (Fin (3 * g - 3) → ℂ) (TeichmullerSpace.{u, u} R) :=
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    hPresentation hΓ hfree hp hsmooth).singletonChartedSpace

/-- Its actual transition maps are analytic. The topology is the original
coinduced realized-coefficient topology throughout this statement. -/
theorem canonicalComplex_isManifold :
    let : ChartedSpace (Fin (3 * g - 3) → ℂ) (TeichmullerSpace.{u, u} R) :=
      canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    IsManifold 𝓘(ℂ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace.{u, u} R) :=
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    hPresentation hΓ hfree hp hsmooth).isManifold_singleton

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
