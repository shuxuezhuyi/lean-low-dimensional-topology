/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.OriginalQuotientArea
/-!
# Area decreases under the quotient projection

The image of a measurable set in the Fuchsian orbit quotient has area at
most the original set, by the countable translated-selector decomposition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance quotientAreaLocalSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance quotientAreaLocalSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Projecting an actual measurable set cannot increase its original hyperbolic area. -/
theorem fuchsianQuotientAreaMeasure_image_le {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) (hS : MeasurableSet S) :
    fuchsianQuotientAreaMeasure P (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier '' S) ≤ P.area S := by
  let _quotientAreaLocalCountable : Countable H := P.countable
  have hsat : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier ⁻¹'
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier ''
        S) = ⋃ g : H, g • S :=
    MulAction.quotient_preimage_image_eq_union_mul S (G := H)
  have hm : MeasurableSet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier '' S) := by
    rw [measurableSet_quotient]
    change MeasurableSet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H
      P.domain.carrier ⁻¹'
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier '' S))
    rw [hsat]
    exact MeasurableSet.iUnion fun g => hS.const_smul g
  have hF : MeasureTheory.IsFundamentalDomain H (fuchsianAreaSelector P) P.area :=
    (fuchsianAreaSelector_spec P).1.measureFundamentalDomain (fuchsianAreaSelector_spec P).2
  rw [fuchsianQuotientAreaMeasure_apply P _ (fuchsianAreaSelector_spec P).1
    (fuchsianAreaSelector_spec P).2 _ hm, hsat, iUnion_inter, hF.measure_eq_tsum S]
  exact measure_iUnion_le _

end LowDimensionalTopology.Geometry.Fuchsian
