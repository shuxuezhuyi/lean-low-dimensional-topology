/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Area
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaIdealVertices
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance originalQuotientSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance originalQuotientSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- Every original Fuchsian disc action admits an actual area-measurable point selector. -/
theorem exists_fuchsianAreaSelector {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) :
    ∃F:Set P.domain.carrier,IsFuchsianFundamentalSet P F ∧NullMeasurableSet F P.area := by
  obtain ⟨w,hw,_hgood⟩:=exists_actual_dirichlet_horocycle_good_center P
  have hD:=dirichletDomain_fundamental P w hw
  obtain ⟨F,hF,hDF,hFC⟩:=hD.exists_fundamentalSet
  exact ⟨F,hF,hD.nullMeasurableSet_between hDF hFC⟩

def fuchsianAreaSelector {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) : Set P.domain.carrier:=
  (exists_fuchsianAreaSelector P).choose

theorem fuchsianAreaSelector_spec {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) :
    IsFuchsianFundamentalSet P (fuchsianAreaSelector P) ∧NullMeasurableSet (fuchsianAreaSelector P) P.area :=
  (exists_fuchsianAreaSelector P).choose_spec

/-- The actual hyperbolic measure on the original whole-group orbit quotient, obtained from the original invariant density. -/
def fuchsianQuotientAreaMeasure {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) :
    Measure (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H P.domain.carrier):=
  (P.area.restrict (fuchsianAreaSelector
    P)).map (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier)

/-- All actual area-measurable point selectors produce the same entire quotient measure. -/
theorem fuchsianQuotientAreaMeasure_eq {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (F:Set P.domain.carrier) (hF:IsFuchsianFundamentalSet P F) (hm:NullMeasurableSet F P.area) :
    fuchsianQuotientAreaMeasure P=(P.area.restrict F).map (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier) := by
  let :Countable H:=P.countable
  exact (fuchsianAreaSelector_spec P).1.measureFundamentalDomain (fuchsianAreaSelector_spec P).2
    |>.quotientMeasure_eq P.area (hF.measureFundamentalDomain hm)

/-- Local quotient area is literally the original density on the lift intersected with any actual selector. -/
theorem fuchsianQuotientAreaMeasure_apply {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (F:Set P.domain.carrier) (hF:IsFuchsianFundamentalSet P F) (hm:NullMeasurableSet F P.area)
    (U:Set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H
      P.domain.carrier)) (hU:MeasurableSet U) :
    fuchsianQuotientAreaMeasure P U=P.area ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier ⁻¹' U) ∩F) := by
  have hπ:Measurable (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H
    P.domain.carrier):=fun _ h=>measurableSet_quotient.mp h
  rw [fuchsianQuotientAreaMeasure_eq P F hF hm,Measure.map_apply hπ hU,
    Measure.restrict_apply (hπ hU)]

/-- The original measurable fundamental set has precisely the area of the actual original orbit quotient. -/
theorem fuchsianFundamentalSet_quotient_area {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (F:Set P.domain.carrier) (hF:IsFuchsianFundamentalSet P F) (hm:NullMeasurableSet F P.area) :
    P.area F=fuchsianQuotientAreaMeasure P univ := by
  rw [fuchsianQuotientAreaMeasure_apply P F hF hm univ MeasurableSet.univ]
  simp only [preimage_univ,univ_inter]

/-- The same original quotient measure can be computed with the original open fundamental domain itself. -/
theorem fuchsianFundamentalDomain_quotient_measure {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (D:Set P.domain.carrier) (hD:IsFuchsianFundamentalDomain P D) :
    fuchsianQuotientAreaMeasure P=(P.area.restrict D).map (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier) := by
  obtain ⟨F,hF,hDF,hFC⟩:=hD.exists_fundamentalSet
  rw [fuchsianQuotientAreaMeasure_eq P F hF (hD.nullMeasurableSet_between hDF hFC),
    Measure.restrict_congr_set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.ae_eq_of_between H P.domain.carrier hD hDF hFC)]

/-- The actual area of every genuine original fundamental domain equals the original quotient area, with no finiteness or elliptic-freeness premise. -/
theorem fuchsianFundamentalDomain_quotient_area {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (D:Set P.domain.carrier) (hD:IsFuchsianFundamentalDomain P D) :
    P.area D=fuchsianQuotientAreaMeasure P univ := by
  obtain ⟨F,hF,hDF,hFC⟩:=hD.exists_fundamentalSet
  exact (hD.area_between hDF hFC).trans
    (fuchsianFundamentalSet_quotient_area P F hF (hD.nullMeasurableSet_between hDF hFC))

/-- The true quotient area agrees with the standard covolume, using an independently proved actual fundamental domain. -/
theorem fuchsianQuotientAreaMeasure_covolume {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H) :
    fuchsianQuotientAreaMeasure P univ=MeasureTheory.covolume H P.domain.carrier P.area := by
  let :Countable H:=P.countable
  have hF:MeasureTheory.IsFundamentalDomain H (fuchsianAreaSelector P) P.area:=
    (fuchsianAreaSelector_spec P).1.measureFundamentalDomain (fuchsianAreaSelector_spec P).2
  rw [←fuchsianFundamentalSet_quotient_area P _ (fuchsianAreaSelector_spec P).1 (fuchsianAreaSelector_spec P).2]
  exact (hF.covolume_eq_volume P.area).symm

end LowDimensionalTopology.Geometry.Fuchsian
