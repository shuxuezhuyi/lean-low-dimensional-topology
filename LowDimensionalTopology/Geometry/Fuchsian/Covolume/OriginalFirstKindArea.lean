/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FirstKindFiniteArea
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalCompletionWeightedEuler
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance originalFirstKindAreaSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance originalFirstKindAreaSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Original finite generation and the first-kind property force finite actual area for every genuine original fundamental domain. -/
theorem firstKind_finitelyGenerated_geometricArea_ne_top {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (hfirst : D₀.IsFirstKind) (hFG : H.FG)
    (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D₀).carrier (geometricModelArea D₀) F) :
    geometricModelArea D₀ F≠⊤ := by
  let q:=geometricDiscNormalizer D₀
  let P:=geometricDiscData D₀
  let E:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hNE:=D₀.firstKind_nonElementary hfirst
  have hNE' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (geometricDiscGroup
    D₀):=hNE.conjugation q
  have : Group.FG H:=(Group.fg_iff_subgroup_fg H).mpr hFG
  have : Group.FG (geometricDiscGroup D₀):=Group.fg_of_surjective (f:=E.toMonoidHom) E.surjective
  have hFG' : (geometricDiscGroup D₀).FG:=(Group.fg_iff_subgroup_fg _).mp inferInstance
  have hfirst' : P.asFuchsianDisc.IsFirstKind:=by
    change (geometricDiscData D₀).asFuchsianDisc.IsFirstKind
    rw [geometricDiscData_asFuchsianDisc]
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.IsFirstKind,fuchsianLimitSet_eq_nonElementary _
      hNE',
      ←nielsen_mobiusLimitSet_conjugation H q,←fuchsianLimitSet_eq_nonElementary H hNE,hfirst,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_frontier D₀.carrier
  have hL:=finite_area_geometricDisc_fundamental_image D₀ F hF
  have ha:=firstKind_finitelyGenerated_area_ne_top P hfirst' hFG' hL
  rwa [geometricDisc_fundamental_area_eq_original D₀ F hF hL] at ha

end LowDimensionalTopology.Geometry.Fuchsian
