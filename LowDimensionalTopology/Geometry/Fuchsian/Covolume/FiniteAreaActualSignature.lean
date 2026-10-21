/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalFiniteAreaCompletionHomeomorph
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance finiteActualSignatureSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteActualSignatureSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual finite-area original Fuchsian quotient admits a genuine cofinite signature, with actual filled-quotient genus and actual elliptic/cusp classes. Its area formula and uniqueness of an independently supplied genus label are separate conclusions. -/
theorem finite_area_actual_cofinite_signature_exists {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D₀:FuchsianDisc H) (F:Set (fuchsianGeometricDomain D₀).carrier)
    (hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D₀).carrier (geometricModelArea D₀) F)
    (harea:geometricModelArea D₀ F≠⊤) :
    ∃g orders cusps,HasCofiniteFuchsianSignature D₀ g orders cusps := by
  obtain ⟨_w,_hw,_hL,_ha,_J,_e,_hc,_hv,_hs,_n,_S,_hr,_hpar,_he,g,hg,_hχ⟩:=
    finite_area_original_word_completion_homeomorph D₀ F hF harea
  let hE:=finite_area_elliptic_classes_finite D₀ F hF harea
  let hP:=finite_area_parabolic_classes_finite D₀ F hF harea
  exact ⟨g,fuchsianEllipticOrderList D₀,Nat.card (FuchsianCyclicConjugacyClasses D₀ .parabolic),
    { ellipticClassesFinite:=hE
      parabolicClassesFinite:=hP
      compact:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.hasTopologicalGenus_compactSpace hg
      topologicalGenus:=hg
      ellipticOrders:=List.Perm.refl _
      cuspCount:=rfl }⟩

end LowDimensionalTopology.Geometry.Fuchsian
