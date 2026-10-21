/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCuspClasses
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalFiniteAreaCompletionHomeomorph
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalCompletionWeightedEuler
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawEllipticOrderLists
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.CyclicClassConjugacy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
local instance actualSignatureAreaSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance actualSignatureAreaSphereBorel : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

/-- The true raw corner deficit is exactly the actual original cusp count plus the actual original maximal elliptic class deficits, with repeated orders retained. -/
theorem originalRawCornerClasses_actual_deficit
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    (harea : geometricModelArea D₀ F≠⊤)
    {L : Set (geometricDiscData D₀).domain.carrier}
    (hL : IsConvexFuchsianPolygon (geometricDiscData D₀) L)
    (ha : (geometricDiscData D₀).area L≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide hL,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hL)
    (e : ZMod J.n≃OriginalRefinedSide hL) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    {n : ℕ} (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hr : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D₀) L)
    (hpar : ∀u : Circle,(u : ℂ)∈fuchsianPolygonIdealBoundary (geometricDiscData D₀) L→
      ∃f : geometricDiscGroup D₀,f≠1∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val∧
        f.val.val ((u : ℂ) : Mobius.ExtendedComplex)=((u : ℂ) : Mobius.ExtendedComplex)) :
    let _actualDeficitOriginalFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
      finite_area_elliptic_classes_finite D₀ F hF harea
    ∑q : Quotient (originalRawCornerSetoid J e),(1-originalRawCornerClassWeight hL ha J hc hv e hs q)=
      (Nat.card (FuchsianCyclicConjugacyClasses D₀ .parabolic) : ℝ)+
        ((fuchsianEllipticOrderList D₀).map (fun m : ℕ=>1-1/(m : ℝ))).sum := by
  let _actualDeficitOriginalFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
    finite_area_elliptic_classes_finite D₀ F hF harea
  let P:=geometricDiscData D₀
  let q:=geometricDiscNormalizer D₀
  let _actualDeficitNormalizedFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hL (finite_area_polygon_finite_sides hL ha)
  let _actualDeficitConjugateFinite : Finite (FuchsianCyclicConjugacyClasses (D₀.nielsenConjugate q) .elliptic):=
    fuchsianCyclicClassConjugacyEquiv_finite D₀ .elliptic q
  have hglobal : (fuchsianEllipticOrderList D₀).Perm (fuchsianEllipticOrderList P.asFuchsianDisc):=by
    have h:=fuchsianEllipticOrderList_global_conjugation D₀ q
    simpa only [P,geometricDiscData_asFuchsianDisc,q] using h
  have horders : (originalRawEllipticOrders hL ha J hc hv e hs).Perm (fuchsianEllipticOrderList D₀):=
    (originalRawEllipticOrders_perm_actual hL ha J hc hv e hs).trans hglobal.symm
  rw [originalRawCornerClasses_deficit_partition,originalRawZeroClassCount_eq_cusps D₀ hL ha J hc hv e hs S hr hpar,
    (horders.map (fun m : ℕ=>1-1/(m : ℝ))).sum_eq]

/-- Original finite quotient area equals the exact expression in actual cusp classes, actual elliptic orders and a genuine genus of its unique actual completion. -/
theorem finite_area_original_actual_signature_area
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    (harea : geometricModelArea D₀ F≠⊤) :
    let _actualSignatureAreaOriginalFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
      finite_area_elliptic_classes_finite D₀ F hF harea
    ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D₀) g ∧
      (geometricModelArea D₀ F).toReal=2*Real.pi*(2*(g : ℝ)-2+
        (Nat.card (FuchsianCyclicConjugacyClasses D₀ .parabolic) : ℝ)+
        ((fuchsianEllipticOrderList D₀).map (fun m : ℕ=>1-1/(m : ℝ))).sum) := by
  let _actualSignatureAreaOriginalFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
    finite_area_elliptic_classes_finite D₀ F hF harea
  obtain ⟨w,_hw,hL,ha,J,e,hc,hv,hs,n,S,hr,hpar,_E,g,hg,hχZ⟩:=
    finite_area_original_word_completion_homeomorph D₀ F hF harea
  have hχ : (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation : ℝ)=2-2*(g : ℝ):=
    by exact_mod_cast hχZ
  have hA:=originalRawCornerClasses_weightedEuler hL ha J hc hv e hs
  rw [hχ,originalRawCornerClasses_actual_deficit D₀ F hF harea hL ha J hc hv e hs S hr hpar] at hA
  refine ⟨g,hg,?_⟩
  rw [geometricDisc_fundamental_area_eq_original D₀ F hF hL.locallyFinite.fundamental] at hA
  linear_combination hA

end LowDimensionalTopology.Geometry.Fuchsian
