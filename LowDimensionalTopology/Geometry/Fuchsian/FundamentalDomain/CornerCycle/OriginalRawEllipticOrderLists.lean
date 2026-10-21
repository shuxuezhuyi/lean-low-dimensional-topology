/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawParabolicProfiles
public import Mathlib.Data.List.NodupEquivFin
/-!
# Elliptic order lists from raw corners

The cone classes are exactly the raw classes with weight strictly between zero
and one. Their orders give the full elliptic order multiset, with multiplicity,
and transport the small-area parabolic profile to the original group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc

/- BEGIN OWN ORIGINAL RAW ELLIPTIC ORDER LISTS -/
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
section ActualRawEllipticOrders
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
  {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
  (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
    hD,v.carrier))
  (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
    originalRefinedEndpointSet hD)
  (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)

/-- Genuine elliptic raw classes are exactly the geometric weights strictly between zero and one. -/
theorem originalRawEllipticClass_iff_weight (q : Quotient (originalRawCornerSetoid J e)) :
    originalRawEllipticClass hD J hv e q ↔
      0<originalRawCornerClassWeight hD ha J hc hv e hs q ∧
      originalRawCornerClassWeight hD ha J hc hv e hs q<1 := by
  constructor
  · rintro ⟨i,x,hi,hx,he⟩
    rw [←hi,originalRawCornerClassWeight_finite hD ha J hc hv e hs i x hx]
    have hp : 0<(fuchsianPointOrder P x : ℝ):=by exact_mod_cast P.pointOrder_pos x
    have hne : fuchsianPointOrder P x≠1:=fun h=>he ((isAccidentalFuchsianPoint_iff_pointOrder_one P x).mpr h)
    have htwo : 2≤fuchsianPointOrder P x:=by have hh:=P.pointOrder_pos x;omega
    exact ⟨one_div_pos.mpr hp,(div_lt_one hp).mpr (by exact_mod_cast (show 1<fuchsianPointOrder P x by omega))⟩
  · intro h
    have hn : 0<originalRawCornerClassOrder hD J hv e q:=by
      by_contra hn
      have hz : originalRawCornerClassOrder hD J hv e q=0:=by omega
      rw [originalRawCornerClassWeight_order,hz,Nat.cast_zero,div_zero] at h
      exact lt_irrefl 0 h.1
    have hfinite:=(originalRawCornerClassOrder_pos_iff hD J hv e q).mp hn
    let x:=P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
      (originalCyclicVertex hD J hv q.out) hfinite)
    have hx : originalCyclicVertex hD J hv q.out=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hfinite).symm
    refine ⟨q.out,x,Quotient.out_eq q,hx,?_⟩
    intro he
    have hw:=originalRawCornerClassWeight_finite hD ha J hc hv e hs q.out x hx
    rw [Quotient.out_eq] at hw
    rw [hw,(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp he] at h
    norm_num at h

/-- The actual nontrivial finite raw classes are equivalent to all actual maximal elliptic cyclic conjugacy classes. -/
def originalRawConeClassesEquiv :
    ↥(originalRawConeClasses hD ha J hc hv e hs) ≃
      FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic :=
  (Equiv.subtypeEquivRight (fun q=>by
    simp only [originalRawConeClasses,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (originalRawEllipticClass_iff_weight hD ha J hc hv e hs q).symm)).trans
    (originalRawEllipticClassesEquiv hD ha J hc hv e hs)

/-- The actual conjugacy-class equivalence retains the true stabilizer order of each raw class. -/
theorem originalRawConeClassesEquiv_order (q : ↥(originalRawConeClasses hD ha J hc hv e hs)) :
    fuchsianEllipticClassOrder P.asFuchsianDisc (originalRawConeClassesEquiv hD ha J hc hv e hs q)=
      originalRawCornerClassOrder hD J hv e q.val := by
  have hq : originalRawEllipticClass hD J hv e q.val:=
    (originalRawEllipticClass_iff_weight hD ha J hc hv e hs q.val).mpr (Finset.mem_filter.mp q.property).2
  have hw:=originalRawEllipticClass_weight hD ha J hc hv e hs ⟨q.val,hq⟩
  rw [originalRawCornerClassWeight_order] at hw
  have hn : (originalRawCornerClassOrder hD J hv e q.val : ℝ)=
      (fuchsianEllipticClassOrder P.asFuchsianDisc (originalRawEllipticClassMap hD J hv e ⟨q.val,hq⟩) : ℝ):=
    inv_injective (by simpa only [one_div] using hw)
  exact_mod_cast hn.symm

/-- The raw order list is the original group's complete elliptic order list, with all multiplicities retained. -/
theorem originalRawEllipticOrders_perm_actual :
    let _originalRawOrderListActualFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD (finite_area_polygon_finite_sides hD ha)
    (originalRawEllipticOrders hD ha J hc hv e hs).Perm (fuchsianEllipticOrderList P.asFuchsianDisc) := by
  let _originalRawOrderListActualFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD (finite_area_polygon_finite_sides hD ha)
  let C:=originalRawConeClasses hD ha J hc hv e hs
  let L:=C.toList
  let originalRawOrderListActualFintype : Fintype (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    Fintype.ofFinite _
  let E0 : Fin L.length≃↥C:=
    (List.Nodup.getEquiv L C.nodup_toList).trans
      (Equiv.subtypeEquivRight (fun q=>Finset.mem_toList))
  let E:=E0.trans ((originalRawConeClassesEquiv hD ha J hc hv e hs).trans
    (Fintype.equivFin (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic)))
  change (L.map (originalRawCornerClassOrder hD J hv e)).Perm
    (List.ofFn (fun i=>fuchsianEllipticClassOrder P.asFuchsianDisc
      ((Fintype.equivFin (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic)).symm i)))
  rw [←List.ofFn_getElem_eq_map L (originalRawCornerClassOrder hD J hv e)]
  apply signature_orderList_perm_of_equiv E
  intro i
  simp only [E,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact originalRawConeClassesEquiv_order hD ha J hc hv e hs (E0 i)

end ActualRawEllipticOrders
end LowDimensionalTopology.Geometry.Fuchsian

/- BEGIN OWN ORIGINAL PARABOLIC ELLIPTIC PROFILES CONSUMER -/
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical

/-- The original finite-area polygon and an actual parabolic determine the original group's complete small-area elliptic order alternatives. -/
theorem finite_area_parabolic_original_elliptic_profiles {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (f : H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (hsmall : (P.area D).toReal<Real.pi) :
    let _originalParabolicProfileActualFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD (finite_area_polygon_finite_sides hD ha)
    ((∃q : ℕ,3≤q ∧ (fuchsianEllipticOrderList P.asFuchsianDisc).Perm [2,q]) ∨
      (∃q : ℕ,(q=3 ∨ q=4 ∨ q=5) ∧ (fuchsianEllipticOrderList P.asFuchsianDisc).Perm [3,q])) := by
  let _originalParabolicProfileActualFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD (finite_area_polygon_finite_sides hD ha)
  obtain ⟨J,e,hc,hv,hs,_g,_hg,_hg0,_hz,hprofiles⟩:=
    finite_area_parabolic_original_raw_profiles hD ha f hf hsmall
  have hp:=originalRawEllipticOrders_perm_actual hD ha J hc hv e hs
  rcases hprofiles with ⟨q,hq,hperm⟩|⟨q,hq,hperm⟩
  · exact Or.inl ⟨q,hq,hp.symm.trans hperm⟩
  · exact Or.inr ⟨q,hq,hp.symm.trans hperm⟩

end LowDimensionalTopology.Geometry.Fuchsian
