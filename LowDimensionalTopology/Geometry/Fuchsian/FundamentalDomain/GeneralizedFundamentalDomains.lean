/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianCharts
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicDirichletBoundary
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section
local instance geometricFundamentalSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance geometricFundamentalSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩
/-- Inverse Cayley transports the entire genuine disc, not just selected points. -/
theorem cayleyInverse_unitDisc_image : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
  rw [←cayleyMobius_image_openHalfPlane]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_image_image _

/-- The original unit-disc group's entire conjugate is the exact native H action in the existing Dirichlet coordinate. -/
theorem unitDisc_halfPlaneConjugate_nativeAction {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (x : P.domain.carrier) :
    let E:=P.asFuchsianDisc.nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
    let hE : E.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=cayleyInverse_unitDisc_image
    let Q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc E hE
    letI :=Q.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H g • P.halfPlaneCoordinate x=
      P.halfPlaneCoordinate (g • x):=by
  let E:=P.asFuchsianDisc.nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  have hE : E.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=cayleyInverse_unitDisc_image
  let Q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc E hE
  let :=Q.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←Q.nativeAction_boundary]
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H g).val.val
    (((P.halfPlaneCoordinate x : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
    (((P.halfPlaneCoordinate (g • x) : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [P.halfPlaneCoordinate_extended,P.halfPlaneCoordinate_extended]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val (g.val.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val x.val)))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val (g.val.val x.val)
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm (g.val.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm x.val)))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm (g.val.val x.val)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.apply_symm_apply]

/-- The original free sphere-center condition entails the actual point stabilizer condition. -/
theorem unitDisc_dirichletCenter_of_free {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)
    (hfree : ∀g : H,g • w.val=w.val→g=1) : IsDirichletCenter P w:=by
  intro g hg
  exact hfree g (congrArg Subtype.val hg)

/-- In the actual standard disc, the original normalized-mirror polygon at an interior point is the genuine metric Dirichlet domain. -/
theorem unitDisc_generalizedPolygon_interior_eq_dirichlet {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)
    (hfree : ∀g : H,g • w.val=w.val→g=1) :
    {x : P.domain.carrier | x.val∈generalizedDirichletPolygon P.asFuchsianDisc w.val hfree}=
      dirichletDomain P w:=by
  let E:=P.asFuchsianDisc.nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  have hE : E.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=cayleyInverse_unitDisc_image
  let Q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc E hE
  let :=Q.nativeAction
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H
  let η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=((P.halfPlaneCoordinate w : ℍ) : ℂ)
  have hη : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val w.val=η:=(P.halfPlaneCoordinate_extended w).symm
  have hfree' : ∀g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H,g • η=η→g=1:=by
    intro g hg
    apply subgroupConjugate_point_free H _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ w.val hfree g
    rwa [hη]
  have hepoly:=generalizedDirichletPolygon_center_congr E
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val w.val) η hη
    (subgroupConjugate_point_free H _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ w.val hfree) hfree'
  have hH:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.generalizedDirichletPolygon_halfPlane_interior_eq_dirichlet E hE (P.halfPlaneCoordinate w) hfree'
  ext x
  have hc:=generalizedDirichletPolygon_mem_conjugation P.asFuchsianDisc w.val hfree _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ x.val
  rw [hepoly,←P.halfPlaneCoordinate_extended x] at hc
  change (x.val∈generalizedDirichletPolygon P.asFuchsianDisc w.val hfree) ↔
    ∀g : H,g≠1→P.hyperbolicDist x w<P.hyperbolicDist x (g • w)
  rw [←hc]
  change (P.halfPlaneCoordinate x∈{z : ℍ | ((z : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈generalizedDirichletPolygon E η hfree'}) ↔ _
  rw [hH]
  constructor
  · intro hx g hg
    have hne : e g≠1:=fun he=>hg (e.injective (he.trans (map_one e).symm))
    have hi:=hx (e g) hne
    rw [unitDisc_halfPlaneConjugate_nativeAction P g w] at hi
    exact hi
  · intro hx k hk
    obtain ⟨g,rfl⟩:=e.surjective k
    have hg : g≠1:=by intro he;apply hk;rw [he,map_one]
    have hi:=hx g hg
    rw [unitDisc_halfPlaneConjugate_nativeAction P g w]
    exact hi


/-- In the original standard disc this is precisely the existing true density area. -/
theorem geometricModelArea_asUnitDisc {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P
  : UnitDiscFuchsianGroup H) :
    geometricModelArea P.asFuchsianDisc=P.area:=by
  apply Measure.ext
  intro S hS
  have hq : (1 : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup).val '' P.asFuchsianDisc.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
    change id '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    exact image_id _
  calc
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (geometricDiscChart P.asFuchsianDisc 1 hq ''
      S):=
      geometricModelArea_eq_discChart P.asFuchsianDisc 1 hq S hS
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.finiteCoordinate '' S):=by congr 1
    _=P.area S:=(P.area_apply S hS).symm

/-- Genuine original-disc structures with identical carriers have identical geometric data. -/
theorem fuchsianDisc_eq_of_carrier_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  E : FuchsianDisc H)
    (h : D.carrier=E.carrier) : D=E:=by
  cases D
  cases E
  cases h
  rfl

/-- The literal polygon as an actual subset of its original geometric model. -/
def geometricPolygonDomain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    Set (fuchsianGeometricDomain D).carrier:=
  {x | x.val∈generalizedDirichletPolygon D ξ hfree}

theorem geometricPolygonDomain_conjugate_preimage {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    geometricConjugateHomeomorph D q ⁻¹' geometricPolygonDomain (D.nielsenConjugate q)
      (q.val ξ) (subgroupConjugate_point_free H q ξ hfree)=geometricPolygonDomain D ξ hfree:=by
  ext x
  exact generalizedDirichletPolygon_mem_conjugation D ξ hfree q x.val

/-- The canonical native disc data are exactly the full conjugate original model. -/
theorem geometricDiscData_asFuchsianDisc {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    (geometricDiscData D).asFuchsianDisc=D.nielsenConjugate (geometricDiscNormalizer D):=by
  apply fuchsianDisc_eq_of_carrier_eq
  exact (geometricDiscNormalizer_image D).symm

/-- At an original interior center, the actual original polygon is exactly the genuine metric Dirichlet domain in its true disc coordinate. -/
theorem geometricPolygonDomain_interior_eq_dirichlet {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (w : (fuchsianGeometricDomain D).carrier)
    (hfree : ∀g : H,g • w.val=w.val→g=1) :
    geometricPolygonDomain D w.val hfree=
      geometricDiscHomeomorph D ⁻¹' dirichletDomain (geometricDiscData D) (geometricDiscHomeomorph D w):=by
  let P:=geometricDiscData D
  let q:=geometricDiscNormalizer D
  let f:=geometricDiscHomeomorph D
  have hfree' : ∀g : geometricDiscGroup D,g • (f w).val=(f w).val→g=1:=
    subgroupConjugate_point_free H q w.val hfree
  have hunit:=unitDisc_generalizedPolygon_interior_eq_dirichlet P (f w) hfree'
  ext x
  have hc:=generalizedDirichletPolygon_mem_conjugation D w.val hfree q x.val
  have he:=geometricDiscData_asFuchsianDisc D
  rw [←he] at hc
  change (x.val∈generalizedDirichletPolygon D w.val hfree) ↔ f x∈dirichletDomain P (f w)
  rw [←hunit]
  exact hc.symm

/-- Every original free interior center gives a genuine fundamental domain, with the actual normalization-independent density area. -/
theorem geometricPolygonDomain_interior_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (w : (fuchsianGeometricDomain D).carrier)
    (hfree : ∀g : H,g • w.val=w.val→g=1) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D)
      (geometricPolygonDomain D w.val hfree):=by
  rw [geometricPolygonDomain_interior_eq_dirichlet]
  apply geometricModel_fundamentalDomain_of_disc
  apply dirichletDomain_fundamental
  apply unitDisc_dirichletCenter_of_free
  exact subgroupConjugate_point_free H (geometricDiscNormalizer D) w.val hfree


/-- The identity really is a whole-model H normalization when the original carrier is H. -/
theorem geometricHalfPlane_identity_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    (1 : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup).val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
  change id '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  exact (image_id D.carrier).trans hD

/-- The original sphere H points and native H points, with no change to the literal finite coordinate. -/
def geometricHalfPlaneIdentity {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    (fuchsianGeometricDomain D).carrier≃ₜℍ:=
  geometricHalfPlaneChart D 1 (geometricHalfPlane_identity_image D hD)

theorem geometricHalfPlaneIdentity_extended {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (x :
      (fuchsianGeometricDomain D).carrier) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (geometricHalfPlaneIdentity D hD x)=x.val:=
  geometricHalfPlaneChart_extended D 1 (geometricHalfPlane_identity_image D hD) x

theorem geometricHalfPlaneIdentity_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (g : H) (x
      : (fuchsianGeometricDomain D).carrier) :
    letI :=(_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD).nativeAction
    geometricHalfPlaneIdentity D hD (g • x)=g • geometricHalfPlaneIdentity D hD x:=by
  let Q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD
  let :=Q.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  calc
    _=(g • x).val:=geometricHalfPlaneIdentity_extended D hD (g • x)
    _=g.val.val x.val:=rfl
    _=g.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (geometricHalfPlaneIdentity D hD
      x)):=
      congrArg g.val.val (geometricHalfPlaneIdentity_extended D hD x).symm
    _=_:=Q.nativeAction_boundary g _

/-- The native H density measure and the original model area agree at measure level. -/
theorem geometricHalfPlaneIdentity_volume_map {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    Measure.map (geometricHalfPlaneIdentity D hD).symm volume=geometricModelArea D:=by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (geometricHalfPlaneIdentity D hD).symm.continuous.measurable hS]
  have he : (geometricHalfPlaneIdentity D hD).symm ⁻¹' S=geometricHalfPlaneIdentity D hD '' S:=
    ((geometricHalfPlaneIdentity D hD).toEquiv.image_eq_preimage_symm S).symm
  rw [he]
  exact (geometricModelArea_eq_halfPlaneChart D 1 (geometricHalfPlane_identity_image D hD) S hS).symm

/-- For the true H model and an ordinary free center at infinity, the actual original polygon is a genuine fundamental domain. -/
theorem geometricPolygonDomain_halfPlane_infty_fundamental
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hD :
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hOrd : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D)
      (geometricPolygonDomain D ∞ hfree):=by
  let Q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD
  let :=Q.nativeAction
  have hF:=generalizedDirichletPolygon_halfPlane_infty_fundamental D hD hOrd hfree
  have hG:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage (MulEquiv.refl H)
    (geometricHalfPlaneIdentity D hD)
    (geometricHalfPlaneIdentity_equivariant D hD) hF
  rw [geometricHalfPlaneIdentity_volume_map D hD] at hG
  have he : geometricHalfPlaneIdentity D hD ⁻¹'
      {z : ℍ | ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈generalizedDirichletPolygon D ∞
        hfree}=
      geometricPolygonDomain D ∞ hfree:=by
    ext x
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (geometricHalfPlaneIdentity D hD
      x)∈generalizedDirichletPolygon D ∞ hfree ↔ _
    rw [geometricHalfPlaneIdentity_extended]
    rfl
  rwa [he] at hG


/-- An original ideal point can be sent to infinity while the entire original model is sent to H. -/
theorem geometricBoundary_normalizer_exists {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hξ : ξ∈frontier
      D.carrier) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧ q.val ξ=∞:=by
  let u:=D.halfPlaneNormalizer
  have hB : u.val '' frontier D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
      u) '' frontier D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
    rw [Homeomorph.image_frontier]
    change frontier (u.val '' D.carrier)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
    rw [D.halfPlaneNormalizer_image,nielsen_openHalfPlane_frontier]
  have hη : u.val ξ∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by rw [←hB];exact mem_image_of_mem _ hξ
  obtain ⟨A,hA⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary_exists_sl2_to_infty (u.val
    ξ) hη
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*u,?_,?_⟩
  · change (fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (u.val
    z)) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [←image_image,D.halfPlaneNormalizer_image,realSLMobius_image_openHalfPlane]
  · exact hA

/-- Original ordinary points remain ordinary under the actual whole-group conjugation. -/
theorem geometric_ordinaryCenter_conjugation {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) {ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hξ :
      ξ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H) :
    q.val ξ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H):=by
  change ξ∉_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H at hξ
  change q.val ξ∉_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
  rw [←nielsen_mobiusLimitSet_conjugation H q]
  rintro ⟨η,hη,he⟩
  exact hξ (q.val.injective he ▸ hη)

/-- Every original ordinary free ideal center gives a genuine original-model fundamental domain. -/
theorem geometricPolygonDomain_boundary_fundamental
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∈frontier D.carrier) (hOrd : ξ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • ξ=ξ→g=1) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D)
      (geometricPolygonDomain D ξ hfree):=by
  obtain ⟨q,hq,hqξ⟩:=geometricBoundary_normalizer_exists D ξ hξ
  let E:=D.nielsenConjugate q
  have hE : E.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=hq
  have hOrd' : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H):=by
    rw [←hqξ]
    exact geometric_ordinaryCenter_conjugation q hOrd
  have hfree' :=subgroupConjugate_point_free H q ξ hfree
  have hfreeInf : ∀g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1:=by
    intro g hg
    apply hfree' g
    rwa [hqξ]
  have hF:=geometricPolygonDomain_halfPlane_infty_fundamental E hE hOrd' hfreeInf
  have hc:=generalizedDirichletPolygon_center_congr E (q.val ξ) ∞ hqξ hfree' hfreeInf
  have hs : geometricPolygonDomain E (q.val ξ) hfree'=geometricPolygonDomain E ∞ hfreeInf:=by
    unfold geometricPolygonDomain
    rw [hc]
  rw [←hs] at hF
  have hG:=geometric_fundamentalDomain_conjugate_preimage D q hF
  rwa [geometricPolygonDomain_conjugate_preimage] at hG


/-- Every actual sphere point is interior, ideal, or has its genuine boundary reflection in the original interior. -/
theorem geometricCenter_trichotomy {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    ξ∈D.carrier ∨ ξ∈frontier D.carrier ∨ modelBoundaryReflection D.carrier D.isDisc ξ∈D.carrier:=by
  by_cases hI : ξ∈D.carrier
  · exact Or.inl hI
  by_cases hB : ξ∈frontier D.carrier
  · exact Or.inr (Or.inl hB)
  obtain ⟨q,hq,hboundary⟩:=geometricModelBoundary_normalization D.carrier D.isDisc
  have hm (η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : q.val η∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ↔ η∈D.carrier:=by
    rw [←hq]
    constructor
    · rintro ⟨ζ,hζ,he⟩
      exact q.val.injective he ▸ hζ
    · exact mem_image_of_mem q.val
  have hfront : q.val '' frontier D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
      q) '' frontier D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
    rw [Homeomorph.image_frontier]
    change frontier (q.val '' D.carrier)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
    rw [hq,nielsen_openHalfPlane_frontier]
  have hηB : q.val ξ∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by
    intro he
    rw [←hfront] at he
    obtain ⟨ζ,hζ,he⟩:=he
    exact hB (q.val.injective he ▸ hζ)
  have hne : q.val ξ≠∞:=by
    intro he
    apply hηB
    rw [he]
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary]
  obtain ⟨z,hz⟩:=OnePoint.ne_infty_iff_exists.mp hne
  have hz0 : z.im≠0:=by
    intro he
    apply hηB
    rw [←hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary]
    exact he
  have hzN : ¬0<z.im:=by
    intro he
    apply hI
    apply (hm ξ).mp
    rw [←hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet]
    exact he
  have hzneg : z.im<0:=lt_of_le_of_ne (le_of_not_gt hzN) hz0
  refine Or.inr (Or.inr ((hm _).mp ?_))
  rw [modelBoundaryReflection_coordinate D.carrier D.isDisc q hboundary,←hz,
    _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet,Complex.conj_im]
  linarith

/-- The actual generalized polygon at every original ordinary free center is a genuine fundamental domain. -/
theorem geometricPolygonDomain_isFundamentalDomain_of_ordinary_free_center {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hOrd :
      ξ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • ξ=ξ→g=1) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D)
      (geometricPolygonDomain D ξ hfree):=by
  rcases geometricCenter_trichotomy D ξ with hI|hB|hR
  · exact geometricPolygonDomain_interior_fundamental D ⟨ξ,hI⟩ hfree
  · exact geometricPolygonDomain_boundary_fundamental D ξ hB hOrd hfree
  · have hF:=geometricPolygonDomain_interior_fundamental D
      ⟨modelBoundaryReflection D.carrier D.isDisc ξ,hR⟩ (boundaryReflected_free_center D ξ hfree)
    have he : geometricPolygonDomain D (modelBoundaryReflection D.carrier D.isDisc ξ)
        (boundaryReflected_free_center D ξ hfree)=geometricPolygonDomain D ξ hfree:=by
      unfold geometricPolygonDomain
      rw [generalizedDirichletPolygon_boundaryReflection]
    rwa [he] at hF

end
end LowDimensionalTopology.Geometry.Fuchsian
