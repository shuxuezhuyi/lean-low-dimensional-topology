/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealBoundary
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeSideEndpointTransport
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletEquivariance
public import Mathlib.Analysis.Normed.Affine.Convex
/-!
# Compactified polygon sides

Closed Klein coordinates identify each side closure with a segment having two
distinct finite or ideal endpoints. The extended group action agrees with the
original Mobius action and carries paired sides and their endpoint sets exactly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane Complex.UnitDisc MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine nontrivial compact convex collinear plane set is exactly a closed segment with distinct actual endpoints. -/
theorem compact_convex_collinear_eq_segment (K : Set ℂ) (hK : IsCompact K)
    (hc : Convex ℝ K) (hcol : Collinear ℝ K) (hn : K.Nontrivial) :
    ∃a∈K,∃b∈K,a≠b∧K=segment ℝ a b := by
  obtain ⟨u,hu,v,hv,huv⟩:=hn
  obtain ⟨p,hp,hmax⟩:=(hK.prod hK).exists_isMaxOn ⟨(u,v),hu,hv⟩
    ((continuous_fst.dist continuous_snd).continuousOn)
  let a:=p.1
  let b:=p.2
  have hab : a≠b:=by
    intro he
    have hh:=hmax (show (u,v)∈K×ˢK from ⟨hu,hv⟩)
    change dist u v≤dist a b at hh
    rw [he,dist_self] at hh
    exact huv (dist_eq_zero.mp (le_antisymm hh dist_nonneg))
  refine ⟨a,hp.1,b,hp.2,hab,subset_antisymm ?_ (hc.segment_subset hp.1 hp.2)⟩
  intro x hx
  have htriple : Collinear ℝ ({a,x,b} : Set ℂ):=hcol.subset (by
    rintro y (rfl|rfl|rfl)
    · exact hp.1
    · exact hx
    · exact hp.2)
  rcases htriple.wbtw_or_wbtw_or_wbtw with h|h|h
  · exact h.mem_segment
  · have hbound:=hmax (show (x,a)∈K×ˢK from ⟨hx,hp.1⟩)
    change dist x a≤dist a b at hbound
    have hadd:=h.dist_add_dist
    rw [dist_comm b a] at hadd
    have hxb : x=b:=dist_eq_zero.mp (by linarith [dist_nonneg (x:=x) (y:=b)])
    rw [hxb]
    exact right_mem_segment ℝ a b
  · have hbound:=hmax (show (b,x)∈K×ˢK from ⟨hp.2,hx⟩)
    change dist b x≤dist a b at hbound
    have hadd:=h.dist_add_dist
    rw [dist_comm b a] at hadd
    have hax : a=x:=dist_eq_zero.mp (by linarith [dist_nonneg (x:=a) (y:=x)])
    rw [←hax]
    exact left_mem_segment ℝ a b

/-- The actual compactified closure of one original polygon side. -/
def fuchsianSideClosedModel {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) : Set 𝕔𝔻:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' s.val)

/-- Its actual closed Klein image is the literal Euclidean closure of the original Klein side. -/
theorem fuchsianSideClosedModel_klein_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' fuchsianSideClosedModel s=closure (P.kleinCoordinate '' s.val) := by
  rw [fuchsianSideClosedModel,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
  rfl

/-- The literal compact Klein side closure is compact, convex, collinear and nontrivial. -/
theorem fuchsianSideClosedModel_klein_geometry {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) :
    IsCompact (closure (P.kleinCoordinate '' s.val))∧
      Convex ℝ (closure (P.kleinCoordinate '' s.val))∧
      Collinear ℝ (closure (P.kleinCoordinate '' s.val))∧
      (closure (P.kleinCoordinate '' s.val)).Nontrivial := by
  have hcompact : IsCompact (closure (P.kleinCoordinate '' s.val)):=by
    rw [←fuchsianSideClosedModel_klein_image s]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isCompact_discClosedModelClosure
      _).image _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous
  have hconv : Convex ℝ (closure (P.kleinCoordinate '' s.val)):=by
    have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp s.property.2.1.1
    rw [image_image] at hh
    exact hh.closure
  obtain ⟨N,hN⟩:=s.property.2.1.2
  obtain ⟨m,t,hm,he⟩:=N.exists_klein_linear_equation
  have hline : ∀x∈s.val,inner ℝ m (P.kleinCoordinate x)=t:=by
    intro x hx
    exact (he (P.finiteCoordinate x)).mp (hN (mem_image_of_mem _ hx))
  obtain ⟨a,ha,_b,_hb,_hab⟩:=s.property.2.2
  have hsub : closure (P.kleinCoordinate '' s.val)⊆{z : ℂ | inner ℝ m z=inner ℝ m (P.kleinCoordinate a)}:=by
    rw [hline a ha]
    apply closure_minimal _ (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    rintro _ ⟨x,hx,rfl⟩
    exact hline x hx
  have hlevel : Collinear ℝ {z : ℂ | inner ℝ m z=inner ℝ m (P.kleinCoordinate a)}:=by
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨P.kleinCoordinate a,Complex.I*m,?_⟩
    intro z hz
    have horth : inner ℝ m (z-P.kleinCoordinate a)=0:=by rw [inner_sub_right,hz,sub_self]
    obtain ⟨t,ht⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul m (z-P.kleinCoordinate a) hm horth
    exact ⟨t,sub_eq_iff_eq_add.mp ht⟩
  have hcoll : Collinear ℝ (closure (P.kleinCoordinate '' s.val)):=hlevel.subset hsub
  have hn : (closure (P.kleinCoordinate '' s.val)).Nontrivial:=
    (s.property.2.2.image P.kleinCoordinate_isOpenEmbedding.injective).mono subset_closure
  exact ⟨hcompact,hconv,hcoll,hn⟩

/-- Every original actual side has two distinct genuine compactified endpoints and its full closure is exactly their genuine finite-or-ideal geodesic segment. No finite-area or finite-sided hypothesis is needed. -/
theorem fuchsianSideClosedModel_eq_segment {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) :
    ∃p q : 𝕔𝔻,p≠q∧fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q := by
  obtain ⟨hc,hv,hl,hn⟩:=fuchsianSideClosedModel_klein_geometry s
  obtain ⟨a,ha,b,hb,hab,he⟩:=compact_convex_collinear_eq_segment _ hc hv hl hn
  rw [←fuchsianSideClosedModel_klein_image s] at ha hb he
  obtain ⟨p,_hp,rfl⟩:=ha
  obtain ⟨q,_hq,rfl⟩:=hb
  refine ⟨p,q,fun hpq=>hab (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hpq),?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.injective.image_injective
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]

/-- An original actual side is closed in the original hyperbolic domain. -/
theorem fuchsian_polygon_side_isClosed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) : IsClosed s.val := by
  obtain ⟨g,_hg,he⟩:=s.property.1
  rw [he]
  exact isClosed_closure.inter (fuchsianDomainTile_closed P L g)

/-- The compactified original side retains exactly its original finite native points. -/
theorem fuchsianSideClosedModel_finite_preimage {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' fuchsianSideClosedModel s=P.finiteCoordinate '' s.val := by
  rw [fuchsianSideClosedModel,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage]
  change closure (P.finiteCoordinate '' s.val)=_
  rw [←P.finiteCoordinate.image_closure,(fuchsian_polygon_side_isClosed s).closure_eq]

/-- Membership at each original finite side point is unchanged by compactification. -/
theorem mem_fuchsianSideClosedModel_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) (x : P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈fuchsianSideClosedModel s↔x∈s.val := by
  change P.finiteCoordinate x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' fuchsianSideClosedModel s↔_
  rw [fuchsianSideClosedModel_finite_preimage]
  exact P.finiteCoordinate.injective.mem_set_image

/-- The genuine compactified side has its literal original ambient sphere closure. -/
theorem fuchsianSideClosedModel_ambient {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended '' fuchsianSideClosedModel s=
      closure ((Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' s.val) := by
  rw [fuchsianSideClosedModel,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure_ambient]
  have he : (fun z : 𝔻=>((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' (P.finiteCoordinate ''
    s.val)=
      (Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' s.val:=by
    rw [image_image]
    congr 1
    funext x
    exact P.finiteCoordinate_extended x
  rw [he]

/-- The actual Klein closure of each original side lies in the actual original polygon Klein closure. -/
theorem fuchsianSideClosedModel_klein_subset_polygon {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (s : FuchsianPolygonSides P L) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' fuchsianSideClosedModel s⊆closure (P.kleinCoordinate '' L) := by
  rw [fuchsianSideClosedModel_klein_image]
  apply closure_minimal _ isClosed_closure
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨g,_hg,he⟩:=s.property.1
  have hxL : x∈closure L:=(he ▸ hx).1
  exact mem_closure_image P.kleinCoordinate_isOpenEmbedding.continuous.continuousAt hxL

/-- The actual original group action extended to the genuine compactified disc by its existing native isometry. -/
def UnitDiscFuchsianGroup.compactifiedAction {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry:=
  _root_.LowDimensionalTopology.Geometry.Polygon.nativeClosedDiscIsometry (P.halfPlaneAction g)

/-- This extension agrees with the actual original action at every original finite point. -/
theorem UnitDiscFuchsianGroup.compactifiedAction_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (x : P.domain.carrier) :
    (P.compactifiedAction g).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate (g•x)) := by
  have hi (y : P.domain.carrier) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate y)=P.finiteCoordinate y:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane _
  have ht:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeClosedDiscIsometry_commutes (P.halfPlaneAction
    g) (P.halfPlaneCoordinate x)
  rw [hi,P.halfPlaneAction_coordinate,hi] at ht
  exact ht

/-- The compactified action is exactly the literal original Mobius transformation on every actual finite or ideal sphere point. -/
theorem UnitDiscFuchsianGroup.compactifiedAction_sphere {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (p : 𝕔𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended ((P.compactifiedAction g).closedMap p)=g.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p) := by
  have he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended ∘ (P.compactifiedAction
    g).closedMap)=
      (g.val.val ∘ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended):=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_discToClosedModel.equalizer
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.continuous.comp
        (P.compactifiedAction g).closedMap.continuous)
      ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph g.val).continuous.comp
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.continuous)
    funext z
    let x:=P.finiteCoordinate.symm z
    have hx : P.finiteCoordinate x=z:=P.finiteCoordinate.apply_symm_apply z
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended ((P.compactifiedAction g).closedMap
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z))=
      g.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z))
    rw [←hx,P.compactifiedAction_finite]
    change (((P.finiteCoordinate (g•x):𝔻):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      g.val.val ((((P.finiteCoordinate x:𝔻):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    rw [P.finiteCoordinate_extended,P.finiteCoordinate_extended]
    rfl
  exact congrFun he p

/-- Actual original group images commute with the genuine compactified closure, including ideal endpoints. -/
theorem UnitDiscFuchsianGroup.compactifiedAction_image_closedModel {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (A : Set P.domain.carrier) :
    (P.compactifiedAction
      g).closedMap '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate ''
      A)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' (g•A)) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,(P.compactifiedAction
    g).closedMap.image_closure,image_image,image_image]
  have he : (fun x : P.domain.carrier=>(P.compactifiedAction g).closedMap
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)))=
      (fun x=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate (g•x))):=by
    funext x
    exact P.compactifiedAction_finite g x
  rw [he]
  change closure ((fun x : P.domain.carrier=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (P.finiteCoordinate (g•x))) '' A)=
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' (P.finiteCoordinate '' ((fun x :
      P.domain.carrier=>g•x) '' A)))
  rw [image_image,image_image]

/-- The original paired side is transported exactly, with its full finite-or-ideal compactified closure. -/
theorem fuchsianSideClosedModel_paired_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (hL : IsConvexFuchsianPolygon P L) (s : FuchsianPolygonSides P L) :
    (P.compactifiedAction (fuchsianSideElement hL s)⁻¹).closedMap '' fuchsianSideClosedModel s=
      fuchsianSideClosedModel (fuchsianPairedSide hL s) := by
  rw [fuchsianSideClosedModel,P.compactifiedAction_image_closedModel]
  rfl

/-- The literal original side pairing carries the entire genuine endpoint pair to the actual paired endpoint pair, with no endpoint-preservation hypothesis. -/
theorem fuchsianSideClosedModel_pairing_endpoints {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {L : Set P.domain.carrier} (hL : IsConvexFuchsianPolygon P L) (s : FuchsianPolygonSides P L)
    (p q a b : 𝕔𝔻) (hs : fuchsianSideClosedModel
      s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (ht : fuchsianSideClosedModel (fuchsianPairedSide hL
      s)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b) :
    ({(P.compactifiedAction (fuchsianSideElement hL s)⁻¹).closedMap p,
      (P.compactifiedAction (fuchsianSideElement hL s)⁻¹).closedMap q} : Set 𝕔𝔻)={a,b} := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.closed_segment_image_endpoints
  rw [←hs,←ht]
  exact fuchsianSideClosedModel_paired_image hL s

/-- Every original paired side admits distinct actual finite-or-ideal endpoints whose genuine whole-sphere images are exactly the partner endpoints. The endpoints are derived from the original side, not supplied finite geodesic data. -/
theorem exists_original_side_pairing_compactified_endpoints {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {L : Set P.domain.carrier}
    (hL : IsConvexFuchsianPolygon P L) (s : FuchsianPolygonSides P L) :
    ∃p q a b : 𝕔𝔻,p≠q∧a≠b∧
      fuchsianSideClosedModel s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q∧
      fuchsianSideClosedModel (fuchsianPairedSide hL
        s)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b∧
      ({(fuchsianSideElement hL s)⁻¹.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p),
        (fuchsianSideElement hL s)⁻¹.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
          q)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
          {_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended b} := by
  obtain ⟨p,q,hpq,hs⟩:=fuchsianSideClosedModel_eq_segment s
  obtain ⟨a,b,hab,ht⟩:=fuchsianSideClosedModel_eq_segment (fuchsianPairedSide hL s)
  refine ⟨p,q,a,b,hpq,hab,hs,ht,?_⟩
  have he:=congrArg (fun A : Set 𝕔𝔻=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended '' A)
    (fuchsianSideClosedModel_pairing_endpoints hL s p q a b hs ht)
  simpa only [image_insert_eq,image_singleton,P.compactifiedAction_sphere] using he

end LowDimensionalTopology.Geometry.Fuchsian
