/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Convexity.FiniteHullSupports
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaCuspCoordinates
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaIdealVertices
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspRestrictedTopology
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
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
local instance cuspCompactSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance cuspCompactSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- The finite hull obtained from genuine cyclic support data is the actual compactified model closure of the original polygon, without deleting any actual side subdivision from that original polygon. -/
theorem finite_cyclic_hull_eq_polygon_closedModel {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (L : Set P.domain.carrier) {n : ℕ}
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hregion : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P L) :
    {p : 𝕔𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ (range (fun
      i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)))}=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' L) := by
  have he : convexHull ℝ (range (fun i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    (S.vertices i)))=
      fuchsianPolygonCompactKlein P L:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.cyclic_support_region_eq_convexHull S).symm.trans hregion
  have him : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' L)=
      fuchsianPolygonCompactKlein P L:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
    rfl
  ext p
  rw [mem_ofPred_eq,he,←him]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.injective.mem_set_image

/-- The actual original finite hull is the inverse original normalizer image of the literal ambient sphere closure of the original polygon. -/
theorem originalFiniteClosedHull_eq_polygon_closure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (L : Set P.domain.carrier) (q₀ :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    {n : ℕ} (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hregion : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P L) :
    originalFiniteClosedHull q₀ S.vertices=
      q₀⁻¹.val '' closure ((Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' L) := by
  rw [originalFiniteClosedHull,finite_cyclic_hull_eq_polygon_closedModel P L S hregion]
  change (q₀⁻¹.val ∘ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' L)=_
  rw [image_comp,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure_ambient]
  have him : (fun z : 𝔻=>((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' (P.finiteCoordinate
    '' L)=
      (Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' L:=by
    rw [image_image]
    congr 1
    funext x
    exact P.finiteCoordinate_extended x
  rw [him]

/-- Genuine parabolic fixers pull back through the original whole-group normalizer. -/
theorem actual_conjugate_parabolic_fixer_pullback (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfix : f.val.val x=x) :
    ∃g : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val∧g.val.val (q⁻¹.val x)=q⁻¹.val x := by
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let g:=e.symm f
  have he : q*g.val*q⁻¹=f.val:=congrArg Subtype.val (e.apply_symm_apply f)
  refine ⟨g,(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,he⟩)).mpr hf,?_⟩
  apply q.val.injective
  have hfx : q.val (g.val.val (q⁻¹.val x))=x:=by
    change (q*g.val*q⁻¹).val x=x
    rw [he]
    exact hfix
  exact hfx.trans (q.val.apply_symm_apply x).symm

/-- If every actual ideal polygon point has a genuine original parabolic fixer, its actual finite hull lies in the unchanged original all-cusp augmented carrier. -/
theorem finite_cyclic_hull_original_cusp_admissible {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (L : Set (geometricDiscData D).domain.carrier) {n : ℕ}
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hregion : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D) L)
    (hpar : ∀u : Circle,(u:ℂ)∈fuchsianPolygonIdealBoundary (geometricDiscData D) L→
      ∃f : geometricDiscGroup D,f≠1∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val∧f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∀z∈originalFiniteClosedHull (geometricDiscNormalizer D) S.vertices,
      z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
        g.val.val (fuchsianParabolicPointRepresentative D c).val=z := by
  rintro z ⟨p,hp,rfl⟩
  by_cases hfin : ‖(p:ℂ)‖<1
  · left
    have hpu : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=⟨(p:ℂ),hfin,rfl⟩
    rw [←geometricDiscNormalizer_image D] at hpu
    obtain ⟨w,hw,he⟩:=hpu
    have hwe : (geometricDiscNormalizer D)⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)=w:=by
      change (geometricDiscNormalizer
        D).val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)=w
      rw [←he]
      exact (geometricDiscNormalizer D).val.symm_apply_apply w
    change (geometricDiscNormalizer D)⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      p)∈D.carrier
    rwa [hwe]
  · have hn : ‖(p:ℂ)‖=1:=le_antisymm p.norm_le_one (le_of_not_gt hfin)
    have hpk : (p:ℂ)∈fuchsianPolygonCompactKlein (geometricDiscData D) L:=by
      have hk : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p=(p:ℂ):=
        congrArg (fun p :
          𝕔𝔻=>(p:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hn)
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ (range (fun
        i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))) at hp
      rw [←_root_.LowDimensionalTopology.Geometry.Polygon.cyclic_support_region_eq_convexHull S,hregion,hk] at hp
      exact hp
    have hi : (p:ℂ)∈fuchsianPolygonIdealBoundary (geometricDiscData D) L:=
      (compactKlein_ideal_mem_iff _ _ _ hn).mp hpk
    let u : Circle:=⟨(p:ℂ),mem_sphere_zero_iff_norm.mpr hn⟩
    obtain ⟨f,_hfn,hf,hfix⟩:=hpar u hi
    obtain ⟨g,hg,hgp⟩:=actual_conjugate_parabolic_fixer_pullback H (geometricDiscNormalizer D) f hf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p) hfix
    let x : fuchsianCyclicFixedPoints D .parabolic:=⟨_,by
      constructor
      · intro he
        cases he
      · exact ⟨g.val,g.property,hg,hgp⟩⟩
    right
    exact fuchsianParabolicPointRepresentative_orbit_cover D x

/-- Actual parabolic fixers push forward through the original entire-group normalizer. -/
theorem actual_conjugate_parabolic_fixer_pushforward (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f : H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfix : f.val.val x=x) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H f).val∧
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H f).val.val (q.val x)=q.val x := by
  constructor
  · exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  · change q.val (f.val.val (q.val.symm (q.val x)))=q.val x
    rw [Equiv.symm_apply_apply,hfix]

/-- Literal original group action is intertwined by its actual whole-disc normalizer, on the entire sphere. -/
theorem geometricDiscNormalizer_sphere_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (g : H) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    (geometricDiscNormalizer D).val (g.val.val z)=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
        (geometricDiscNormalizer D) H g).val.val
        ((geometricDiscNormalizer D).val z) := by
  change _=(geometricDiscNormalizer D).val
    (g.val.val ((geometricDiscNormalizer D).val.symm ((geometricDiscNormalizer D).val z)))
  rw [Equiv.symm_apply_apply]

/-- Every original augmented orbit meets the actual compact finite hull of any genuine finite cyclic model of an original locally finite fundamental polygon. Actual parabolic orbit incidence is derived from local finiteness. -/
theorem finite_cyclic_hull_meets_original_augmented_orbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) {L : Set (geometricDiscData D).domain.carrier}
    (hL : IsLocallyFiniteFuchsianDomain (geometricDiscData D) L) {n : ℕ}
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hregion : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D) L)
    (z : _root_.LowDimensionalTopology.Geometry.Surfaces.MultipleCuspAugmentedDomain (fuchsianCuspChartNormalization
      D)) :
    ∃w∈originalFiniteClosedHull (geometricDiscNormalizer D) S.vertices,∃g : H,g.val.val z.val=w := by
  let q:=geometricDiscNormalizer D
  let P:=geometricDiscData D
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hreturn (y : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (hy : y∈closure ((Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
        L)) :
      q⁻¹.val y∈originalFiniteClosedHull q S.vertices:=by
    rw [originalFiniteClosedHull_eq_polygon_closure P L q S hregion]
    exact mem_image_of_mem q⁻¹.val hy
  have hrel (k : geometricDiscGroup D) (y : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (hy : k.val.val (q.val z.val)=y) : (e.symm k).val.val z.val=q⁻¹.val y:=by
    apply q.val.injective
    rw [geometricDiscNormalizer_sphere_equivariant]
    change (e (e.symm k)).val.val (q.val z.val)=q.val (q⁻¹.val y)
    rw [e.apply_symm_apply]
    exact hy.trans (q.val.apply_symm_apply y).symm
  rcases (fuchsianCuspCompletion_augmented_carrier_iff D z.val).mp z.property with hzD|⟨f,hfH,hf,hfix⟩
  · have hqz : q.val z.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
      rw [←geometricDiscNormalizer_image D]
      exact mem_image_of_mem q.val hzD
    let x : P.domain.carrier:=⟨q.val z.val,hqz⟩
    have hx : x∈⋃k : geometricDiscGroup D,(fun y : P.domain.carrier=>k•y) '' closure L:=by
      rw [hL.fundamental.closure_cover]
      exact mem_univ x
    obtain ⟨k,y,hy,he⟩:=mem_iUnion.mp hx
    have hycl : y.val∈closure ((Subtype.val :
      P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' L):=
      mem_closure_image continuous_subtype_val.continuousAt hy
    have hky : k⁻¹.val.val (q.val z.val)=y.val:=by
      have hh:=congrArg Subtype.val he
      change k.val.val y.val=q.val z.val at hh
      change k.val.val.symm (q.val z.val)=y.val
      rw [←hh,Equiv.symm_apply_apply]
    exact ⟨q⁻¹.val y.val,hreturn y.val hycl,e.symm k⁻¹,hrel k⁻¹ y.val hky⟩
  · let f₀ : H:=⟨f,hfH⟩
    have hfq:=actual_conjugate_parabolic_fixer_pushforward H q f₀ hf z.val hfix
    obtain ⟨k,η,hk,hη⟩:=hL.parabolic_fixedPoint_orbit_mem_idealBoundary (e f₀) hfq.1
      (q.val z.val) hfq.2
    have hηcl : (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈closure ((Subtype.val :
      P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' L):=
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P L η).mp hη).2
    exact ⟨q⁻¹.val (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),hreturn
      (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hηcl,e.symm k,hrel k _ hk⟩

/-- Every original Fuchsian action with a genuine finite-area fundamental domain has a genuinely compact all-cusp completion. Actual good centres, original finite polygons, parabolic ideal vertices, all chart bounds and whole-group orbit coverage are constructed from those original hypotheses. -/
theorem finite_area_fuchsianCuspCompletion_compact {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) F)
    (harea : geometricModelArea D F≠⊤) : CompactSpace (FuchsianCuspCompletion D) := by
  let P:=geometricDiscData D
  obtain ⟨w₀,hw₀,ha₀⟩:=finite_area_geometricDisc_dirichlet D F hF harea
  have hF₀:=dirichletDomain_fundamental P w₀ hw₀
  obtain ⟨w,_hw,hpoly,ha,hpar⟩:=finite_area_exists_dirichlet_all_ideal_parabolic hF₀ ha₀
  let L:=dirichletDomain P w
  obtain ⟨n,S,hregion,_hint⟩:=finite_area_polygon_actual_cyclic_model hpoly ha
  let K:=originalFiniteClosedHull (geometricDiscNormalizer D) S.vertices
  have hK:=finite_cyclic_hull_original_cusp_admissible D L S hregion hpar
  exact fuchsianCuspCompletion_compact_of_bounded_compact_cover D K
    (originalFiniteClosedHull_isCompact _ _) hK
    (originalFiniteClosedHull_cusp_bounds D _ (geometricDiscNormalizer_image D) S.vertices)
    (finite_cyclic_hull_meets_original_augmented_orbit D hpoly.locallyFinite S hregion)

end LowDimensionalTopology.Geometry.Fuchsian
