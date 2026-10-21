module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicAngularArea
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.DiscreteSubset
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenFiniteCorePolygon
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleRationalCounterexample
public import LowDimensionalTopology.Geometry.Fuchsian.GeometricFiniteness.SplitLimitPolygons
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.Homeomorph.Defs
/-!
# Cyclic presentations of the Nielsen boundary

This module constructs the finite cyclic boundary data of a Dirichlet polygon
intersected with the Nielsen core of a finitely generated non-elementary
Fuchsian group. Boundary first-return cycles determine the additional faces of
its capped presentation. The edge indices, vertices and cap occurrences retain
maps to the original disc polygon.

The geometric realization of this presentation and its relation to the whole
quotient surface are developed in the subsequent Nielsen modules.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace Pointwise


namespace LowDimensionalTopology.Geometry.Fuchsian
local instance nielsenCutSideSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenCutSideSphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩
def nielsenClosedCore {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) : Set 𝕔𝔻 :=
  Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' fuchsianNielsenCore P hNE)

theorem nielsenClosedCore_image {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H) (g:H) :
    (P.compactifiedAction g).closedMap '' nielsenClosedCore P hNE=nielsenClosedCore P hNE := by
  rw [nielsenClosedCore,P.compactifiedAction_image_closedModel]
  have he:g • fuchsianNielsenCore P hNE=fuchsianNielsenCore P hNE := by
    apply subset_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact fuchsianNielsenCore_invariant P hNE g x hx
    · intro x hx
      exact ⟨g⁻¹ • x,fuchsianNielsenCore_invariant P hNE g⁻¹ x hx,smul_inv_smul g x⟩
  rw [he]

def nielsenRefinedSideCarrier {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    (hNE:DiscreteGroups.IsNonElementary H)
    (v:OriginalRefinedSide hD) : Set 𝕔𝔻 :=
  v.carrier∩nielsenClosedCore P hNE

theorem nielsenRefinedSideCarrier_pair_image
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    (hNE:DiscreteGroups.IsNonElementary H)
    (v:OriginalRefinedSide hD) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.1)⁻¹).closedMap '' nielsenRefinedSideCarrier hNE v=
      nielsenRefinedSideCarrier hNE v.pair := by
  rw [nielsenRefinedSideCarrier,image_inter (P.compactifiedAction _).closedMap.injective,
    v.pair_carrier,nielsenClosedCore_image]
  rfl

def NielsenRefinedSide {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (hNE:DiscreteGroups.IsNonElementary H) :=
  {v:OriginalRefinedSide hD // (nielsenRefinedSideCarrier hNE v).Nontrivial}

def NielsenRefinedSide.carrier {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (v:NielsenRefinedSide hD hNE) : Set 𝕔𝔻 :=
  nielsenRefinedSideCarrier hNE v.val

def NielsenRefinedSide.pair {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (v:NielsenRefinedSide hD hNE) :
    NielsenRefinedSide hD hNE :=
  ⟨v.val.pair,by
    rw [←nielsenRefinedSideCarrier_pair_image hNE v.val]
    exact v.property.image (P.compactifiedAction _).closedMap.injective⟩

theorem NielsenRefinedSide.pair_involutive {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (hNE:DiscreteGroups.IsNonElementary H) :
    Function.Involutive (NielsenRefinedSide.pair (hD:=hD) (hNE:=hNE)) := by
  intro v
  apply Subtype.ext
  exact OriginalRefinedSide.pair_involutive hD v.val

theorem NielsenRefinedSide.pair_ne_self {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (v:NielsenRefinedSide hD hNE) :
    v.pair≠v := by
  intro h
  exact v.val.pair_ne_self (congrArg Subtype.val h)

theorem NielsenRefinedSide.pair_carrier {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (v:NielsenRefinedSide hD hNE) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap '' v.carrier=v.pair.carrier :=
  nielsenRefinedSideCarrier_pair_image hNE v.val

theorem NielsenRefinedSide.finite {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (hNE:DiscreteGroups.IsNonElementary H)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite) :
    Finite (NielsenRefinedSide hD hNE) := by
  let :Fintype (FuchsianPolygonSides P D):=hfin.fintype
  let :Finite (OriginalRefinedSide hD):=by unfold OriginalRefinedSide;infer_instance
  unfold NielsenRefinedSide
  infer_instance

theorem NielsenRefinedSide.carrier_eq_segment
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (v:NielsenRefinedSide hD hNE) :
    ∃p q:𝕔𝔻,p≠q∧v.carrier=Hyperbolic.closedModelDiscHSegment p q := by
  obtain ⟨a,b,hab,hseg⟩:=v.val.carrier_eq_segment
  let K:=Hyperbolic.closedKleinCoordinate '' v.carrier
  have he:K=segment ℝ (Hyperbolic.closedKleinCoordinate a) (Hyperbolic.closedKleinCoordinate b)∩
      closure (P.kleinCoordinate '' fuchsianNielsenCore P hNE) := by
    rw [show K=Hyperbolic.closedKleinCoordinate '' (v.val.carrier∩nielsenClosedCore P hNE) from rfl,
      image_inter Hyperbolic.closedKleinCoordinate_injective,hseg,Hyperbolic.closedKlein_image_closedModelDiscHSegment,
      nielsenClosedCore,Hyperbolic.discClosedModelClosure,Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
    rfl
  have hc:Convex ℝ K := by
    rw [he]
    apply (convex_segment _ _).inter
    have hn:=(Hyperbolic.discHConvex_iff_klein_convex _).mp (fuchsianNielsenCore_convex P hNE)
    have hn':Convex ℝ (P.kleinCoordinate '' fuchsianNielsenCore P hNE) := by
      simpa only [image_image,UnitDiscFuchsianGroup.kleinCoordinate] using hn
    exact hn'.closure
  have hk:IsCompact K:=by
    rw [he]
    have hs:IsCompact (segment ℝ (Hyperbolic.closedKleinCoordinate a) (Hyperbolic.closedKleinCoordinate b)):=by
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous
    exact hs.inter_right isClosed_closure
  have hcol:Collinear ℝ K:=by
    rw [he]
    have hs:Collinear ℝ (segment ℝ (Hyperbolic.closedKleinCoordinate a) (Hyperbolic.closedKleinCoordinate b)):=by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨Hyperbolic.closedKleinCoordinate a,Hyperbolic.closedKleinCoordinate b-Hyperbolic.closedKleinCoordinate
        a,?_⟩
      intro z hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨t,ht,rfl⟩:=hz
      exact ⟨t,rfl⟩
    exact hs.subset inter_subset_left
  have hnt:K.Nontrivial:=v.property.image Hyperbolic.closedKleinCoordinate_injective
  obtain ⟨p,hp,q,hq,hpq,hpqseg⟩:=compact_convex_collinear_eq_segment K hk hc hcol hnt
  obtain ⟨p',hp',rfl⟩:=hp
  obtain ⟨q',hq',rfl⟩:=hq
  refine ⟨p',q',fun h=>hpq (congrArg Hyperbolic.closedKleinCoordinate h),?_⟩
  apply Hyperbolic.closedKleinCoordinate_injective.image_injective
  rw [Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  exact hpqseg

/-- A nonzero real translation in the actual group rules out infinity as
an endpoint of any genuine complementary ordinary real gap. -/
theorem nielsen_gap_infty_not_endpoint_of_translation
    (K : Subgroup Mobius.complexMobiusGroup) (t : ℝ) (ht : t≠0)
    (hT : DiscreteGroups.mobiusTranslation (t:ℂ)∈K)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet K)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet
      (DiscreteGroups.mobiusLimitSet K))) :
    (∞:Mobius.ExtendedComplex)∉G.line.idealEndpoints := by
  have hpos : DiscreteGroups.mobiusTranslation ((|t|:ℝ):ℂ)∈K := by
    by_cases hp : 0≤t
    · simpa only [abs_of_nonneg hp] using hT
    · have hn : t<0:=lt_of_not_ge hp
      simpa only [abs_of_neg hn,Complex.ofReal_neg,DiscreteGroups.mobiusTranslation_neg] using K.inv_mem hT
  have hneg : DiscreteGroups.mobiusTranslation (- ((|t|:ℝ):ℂ))∈K := by
    rw [DiscreteGroups.mobiusTranslation_neg]
    exact K.inv_mem hpos
  have ha : 0 < |t|:=abs_pos.mpr ht
  have hGArc : Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈Hyperbolic.nielsenHalfPlaneArcFamily (DiscreteGroups.mobiusLimitSet K) := by
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨G.carrier,hG,rfl⟩
  have hend:=nielsen_gap_idealEndpoints_limit_subset _ hinf G hGArc
  have hsub : G.carrier⊆(Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K))ᶜ := by
    obtain ⟨x,_hx,hxG⟩ := hG
    rw [hxG]
    exact connectedComponentIn_subset _ _
  cases G with
  | bounded a b hab =>
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    simp
  | left b =>
    have hb : Hyperbolic.nielsenRealBoundaryPoint b∈DiscreteGroups.mobiusLimitSet K := by
      apply hend
      rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
      exact mem_insert _ _
    have hbn:=DiscreteGroups.mobiusLimitSet_invariant K ⟨DiscreteGroups.mobiusTranslation (- ((|t|:ℝ):ℂ)),hneg⟩ hb
    have hbad : b-|t|∈Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K) := by
      change Hyperbolic.nielsenRealBoundaryPoint (b-|t|)∈DiscreteGroups.mobiusLimitSet K
      convert hbn using 1
      change (((b-|t|:ℝ):ℂ):Mobius.ExtendedComplex)=
        (DiscreteGroups.mobiusTranslation (- ((|t|:ℝ):ℂ))).val ((b:ℂ):Mobius.ExtendedComplex)
      rw [DiscreteGroups.mobiusTranslation_coe]
      congr 1
      push_cast
      ring
    exact fun _=>hsub (show b-|t|<b by linarith) hbad
  | right b =>
    have hb : Hyperbolic.nielsenRealBoundaryPoint b∈DiscreteGroups.mobiusLimitSet K := by
      apply hend
      rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
      exact mem_insert _ _
    have hbp:=DiscreteGroups.mobiusLimitSet_invariant K ⟨DiscreteGroups.mobiusTranslation ((|t|:ℝ):ℂ),hpos⟩ hb
    have hbad : b+|t|∈Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K) := by
      change Hyperbolic.nielsenRealBoundaryPoint (b+|t|)∈DiscreteGroups.mobiusLimitSet K
      convert hbp using 1
      change (((b+|t|:ℝ):ℂ):Mobius.ExtendedComplex)=
        (DiscreteGroups.mobiusTranslation ((|t|:ℝ):ℂ)).val ((b:ℂ):Mobius.ExtendedComplex)
      rw [DiscreteGroups.mobiusTranslation_coe]
      congr 1
      push_cast
      ring
    exact fun _=>hsub (show b<b+|t| by linarith) hbad

/-- The same genuine whole-disc normalizer sends an actual parabolic to
a nonzero real translation and its unique actual fixed point to infinity. -/
theorem original_parabolic_real_translation_normalizer
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (p : H) (hp : Mobius.MobiusParabolic p.val) :
    ∃q : Mobius.complexMobiusGroup,∃t : ℝ,t≠0 ∧
      q.val '' D.carrier=Hyperbolic.openHalfPlaneSet ∧
      q*p.val*q⁻¹=DiscreteGroups.mobiusTranslation (t:ℂ) ∧
      ∀ξ : Mobius.ExtendedComplex,p.val.val ξ=ξ → q.val ξ=∞ := by
  let r:=D.halfPlaneNormalizer
  obtain ⟨A,hA⟩ := D.normalizedGroup_exists_realSL (r*p.val*r⁻¹)
    ((DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff r H _).mpr ⟨p.val,p.property,rfl⟩)
  have hAP : Mobius.MobiusParabolic (Hyperbolic.realSLMobius A) := by
    rw [hA]
    exact (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨r,rfl⟩)).mp hp
  obtain ⟨s,t,ht,hst⟩ := Hyperbolic.realSLMobius_parabolic_normal_form A hAP
  have hsA : Hyperbolic.realSLMobius (s*A*s⁻¹)=Hyperbolic.realSLMobius (Hyperbolic.hTranslationSL t) := by
    rcases hst with h|h
    · rw [h]
    · rw [h,Hyperbolic.realSLMobius_neg]
  let q:=Hyperbolic.realSLMobius s*r
  have hqD : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet := by
    change (fun z=>(Hyperbolic.realSLMobius s).val (r.val z)) '' D.carrier=_
    rw [←image_image,D.halfPlaneNormalizer_image,realSLMobius_image_openHalfPlane]
  have hqP : q*p.val*q⁻¹=DiscreteGroups.mobiusTranslation (t:ℂ) := by
    rw [←rationalTriangle_translation_projection,←hsA,map_mul,map_mul,map_inv,hA]
    dsimp only [q]
    group
  refine ⟨q,t,ht,hqD,hqP,?_⟩
  intro ξ hξ
  have hP : Mobius.MobiusParabolic (q*p.val*q⁻¹):=
    (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hp
  have hfix := DiscreteGroups.mobius_conjugate_fixedpoint p.val q ξ hξ
  have hinf : (q*p.val*q⁻¹).val ∞=∞ := by rw [hqP,DiscreteGroups.mobiusTranslation_infty]
  obtain ⟨a,ha⟩ := hP.2
  exact ((ha _).mp hfix).trans ((ha _).mp hinf).symm

/-- No actual parabolic fixed point can be an endpoint of any ordinary
Nielsen interval of the original non-elementary Fuchsian group. -/
theorem nielsenArc_endpoint_not_parabolic_fixed
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (I : Set Mobius.ExtendedComplex) (hI : I∈D.nielsenArcFamily)
    (p : H) (hp : Mobius.MobiusParabolic p.val)
    (ξ : Mobius.ExtendedComplex) (hξ : ξ∈closure I\I) : p.val.val ξ≠ξ := by
  intro hfix
  obtain ⟨q,t,ht,hq,hqP,hqFix⟩ := original_parabolic_real_translation_normalizer D p hp
  have hξInf:=hqFix ξ hfix
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hpK : DiscreteGroups.mobiusTranslation (t:ℂ)∈K := by
    rw [←hqP]
    exact (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨p.val,p.property,rfl⟩
  have hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet K := by
    rw [←nielsen_mobiusLimitSet_conjugation H q]
    exact ⟨ξ,DiscreteGroups.mobius_parabolic_fixed_mem_limitSet H hNE p hp ξ hfix,hξInf⟩
  obtain ⟨G,hGI⟩ := D.nielsenArcFamily_exists_gap q hq hNE hinf hI
  have hGArc : Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈Hyperbolic.nielsenHalfPlaneArcFamily (DiscreteGroups.mobiusLimitSet K) := by
    apply (D.nielsenArcFamily_gap_mem q hq G).mp
    rw [hGI]
    exact hI
  have hGF : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K)) := by
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf] at hGArc
    exact Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.injective.image_injective.mem_set_image.mp hGArc
  have hqI : q.val '' I=Hyperbolic.nielsenRealBoundaryPoint '' G.carrier := by
    rw [←hGI]
    exact q.val.image_symm_image _
  have hcl : q.val ξ∈closure (q.val '' I)\(q.val '' I) := by
    refine ⟨image_closure_subset_closure_image (Mobius.mobiusBoundaryHomeomorph q).continuous
      (mem_image_of_mem _ hξ.1),?_⟩
    rintro ⟨z,hz,he⟩
    exact hξ.2 (q.val.injective he ▸ hz)
  rw [hqI,nielsenGap_interval_endpoints,hξInf] at hcl
  exact nielsen_gap_infty_not_endpoint_of_translation K t ht hpK hinf G hGF hcl

/-- The actual finite or infinite ideal endpoint of any genuine gap line
in any original whole-domain Nielsen chart is not a parabolic fixed point. -/
theorem nielsenGap_original_endpoint_not_parabolic_fixed
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup)
    (_hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈D.nielsenArcFamily)
    (p : H) (hp : Mobius.MobiusParabolic p.val)
    (ξ : Mobius.ExtendedComplex) (hξ : ξ∈G.line.idealEndpoints) :
    p.val.val (q⁻¹.val ξ)≠q⁻¹.val ξ := by
  have hξI : q⁻¹.val ξ∈closure (q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier))\
      (q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)) := by
    rw [←nielsenGap_interval_endpoints] at hξ
    refine ⟨image_closure_subset_closure_image (Mobius.mobiusBoundaryHomeomorph q⁻¹).continuous
      (mem_image_of_mem _ hξ.1),?_⟩
    rintro ⟨z,hz,he⟩
    exact hξ.2 (q⁻¹.val.injective he ▸ hz)
  exact nielsenArc_endpoint_not_parabolic_fixed D hNE _ hG p hp _ hξI

/-- In the original physical disc, no actual parabolic fixes an actual
ideal endpoint of any genuine Nielsen boundary geodesic. -/
theorem nielsen_boundary_geodesic_ideal_endpoint_not_parabolic_fixed
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈D.nielsenArcFamily)
    (p : H)
    (hp : Mobius.MobiusParabolic p.val)
    (ξ : Mobius.ExtendedComplex)
    (hξ : ξ∈closure (nielsenModelSet q G.line.carrier)∩frontier D.carrier) :
    p.val.val ξ≠ξ := by
  rw [D.nielsenArcGeodesic_idealEndpoints q hq G] at hξ
  obtain ⟨η,hη,rfl⟩ := hξ
  exact nielsenGap_original_endpoint_not_parabolic_fixed D hNE q hq G hG p hp η hη

/-- At every actual ideal closure point in the actual limit set, a
finitely generated group's genuine convex locally finite polygon has an
actual parabolic fixing that point. -/
theorem finitelyGenerated_polygon_ideal_limit_parabolic
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (ξ : Mobius.ExtendedComplex)
    (hξC : ξ∈closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' D))
    (hξL : ξ∈DiscreteGroups.mobiusLimitSet H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    ∃p : H,Mobius.MobiusParabolic p.val ∧ p.val.val ξ=ξ := by
  have hξF : ξ∈fuchsianLimitSet H:=by rwa [fuchsianLimitSet_eq_nonElementary H hNE]
  obtain ⟨z,_hz,hzξ⟩ := fuchsian_limit_unitDisc_finite P ξ hξF
  rw [hzξ] at hξC hξF ⊢
  rcases finitelyGenerated_split_limitSet P hFG z hξF with hpar|hApprox
  · exact hpar
  · exact False.elim (fuchsian_pointOfApproximation_not_polygon_closure P hD z hApprox hξC)

/-- A genuine whole-domain half-plane chart retains the literal original
physical sphere trace of every complete native gap geodesic. -/
theorem nielsen_gap_chart_line_sphere_image
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (G : Hyperbolic.NielsenHalfPlaneGap) :
    (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) ''
      ((geometricHalfPlaneChart P.asFuchsianDisc q hq).symm '' G.line.carrier)=
      nielsenModelSet q G.line.carrier := by
  let E:=geometricHalfPlaneChart P.asFuchsianDisc q hq
  rw [image_image,nielsenModelSet,image_image]
  apply image_congr
  intro z _hz
  apply q.val.injective
  have he:=geometricHalfPlaneChart_extended P.asFuchsianDisc q hq (E.symm z)
  change Hyperbolic.extendedHalfPlanePoint (E (E.symm z))=q.val (E.symm z).val at he
  rw [E.apply_symm_apply] at he
  change q.val (E.symm z).val=q.val (q.val.symm (Hyperbolic.extendedHalfPlanePoint z))
  rw [q.val.apply_symm_apply]
  exact he.symm

/-- Neither actual ideal end of any genuine Nielsen gap line belongs to
the actual original polygon's sphere closure. -/
theorem finitelyGenerated_nielsen_gap_ideal_endpoint_not_polygon_closure
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q
      H))
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈P.asFuchsianDisc.nielsenArcFamily)
    (ξ : Mobius.ExtendedComplex)
    (hξ : ξ∈closure (nielsenModelSet q G.line.carrier)∩frontier P.domain.carrier) :
    ξ∉closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' D) := by
  intro hξD
  have hξL:=P.asFuchsianDisc.nielsenArcGeodesic_endpoints_subset_limit q hq hinf G hG hξ
  obtain ⟨p,hp,hfix⟩ := finitelyGenerated_polygon_ideal_limit_parabolic P hFG hD ξ hξD hξL hNE
  exact nielsen_boundary_geodesic_ideal_endpoint_not_parabolic_fixed
    P.asFuchsianDisc hNE q hq G hG p hp ξ hξ hfix

/-- Every genuine ordinary-gap geodesic meets the actual closed polygon
in a compact subset of the original open hyperbolic disc. Thus no end of
this actual line intersection can escape to an ideal cusp. -/
theorem finitelyGenerated_nielsen_gap_closedPolygon_inter_compact
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q
      H))
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈P.asFuchsianDisc.nielsenArcFamily) :
    IsCompact (((geometricHalfPlaneChart P.asFuchsianDisc q hq).symm '' G.line.carrier)∩closure D) := by
  let E:=geometricHalfPlaneChart P.asFuchsianDisc q hq
  let T:=(E.symm '' G.line.carrier)∩closure D
  have hTs : (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' T⊆nielsenModelSet q G.line.carrier := by
    rw [←nielsen_gap_chart_line_sphere_image P q hq G]
    exact image_mono inter_subset_left
  have hTD : (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' T⊆
      closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' D) := by
    rintro _ ⟨x,hx,rfl⟩
    exact image_closure_subset_closure_image continuous_subtype_val ⟨x,hx.2,rfl⟩
  have hEmpty : fuchsianPolygonIdealBoundary P T=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzN,hzC⟩ := (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P T z).mp hz
    have hzD : (z:Mobius.ExtendedComplex)∈closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' D) :=
      closure_minimal hTD isClosed_closure hzC
    have hzS : (z:Mobius.ExtendedComplex)∈closure (nielsenModelSet q G.line.carrier) := closure_mono hTs hzC
    have hzB : (z:Mobius.ExtendedComplex)∈frontier P.asFuchsianDisc.carrier := by
      rw [show P.asFuchsianDisc.carrier=Hyperbolic.extendedUnitDisc from rfl,nielsen_unitDisc_frontier]
      exact ⟨z,mem_sphere_zero_iff_norm.mpr hzN,rfl⟩
    exact finitelyGenerated_nielsen_gap_ideal_endpoint_not_polygon_closure
      P hNE hFG hD q hq hinf G hG _ ⟨hzS,hzB⟩ hzD
  have hC := unitDisc_no_ideal_closure_compact P T hEmpty
  have hclosed : IsClosed T := (E.symm.isClosedMap _ G.line.isClosed_carrier).inter isClosed_closure
  rwa [hclosed.closure_eq] at hC

/-- A complete true gap line clipped by the actual closed polygon is
bounded in the genuine hyperbolic metric, not merely in the sphere model. -/
theorem finitelyGenerated_nielsen_gap_closedPolygon_inter_bounded
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q
      H))
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈P.asFuchsianDisc.nielsenArcFamily) :
    ∃R : ℝ,0<R ∧ ∀z∈G.line.carrier,
      (geometricHalfPlaneChart P.asFuchsianDisc q hq).symm z∈closure D →
      dist UpperHalfPlane.I z≤R := by
  let E:=geometricHalfPlaneChart P.asFuchsianDisc q hq
  have hC:=finitelyGenerated_nielsen_gap_closedPolygon_inter_compact P hNE hFG hD q hq hinf G hG
  obtain ⟨R,hR⟩ := (hC.image E.continuous).isBounded.subset_closedBall UpperHalfPlane.I
  refine ⟨max R 0+1,by positivity,?_⟩
  intro z hz hzD
  have hzC : E.symm z∈(E.symm '' G.line.carrier)∩closure D:=⟨mem_image_of_mem _ hz,hzD⟩
  have hb:=hR (mem_image_of_mem E hzC)
  rw [E.apply_symm_apply,Metric.mem_closedBall,dist_comm] at hb
  exact hb.trans (by linarith [le_max_left R 0])

/-- For any actual free Dirichlet centre, all true Nielsen gap-line
intersections with the original closed Dirichlet domain are compact.
The chart and its infinite limit point are constructed, not hypotheses. -/
theorem finitelyGenerated_nielsen_gap_closedDirichlet_inter_compact
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet
      (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
        (P.asFuchsianDisc.nielsenArcNormalizer hNE) H)))) :
    IsCompact (((geometricHalfPlaneChart P.asFuchsianDisc
      (P.asFuchsianDisc.nielsenArcNormalizer hNE)
      (P.asFuchsianDisc.nielsenArcNormalizer_image hNE)).symm '' G.line.carrier)∩closure (dirichletDomain P w)) := by
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  have hq:=P.asFuchsianDisc.nielsenArcNormalizer_image hNE
  have hinf:=P.asFuchsianDisc.nielsenArcNormalizer_limit hNE
  have hGArc : q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈P.asFuchsianDisc.nielsenArcFamily := by
    apply (P.asFuchsianDisc.nielsenArcFamily_gap_mem q hq G).mpr
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨G.carrier,hG,rfl⟩
  exact finitelyGenerated_nielsen_gap_closedPolygon_inter_compact
    P hNE hFG (dirichletDomain_isConvexFuchsianPolygon P w hw) q hq hinf G hGArc


def nielsenUnpairedNativeCarrier {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (D:Set P.domain.carrier)
    (L:Hyperbolic.DiscLine) : Set 𝔻 :=
  L.carrier∩P.finiteCoordinate '' closure D

theorem nielsenUnpairedNativeCarrier_isCompact
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (L:Hyperbolic.DiscLine) (hL:L∈nielsenBoundaryDiscLineFamily P hNE) :
    IsCompact (nielsenUnpairedNativeCarrier P D L) := by
  obtain ⟨G,hG,hGL⟩:=hL
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  have hq:=P.asFuchsianDisc.nielsenArcNormalizer_image hNE
  have hinf:=P.asFuchsianDisc.nielsenArcNormalizer_limit hNE
  have hArc:q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈P.asFuchsianDisc.nielsenArcFamily := by
    apply (P.asFuchsianDisc.nielsenArcFamily_gap_mem q hq G).mpr
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨G.carrier,hG,rfl⟩
  have hc:=finitelyGenerated_nielsen_gap_closedPolygon_inter_compact P hNE hFG hD q hq hinf G hArc
  have he:nielsenUnpairedNativeCarrier P D L=
      P.finiteCoordinate '' (((nielsenHalfPlaneChart P hNE).symm '' G.line.carrier)∩closure D) := by
    rw [image_inter P.finiteCoordinate.injective,hGL]
    rfl
  rw [he]
  exact hc.image P.finiteCoordinate.continuous

def NielsenUnpairedSide {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (D:Set P.domain.carrier) :=
  {L:Hyperbolic.DiscLine // L∈nielsenBoundaryDiscLineFamily P hNE ∧ (nielsenUnpairedNativeCarrier P D L).Nontrivial}

def NielsenUnpairedSide.carrier {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H}
    {hNE:DiscreteGroups.IsNonElementary H}
    {D:Set P.domain.carrier}
    (s:NielsenUnpairedSide P hNE D) : Set 𝕔𝔻 :=
  Hyperbolic.discToClosedModel '' nielsenUnpairedNativeCarrier P D s.val

theorem NielsenUnpairedSide.native_eq_segment
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} (hFG:H.FG)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (s:NielsenUnpairedSide P hNE D) :
    ∃a b:𝔻,a≠b∧nielsenUnpairedNativeCarrier P D s.val=Hyperbolic.closedDiscHSegment a b := by
  let C:=nielsenUnpairedNativeCarrier P D s.val
  let K:=Hyperbolic.kleinCoordinate '' C
  have hc:IsCompact K:=(nielsenUnpairedNativeCarrier_isCompact P hNE hFG hD s.val s.property.1).image
    Hyperbolic.isOpenEmbedding_kleinCoordinate.continuous
  have hconvC:Hyperbolic.DiscHConvex C := by
    intro a ha b hb z hz
    refine ⟨s.val.hConvex a ha.1 b hb.1 hz,?_⟩
    rw [P.finiteCoordinate.image_closure]
    exact hD.convex.closure a (by simpa only [P.finiteCoordinate.image_closure] using ha.2)
      b (by simpa only [P.finiteCoordinate.image_closure] using hb.2) hz
  have hconv:Convex ℝ K:=(Hyperbolic.discHConvex_iff_klein_convex C).mp hconvC
  have hcol:Collinear ℝ K := by
    obtain ⟨m,t,hm,hL⟩:=s.val.klein_image_carrier
    obtain ⟨x,hx⟩:=s.property.2.nonempty
    have hxlev:inner ℝ m (Hyperbolic.kleinCoordinate x)=t := (hL ▸ mem_image_of_mem _ hx.1).1
    apply (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_inner_level_collinear m (Hyperbolic.kleinCoordinate
      x) hm).subset
    rintro z ⟨u,hu,rfl⟩
    exact ((hL ▸ mem_image_of_mem _ hu.1).1).trans hxlev.symm
  have hnt:K.Nontrivial:=s.property.2.image Hyperbolic.kleinCoordinate_injective
  obtain ⟨a,ha,b,hb,hab,hK⟩:=compact_convex_collinear_eq_segment K hc hconv hcol hnt
  obtain ⟨a',ha',rfl⟩:=ha
  obtain ⟨b',hb',rfl⟩:=hb
  refine ⟨a',b',fun h=>hab (congrArg Hyperbolic.kleinCoordinate h),?_⟩
  apply Hyperbolic.kleinCoordinate_injective.image_injective
  rw [Hyperbolic.klein_image_closedDiscHSegment]
  exact hK

theorem NielsenUnpairedSide.carrier_finite_endpoints
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} (hFG:H.FG)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (s:NielsenUnpairedSide P hNE D) :
    ∃a b:𝔻,a≠b∧s.carrier=Hyperbolic.closedModelDiscHSegment (Hyperbolic.discToClosedModel a) (Hyperbolic.discToClosedModel b) := by
  obtain ⟨a,b,hab,he⟩:=s.native_eq_segment hFG hD
  refine ⟨a,b,hab,?_⟩
  rw [Hyperbolic.closedModelDiscHSegment_interior]
  exact congrArg (fun C:Set 𝔻=>Hyperbolic.discToClosedModel '' C) he

theorem NielsenUnpairedSide.carrier_isCompact
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} (hFG:H.FG)
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (s:NielsenUnpairedSide P hNE D) : IsCompact s.carrier :=
  (nielsenUnpairedNativeCarrier_isCompact P hNE hFG hD s.val s.property.1).image
    Hyperbolic.isEmbedding_discToClosedModel.continuous

theorem NielsenUnpairedSide.finite {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    Finite (NielsenUnpairedSide P hNE D) := by
  have ha:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
  have hf:=finite_nielsenCore_boundary_lines hD hNE ha w hwD hwN
  have hs:{L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧
      (nielsenUnpairedNativeCarrier P D L).Nontrivial}.Finite := by
    apply hf.subset
    rintro L ⟨hL,z,hz,u,hu,hzu⟩
    obtain ⟨x,hxD,hxz⟩:=hz.2
    have hxN:x∈frontier (fuchsianNielsenCore P hNE) := by
      obtain ⟨y,hy,hye⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hz.1
      have hxy:y=x:=P.finiteCoordinate.injective (hye.trans hxz.symm)
      exact hxy ▸ hy
    refine ⟨hL,z,hz.1,x,?_,hxz⟩
    rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
    exact ⟨hxD,frontier_subset_closure hxN⟩
  exact hs.to_subtype


theorem nielsenCore_closedModel_inter
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) :
    Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))=
      Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)∩nielsenClosedCore P hNE := by
  apply Hyperbolic.closedKleinCoordinate_injective.image_injective
  rw [image_inter Hyperbolic.closedKleinCoordinate_injective]
  unfold nielsenClosedCore Hyperbolic.discClosedModelClosure
  rw [Hyperbolic.closedKlein_image_discClosedModelClosure,Hyperbolic.closedKlein_image_discClosedModelClosure,
    Hyperbolic.closedKlein_image_discClosedModelClosure,image_inter P.finiteCoordinate.injective,
    image_inter Hyperbolic.kleinCoordinate_injective]
  exact complex_open_convex_closure_inter
    ((Hyperbolic.discHConvex_iff_klein_convex _).mp hD.convex)
    ((Hyperbolic.discHConvex_iff_klein_convex _).mp (fuchsianNielsenCore_convex P hNE))
    (Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap _
      (P.finiteCoordinate.isOpenMap _ hD.locallyFinite.fundamental.isOpen))
    (Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap _
      (P.finiteCoordinate.isOpenMap _ (fuchsianNielsenCore_isOpen P hNE)))
    (Hyperbolic.kleinCoordinate (P.finiteCoordinate w))
    (mem_image_of_mem _ (mem_image_of_mem _ hwD))
    (mem_image_of_mem _ (mem_image_of_mem _ hwN))

theorem nielsenCore_ideal_mem_refined_side
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG) (p:𝕔𝔻)
    (hp:p∈Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)))
    (hn:‖(p:ℂ)‖=1) :
    ∃v:OriginalRefinedSide hD,p∈nielsenRefinedSideCarrier hNE v := by
  have hpK:Hyperbolic.closedKleinCoordinate p∈fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE) := by
    change Hyperbolic.closedKleinCoordinate p∈closure (P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE))
    have he:P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE)=
        Hyperbolic.kleinCoordinate '' (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)) := by
      rw [image_image]
      rfl
    rw [he,←Hyperbolic.closedKlein_image_discClosedModelClosure]
    exact ⟨p,hp,rfl⟩
  have hkp:Hyperbolic.closedKleinCoordinate p=(p:ℂ):=
    congrArg (fun z:𝕔𝔻=>(z:ℂ)) (Hyperbolic.closedPoincareToKlein_ideal_fixed p hn)
  rw [hkp] at hpK
  have hξQ: (p:ℂ)∈fuchsianPolygonIdealBoundary P (D∩fuchsianNielsenCore P hNE):=
    (compactKlein_ideal_mem_iff P _ (p:ℂ) hn).mp hpK
  have hξD:(p:ℂ)∈fuchsianPolygonIdealBoundary P D:=
    inter_subset_inter_left _ (closure_mono (image_mono inter_subset_left)) hξQ
  have hξL:=nielsenCore_inter_idealBoundary_subset_limit P hNE D (p:ℂ) hξQ
  obtain ⟨hξnorm,hξC⟩:=(mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (p:ℂ)).mp hξD
  obtain ⟨f,hf,hfix⟩:=finitelyGenerated_polygon_ideal_limit_parabolic P hFG hD
    ((p:ℂ):Mobius.ExtendedComplex) hξC hξL hNE
  let ξ:Circle:=⟨(p:ℂ),mem_sphere_zero_iff_norm.mpr hξnorm⟩
  obtain ⟨_,S,_T,hS,_hT,_hne,hξS,_hξT⟩:=hD.parabolic_ideal_isProper f hf ξ hξD hfix
  let s:FuchsianPolygonSides P D:=⟨S,hS⟩
  have hpS:p∈fuchsianSideClosedModel s := by
    have hcl:((p:ℂ):Mobius.ExtendedComplex)∈closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' s.val):=
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P s.val (p:ℂ)).mp
        ⟨hξS,mem_sphere_zero_iff_norm.mpr hn⟩).2
    rw [←fuchsianSideClosedModel_ambient s] at hcl
    obtain ⟨u,hu,he⟩:=hcl
    exact Hyperbolic.isEmbedding_closedDiscToExtended.injective he ▸ hu
  have hpR:p∈⋃v:OriginalRefinedSide hD,v.carrier := by
    rw [originalRefinedSide_iUnion_carrier]
    exact mem_iUnion.mpr ⟨s,hpS⟩
  obtain ⟨v,hv⟩:=mem_iUnion.mp hpR
  refine ⟨v,hv,?_⟩
  exact closure_mono (image_mono (image_mono inter_subset_right)) hp


theorem nielsenCore_boundary_mem_raw_side
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (w:P.domain.carrier)
    (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) (p:𝕔𝔻)
    (hp:Hyperbolic.closedKleinCoordinate p∈frontier (fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE))) :
    (∃v:OriginalRefinedSide hD,p∈nielsenRefinedSideCarrier hNE v) ∨
      ∃L:Hyperbolic.DiscLine,L∈nielsenBoundaryDiscLineFamily P hNE ∧
        p∈Hyperbolic.discToClosedModel '' nielsenUnpairedNativeCarrier P D L := by
  have hpQ:p∈Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)) := by
    apply Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
    rw [Hyperbolic.discClosedModelClosure,Hyperbolic.closedKlein_image_discClosedModelClosure]
    have he:P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE)=
        Hyperbolic.kleinCoordinate '' (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)) := by
      rw [image_image]
      rfl
    rw [←he]
    simpa only [fuchsianPolygonCompactKlein,closure_closure] using frontier_subset_closure hp
  by_cases hn:‖(p:ℂ)‖=1
  · exact Or.inl (nielsenCore_ideal_mem_refined_side hD hNE hFG p hpQ hn)
  · have hlt:‖(p:ℂ)‖<1:=lt_of_le_of_ne p.norm_le_one hn
    let z:𝔻:=Complex.UnitDisc.mk (p:ℂ) hlt
    let x:=P.finiteCoordinate.symm z
    have hxz:P.finiteCoordinate x=z:=P.finiteCoordinate.apply_symm_apply z
    have hpz:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=p := by
      rw [hxz]
      exact Subtype.ext rfl
    have hKx:Hyperbolic.closedKleinCoordinate p=P.kleinCoordinate x:=by
      rw [←hpz]
      rfl
    have hx:x∈frontier (D∩fuchsianNielsenCore P hNE):=
      (nielsenCore_klein_finite_frontier hD hNE w hwD hwN x).mp (hKx ▸ hp)
    rcases frontier_inter_subset D (fuchsianNielsenCore P hNE) hx with hxD|hxN
    · obtain ⟨S,hS,hxS⟩:=hD.boundary_mem_side hxD.1
      let s:FuchsianPolygonSides P D:=⟨S,hS⟩
      have hpS:p∈fuchsianSideClosedModel s:=hpz ▸ (mem_fuchsianSideClosedModel_finite s x).mpr hxS
      have hpR:p∈⋃v:OriginalRefinedSide hD,v.carrier := by
        rw [originalRefinedSide_iUnion_carrier]
        exact mem_iUnion.mpr ⟨s,hpS⟩
      obtain ⟨v,hv⟩:=mem_iUnion.mp hpR
      exact Or.inl ⟨v,hv,closure_mono (image_mono (image_mono inter_subset_right)) hpQ⟩
    · have hxNF:P.finiteCoordinate x∈P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE):=
        mem_image_of_mem _ hxN.2
      rw [nielsenBoundaryDiscLineFamily_frontier_cover P hNE] at hxNF
      obtain ⟨L,hL⟩:=mem_iUnion.mp hxNF
      obtain ⟨hL,hxL⟩:=mem_iUnion.mp hL
      exact Or.inr ⟨L,hL,P.finiteCoordinate x,⟨hxL,x,hxN.1,rfl⟩,hpz⟩


theorem nielsen_boundary_original_side_subsingleton
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE)
    (s:FuchsianPolygonSides P D) (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) :
    (s.val∩P.finiteCoordinate ⁻¹' L.carrier).Subsingleton := by
  intro a ha b hb
  by_contra hab
  let g:=fuchsianSideElement hD s
  let U:=P.kleinCoordinate '' D
  let V:=P.kleinCoordinate '' (g • D)
  have hgne:g≠1:=(fuchsianSideElement_spec hD s).1
  have hdis:Disjoint U V := by
    simpa only [U,V,one_smul] using
      hD.locallyFinite.fundamental.klein_images_disjoint (Ne.symm hgne)
  obtain ⟨n,t,hn,hU,hV⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator hD.klein_convex
    (P.kleinCoordinate_isOpenEmbedding.isOpenMap _ hD.locallyFinite.fundamental.isOpen)
    ⟨P.kleinCoordinate w,w,hwD,rfl⟩ (hD.klein_smul_convex g)
    (P.kleinCoordinate_isOpenEmbedding.isOpenMap _
      ((Homeomorph.smul g).isOpenMap _ hD.locallyFinite.fundamental.isOpen))
    ⟨P.kleinCoordinate (g•w),g•w,mem_smul_set.mpr ⟨w,hwD,rfl⟩,rfl⟩ hdis
  have hna:inner ℝ n (P.kleinCoordinate a)=t := by
    apply _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hU hV
    exact OriginalOrientation.original_side_endpoint_closures hD s
      (Hyperbolic.discToClosedModel (P.finiteCoordinate a)) ((mem_fuchsianSideClosedModel_finite s a).mpr ha.1)
  have hnb:inner ℝ n (P.kleinCoordinate b)=t := by
    apply _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hU hV
    exact OriginalOrientation.original_side_endpoint_closures hD s
      (Hyperbolic.discToClosedModel (P.finiteCoordinate b)) ((mem_fuchsianSideClosedModel_finite s b).mpr hb.1)
  obtain ⟨m,k,hm,hform⟩:=L.klein_image_carrier
  have hma:inner ℝ m (P.kleinCoordinate a)=k :=
    (hform ▸ mem_image_of_mem Hyperbolic.kleinCoordinate ha.2).1
  have hmb:inner ℝ m (P.kleinCoordinate b)=k :=
    (hform ▸ mem_image_of_mem Hyperbolic.kleinCoordinate hb.2).1
  let u:=P.kleinCoordinate w
  let v:=P.kleinCoordinate (g•w)
  have hut:inner ℝ n u<t:=hU u ⟨w,hwD,rfl⟩
  have htv:t < inner ℝ n v:=hV v ⟨g•w,mem_smul_set.mpr ⟨w,hwD,rfl⟩,rfl⟩
  have hd:0 < inner ℝ n v-inner ℝ n u:=by linarith
  let c:ℝ:=(t-inner ℝ n u)/(inner ℝ n v-inner ℝ n u)
  have hc0:0<c:=div_pos (sub_pos.mpr hut) hd
  have hc1:c<1:=(div_lt_one hd).mpr (by linarith)
  let r:ℂ:=(1-c) • u+c • v
  have hNconv:Convex ℝ (P.kleinCoordinate '' fuchsianNielsenCore P hNE) := by
    have h:=(Hyperbolic.discHConvex_iff_klein_convex _).mp (fuchsianNielsenCore_convex P hNE)
    simpa only [image_image,UnitDiscFuchsianGroup.kleinCoordinate] using h
  have hrN:r∈P.kleinCoordinate '' fuchsianNielsenCore P hNE :=
    hNconv ⟨w,hwN,rfl⟩ ⟨g•w,fuchsianNielsenCore_invariant P hNE g w hwN,rfl⟩
      (sub_pos.mpr hc1).le hc0.le (by ring)
  have hnr:inner ℝ n r=t := by
    dsimp only [r]
    rw [inner_add_right,inner_smul_right,inner_smul_right]
    dsimp only [c]
    field_simp [hd.ne']
    ring
  have hmr:inner ℝ m r=k :=
    (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points (x:=r) hn hm
      (P.kleinCoordinate_isOpenEmbedding.injective.ne hab) hna hnb hma hmb).mp hnr
  obtain ⟨x,hxN,hxr⟩:=hrN
  have hxL:P.finiteCoordinate x∈L.carrier := by
    apply Hyperbolic.kleinCoordinate_injective.mem_set_image.mp
    rw [hform]
    constructor
    · change inner ℝ m (P.kleinCoordinate x)=k
      rw [hxr]
      exact hmr
    · rw [←Hyperbolic.range_kleinCoordinate]
      exact mem_range_self _
  obtain ⟨y,hy,hyx⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hxL
  have hyx':y=x:=P.finiteCoordinate.injective hyx
  subst y
  exact ((fuchsianNielsenCore_isOpen P hNE).frontier_eq ▸ hy).2 hxN



theorem nielsenCore_closedModel_klein_image
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (D:Set P.domain.carrier) :
    Hyperbolic.closedKleinCoordinate '' Hyperbolic.discClosedModelClosure
      (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))=
      fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE) := by
  unfold Hyperbolic.discClosedModelClosure
  rw [Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
  rfl

theorem nielsenRefinedSideCarrier_subset_frontier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) (v:OriginalRefinedSide hD) :
    Hyperbolic.closedKleinCoordinate '' nielsenRefinedSideCarrier hNE v⊆
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
  rintro z ⟨p,hp,rfl⟩
  have hpOld:p∈fuchsianSideClosedModel v.val.1:=v.carrier_subset_original hp.1
  have hpD:p∈Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D) := by
    apply closure_minimal ?_ isClosed_closure hpOld
    rintro _ ⟨z,⟨x,hx,rfl⟩,rfl⟩
    apply mem_closure_image Hyperbolic.isEmbedding_discToClosedModel.continuous.continuousAt
    rw [←P.finiteCoordinate.image_closure]
    exact mem_image_of_mem _ (frontier_subset_closure
      (v.val.1.property.subset_frontier hD.locallyFinite.fundamental hx))
  have hpQ:p∈Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)) := by
    rw [nielsenCore_closedModel_inter hD hNE w hwD hwN]
    exact ⟨hpD,hp.2⟩
  have hOld:Hyperbolic.closedKleinCoordinate p∈frontier (fuchsianPolygonCompactKlein P D) := by
    apply original_side_klein_subset_frontier hD v.val.1
    rw [←fuchsianSideClosedModel_klein_image]
    exact ⟨p,hpOld,rfl⟩
  rw [frontier,(show IsClosed (fuchsianPolygonCompactKlein P
    (D∩fuchsianNielsenCore P hNE)) from isClosed_closure).closure_eq]
  refine ⟨?_,fun hi=>hOld.2 (interior_mono ?_ hi)⟩
  · rw [←nielsenCore_closedModel_klein_image P hNE D]
    exact ⟨p,hpQ,rfl⟩
  · exact closure_mono (image_mono inter_subset_left)

theorem nielsenUnpairedNativeCarrier_subset_frontier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) :
    Hyperbolic.closedKleinCoordinate '' (Hyperbolic.discToClosedModel '' nielsenUnpairedNativeCarrier P D L)⊆
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
  rintro z ⟨p,⟨u,hu,rfl⟩,rfl⟩
  obtain ⟨x,hxD,hxu⟩:=hu.2
  have hxN:x∈frontier (fuchsianNielsenCore P hNE) := by
    obtain ⟨y,hy,hye⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hu.1
    exact (P.finiteCoordinate.injective (hye.trans hxu.symm)) ▸ hy
  have hxC:x∈closure (D∩fuchsianNielsenCore P hNE) := by
    rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
    exact ⟨hxD,frontier_subset_closure hxN⟩
  have hxF:x∈frontier (D∩fuchsianNielsenCore P hNE) := by
    rw [(hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)).frontier_eq]
    exact ⟨hxC,fun hx=>((fuchsianNielsenCore_isOpen P hNE).frontier_eq ▸ hxN).2 hx.2⟩
  rw [←hxu]
  exact (nielsenCore_klein_finite_frontier hD hNE w hwD hwN x).mpr hxF

theorem nielsenUnpairedNativeCarrier_nonempty_finite
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    {L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧
      (nielsenUnpairedNativeCarrier P D L).Nonempty}.Finite := by
  apply (finite_nielsenCore_boundary_lines hD hNE ha w hwD hwN).subset
  rintro L ⟨hL,z,hzL,x,hxD,hxz⟩
  have hxN:x∈frontier (fuchsianNielsenCore P hNE) := by
    obtain ⟨y,hy,hye⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hzL
    exact (P.finiteCoordinate.injective (hye.trans hxz.symm)) ▸ hy
  refine ⟨hL,z,hzL,x,?_,hxz⟩
  rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
  exact ⟨hxD,frontier_subset_closure hxN⟩


theorem nielsenCore_boundary_eq_raw_carriers
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (w:P.domain.carrier)
    (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) :
    frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))=
      (⋃v:OriginalRefinedSide hD,Hyperbolic.closedKleinCoordinate '' nielsenRefinedSideCarrier hNE v) ∪
      ⋃L:{L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧
        (nielsenUnpairedNativeCarrier P D L).Nonempty},
        Hyperbolic.closedKleinCoordinate '' (Hyperbolic.discToClosedModel '' nielsenUnpairedNativeCarrier P D L.val) := by
  apply subset_antisymm
  · intro z hz
    have hzK:z∈fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE) := by
      simpa only [fuchsianPolygonCompactKlein,closure_closure] using frontier_subset_closure hz
    have hbound:fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)⊆Metric.closedBall (0:ℂ) 1 := by
      apply closure_minimal _ Metric.isClosed_closedBall
      rintro y ⟨x,_hx,rfl⟩
      exact Metric.ball_subset_closedBall (P.kleinCoordinate_range ▸ mem_range_self x)
    obtain ⟨p,rfl⟩:=(Hyperbolic.range_closedKleinCoordinate ▸ hbound hzK)
    rcases nielsenCore_boundary_mem_raw_side hD hNE hFG w hwD hwN p hz with ⟨v,hv⟩|⟨L,hL,hpL⟩
    · exact Or.inl (mem_iUnion.mpr ⟨v,p,hv,rfl⟩)
    · have hn:(nielsenUnpairedNativeCarrier P D L).Nonempty := by
        obtain ⟨u,hu,_he⟩:=hpL
        exact ⟨u,hu⟩
      exact Or.inr (mem_iUnion.mpr ⟨⟨L,hL,hn⟩,p,hpL,rfl⟩)
  · intro z hz
    rcases hz with hz|hz
    · obtain ⟨v,hv⟩:=mem_iUnion.mp hz
      exact nielsenRefinedSideCarrier_subset_frontier hD hNE w hwD hwN v hv
    · obtain ⟨L,hL⟩:=mem_iUnion.mp hz
      exact nielsenUnpairedNativeCarrier_subset_frontier hD hNE w hwD hwN L.val L.property.1 hL

theorem nielsenCore_boundary_preperfect
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    Preperfect (frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))) := by
  obtain ⟨n,S,hregion,_hI⟩:=nielsenCore_actual_cyclic_model hD hNE ha hfin w hwD hwN
  let Q:=S.toDiscPolygon
  let J:=Q.toPolygonalCircle
  let e:=LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  have he:e '' J.carrier=frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
    rw [Q.toPolygonalCircle_carrier,image_image]
    have hcomp:(e ∘ Polygon.discPolygonKleinPlane)=Hyperbolic.closedKleinCoordinate := by
      funext p
      exact e.apply_symm_apply (Hyperbolic.closedKleinCoordinate p)
    change (e ∘ Polygon.discPolygonKleinPlane) '' Q.boundary=_
    rw [hcomp]
    have hb:=S.toCenteredData.boundary_image_eq_frontier
    change Hyperbolic.closedKleinCoordinate '' Q.boundary=frontier S.toCenteredData.kleinRegion at hb
    rwa [hregion] at hb
  have hc:IsPreconnected (frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))) := by
    rw [←he]
    exact J.isConnected_carrier.isPreconnected.image e e.continuous.continuousOn
  have hn:(frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))).Nontrivial := by
    rw [←he]
    have hv0:J.vertex 0∈J.carrier:=J.vertex_mem_carrier 0
    have hv1:J.vertex (0+1)∈J.carrier:=J.vertex_mem_carrier (0+1)
    exact ⟨e (J.vertex 0),mem_image_of_mem _ hv0,e (J.vertex (0+1)),
      mem_image_of_mem _ hv1,e.injective.ne (J.adjacent_ne 0)⟩
  exact hc.preperfect_of_nontrivial hn


theorem nielsenCore_boundary_eq_positive_carriers
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))=
      (⋃v:NielsenRefinedSide hD hNE,Hyperbolic.closedKleinCoordinate '' v.carrier) ∪
      ⋃s:NielsenUnpairedSide P hNE D,Hyperbolic.closedKleinCoordinate '' s.carrier := by
  classical
  let B:=frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
  let R:=(⋃v:NielsenRefinedSide hD hNE,Hyperbolic.closedKleinCoordinate '' v.carrier) ∪
    ⋃s:NielsenUnpairedSide P hNE D,Hyperbolic.closedKleinCoordinate '' s.carrier
  let :Fintype (FuchsianPolygonSides P D):=hfin.fintype
  let :Finite (OriginalRefinedSide hD):=by unfold OriginalRefinedSide;infer_instance
  let :Finite (NielsenRefinedSide hD hNE):=NielsenRefinedSide.finite hD hNE hfin
  let :Finite (NielsenUnpairedSide P hNE D):=NielsenUnpairedSide.finite hD hNE hFG w hwD hwN
  have ha:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
  let A:={L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧
    (nielsenUnpairedNativeCarrier P D L).Nonempty}
  let :Finite A:=(nielsenUnpairedNativeCarrier_nonempty_finite hD hNE ha w hwD hwN).to_subtype
  let E:Set ℂ:=(⋃v:OriginalRefinedSide hD,
      if (nielsenRefinedSideCarrier hNE v).Nontrivial then ∅ else
        Hyperbolic.closedKleinCoordinate '' nielsenRefinedSideCarrier hNE v) ∪
    ⋃L:A,if (nielsenUnpairedNativeCarrier P D L.val).Nontrivial then ∅ else
      Hyperbolic.closedKleinCoordinate '' (Hyperbolic.discToClosedModel '' nielsenUnpairedNativeCarrier P D L.val)
  have hE:E.Finite := by
    apply Set.Finite.union
    · apply Set.finite_iUnion
      intro v
      by_cases h:(nielsenRefinedSideCarrier hNE v).Nontrivial
      · simp only [ite_eq_left h,finite_empty]
      · rw [ite_eq_right h]
        apply Set.Finite.image
        apply Set.Subsingleton.finite
        intro a ha b hb
        by_contra hab
        exact h ⟨a,ha,b,hb,hab⟩
    · apply Set.finite_iUnion
      intro L
      by_cases h:(nielsenUnpairedNativeCarrier P D L.val).Nontrivial
      · simp only [ite_eq_left h,finite_empty]
      · rw [ite_eq_right h]
        apply Set.Finite.image
        apply Set.Finite.image
        apply Set.Subsingleton.finite
        intro a ha b hb
        by_contra hab
        exact h ⟨a,ha,b,hb,hab⟩
  have hR:IsClosed R := by
    apply IsClosed.union
    · apply isClosed_iUnion_of_finite
      intro v
      obtain ⟨p,q,_hne,hseg⟩:=v.carrier_eq_segment
      rw [hseg]
      exact ((Polygon.closedModelDiscHSegment_isCompact p q).image
        Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous).isClosed
    · apply isClosed_iUnion_of_finite
      intro s
      exact ((s.carrier_isCompact hFG hD).image Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous).isClosed
  have hRB:R⊆B := by
    intro z hz
    rcases hz with hz|hz
    · obtain ⟨v,hv⟩:=mem_iUnion.mp hz
      exact nielsenRefinedSideCarrier_subset_frontier hD hNE w hwD hwN v.val hv
    · obtain ⟨s,hs⟩:=mem_iUnion.mp hz
      exact nielsenUnpairedNativeCarrier_subset_frontier hD hNE w hwD hwN s.val s.property.1 hs
  have hcover:B⊆R∪E := by
    intro z hz
    change z∈frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) at hz
    rw [nielsenCore_boundary_eq_raw_carriers hD hNE hFG w hwD hwN] at hz
    rcases hz with hz|hz
    · obtain ⟨v,hv⟩:=mem_iUnion.mp hz
      by_cases h:(nielsenRefinedSideCarrier hNE v).Nontrivial
      · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨⟨v,h⟩,hv⟩))
      · right
        left
        exact mem_iUnion.mpr ⟨v,by rw [ite_eq_right h];exact hv⟩
    · obtain ⟨L,hL⟩:=mem_iUnion.mp hz
      by_cases h:(nielsenUnpairedNativeCarrier P D L.val).Nontrivial
      · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨L.val,L.property.1,h⟩,hL⟩))
      · right
        right
        exact mem_iUnion.mpr ⟨L,by rw [ite_eq_right h];exact hL⟩
  have hpre:Preperfect B:=nielsenCore_boundary_preperfect hD hNE ha hfin w hwD hwN
  apply subset_antisymm _ hRB
  intro p hp
  by_contra hn
  have hacc:AccPt p (𝓟 (Rᶜ∩B)) :=
    hpre.open_inter hR.isOpen_compl p ⟨hn,hp⟩
  have hf:(Rᶜ∩B).Finite:=hE.subset (fun x hx=>(hcover hx.2).resolve_left hx.1)
  exact (Set.Infinite.of_accPt hacc) hf


def nielsenBoundaryCornerOrbitTrace {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (D:Set P.domain.carrier)
    (p:𝕔𝔻) : Set 𝕔𝔻 :=
  {u | Hyperbolic.closedKleinCoordinate u∈frontier (fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE)) ∧ ∃g:H,(P.compactifiedAction g).closedMap p=u}

theorem nielsenBoundaryCornerOrbitTrace_finite
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) (p:𝕔𝔻) :
    (nielsenBoundaryCornerOrbitTrace P hNE D p).Finite := by
  rcases Hyperbolic.closedDisc_interior_or_ideal p with ⟨z,hzp⟩|hp
  · let x:=P.finiteCoordinate.symm z
    have hpx:p=Hyperbolic.discToClosedModel (P.finiteCoordinate x) := by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact hzp.symm
    apply ((hD.locallyFinite.cycle_finite x).image
      (fun y=>Hyperbolic.discToClosedModel (P.finiteCoordinate y))).subset
    rintro u ⟨hu,g,hgu⟩
    rw [hpx,P.compactifiedAction_finite] at hgu
    have hyF:g•x∈frontier (D∩fuchsianNielsenCore P hNE) :=
      (nielsenCore_klein_finite_frontier hD hNE w hwD hwN (g•x)).mp (by
        rw [←hgu] at hu
        exact hu)
    refine ⟨g•x,⟨closure_mono inter_subset_left (frontier_subset_closure hyF),?_⟩,hgu⟩
    exact MulAction.mem_orbit_iff.mpr ⟨g,rfl⟩
  · apply ((finite_nielsenCore_idealBoundary hD hNE ha).preimage
      Complex.UnitClosedDisc.isEmbedding_coe.injective.injOn).subset
    rintro u ⟨hu,g,hgu⟩
    have hnu:‖(u:ℂ)‖=1 := by
      rw [←hgu]
      exact ((P.compactifiedAction g).ideal_iff p).mpr hp
    have hku:Hyperbolic.closedKleinCoordinate u=(u:ℂ):=
      congrArg (fun v:𝕔𝔻=>(v:ℂ)) (Hyperbolic.closedPoincareToKlein_ideal_fixed u hnu)
    apply (compactKlein_ideal_mem_iff P _ (u:ℂ) hnu).mp
    rw [←hku]
    simpa only [fuchsianPolygonCompactKlein,closure_closure] using frontier_subset_closure hu

theorem nielsen_compactifiedAction_one {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (p:𝕔𝔻) : (P.compactifiedAction 1).closedMap p=p := by
  apply Hyperbolic.isEmbedding_closedDiscToExtended.injective
  rw [P.compactifiedAction_sphere]
  rfl

theorem nielsen_compactifiedAction_mul {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (g h:H) (p:𝕔𝔻) :
    (P.compactifiedAction (g*h)).closedMap p=
      (P.compactifiedAction g).closedMap ((P.compactifiedAction h).closedMap p) := by
  apply Hyperbolic.isEmbedding_closedDiscToExtended.injective
  rw [P.compactifiedAction_sphere,P.compactifiedAction_sphere,P.compactifiedAction_sphere]
  rfl

def nielsenBoundaryMarkSaturation {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (D:Set P.domain.carrier)
    (F:Set 𝕔𝔻) : Set 𝕔𝔻 :=
  ⋃p∈F,nielsenBoundaryCornerOrbitTrace P hNE D p

theorem nielsenBoundaryMarkSaturation_finite
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (F:Set 𝕔𝔻) (hF:F.Finite) : (nielsenBoundaryMarkSaturation P hNE D F).Finite :=
  hF.biUnion (fun p _=>nielsenBoundaryCornerOrbitTrace_finite hD hNE ha w hwD hwN p)

theorem nielsenBoundaryMarkSaturation_subset_boundary
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (D:Set P.domain.carrier) (F:Set 𝕔𝔻) :
    Hyperbolic.closedKleinCoordinate '' nielsenBoundaryMarkSaturation P hNE D F⊆
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
  rintro z ⟨u,hu,rfl⟩
  obtain ⟨p,_hp,hu⟩:=mem_iUnion₂.mp hu
  exact hu.1

theorem nielsenBoundaryMarkSaturation_contains
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (D:Set P.domain.carrier) (F:Set 𝕔𝔻)
    (hF:Hyperbolic.closedKleinCoordinate '' F⊆frontier (fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE))) : F⊆nielsenBoundaryMarkSaturation P hNE D F := by
  intro p hp
  exact mem_iUnion₂.mpr ⟨p,hp,hF (mem_image_of_mem _ hp),1,nielsen_compactifiedAction_one P p⟩

theorem nielsenBoundaryMarkSaturation_pair_image
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) (F:Set 𝕔𝔻) (v:NielsenRefinedSide hD hNE) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ''
      (nielsenBoundaryMarkSaturation P hNE D F∩v.carrier)⊆nielsenBoundaryMarkSaturation P hNE D F := by
  rintro y ⟨x,⟨hx,hxv⟩,rfl⟩
  obtain ⟨p,hp,hxB,g,hgx⟩:=mem_iUnion₂.mp hx
  let k:=(fuchsianSideElement hD v.val.val.1)⁻¹
  have hky:(P.compactifiedAction k).closedMap x∈v.pair.carrier := by
    rw [←v.pair_carrier]
    exact ⟨x,hxv,rfl⟩
  refine mem_iUnion₂.mpr ⟨p,hp,?_,k*g,?_⟩
  · exact nielsenRefinedSideCarrier_subset_frontier hD hNE w hwD hwN v.pair.val
      (mem_image_of_mem _ hky)
  · rw [nielsen_compactifiedAction_mul,hgx]


def NielsenBoundarySide {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (hNE:DiscreteGroups.IsNonElementary H) :=
  NielsenRefinedSide hD hNE ⊕ NielsenUnpairedSide P hNE D

def NielsenBoundarySide.carrier {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D} {hNE:DiscreteGroups.IsNonElementary H}
    (s:NielsenBoundarySide hD hNE) : Set 𝕔𝔻 :=
  Sum.elim NielsenRefinedSide.carrier NielsenUnpairedSide.carrier s

theorem NielsenBoundarySide.carrier_eq_segment
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (hFG:H.FG)
    (s:NielsenBoundarySide hD hNE) :
    ∃p q:𝕔𝔻,p≠q ∧ s.carrier=Hyperbolic.closedModelDiscHSegment p q := by
  cases s with
  | inl v => exact v.carrier_eq_segment
  | inr u =>
    obtain ⟨p,q,hpq,he⟩:=u.carrier_finite_endpoints hFG hD
    exact ⟨Hyperbolic.discToClosedModel p,Hyperbolic.discToClosedModel
      q,Hyperbolic.isEmbedding_discToClosedModel.injective.ne hpq,he⟩

def NielsenBoundarySide.leftEndpoint {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (hFG:H.FG)
    (s:NielsenBoundarySide hD hNE) : 𝕔𝔻:=Classical.choose (s.carrier_eq_segment hFG)

def NielsenBoundarySide.rightEndpoint {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (hFG:H.FG)
    (s:NielsenBoundarySide hD hNE) : 𝕔𝔻:=Classical.choose (Classical.choose_spec (s.carrier_eq_segment hFG))

theorem NielsenBoundarySide.endpoints_spec {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (hFG:H.FG)
    (s:NielsenBoundarySide hD hNE) :
    s.leftEndpoint hFG≠s.rightEndpoint hFG ∧
      s.carrier=Hyperbolic.closedModelDiscHSegment (s.leftEndpoint hFG) (s.rightEndpoint hFG) :=
  Classical.choose_spec (Classical.choose_spec (s.carrier_eq_segment hFG))

theorem NielsenBoundarySide.carrier_subset_frontier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) (s:NielsenBoundarySide hD hNE) :
    Hyperbolic.closedKleinCoordinate '' s.carrier⊆frontier
      (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
  cases s with
  | inl v => exact nielsenRefinedSideCarrier_subset_frontier hD hNE w hwD hwN v.val
  | inr u => exact nielsenUnpairedNativeCarrier_subset_frontier hD hNE w hwD hwN u.val u.property.1

theorem nielsen_paired_unpaired_inter_subsingleton
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE)
    (v:NielsenRefinedSide hD hNE) (s:NielsenUnpairedSide P hNE D) :
    (v.carrier∩s.carrier).Subsingleton := by
  rintro a ⟨hav,z,hz,rfl⟩ b ⟨hbv,u,hu,rfl⟩
  let x:=P.finiteCoordinate.symm z
  let y:=P.finiteCoordinate.symm u
  have hx:P.finiteCoordinate x=z:=P.finiteCoordinate.apply_symm_apply z
  have hy:P.finiteCoordinate y=u:=P.finiteCoordinate.apply_symm_apply u
  have hxS:x∈v.val.val.1.val := by
    apply (mem_fuchsianSideClosedModel_finite v.val.val.1 x).mp
    rw [hx]
    exact v.val.carrier_subset_original hav.1
  have hyS:y∈v.val.val.1.val := by
    apply (mem_fuchsianSideClosedModel_finite v.val.val.1 y).mp
    rw [hy]
    exact v.val.carrier_subset_original hbv.1
  have hxy:x=y:=nielsen_boundary_original_side_subsingleton hD hNE w hwD hwN
    v.val.val.1 s.val s.property.1
      ⟨hxS,by change P.finiteCoordinate x∈s.val.carrier; rw [hx];exact hz.1⟩
      ⟨hyS,by change P.finiteCoordinate y∈s.val.carrier; rw [hy];exact hu.1⟩
  exact congrArg Hyperbolic.discToClosedModel (hx.symm.trans ((congrArg P.finiteCoordinate hxy).trans hy))

theorem NielsenBoundarySide.inter_finite
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (w:P.domain.carrier) (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) (s t:NielsenBoundarySide hD hNE) (hne:s≠t) :
    (s.carrier∩t.carrier).Finite := by
  cases s with
  | inl v =>
    cases t with
    | inl u =>
      have hvu:v.val≠u.val:=by intro he;exact hne (congrArg Sum.inl (Subtype.ext he))
      apply (Set.toFinite ({v.val.leftEndpoint,v.val.rightEndpoint}:Set 𝕔𝔻)).subset
      intro p hp
      exact (v.val.inter_subset_endpoints u.val hvu _ _ _ _
        v.val.carrier_eq_endpoints u.val.carrier_eq_endpoints ⟨hp.1.1,hp.2.1⟩).1
    | inr u => exact (nielsen_paired_unpaired_inter_subsingleton hD hNE w hwD hwN v u).finite
  | inr v =>
    cases t with
    | inl u =>
      rw [inter_comm]
      exact (nielsen_paired_unpaired_inter_subsingleton hD hNE w hwD hwN u v).finite
    | inr u =>
      have hvu:v.val≠u.val:=by intro he;exact hne (congrArg Sum.inr (Subtype.ext he))
      have hd:=nielsenBoundaryDiscLineFamily_pairwise_disjoint P hNE v.property.1 u.property.1 hvu
      apply Set.Subsingleton.finite
      rintro a ⟨⟨z,hz,rfl⟩,w,hw,he⟩ _b _hb
      have hwz:w=z:=Hyperbolic.isEmbedding_discToClosedModel.injective he
      exact False.elim (disjoint_left.mp hd hz.1 (hwz ▸ hw.1))


theorem NielsenBoundarySide.finite
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    Finite (NielsenBoundarySide hD hNE) := by
  let :Finite (NielsenRefinedSide hD hNE):=NielsenRefinedSide.finite hD hNE hfin
  let :Finite (NielsenUnpairedSide P hNE D):=NielsenUnpairedSide.finite hD hNE hFG w hwD hwN
  unfold NielsenBoundarySide
  infer_instance

theorem NielsenBoundarySide.endpoints_mem_carrier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (hFG:H.FG) (s:NielsenBoundarySide hD hNE) :
    s.leftEndpoint hFG∈s.carrier ∧ s.rightEndpoint hFG∈s.carrier := by
  rw [s.endpoints_spec hFG |>.2]
  exact ⟨Polygon.closedModelDiscHSegment_left_mem _ _,Polygon.closedModelDiscHSegment_right_mem _ _⟩

def nielsenBoundarySeedMarks
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG) : Set 𝕔𝔻 := by
  classical
  exact (range (fun s:NielsenBoundarySide hD hNE=>s.leftEndpoint hFG) ∪
    range (fun s:NielsenBoundarySide hD hNE=>s.rightEndpoint hFG)) ∪
    ⋃s:NielsenBoundarySide hD hNE,⋃t:NielsenBoundarySide hD hNE,
      if s=t then ∅ else s.carrier∩t.carrier

theorem nielsenBoundarySeedMarks_finite
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    (nielsenBoundarySeedMarks hD hNE hFG).Finite := by
  classical
  let :Finite (NielsenBoundarySide hD hNE):=NielsenBoundarySide.finite hD hNE hFG hfin w hwD hwN
  apply Set.Finite.union ((Set.finite_range _).union (Set.finite_range _))
  apply Set.finite_iUnion
  intro s
  apply Set.finite_iUnion
  intro t
  by_cases h:s=t
  · simp only [ite_eq_left h,finite_empty]
  · rw [ite_eq_right h]
    exact NielsenBoundarySide.inter_finite hD hNE w hwD hwN s t h

theorem nielsenBoundarySeedMarks_subset_frontier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    Hyperbolic.closedKleinCoordinate '' nielsenBoundarySeedMarks hD hNE hFG⊆
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
  classical
  rintro z ⟨p,hp,rfl⟩
  rcases hp with (⟨s,rfl⟩|⟨s,rfl⟩)|hp
  · exact NielsenBoundarySide.carrier_subset_frontier hD hNE w hwD hwN s
      (mem_image_of_mem _ (s.endpoints_mem_carrier hFG).1)
  · exact NielsenBoundarySide.carrier_subset_frontier hD hNE w hwD hwN s
      (mem_image_of_mem _ (s.endpoints_mem_carrier hFG).2)
  · obtain ⟨s,hs⟩:=mem_iUnion.mp hp
    obtain ⟨t,ht⟩:=mem_iUnion.mp hs
    by_cases h:s=t
    · simp only [ite_eq_left h,mem_empty_iff_false] at ht
    · rw [ite_eq_right h] at ht
      exact NielsenBoundarySide.carrier_subset_frontier hD hNE w hwD hwN s (mem_image_of_mem _ ht.1)

theorem NielsenBoundarySide.extreme_mem_seed
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (s:NielsenBoundarySide hD hNE) (p:𝕔𝔻) (hp:p∈s.carrier)
    (hext:Hyperbolic.closedKleinCoordinate p∈(fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE)).extremePoints ℝ) :
    p∈nielsenBoundarySeedMarks hD hNE hFG := by
  by_cases hl:p=s.leftEndpoint hFG
  · exact Or.inl (Or.inl ⟨s,hl.symm⟩)
  by_cases hr:p=s.rightEndpoint hFG
  · exact Or.inl (Or.inr ⟨s,hr.symm⟩)
  have hpseg:Hyperbolic.closedKleinCoordinate p∈segment ℝ (Hyperbolic.closedKleinCoordinate (s.leftEndpoint hFG))
      (Hyperbolic.closedKleinCoordinate (s.rightEndpoint hFG)) := by
    rw [←Hyperbolic.closedKlein_image_closedModelDiscHSegment,←(s.endpoints_spec hFG).2]
    exact mem_image_of_mem _ hp
  have hopen:=mem_openSegment_of_ne_left_right (Hyperbolic.closedKleinCoordinate_injective.ne (Ne.symm hl))
    (Hyperbolic.closedKleinCoordinate_injective.ne (Ne.symm hr)) hpseg
  have haB:=NielsenBoundarySide.carrier_subset_frontier hD hNE w hwD hwN s
    (mem_image_of_mem _ (s.endpoints_mem_carrier hFG).1)
  have hbB:=NielsenBoundarySide.carrier_subset_frontier hD hNE w hwD hwN s
    (mem_image_of_mem _ (s.endpoints_mem_carrier hFG).2)
  have haK:Hyperbolic.closedKleinCoordinate (s.leftEndpoint hFG)∈fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE) := by
    simpa only [fuchsianPolygonCompactKlein,closure_closure] using frontier_subset_closure haB
  have hbK:Hyperbolic.closedKleinCoordinate (s.rightEndpoint hFG)∈fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE) := by
    simpa only [fuchsianPolygonCompactKlein,closure_closure] using frontier_subset_closure hbB
  exact False.elim (hl (Hyperbolic.closedKleinCoordinate_injective (hext.2 haK hbK hopen).symm))

theorem nielsenBoundarySide_covers_frontier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (p:𝕔𝔻) (hp:Hyperbolic.closedKleinCoordinate p∈frontier
      (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))) :
    ∃s:NielsenBoundarySide hD hNE,p∈s.carrier := by
  rw [nielsenCore_boundary_eq_positive_carriers hD hNE hFG hfin w hwD hwN] at hp
  rcases hp with hp|hp
  · obtain ⟨v,u,hu,hup⟩:=mem_iUnion.mp hp
    exact ⟨Sum.inl v,Hyperbolic.closedKleinCoordinate_injective hup ▸ hu⟩
  · obtain ⟨s,u,hu,hup⟩:=mem_iUnion.mp hp
    exact ⟨Sum.inr s,Hyperbolic.closedKleinCoordinate_injective hup ▸ hu⟩


def nielsenCanonicalBoundaryMarks
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG) : Set 𝕔𝔻 :=
  nielsenBoundaryMarkSaturation P hNE D (nielsenBoundarySeedMarks hD hNE hFG)

theorem nielsenCore_actual_marked_cyclic_boundary
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    ∃J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle,
      J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier) ∧
      ∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG := by
  classical
  have ha:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
  obtain ⟨n,S,hregion,_hI⟩:=nielsenCore_actual_cyclic_model hD hNE ha hfin w hwD hwN
  let Q:=S.toDiscPolygon
  let J:=Q.toPolygonalCircle
  let M:=nielsenCanonicalBoundaryMarks hD hNE hFG
  have hM:M.Finite:=nielsenBoundaryMarkSaturation_finite hD hNE ha w hwD hwN _
    (nielsenBoundarySeedMarks_finite hD hNE hFG hfin w hwD hwN)
  have hMB:Hyperbolic.closedKleinCoordinate '' M⊆frontier (fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE)) :=
    nielsenBoundaryMarkSaturation_subset_boundary P hNE D _
  have hseed:nielsenBoundarySeedMarks hD hNE hFG⊆M :=
    nielsenBoundaryMarkSaturation_contains P hNE D _
      (nielsenBoundarySeedMarks_subset_frontier hD hNE hFG w hwD hwN)
  have hB:Hyperbolic.closedKleinCoordinate '' Q.boundary=frontier (fuchsianPolygonCompactKlein P
      (D∩fuchsianNielsenCore P hNE)) := by
    have hb:=S.toCenteredData.boundary_image_eq_frontier
    change Hyperbolic.closedKleinCoordinate '' Q.boundary=frontier S.toCenteredData.kleinRegion at hb
    rwa [hregion] at hb
  have hQ:Q.boundary=⋃s:NielsenBoundarySide hD hNE,s.carrier := by
    apply Hyperbolic.closedKleinCoordinate_injective.image_injective
    rw [hB,image_iUnion]
    unfold NielsenBoundarySide
    rw [iUnion_sum]
    exact nielsenCore_boundary_eq_positive_carriers hD hNE hFG hfin w hwD hwN
  have hf:(Polygon.discPolygonKleinPlane '' M).Finite:=hM.image _
  let F:=hf.toFinset
  have hF:∀p∈F,p∈J.carrier := by
    intro p hp
    obtain ⟨u,hu,rfl⟩:=hf.mem_toFinset.mp hp
    have huQ:u∈Q.boundary:=Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
      (hB.symm ▸ hMB (mem_image_of_mem _ hu))
    rw [Q.toPolygonalCircle_carrier]
    exact ⟨u,huQ,rfl⟩
  have hkeep:∀p,J.IsVertexPoint p→p∈F := by
    rintro p ⟨j,hj⟩
    let i:=Q.jordanIndexEquiv.symm j
    have hp:Polygon.discPolygonKleinPlane (S.vertices i)=p:=hj
    apply hf.mem_toFinset.mpr
    refine ⟨S.vertices i,?_,hp⟩
    have hpB:Hyperbolic.closedKleinCoordinate (S.vertices i)∈frontier (fuchsianPolygonCompactKlein P
        (D∩fuchsianNielsenCore P hNE)):=hB ▸ mem_image_of_mem _ (Q.vertex_mem_boundary i)
    obtain ⟨s,hs⟩:=nielsenBoundarySide_covers_frontier hD hNE hFG hfin w hwD hwN (S.vertices i) hpB
    have hext:Hyperbolic.closedKleinCoordinate (S.vertices i)∈(fuchsianPolygonCompactKlein P
        (D∩fuchsianNielsenCore P hNE)).extremePoints ℝ := by
      rw [←hregion]
      exact S.vertex_mem_extreme i
    exact hseed (NielsenBoundarySide.extreme_mem_seed hD hNE hFG w hwD hwN s _ hs hext)
  obtain ⟨L,hL,hvertices⟩:=Surfaces.polygonalCircle_exists_refinement_exact_of_vertex_cover J F hF hkeep
  refine ⟨L,?_,fun p=>?_⟩
  · rw [hL,Q.toPolygonalCircle_carrier,hQ]
  · rw [hvertices,hf.mem_toFinset]


def NielsenBoundarySide.planeCarrier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (s:NielsenBoundarySide hD hNE) : Set LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane :=
  Polygon.discPolygonKleinPlane '' s.carrier

theorem NielsenBoundarySide.planeCarrier_isClosed
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D}
    {hNE:DiscreteGroups.IsNonElementary H}
    (hFG:H.FG) (s:NielsenBoundarySide hD hNE) : IsClosed s.planeCarrier := by
  have hc:Continuous Polygon.discPolygonKleinPlane :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm.continuous.comp
      Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous
  obtain ⟨a,b,_hab,he⟩:=s.carrier_eq_segment hFG
  unfold NielsenBoundarySide.planeCarrier
  rw [he]
  exact ((Polygon.closedModelDiscHSegment_isCompact a b).image hc).isClosed

theorem nielsenCanonicalBoundaryMarks_seed_subset
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    nielsenBoundarySeedMarks hD hNE hFG⊆nielsenCanonicalBoundaryMarks hD hNE hFG :=
  nielsenBoundaryMarkSaturation_contains P hNE D _
    (nielsenBoundarySeedMarks_subset_frontier hD hNE hFG w hwD hwN)

theorem nielsen_cyclic_openEdge_not_marked
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) (x:LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane)
    (hx:x∈openSegment ℝ (J.vertex i) (J.vertex (i+1))) :
    x∉Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG := by
  intro he
  have hxv:=(hv x).mpr he
  rcases hxv.mem_edgeSegment_iff i |>.mp (openSegment_subset_segment ℝ _ _ hx) with hi|hi
  · rw [hi] at hx
    exact J.adjacent_ne i (left_mem_openSegment_iff.mp hx)
  · rw [hi] at hx
    exact J.adjacent_ne i (right_mem_openSegment_iff.mp hx)

theorem nielsen_cyclic_edge_unique_tag
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : ∃!s:NielsenBoundarySide hD hNE,J.edgeSegment i⊆s.planeCarrier := by
  classical
  let :Finite (NielsenBoundarySide hD hNE):=NielsenBoundarySide.finite hD hNE hFG hfin w hwD hwN
  let U:=openSegment ℝ (J.vertex i) (J.vertex (i+1))
  have hcover:U⊆⋃s:NielsenBoundarySide hD hNE,s.planeCarrier := by
    intro x hx
    change x∈⋃s:NielsenBoundarySide hD hNE,Polygon.discPolygonKleinPlane '' s.carrier
    rw [←image_iUnion,←hc]
    exact J.edgeSegment_subset_carrier i (openSegment_subset_segment ℝ _ _ hx)
  have hseed:=nielsenCanonicalBoundaryMarks_seed_subset hD hNE hFG w hwD hwN
  have hsep:∀s t:NielsenBoundarySide hD hNE,s≠t→∀x∈U,x∈s.planeCarrier→x∉t.planeCarrier := by
    rintro s t hst x hx ⟨a,ha,hax⟩ ⟨b,hb,hbx⟩
    have hab:a=b:=Polygon.discPolygonKleinPlane_injective (hax.trans hbx.symm)
    subst b
    have haSeed:a∈nielsenBoundarySeedMarks hD hNE hFG := by
      right
      exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨t,by rw [ite_eq_right hst];exact ⟨ha,hb⟩⟩⟩
    exact nielsen_cyclic_openEdge_not_marked hD hNE hFG J hv i x hx ⟨a,hseed haSeed,hax⟩
  obtain ⟨s,hs⟩:=Auxiliary.Topology.isPreconnected_subset_one_finite_closed_cover U
    (convex_openSegment _ _ |>.isPreconnected) ⟨_,midpoint_mem_openSegment _ _⟩
    (fun s:NielsenBoundarySide hD hNE=>s.planeCarrier)
    (fun s=>s.planeCarrier_isClosed hFG) hcover hsep
  have hsub:J.edgeSegment i⊆s.planeCarrier := by
    change segment ℝ (J.vertex i) (J.vertex (i+1))⊆_
    rw [←closure_openSegment]
    exact closure_minimal hs (s.planeCarrier_isClosed hFG)
  refine ⟨s,hsub,?_⟩
  intro t ht
  by_contra hts
  let x:=midpoint ℝ (J.vertex i) (J.vertex (i+1))
  have hx:x∈U:=midpoint_mem_openSegment _ _
  have hxe:x∈J.edgeSegment i:=midpoint_mem_segment _ _
  exact hsep s t (Ne.symm hts) x hx (hsub hxe) (ht hxe)


def nielsenCyclicVertex
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : 𝕔𝔻:=Classical.choose ((hv (J.vertex i)).mp ⟨i,rfl⟩)

theorem nielsenCyclicVertex_marked
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : nielsenCyclicVertex hD hNE hFG J hv i∈nielsenCanonicalBoundaryMarks hD hNE hFG :=
  (Classical.choose_spec ((hv (J.vertex i)).mp ⟨i,rfl⟩)).1

theorem nielsenCyclicVertex_plane
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : Polygon.discPolygonKleinPlane (nielsenCyclicVertex hD hNE hFG J hv i)=J.vertex i :=
  (Classical.choose_spec ((hv (J.vertex i)).mp ⟨i,rfl⟩)).2

theorem nielsenCyclicVertex_injective
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG) :
    Function.Injective (nielsenCyclicVertex hD hNE hFG J hv) := by
  intro i j he
  apply J.vertex_injective
  rw [←nielsenCyclicVertex_plane hD hNE hFG J hv i,←nielsenCyclicVertex_plane hD hNE hFG J hv j,he]

def nielsenCyclicEdge
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : Set 𝕔𝔻:=Hyperbolic.closedModelDiscHSegment
      (nielsenCyclicVertex hD hNE hFG J hv i) (nielsenCyclicVertex hD hNE hFG J hv (i+1))

theorem nielsenCyclicEdge_plane
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : Polygon.discPolygonKleinPlane '' nielsenCyclicEdge hD hNE hFG J hv i=J.edgeSegment i := by
  let a:=nielsenCyclicVertex hD hNE hFG J hv i
  let b:=nielsenCyclicVertex hD hNE hFG J hv (i+1)
  let e:=LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm
  have he:Polygon.discPolygonKleinPlane '' nielsenCyclicEdge hD hNE hFG J hv i=
      e '' (Hyperbolic.closedKleinCoordinate '' Hyperbolic.closedModelDiscHSegment a b) := by
    rw [image_image]
    rfl
  rw [he,Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  have hseg:e '' segment ℝ (Hyperbolic.closedKleinCoordinate a) (Hyperbolic.closedKleinCoordinate b)=
      segment ℝ (e (Hyperbolic.closedKleinCoordinate a)) (e (Hyperbolic.closedKleinCoordinate b)) :=
    image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  rw [hseg]
  change segment ℝ (Polygon.discPolygonKleinPlane a) (Polygon.discPolygonKleinPlane b)=J.edgeSegment i
  rw [nielsenCyclicVertex_plane hD hNE hFG J hv i,nielsenCyclicVertex_plane hD hNE hFG J hv (i+1)]
  rfl

theorem nielsenCyclicEdge_no_extra_marks
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) (p:𝕔𝔻) (hp:p∈nielsenCyclicEdge hD hNE hFG J hv i)
    (hpm:p∈nielsenCanonicalBoundaryMarks hD hNE hFG) :
    p=nielsenCyclicVertex hD hNE hFG J hv i ∨ p=nielsenCyclicVertex hD hNE hFG J hv (i+1) := by
  have hpE:Polygon.discPolygonKleinPlane p∈J.edgeSegment i := by
    rw [←nielsenCyclicEdge_plane hD hNE hFG J hv i]
    exact mem_image_of_mem _ hp
  have hpV:J.IsVertexPoint (Polygon.discPolygonKleinPlane p):=(hv _).mpr ⟨p,hpm,rfl⟩
  rcases hpV.mem_edgeSegment_iff i |>.mp hpE with hi|hi
  · left
    apply Polygon.discPolygonKleinPlane_injective
    rw [hi,nielsenCyclicVertex_plane]
  · right
    apply Polygon.discPolygonKleinPlane_injective
    rw [hi,nielsenCyclicVertex_plane]


private theorem nielsen_segment_eq_cyclic_edge
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (a b:LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane) (hab:a≠b)
    (ha:J.IsVertexPoint a) (hb:J.IsVertexPoint b)
    (hsub:segment ℝ a b⊆J.carrier)
    (hno:∀p∈openSegment ℝ a b,¬J.IsVertexPoint p) :
    ∃j:ZMod J.n,J.edgeSegment j=segment ℝ a b := by
  let U:=openSegment ℝ a b
  have hcover:U⊆⋃j:ZMod J.n,J.edgeSegment j:=by
    intro x hx
    exact hsub (openSegment_subset_segment ℝ a b hx)
  have hsep:∀i j:ZMod J.n,i≠j→∀x∈U,x∈J.edgeSegment i→x∉J.edgeSegment j := by
    intro i j hij x hx hxi hxj
    rcases J.edgeSegment_inter_subset_endpoints hij ⟨hxi,hxj⟩ with hi|hi
    · exact hno x hx (hi.symm ▸ ⟨i,rfl⟩)
    · exact hno x hx (hi.symm ▸ ⟨i+1,rfl⟩)
  obtain ⟨j,hj⟩:=Auxiliary.Topology.isPreconnected_subset_one_finite_closed_cover U
    (convex_openSegment _ _ |>.isPreconnected) ⟨_,midpoint_mem_openSegment _ _⟩
    (fun j:ZMod J.n=>J.edgeSegment j) (fun j=>J.isClosed_edgeSegment j) hcover hsep
  have hs:segment ℝ a b⊆J.edgeSegment j := by
    rw [←closure_openSegment]
    exact closure_minimal hj (J.isClosed_edgeSegment j)
  rcases (ha.mem_edgeSegment_iff j).mp (hs (left_mem_segment ℝ a b)) with hja|hja <;>
    rcases (hb.mem_edgeSegment_iff j).mp (hs (right_mem_segment ℝ a b)) with hjb|hjb
  · exact False.elim (hab (hja.trans hjb.symm))
  · exact ⟨j,by rw [hja,hjb];rfl⟩
  · exact ⟨j,by rw [hja,hjb,segment_symm];rfl⟩
  · exact False.elim (hab (hja.trans hjb.symm))

theorem nielsenBoundaryMarkSaturation_map_mem
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (D:Set P.domain.carrier) (F:Set 𝕔𝔻)
    (g:H) (p:𝕔𝔻) (hp:p∈nielsenBoundaryMarkSaturation P hNE D F)
    (hB:Hyperbolic.closedKleinCoordinate ((P.compactifiedAction g).closedMap p)∈
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))) :
    (P.compactifiedAction g).closedMap p∈nielsenBoundaryMarkSaturation P hNE D F := by
  obtain ⟨a,ha,_hpB,k,hkp⟩:=mem_iUnion₂.mp hp
  refine mem_iUnion₂.mpr ⟨a,ha,hB,g*k,?_⟩
  rw [nielsen_compactifiedAction_mul,hkp]

theorem nielsenCyclicEdge_paired_image
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) (v:NielsenRefinedSide hD hNE)
    (hsub:nielsenCyclicEdge hD hNE hFG J hv i⊆v.carrier) :
    ∃j:ZMod J.n,
      (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ''
        nielsenCyclicEdge hD hNE hFG J hv i=nielsenCyclicEdge hD hNE hFG J hv j ∧
      nielsenCyclicEdge hD hNE hFG J hv j⊆v.pair.carrier := by
  let k:=(fuchsianSideElement hD v.val.val.1)⁻¹
  let f:=(P.compactifiedAction k).closedMap
  let a:=nielsenCyclicVertex hD hNE hFG J hv i
  let b:=nielsenCyclicVertex hD hNE hFG J hv (i+1)
  let C:=f '' nielsenCyclicEdge hD hNE hFG J hv i
  have hC:C⊆v.pair.carrier := by
    rintro y ⟨x,hx,rfl⟩
    rw [←v.pair_carrier]
    exact ⟨x,hsub hx,rfl⟩
  have hmark:∀p∈C,p∈nielsenCanonicalBoundaryMarks hD hNE hFG→p=f a∨p=f b := by
    rintro p ⟨x,hx,rfl⟩ hpm
    have hxp:(P.compactifiedAction k⁻¹).closedMap (f x)=x := by
      rw [←nielsen_compactifiedAction_mul,inv_mul_cancel,nielsen_compactifiedAction_one]
    have hxB:Hyperbolic.closedKleinCoordinate ((P.compactifiedAction k⁻¹).closedMap (f x))∈
        frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
      rw [hxp]
      exact nielsenRefinedSideCarrier_subset_frontier hD hNE w hwD hwN v.val (mem_image_of_mem _ (hsub hx))
    have hxm:x∈nielsenCanonicalBoundaryMarks hD hNE hFG := by
      rw [←hxp]
      exact nielsenBoundaryMarkSaturation_map_mem P hNE D _ k⁻¹ (f x) hpm hxB
    rcases nielsenCyclicEdge_no_extra_marks hD hNE hFG J hv i x hx hxm with he|he
    · exact Or.inl (congrArg f he)
    · exact Or.inr (congrArg f he)
  have haE:a∈nielsenCyclicEdge hD hNE hFG J hv i:=Polygon.closedModelDiscHSegment_left_mem _ _
  have hbE:b∈nielsenCyclicEdge hD hNE hFG J hv i:=Polygon.closedModelDiscHSegment_right_mem _ _
  have hfaMark:f a∈nielsenCanonicalBoundaryMarks hD hNE hFG := by
    exact nielsenBoundaryMarkSaturation_pair_image hD hNE w hwD hwN _ v
      ⟨a,⟨nielsenCyclicVertex_marked hD hNE hFG J hv i,hsub haE⟩,rfl⟩
  have hfbMark:f b∈nielsenCanonicalBoundaryMarks hD hNE hFG := by
    exact nielsenBoundaryMarkSaturation_pair_image hD hNE w hwD hwN _ v
      ⟨b,⟨nielsenCyclicVertex_marked hD hNE hFG J hv (i+1),hsub hbE⟩,rfl⟩
  have hfa:J.IsVertexPoint (Polygon.discPolygonKleinPlane (f a)):=(hv _).mpr ⟨f a,hfaMark,rfl⟩
  have hfb:J.IsVertexPoint (Polygon.discPolygonKleinPlane (f b)):=(hv _).mpr ⟨f b,hfbMark,rfl⟩
  have hab:a≠b := by
    intro he
    apply J.adjacent_ne i
    rw [←nielsenCyclicVertex_plane hD hNE hFG J hv i,
      ←nielsenCyclicVertex_plane hD hNE hFG J hv (i+1)]
    exact congrArg Polygon.discPolygonKleinPlane he
  have hab':Polygon.discPolygonKleinPlane (f a)≠Polygon.discPolygonKleinPlane (f b):=
    Polygon.discPolygonKleinPlane_injective.ne (f.injective.ne hab)
  have heC:C=Hyperbolic.closedModelDiscHSegment (f a) (f b) :=
    (P.compactifiedAction k).image_closedModelDiscHSegment a b
  have hplane:Polygon.discPolygonKleinPlane '' C=segment ℝ (Polygon.discPolygonKleinPlane (f a)) (Polygon.discPolygonKleinPlane (f b)) := by
    let e:=LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm
    rw [heC]
    calc
      _=e '' (Hyperbolic.closedKleinCoordinate '' Hyperbolic.closedModelDiscHSegment (f a) (f b)) := by rw [image_image];rfl
      _=e '' segment ℝ (Hyperbolic.closedKleinCoordinate (f a)) (Hyperbolic.closedKleinCoordinate (f b)) := by
        rw [Hyperbolic.closedKlein_image_closedModelDiscHSegment]
      _=_:=image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  have hplaneSub:segment ℝ (Polygon.discPolygonKleinPlane (f a)) (Polygon.discPolygonKleinPlane (f b))⊆J.carrier := by
    rw [←hplane,hc]
    rintro y ⟨p,hp,rfl⟩
    exact ⟨p,mem_iUnion.mpr ⟨Sum.inl v.pair,hC hp⟩,rfl⟩
  have hno:∀p∈openSegment ℝ (Polygon.discPolygonKleinPlane (f a)) (Polygon.discPolygonKleinPlane (f b)),¬J.IsVertexPoint p := by
    intro p hp hpV
    have hpSeg:=openSegment_subset_segment ℝ _ _ hp
    rw [←hplane] at hpSeg
    obtain ⟨x,hx,hxp⟩:=hpSeg
    obtain ⟨y,hym,hyp⟩:=(hv p).mp hpV
    have hyx:y=x:=Polygon.discPolygonKleinPlane_injective (hyp.trans hxp.symm)
    subst y
    rcases hmark x hx hym with he|he
    · have heq:p=Polygon.discPolygonKleinPlane (f a):=hxp.symm.trans (congrArg Polygon.discPolygonKleinPlane he)
      rw [heq] at hp
      exact hab' (left_mem_openSegment_iff.mp hp)
    · have heq:p=Polygon.discPolygonKleinPlane (f b):=hxp.symm.trans (congrArg Polygon.discPolygonKleinPlane he)
      rw [heq] at hp
      exact hab' (right_mem_openSegment_iff.mp hp)
  obtain ⟨j,hj⟩:=nielsen_segment_eq_cyclic_edge J _ _ hab' hfa hfb hplaneSub hno
  have hCj:C=nielsenCyclicEdge hD hNE hFG J hv j := by
    apply Polygon.discPolygonKleinPlane_injective.image_injective
    rw [hplane,nielsenCyclicEdge_plane,hj]
  exact ⟨j,hCj,hCj ▸ hC⟩


def nielsenCyclicSideTag
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : NielsenBoundarySide hD hNE:=
  Classical.choose (nielsen_cyclic_edge_unique_tag hD hNE hFG hfin w hwD hwN J hc hv i)

theorem nielsenCyclicSideTag_spec
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) :
    nielsenCyclicEdge hD hNE hFG J hv i⊆(nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv i).carrier := by
  have h: J.edgeSegment i⊆(nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv i).planeCarrier:=
    (Classical.choose_spec (nielsen_cyclic_edge_unique_tag hD hNE hFG hfin w hwD hwN J hc hv i)).1
  intro p hp
  apply Polygon.discPolygonKleinPlane_injective.mem_set_image.mp
  apply h
  rw [←nielsenCyclicEdge_plane hD hNE hFG J hv i]
  exact mem_image_of_mem _ hp

theorem nielsenCyclicSideTag_eq_of_subset
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) (s:NielsenBoundarySide hD hNE)
    (hs:nielsenCyclicEdge hD hNE hFG J hv i⊆s.carrier) :
    nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv i=s := by
  apply Eq.symm
  apply (Classical.choose_spec (nielsen_cyclic_edge_unique_tag hD hNE hFG hfin w hwD hwN J hc hv i)).2
  rw [←nielsenCyclicEdge_plane hD hNE hFG J hv i]
  exact image_mono hs

theorem nielsenCyclicEdge_injective
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG) :
    Function.Injective (nielsenCyclicEdge hD hNE hFG J hv) := by
  intro i j he
  have hE:J.edgeSegment i=J.edgeSegment j := by
    rw [←nielsenCyclicEdge_plane hD hNE hFG J hv i,←nielsenCyclicEdge_plane hD hNE hFG J hv j,he]
  by_contra hne
  let x:=midpoint ℝ (J.vertex i) (J.vertex (i+1))
  have hx:x∈J.edgeSegment i:=midpoint_mem_segment _ _
  rcases J.edgeSegment_inter_subset_endpoints hne ⟨hx,hE ▸ hx⟩ with h|h
  · exact J.adjacent_ne i ((midpoint_eq_left_iff ℝ).mp h)
  · exact J.adjacent_ne i ((midpoint_eq_right_iff ℝ).mp h)

theorem nielsenCyclicSideTag_paired_unique_image
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) (v:NielsenRefinedSide hD hNE)
    (htag:nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv i=Sum.inl v) :
    ∃!j:ZMod J.n,j≠i ∧
      nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv j=Sum.inl v.pair ∧
      (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ''
        nielsenCyclicEdge hD hNE hFG J hv i=nielsenCyclicEdge hD hNE hFG J hv j := by
  have hs:nielsenCyclicEdge hD hNE hFG J hv i⊆v.carrier := by
    have h:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv i
    rw [htag] at h
    exact h
  obtain ⟨j,hj,hjSub⟩:=nielsenCyclicEdge_paired_image hD hNE hFG w hwD hwN J hc hv i v hs
  have hjTag:nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv j=Sum.inl v.pair :=
    nielsenCyclicSideTag_eq_of_subset hD hNE hFG hfin w hwD hwN J hc hv j (Sum.inl v.pair) hjSub
  have hji:j≠i := by
    intro he
    subst j
    exact v.pair_ne_self (Sum.inl.inj (hjTag.symm.trans htag))
  refine ⟨j,⟨hji,hjTag,hj⟩,?_⟩
  rintro k ⟨_hki,_hkTag,hk⟩
  exact nielsenCyclicEdge_injective hD hNE hFG J hv (hk.symm.trans hj)


theorem nielsen_paired_subsegment_reverse_positive
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    {hNE:DiscreteGroups.IsNonElementary H} (v:NielsenRefinedSide hD hNE)
    (p q a b:𝕔𝔻) (hpq:p≠q) (hab:a≠b)
    (hm:(P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ''
      Hyperbolic.closedModelDiscHSegment p q=Hyperbolic.closedModelDiscHSegment a b)
    (ht:Hyperbolic.closedModelDiscHSegment a b⊆v.pair.carrier)
    (w:P.domain.carrier) (hw:w∈D)
    (hleft:0<OriginalOrientation.signedArea
      (Hyperbolic.closedKleinCoordinate p)
      (Hyperbolic.closedKleinCoordinate q) (P.kleinCoordinate w))
    (hleft':0<OriginalOrientation.signedArea
      (Hyperbolic.closedKleinCoordinate a)
      (Hyperbolic.closedKleinCoordinate b) (P.kleinCoordinate w)) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap p=b ∧
      (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap q=a := by
  let g:=(fuchsianSideElement hD v.val.val.1)⁻¹
  let f:=(P.compactifiedAction g).closedMap
  have he:({f p,f q}:Set 𝕔𝔻)={a,b}:=
    Hyperbolic.ClosedDiscIsometry.closed_segment_image_endpoints (P.compactifiedAction g) p q a b hm
  have hpa:a∈fuchsianSideClosedModel v.pair.val.val.1:=
    v.pair.val.carrier_subset_original (ht (Polygon.closedModelDiscHSegment_left_mem a b)).1
  have hpb:b∈fuchsianSideClosedModel v.pair.val.val.1:=
    v.pair.val.carrier_subset_original (ht (Polygon.closedModelDiscHSegment_right_mem a b)).1
  have hgo:g•w∈fuchsianSideElement hD v.pair.val.val.1 • D := by
    change g•w∈fuchsianSideElement hD v.val.pair.val.1 • D
    rw [v.val.pair_element]
    exact mem_smul_set.mpr ⟨w,hw,rfl⟩
  have hnegative:=OriginalOrientation.original_side_opposite_signedArea hD v.pair.val.val.1
    a b hab hpa hpb w (g•w) hw hgo hleft'
  have hpositive:=(OriginalOrientation.compactified_signedArea_pos_iff P g p q
    (Hyperbolic.discToClosedModel (P.finiteCoordinate w))).mpr hleft
  rw [P.compactifiedAction_finite,Hyperbolic.closedKleinCoordinate_disc_inclusion] at hpositive
  have hpmap:f p=a∨f p=b := by
    have hh:f p∈({a,b}:Set 𝕔𝔻):=he ▸ (by simp)
    exact hh
  have hqmap:f q=a∨f q=b := by
    have hh:f q∈({a,b}:Set 𝕔𝔻):=he ▸ (by simp)
    exact hh
  change OriginalOrientation.signedArea
    (Hyperbolic.closedKleinCoordinate (f p))
    (Hyperbolic.closedKleinCoordinate (f q))
    (P.kleinCoordinate (g•w))>0 at hpositive
  rcases hpmap with hp|hp
  · rcases hqmap with hq|hq
    · exact False.elim (hpq (f.injective (hp.trans hq.symm)))
    · rw [hp,hq] at hpositive
      exact False.elim (hnegative.not_gt hpositive)
  · refine ⟨hp,?_⟩
    rcases hqmap with hq|hq
    · exact hq
    · exact False.elim (hpq (f.injective (hp.trans hq.symm)))

theorem nielsen_paired_subsegment_reverse
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    {hNE:DiscreteGroups.IsNonElementary H} (v:NielsenRefinedSide hD hNE)
    (p q a b:𝕔𝔻) (hpq:p≠q) (hab:a≠b)
    (hm:(P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ''
      Hyperbolic.closedModelDiscHSegment p q=Hyperbolic.closedModelDiscHSegment a b)
    (ht:Hyperbolic.closedModelDiscHSegment a b⊆v.pair.carrier)
    (w:P.domain.carrier) (hw:w∈D)
    (htr:0<OriginalOrientation.signedArea
      (Hyperbolic.closedKleinCoordinate p)
      (Hyperbolic.closedKleinCoordinate q) (P.kleinCoordinate w)*
      OriginalOrientation.signedArea
        (Hyperbolic.closedKleinCoordinate a)
        (Hyperbolic.closedKleinCoordinate b) (P.kleinCoordinate w)) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap p=b ∧
      (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap q=a := by
  rcases mul_pos_iff.mp htr with h|h
  · exact nielsen_paired_subsegment_reverse_positive hD v p q a b hpq hab hm ht w hw h.1 h.2
  · have hm':(P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ''
        Hyperbolic.closedModelDiscHSegment q p=Hyperbolic.closedModelDiscHSegment b a := by
      rw [Hyperbolic.closedModelDiscHSegment_comm q p,Hyperbolic.closedModelDiscHSegment_comm b a]
      exact hm
    have ht':Hyperbolic.closedModelDiscHSegment b a⊆v.pair.carrier:=by rwa [Hyperbolic.closedModelDiscHSegment_comm b a]
    have h1:0<OriginalOrientation.signedArea
        (Hyperbolic.closedKleinCoordinate q)
        (Hyperbolic.closedKleinCoordinate p) (P.kleinCoordinate w) := by
      rw [OriginalOrientation.signedArea_swap]
      exact neg_pos.mpr h.1
    have h2:0<OriginalOrientation.signedArea
        (Hyperbolic.closedKleinCoordinate b)
        (Hyperbolic.closedKleinCoordinate a) (P.kleinCoordinate w) := by
      rw [OriginalOrientation.signedArea_swap]
      exact neg_pos.mpr h.2
    have hh:=nielsen_paired_subsegment_reverse_positive hD v q p b a hpq.symm hab.symm hm' ht' w hw h1 h2
    exact ⟨hh.2,hh.1⟩


theorem nielsenCyclicVertex_adjacent_ne
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i:ZMod J.n) : nielsenCyclicVertex hD hNE hFG J hv i≠nielsenCyclicVertex hD hNE hFG J hv (i+1) := by
  intro he
  apply J.adjacent_ne i
  rw [←nielsenCyclicVertex_plane hD hNE hFG J hv i,←nielsenCyclicVertex_plane hD hNE hFG J hv (i+1),he]

theorem nielsen_cyclic_signedArea
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i j:ZMod J.n) :
    0<OriginalOrientation.signedArea
      (Hyperbolic.closedKleinCoordinate
        (nielsenCyclicVertex hD hNE hFG J hv i))
      (Hyperbolic.closedKleinCoordinate (nielsenCyclicVertex hD hNE hFG J hv (i+1))) (P.kleinCoordinate w)*
      OriginalOrientation.signedArea
        (Hyperbolic.closedKleinCoordinate
          (nielsenCyclicVertex hD hNE hFG J hv j))
      (Hyperbolic.closedKleinCoordinate (nielsenCyclicVertex hD hNE hFG J hv (j+1))) (P.kleinCoordinate w) := by
  let U:=P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE)
  let E:=LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  have hUc:Convex ℝ U := by
    have h:=(Hyperbolic.discHConvex_iff_klein_convex _).mp (nielsenCore_inter_native_convex hD hNE)
    change Convex ℝ (P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE))
    simpa only [image_image,UnitDiscFuchsianGroup.kleinCoordinate] using h
  have hUo:IsOpen U:=P.kleinCoordinate_isOpenEmbedding.isOpenMap _
    (hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE))
  have hUw:P.kleinCoordinate w∈U:=⟨w,⟨hwD,hwN⟩,rfl⟩
  have hfront:frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))=frontier U := by
    change frontier (closure U)=frontier U
    rw [frontier,frontier,closure_closure,hUc.interior_closure_eq_interior_of_nonempty_interior
      (hUo.interior_eq.symm ▸ ⟨P.kleinCoordinate w,hUw⟩)]
  have hJ:E '' J.carrier=frontier U := by
    have hJ':E '' J.carrier=frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
      rw [hc,image_image]
      have hcomp:(fun p:𝕔𝔻 => E (Polygon.discPolygonKleinPlane p))=Hyperbolic.closedKleinCoordinate := by
        funext p
        exact E.apply_symm_apply _
      rw [hcomp,image_iUnion]
      unfold NielsenBoundarySide
      rw [iUnion_sum]
      exact (nielsenCore_boundary_eq_positive_carriers hD hNE hFG hfin w hwD hwN).symm
    exact hJ'.trans hfront
  have hpoint (k:ZMod J.n):E (J.vertex k)=Hyperbolic.closedKleinCoordinate (nielsenCyclicVertex hD hNE hFG J hv k) := by
    rw [←nielsenCyclicVertex_plane hD hNE hFG J hv k]
    exact E.apply_symm_apply _
  have hs:=OriginalOrientation.polygonalCircle_convex_signedArea J hUc hUo hJ (P.kleinCoordinate w) hUw i j
  rwa [hpoint i,hpoint (i+1),hpoint j,hpoint (j+1)] at hs

theorem nielsen_cyclic_paired_reverse
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
    (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
    (i j:ZMod J.n) (v:NielsenRefinedSide hD hNE)
    (hm:(P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ''
      nielsenCyclicEdge hD hNE hFG J hv i=nielsenCyclicEdge hD hNE hFG J hv j)
    (ht:nielsenCyclicEdge hD hNE hFG J hv j⊆v.pair.carrier) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap
      (nielsenCyclicVertex hD hNE hFG J hv i)=nielsenCyclicVertex hD hNE hFG J hv (j+1) ∧
      (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap
      (nielsenCyclicVertex hD hNE hFG J hv (i+1))=nielsenCyclicVertex hD hNE hFG J hv j :=
  nielsen_paired_subsegment_reverse hD v _ _ _ _
    (nielsenCyclicVertex_adjacent_ne hD hNE hFG J hv i) (nielsenCyclicVertex_adjacent_ne hD hNE hFG J hv j)
    hm ht w hwD (nielsen_cyclic_signedArea hD hNE hFG hfin w hwD hwN J hc hv i j)


section NielsenCyclicPairInvolution
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "tag" => nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv

/-- The actual old side pairing, extended by the identity on genuine Nielsen boundary edges. -/
def nielsenCyclicPairIndex (i:ZMod J.n) : ZMod J.n := by
  classical
  exact if h:∃v:NielsenRefinedSide hD hNE,tag i=Sum.inl v then
    Classical.choose (nielsenCyclicSideTag_paired_unique_image hD hNE hFG hfin w hwD hwN
      J hc hv i (Classical.choose h) (Classical.choose_spec h)) else i

local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicPairIndex_paired (i:ZMod J.n) (v:NielsenRefinedSide hD hNE)
    (hi:tag i=Sum.inl v) :
    pairIndex i≠i ∧ tag (pairIndex i)=Sum.inl v.pair ∧
      (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap '' edge i=
        edge (pairIndex i) := by
  classical
  have hex:∃v:NielsenRefinedSide hD hNE,tag i=Sum.inl v:=⟨v,hi⟩
  have he:Classical.choose hex=v:=Sum.inl.inj ((Classical.choose_spec hex).symm.trans hi)
  unfold nielsenCyclicPairIndex
  rw [dite_eq_left hex]
  simpa only [he] using
    (Classical.choose_spec (nielsenCyclicSideTag_paired_unique_image hD hNE hFG hfin w hwD hwN
      J hc hv i (Classical.choose hex) (Classical.choose_spec hex))).1

theorem nielsenCyclicPairIndex_unpaired (i:ZMod J.n) (v:NielsenUnpairedSide P hNE D)
    (hi:tag i=Sum.inr v) : pairIndex i=i := by
  classical
  have hn:¬∃v:NielsenRefinedSide hD hNE,tag i=Sum.inl v:=by
    rintro ⟨v,hv⟩
    cases hv.symm.trans hi
  exact dite_eq_right hn

theorem nielsenCyclicPairIndex_fixed_iff (i:ZMod J.n) :
    pairIndex i=i ↔ ∃v:NielsenUnpairedSide P hNE D,tag i=Sum.inr v := by
  cases hi:tag i with
  | inl v =>
    refine ⟨fun he=>False.elim ((nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv i v hi).1 he),?_⟩
    rintro ⟨v',hv'⟩
    cases hv'
  | inr v => exact ⟨fun _=>⟨v,rfl⟩,fun _=>nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv i v hi⟩

private theorem nielsenRefinedSide_pair_image_inverse (v:NielsenRefinedSide hD hNE) (S:Set 𝕔𝔻) :
    (P.compactifiedAction (fuchsianSideElement hD v.pair.val.val.1)⁻¹).closedMap ''
      ((P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap '' S)=S := by
  have he:fuchsianSideElement hD v.pair.val.val.1=(fuchsianSideElement hD v.val.val.1)⁻¹ :=
    v.val.pair_element
  rw [he,inv_inv,image_image]
  have hcomp:(fun x:𝕔𝔻=>(P.compactifiedAction (fuchsianSideElement hD v.val.val.1)).closedMap
      ((P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap x))=id := by
    funext x
    rw [←nielsen_compactifiedAction_mul,mul_inv_cancel,nielsen_compactifiedAction_one]
    rfl
  rw [hcomp,image_id]

theorem nielsenCyclicPairIndex_involutive : Function.Involutive pairIndex := by
  intro i
  cases hi:tag i with
  | inr v =>
    have hp:=nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv i v hi
    exact (congrArg pairIndex hp).trans hp
  | inl v =>
    have h1:=nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv i v hi
    have h2:=nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv (pairIndex i) v.pair h1.2.1
    apply nielsenCyclicEdge_injective hD hNE hFG J hv
    rw [←h2.2.2,←h1.2.2]
    exact nielsenRefinedSide_pair_image_inverse hD hNE v (edge i)

/-- This is the actual finite involution, with fixed edges exactly the unpaired Nielsen boundary. -/
def nielsenCyclicPairEquiv : Equiv.Perm (ZMod J.n) :=
  (nielsenCyclicPairIndex_involutive hD hNE hFG hfin w hwD hwN J hc hv).toPerm

theorem nielsenCyclicPairIndex_endpoint_reverse (i:ZMod J.n) (v:NielsenRefinedSide hD hNE)
    (hi:tag i=Sum.inl v) :
    (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap (vertex i)=vertex (pairIndex i+1) ∧
      (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap (vertex (i+1))=vertex (pairIndex i) := by
  have h:=nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv i v hi
  apply nielsen_cyclic_paired_reverse hD hNE hFG hfin w hwD hwN J hc hv i (pairIndex i) v h.2.2
  have hs:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv (pairIndex i)
  rwa [h.2.1] at hs

end NielsenCyclicPairInvolution


section NielsenCyclicBoundaryNext
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv

/-- Follow a corner through its actual old pairing, then along the positive polygon boundary. -/
def nielsenCyclicCornerEquiv : Equiv.Perm (ZMod J.n) :=
  (nielsenCyclicPairEquiv hD hNE hFG hfin w hwD hwN J hc hv).trans (Equiv.addRight 1)

local notation "σ" => nielsenCyclicCornerEquiv hD hNE hFG hfin w hwD hwN J hc hv

/-- Exactly the genuine unpaired boundary edges, rather than all cyclic side indices. -/
def NielsenCyclicBoundaryIndex := {i:ZMod J.n // pairIndex i=i}
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundary_return_exists (x:B) :
    ∃k:ℕ,0<k ∧ pairIndex ((σ^k) x.val)=(σ^k) x.val := by
  obtain ⟨k,hk,_hle,he⟩:=(Equiv.Perm.SameCycle.refl σ x.val).exists_pow_eq''
  refine ⟨k,hk,?_⟩
  rw [he]
  exact x.property

def nielsenCyclicBoundaryReturnTime (x:B) : ℕ :=
  Nat.find (nielsenCyclicBoundary_return_exists hD hNE hFG hfin w hwD hwN J hc hv x)
local notation "τ" => nielsenCyclicBoundaryReturnTime hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryReturnTime_spec (x:B) :
    0<τ x ∧ pairIndex ((σ^(τ x)) x.val)=(σ^(τ x)) x.val :=
  Nat.find_spec (nielsenCyclicBoundary_return_exists hD hNE hFG hfin w hwD hwN J hc hv x)

theorem nielsenCyclicBoundaryReturnTime_le (x:B) (k:ℕ) (hk:0<k)
    (hmem:pairIndex ((σ^k) x.val)=(σ^k) x.val) : τ x≤k :=
  Nat.find_min' (nielsenCyclicBoundary_return_exists hD hNE hFG hfin w hwD hwN J hc hv x) ⟨hk,hmem⟩

/-- The first actual unpaired edge encountered after traversing the glued corners. -/
def nielsenCyclicBoundaryNext (x:B) : B :=
  ⟨(σ^(τ x)) x.val,(nielsenCyclicBoundaryReturnTime_spec hD hNE hFG hfin w hwD hwN J hc hv x).2⟩
local notation "R" => nielsenCyclicBoundaryNext hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryNext_injective : Function.Injective R := by
  have aux (x y:B) (hxy:R x=R y) (hle:τ x≤τ y) : x=y := by
    let d:=τ y-τ x
    have hd:τ x+d=τ y:=Nat.add_sub_of_le hle
    have he:(σ^(τ x)) x.val=(σ^(τ y)) y.val:=congrArg Subtype.val hxy
    rw [←hd,pow_add,Equiv.Perm.mul_apply] at he
    have h0:x.val=(σ^d) y.val:=(σ^(τ x)).injective he
    by_cases hdz:d=0
    · apply Subtype.ext
      simpa only [hdz,pow_zero,Equiv.Perm.one_apply] using h0
    · have hmem:pairIndex ((σ^d) y.val)=(σ^d) y.val:=h0 ▸ x.property
      have hmin:=nielsenCyclicBoundaryReturnTime_le hD hNE hFG hfin w hwD hwN J hc hv y d
        (Nat.pos_of_ne_zero hdz) hmem
      have hpos:0<τ x:=(nielsenCyclicBoundaryReturnTime_spec hD hNE hFG hfin w hwD hwN J hc hv x).1
      omega
  intro x y hxy
  rcases le_total (τ x) (τ y) with h|h
  · exact aux x y hxy h
  · exact (aux y x hxy.symm h).symm

/-- The boundary continuation is a permutation, including a boundary component with one edge. -/
def nielsenCyclicBoundaryEquiv : Equiv.Perm B := by
  letI : Finite B := by unfold NielsenCyclicBoundaryIndex; infer_instance
  exact Equiv.ofBijective R ⟨nielsenCyclicBoundaryNext_injective hD hNE hFG hfin w hwD hwN J hc hv,
    Finite.surjective_of_injective (nielsenCyclicBoundaryNext_injective hD hNE hFG hfin w hwD hwN J hc hv)⟩

theorem nielsenCyclicBoundaryNext_sameCycle (x:B) : Equiv.Perm.SameCycle σ x.val (R x).val := by
  refine ⟨(τ x:ℤ),?_⟩
  rw [zpow_natCast]
  rfl

end NielsenCyclicBoundaryNext


section NielsenCyclicBoundaryCycles
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "σ" => nielsenCyclicCornerEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "τ" => nielsenCyclicBoundaryReturnTime hD hNE hFG hfin w hwD hwN J hc hv
local notation "R" => nielsenCyclicBoundaryNext hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryEquiv_nat_pow_sameCycle (x:B) (m:ℕ) :
    Equiv.Perm.SameCycle σ x.val ((ρ^m) x).val := by
  induction m with
  | zero => exact Equiv.Perm.SameCycle.refl _ _
  | succ m ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact ih.trans (nielsenCyclicBoundaryNext_sameCycle hD hNE hFG hfin w hwD hwN J hc hv ((ρ^m) x))

theorem nielsenCyclicBoundaryEquiv_sameCycle_iff (x y:B) :
    Equiv.Perm.SameCycle ρ x y ↔ Equiv.Perm.SameCycle σ x.val y.val := by
  let : Finite B := by unfold NielsenCyclicBoundaryIndex; infer_instance
  constructor
  · intro h
    obtain ⟨m,hm⟩:=h.exists_nat_pow_eq
    have he:=nielsenCyclicBoundaryEquiv_nat_pow_sameCycle hD hNE hFG hfin w hwD hwN J hc hv x m
    rwa [hm] at he
  · intro h
    obtain ⟨m,hm⟩:=h.exists_nat_pow_eq
    have aux : ∀n:ℕ,∀a b:B,(σ^n) a.val=b.val→Equiv.Perm.SameCycle ρ a b := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro a b he
        by_cases hn:n=0
        · have hab:a=b:=Subtype.ext (by simpa only [hn,pow_zero,Equiv.Perm.one_apply] using he)
          exact hab.sameCycle _
        · have hnpos:0<n:=Nat.pos_of_ne_zero hn
          have hmem:pairIndex ((σ^n) a.val)=(σ^n) a.val:=by rw [he];exact b.property
          have hle:τ a≤n:=nielsenCyclicBoundaryReturnTime_le hD hNE hFG hfin w hwD hwN J hc hv a n hnpos hmem
          have hpos:0<τ a:=(nielsenCyclicBoundaryReturnTime_spec hD hNE hFG hfin w hwD hwN J hc hv a).1
          have hlt:n-τ a<n:=Nat.sub_lt hnpos hpos
          have he':(σ^(n-τ a)) (R a).val=b.val := by
            change (σ^(n-τ a)) ((σ^(τ a)) a.val)=b.val
            rw [←Equiv.Perm.mul_apply,←pow_add,Nat.sub_add_cancel hle]
            exact he
          have htail:=ih (n-τ a) hlt (R a) b he'
          have hfirst:Equiv.Perm.SameCycle ρ a (R a):=⟨1,by rw [zpow_one];rfl⟩
          exact hfirst.trans htail
    exact aux m x y hm

/-- Actual boundary components as cycles of the genuine partial-pairing continuation.
Singleton cycles are retained. -/
def NielsenCyclicBoundaryClasses := Quotient (Equiv.Perm.SameCycle.setoid ρ)

end NielsenCyclicBoundaryCycles


section NielsenBoundaryCapLists
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv

/-- The exact positive boundary cycle of a genuine boundary component. -/
def nielsenBoundaryCapCycle (c:C) : Cycle B := Function.periodicOrbit ρ c.out

/-- A cyclically ordered list for the actual cap, before reversing its traversal. -/
def nielsenBoundaryCapList (c:C) : List B :=
  (nielsenBoundaryCapCycle hD hNE hFG hfin w hwD hwN J hc hv c).out
local notation "capList" => nielsenBoundaryCapList hD hNE hFG hfin w hwD hwN J hc hv
local notation "capCycle" => nielsenBoundaryCapCycle hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenBoundaryCapList_coe (c:C) : (capList c:Cycle B)=capCycle c :=
  Quotient.out_eq _

theorem nielsenBoundaryCapList_nodup (c:C) : (capList c).Nodup := by
  rw [←Cycle.nodup_coe_iff,nielsenBoundaryCapList_coe]
  exact Function.nodup_periodicOrbit

theorem nielsenBoundaryCapList_ne_nil (c:C) : capList c≠[] := by
  let : Finite B := by unfold NielsenCyclicBoundaryIndex;infer_instance
  intro he
  have hp:=(Equiv.injective ρ).mem_periodicPts c.out
  have hn:capCycle c≠Cycle.nil:=fun h=>(Function.periodicOrbit_eq_nil_iff_not_periodic_pt.mp h) hp
  apply hn
  rw [←nielsenBoundaryCapList_coe,he]
  rfl

theorem nielsenBoundaryCapList_mem_iff (c:C) (x:B) :
    x∈capList c ↔ (Quotient.mk (Equiv.Perm.SameCycle.setoid ρ) x:C)=c := by
  let : Finite B := by unfold NielsenCyclicBoundaryIndex;infer_instance
  have hp:=(Equiv.injective ρ).mem_periodicPts c.out
  rw [←Cycle.mem_coe_iff,nielsenBoundaryCapList_coe]
  change x∈Function.periodicOrbit ρ c.out ↔ _
  rw [Function.mem_periodicOrbit_iff hp]
  constructor
  · rintro ⟨k,hk⟩
    have hsame:Equiv.Perm.SameCycle ρ c.out x:=⟨(k:ℤ),by simpa only [zpow_natCast,Equiv.Perm.coe_pow] using hk⟩
    exact (Quotient.sound hsame.symm).trans (Quotient.out_eq c)
  · intro he
    have hsame:Equiv.Perm.SameCycle ρ c.out x:=Quotient.exact ((Quotient.out_eq c).trans he.symm)
    obtain ⟨k,hk⟩:=hsame.exists_nat_pow_eq
    exact ⟨k,by simpa only [Equiv.Perm.coe_pow] using hk⟩

theorem nielsenBoundaryCapList_unique (x:B) : ∃!c:C,x∈capList c := by
  refine ⟨Quotient.mk _ x,(nielsenBoundaryCapList_mem_iff hD hNE hFG hfin w hwD hwN J hc hv _ x).mpr rfl,?_⟩
  intro c hcm
  exact ((nielsenBoundaryCapList_mem_iff hD hNE hFG hfin w hwD hwN J hc hv c x).mp hcm).symm

theorem nielsenBoundaryCapCycle_chain (c:C) :
    (capCycle c).Chain (fun x y:B=>ρ x=y) := by
  apply (Function.periodicOrbit_chain _).mpr
  intro k _hk
  rw [Function.iterate_succ_apply']

end NielsenBoundaryCapLists


section NielsenCapOccurrences
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv

instance nielsenCyclicBoundaryIndexFintype : Fintype B := by
  let : Finite B := by unfold NielsenCyclicBoundaryIndex;infer_instance
  exact Fintype.ofFinite B

instance nielsenCyclicBoundaryClassesFintype : Fintype C := by
  unfold NielsenCyclicBoundaryClasses
  exact Fintype.ofFinite _

/-- Occurrences on the original actual polygon, plus the genuine cap copy of each unpaired edge. -/
def NielsenCapOccurrence := ZMod J.n ⊕ B
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv

instance nielsenCapOccurrenceFintype : Fintype O :=
  inferInstanceAs (Fintype (ZMod J.n ⊕ B))

/-- Original paired edges keep their original partner; an unpaired edge is paired only with its cap copy. -/
def nielsenCapOccurrencePair : O→O
  | .inl i=>if hi:pairIndex i=i then .inr ⟨i,hi⟩ else .inl (pairIndex i)
  | .inr b=>.inl b.val
local notation "p" => nielsenCapOccurrencePair hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCapOccurrencePair_involutive : Function.Involutive p := by
  intro x
  have hinv:=nielsenCyclicPairIndex_involutive hD hNE hFG hfin w hwD hwN J hc hv
  cases x with
  | inl i =>
    by_cases hi:pairIndex i=i
    · simp only [nielsenCapOccurrencePair,dite_eq_left hi]
    · have hn:¬pairIndex (pairIndex i)=pairIndex i:=by rw [hinv i];exact Ne.symm hi
      rw [nielsenCapOccurrencePair,dite_eq_right hi,nielsenCapOccurrencePair,dite_eq_right hn,hinv i]
  | inr b =>
    rw [nielsenCapOccurrencePair,nielsenCapOccurrencePair,dite_eq_left b.property]
    congr 1

theorem nielsenCapOccurrencePair_ne_self (x:O) : p x≠x := by
  cases x with
  | inl i =>
    by_cases hi:pairIndex i=i
    · rw [nielsenCapOccurrencePair,dite_eq_left hi]
      intro he
      cases he
    · rw [nielsenCapOccurrencePair,dite_eq_right hi]
      intro he
      exact hi (Sum.inl.inj he)
  | inr b => exact Sum.inl_ne_inr

/-- A finite numerical index for the actual occurrences, without changing the original face order. -/
def nielsenCapOccurrenceIndex : O≃Fin (Fintype.card O) := Fintype.equivFin O
local notation "eO" => nielsenCapOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCapFinPair (i:Fin (Fintype.card O)) : Fin (Fintype.card O) := eO (p ((eO).symm i))
local notation "pF" => nielsenCapFinPair hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCapFinPair_involutive : Function.Involutive pF := by
  intro i
  unfold nielsenCapFinPair
  rw [Equiv.symm_apply_apply,nielsenCapOccurrencePair_involutive hD hNE hFG hfin w hwD hwN J hc hv,
    Equiv.apply_symm_apply]

theorem nielsenCapFinPair_ne_self (i:Fin (Fintype.card O)) : pF i≠i := by
  intro he
  apply nielsenCapOccurrencePair_ne_self hD hNE hFG hfin w hwD hwN J hc hv ((eO).symm i)
  have h:=congrArg (eO).symm he
  simpa only [nielsenCapFinPair,Equiv.symm_apply_apply] using h

/-- Every genuine occurrence has exactly one signed edge label of the capped word. -/
def nielsenCapDartEquiv : O≃LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart
    (Surfaces.CyclicSurface.InvolutionPositive pF) :=
  (eO).trans (Surfaces.CyclicSurface.freeInvolutionDartEquiv pF
    (nielsenCapFinPair_involutive hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCapFinPair_ne_self hD hNE hFG hfin w hwD hwN J hc hv))

theorem nielsenCapDartEquiv_pair (x:O) :
    nielsenCapDartEquiv hD hNE hFG hfin w hwD hwN J hc hv (p x)=
      (nielsenCapDartEquiv hD hNE hFG hfin w hwD hwN J hc hv x).flip := by
  change Surfaces.CyclicSurface.freeInvolutionDartEquiv pF
    (nielsenCapFinPair_involutive hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCapFinPair_ne_self hD hNE hFG hfin w hwD hwN J hc hv) (eO (p x))=_
  have hp:eO (p x)=pF (eO x):=by unfold nielsenCapFinPair;rw [Equiv.symm_apply_apply]
  rw [hp]
  exact Surfaces.CyclicSurface.freeInvolutionDartEquiv_pair _ _ _ _

end NielsenCapOccurrences


section NielsenCapFaceOccurrences
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv
local notation "capList" => nielsenBoundaryCapList hD hNE hFG hfin w hwD hwN J hc hv

/-- The original polygon face remains in its original actual cyclic vertex order. -/
def nielsenCapOriginalOccurrences : List O :=
  List.ofFn (fun i:Fin J.n=>(Sum.inl ((ZMod.finEquiv J.n) i):O))
local notation "oldFace" => nielsenCapOriginalOccurrences hD hNE hFG hfin w hwD hwN J hc hv

/-- The cap has the opposite traversal of its genuine boundary cycle. -/
def nielsenCapBoundaryOccurrences (c:C) : List O := (capList c).reverse.map Sum.inr
local notation "capFace" => nielsenCapBoundaryOccurrences hD hNE hFG hfin w hwD hwN J hc hv

/-- One actual polygon face followed by exactly one actual cap for each boundary cycle. -/
def nielsenCapFaceOccurrences : List (List O) :=
  oldFace :: List.ofFn (fun k:Fin (Fintype.card C)=>capFace ((Fintype.equivFin C).symm k))
local notation "faces" => nielsenCapFaceOccurrences hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCapOriginalOccurrences_mem (x:O) :
    x∈oldFace ↔ ∃i:ZMod J.n,x=Sum.inl i := by
  rw [nielsenCapOriginalOccurrences,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨(ZMod.finEquiv J.n) i,hi.symm⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨k,rfl⟩:=(ZMod.finEquiv J.n).surjective i
    exact ⟨k,rfl⟩

theorem nielsenCapBoundaryOccurrences_mem (c:C) (x:O) :
    x∈capFace c ↔ ∃b:B,x=Sum.inr b ∧ b∈capList c := by
  rw [nielsenCapBoundaryOccurrences,List.mem_map]
  constructor
  · rintro ⟨b,hb,hx⟩
    exact ⟨b,hx.symm,List.mem_reverse.mp hb⟩
  · rintro ⟨b,rfl,hb⟩
    exact ⟨b,List.mem_reverse.mpr hb,rfl⟩

theorem nielsenCapOriginalOccurrences_nodup : (oldFace).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  exact (ZMod.finEquiv J.n).injective (Sum.inl.inj hij)

theorem nielsenCapBoundaryOccurrences_nodup (c:C) : (capFace c).Nodup :=
  List.Nodup.map Sum.inr_injective (List.nodup_reverse.mpr
    (nielsenBoundaryCapList_nodup hD hNE hFG hfin w hwD hwN J hc hv c))

theorem nielsenCapOldBoundaryOccurrences_disjoint (c:C) : List.Disjoint oldFace (capFace c) := by
  rw [List.disjoint_left]
  intro x hxOld hxCap
  obtain ⟨i,rfl⟩:=(nielsenCapOriginalOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv x).mp hxOld
  obtain ⟨b,hb,_⟩:=(nielsenCapBoundaryOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv c _).mp hxCap
  cases hb

theorem nielsenCapBoundaryOccurrences_disjoint {c d:C} (hne:c≠d) : List.Disjoint (capFace c) (capFace d) := by
  rw [List.disjoint_left]
  intro x hxc hxd
  obtain ⟨b,rfl,hbc⟩:=(nielsenCapBoundaryOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv c x).mp hxc
  obtain ⟨a,hab,had⟩:=(nielsenCapBoundaryOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv d _).mp hxd
  have hab':b=a:=Sum.inr.inj hab
  subst a
  have hec:Quotient.mk _ b=c:=(nielsenBoundaryCapList_mem_iff hD hNE hFG hfin w hwD hwN J hc hv c b).mp hbc
  have hed:Quotient.mk _ b=d:=(nielsenBoundaryCapList_mem_iff hD hNE hFG hfin w hwD hwN J hc hv d b).mp had
  exact hne (hec.symm.trans hed)

theorem nielsenCapFaceOccurrences_nodup_flatten : ((faces).flatten).Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    rcases List.mem_cons.mp hl with he|hl
    · subst l
      exact nielsenCapOriginalOccurrences_nodup hD hNE hFG hfin w hwD hwN J hc hv
    · obtain ⟨k,rfl⟩:=List.mem_ofFn.mp hl
      exact nielsenCapBoundaryOccurrences_nodup hD hNE hFG hfin w hwD hwN J hc hv _
  · apply List.pairwise_cons.mpr
    constructor
    · intro l hl
      obtain ⟨k,rfl⟩:=List.mem_ofFn.mp hl
      exact nielsenCapOldBoundaryOccurrences_disjoint hD hNE hFG hfin w hwD hwN J hc hv _
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      apply nielsenCapBoundaryOccurrences_disjoint hD hNE hFG hfin w hwD hwN J hc hv
      intro he
      exact (ne_of_lt hij) ((Fintype.equivFin C).symm.injective he)

theorem nielsenCapFaceOccurrences_mem_flatten (x:O) : x∈(faces).flatten := by
  apply List.mem_flatten.mpr
  cases x with
  | inl i =>
    exact ⟨oldFace,List.mem_cons_self, (nielsenCapOriginalOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv _).mpr
      ⟨i,rfl⟩⟩
  | inr b =>
    let c:C:=Quotient.mk _ b
    have hb:b∈capList c:=(nielsenBoundaryCapList_mem_iff hD hNE hFG hfin w hwD hwN J hc hv c b).mpr rfl
    refine ⟨capFace c,List.mem_cons_of_mem _ ?_,?_⟩
    · apply List.mem_ofFn.mpr
      exact ⟨(Fintype.equivFin C) c,by rw [Equiv.symm_apply_apply]⟩
    · exact (nielsenCapBoundaryOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv c _).mpr ⟨b,rfl,hb⟩

theorem nielsenCapFaceOccurrences_ne_nil (l:List O) (hl:l∈faces) : l≠[] := by
  rcases List.mem_cons.mp hl with he|hl
  · subst l
    intro he
    have hh:=congrArg List.length he
    simp only [nielsenCapOriginalOccurrences,List.length_ofFn,List.length_nil] at hh
    have h:=J.three_le
    omega
  · obtain ⟨k,rfl⟩:=List.mem_ofFn.mp hl
    intro he
    have hh:=congrArg List.length he
    simp only [nielsenCapBoundaryOccurrences,List.length_map,List.length_reverse,List.length_nil] at hh
    exact nielsenBoundaryCapList_ne_nil hD hNE hFG hfin w hwD hwN J hc hv
      ((Fintype.equivFin C).symm k) (List.length_eq_zero_iff.mp hh)

end NielsenCapFaceOccurrences


section NielsenCappedPresentation
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv
local notation "facesO" => nielsenCapFaceOccurrences hD hNE hFG hfin w hwD hwN J hc hv
local notation "pF" => nielsenCapFinPair hD hNE hFG hfin w hwD hwN J hc hv

abbrev NielsenCapEdge := Surfaces.CyclicSurface.InvolutionPositive pF
local notation "E" => NielsenCapEdge hD hNE hFG hfin w hwD hwN J hc hv

instance nielsenCapEdgeFintype : Fintype E := by
  classical
  exact inferInstanceAs (Fintype {i:Fin (Fintype.card O) // i<pF i})

def nielsenCapFiniteDartEquiv : O≃SignedDart (Fin (Fintype.card E)) :=
  (nielsenCapDartEquiv hD hNE hFG hfin w hwD hwN J hc hv).trans (SignedDart.mapEquiv (Fintype.equivFin E))
local notation "d" => nielsenCapFiniteDartEquiv hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCapFiniteDartEquiv_pair (x:O) :
    d (nielsenCapOccurrencePair hD hNE hFG hfin w hwD hwN J hc hv x)=(d x).flip := by
  change SignedDart.mapEquiv (Fintype.equivFin E)
    (nielsenCapDartEquiv hD hNE hFG hfin w hwD hwN J hc hv _)=_
  rw [nielsenCapDartEquiv_pair,SignedDart.mapEquiv_flip]
  rfl

/-- The faithful capped presentation: the actual polygon face and one reversed cap per derived boundary cycle. -/
def nielsenCappedPresentation : FiniteCyclicPresentation where
  edgeCount:=Fintype.card E
  faces:=(facesO).map (List.map d)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedPresentation_flatten : (Pcap).faces.flatten=(facesO).flatten.map d := by
  simp only [nielsenCappedPresentation,List.map_flatten]

theorem nielsenCappedPresentation_flatten_nodup : (Pcap).faces.flatten.Nodup := by
  rw [nielsenCappedPresentation_flatten]
  exact List.Nodup.map (Equiv.injective d) (nielsenCapFaceOccurrences_nodup_flatten hD hNE hFG hfin w hwD hwN J hc hv)

theorem nielsenCappedPresentation_flatten_mem (a:(Pcap).Dart) : a∈(Pcap).faces.flatten := by
  obtain ⟨x,rfl⟩:=(Equiv.surjective d) a
  rw [nielsenCappedPresentation_flatten]
  exact List.mem_map.mpr ⟨x,nielsenCapFaceOccurrences_mem_flatten hD hNE hFG hfin w hwD hwN J hc hv x,rfl⟩

theorem nielsenCappedPresentation_flatten_count (a:(Pcap).Dart) : ((Pcap).faces.flatten).count a=1 :=
  List.count_eq_one_of_mem (nielsenCappedPresentation_flatten_nodup hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCappedPresentation_flatten_mem hD hNE hFG hfin w hwD hwN J hc hv a)

private theorem nielsen_list_faces_edge_count {A:Type} [DecidableEq A] (ls:List (List (SignedDart A))) (a:A) :
    ∑i:Fin ls.length,((ls.get i).map edgeOfDart).count a=(ls.flatten.map edgeOfDart).count a := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.length_cons,Fin.sum_univ_succ,List.get_eq_getElem,Fin.val_zero,Fin.val_succ,
      List.getElem_cons_zero,List.getElem_cons_succ,List.flatten_cons,List.map_append,List.count_append]
    exact congrArg (fun n=> (l.map edgeOfDart).count a+n) ih

theorem nielsenCappedPresentation_closed : Surfaces.CyclicSurface.IsClosed
    (Pcap) := by
  intro a
  change (∑i:Fin (Pcap).faces.length,(((Pcap).faces.get i).map edgeOfDart).count a)=2
  rw [nielsen_list_faces_edge_count,Surfaces.CyclicSurface.count_map_signed_edge,
    nielsenCappedPresentation_flatten_count,nielsenCappedPresentation_flatten_count]

private theorem nielsen_list_faces_coefficient {A:Type} [DecidableEq A] (ls:List (List (SignedDart A))) (a:A) :
    ∑i:Fin ls.length,Surfaces.CyclicSurface.wordCoefficient a (ls.get i)=Surfaces.CyclicSurface.wordCoefficient a ls.flatten := by
  induction ls with
  | nil => simp only [List.length_nil,Finset.univ_eq_empty,Finset.sum_empty,List.flatten_nil,Surfaces.CyclicSurface.wordCoefficient_nil]
  | cons l ls ih =>
    simp only [List.length_cons,Fin.sum_univ_succ,List.get_eq_getElem,Fin.val_zero,Fin.val_succ,
      List.getElem_cons_zero,List.getElem_cons_succ,List.flatten_cons,Surfaces.CyclicSurface.wordCoefficient_append]
    exact congrArg (fun n=>Surfaces.CyclicSurface.wordCoefficient a l+n) ih

theorem nielsenCappedPresentation_coherent : Surfaces.CyclicSurface.IsCoherentlyOrientable (Pcap) := by
  refine ⟨fun _=>1,⟨fun _=>Or.inl rfl,?_⟩⟩
  intro a
  simp only [one_mul]
  change (∑i:Fin (Pcap).faces.length,Surfaces.CyclicSurface.wordCoefficient a ((Pcap).faces.get i))=0
  rw [nielsen_list_faces_coefficient,Surfaces.CyclicSurface.wordCoefficient_eq_count_difference,
    nielsenCappedPresentation_flatten_count,nielsenCappedPresentation_flatten_count,sub_self]

theorem nielsenCappedPresentation_boundary_ne_nil (f:(Pcap).Face) : (Pcap).boundary f≠[] := by
  have hf:(Pcap).boundary f∈(Pcap).faces:=List.get_mem _ f
  obtain ⟨l,hl,he⟩:=List.mem_map.mp hf
  intro hn
  have hlen:=congrArg List.length (he.trans hn)
  simp only [List.length_map,List.length_nil] at hlen
  exact nielsenCapFaceOccurrences_ne_nil hD hNE hFG hfin w hwD hwN J hc hv l hl (List.length_eq_zero_iff.mp hlen)

theorem nielsenCappedPresentation_faces_length : (Pcap).faces.length=1+
    Fintype.card (NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv) := by
  simp only [nielsenCappedPresentation,List.length_map,nielsenCapFaceOccurrences,List.length_cons,List.length_ofFn,Nat.add_comm]

private theorem nielsenCappedPresentation_boundary_disjoint (f g:(Pcap).Face) (hne:f≠g) :
    List.Disjoint ((Pcap).boundary f) ((Pcap).boundary g) := by
  have hp:List.Pairwise List.Disjoint (Pcap).faces:=
    (List.nodup_flatten.mp (nielsenCappedPresentation_flatten_nodup hD hNE hFG hfin w hwD hwN J hc hv)).2
  rcases lt_or_gt_of_ne hne with hlt|hlt
  · exact (List.pairwise_iff_get.mp hp) f g hlt
  · exact ((List.pairwise_iff_get.mp hp) g f hlt).symm

theorem nielsenCappedPresentation_valid : (Pcap).IsSurfaceValid := by
  refine ⟨⟨⟨0,by rw [nielsenCappedPresentation_faces_length];omega⟩⟩,
    nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc hv,?_,?_⟩
  · intro f g hrot
    by_contra hne
    obtain ⟨a,ha⟩:=List.exists_mem_of_ne_nil _ (nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc
      hv f)
    exact List.disjoint_left.mp (nielsenCappedPresentation_boundary_disjoint hD hNE hFG hfin w hwD hwN J hc hv f g hne)
      ha (hrot.mem_iff.mp ha)
  · intro a
    exact Or.inr (nielsenCappedPresentation_closed hD hNE hFG hfin w hwD hwN J hc hv a)

end NielsenCappedPresentation


section NielsenCappedGenus
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv
local notation "d" => nielsenCapFiniteDartEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldFace" => nielsenCapOriginalOccurrences hD hNE hFG hfin w hwD hwN J hc hv
local notation "capFace" => nielsenCapBoundaryOccurrences hD hNE hFG hfin w hwD hwN J hc hv
local notation "capList" => nielsenBoundaryCapList hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCappedOriginalFace : (Pcap).Face :=
  ⟨0,by rw [nielsenCappedPresentation_faces_length];omega⟩
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedPresentation_original_boundary : (Pcap).boundary (f₀)=(oldFace).map d := rfl

theorem nielsenCappedPresentation_other_boundary (f:(Pcap).Face) (hf:f≠f₀) :
    ∃c:C,(Pcap).boundary f=(capFace c).map d := by
  rcases f with ⟨_ | k,hk⟩
  · exact False.elim (hf (Fin.ext rfl))
  · have hk':k<Fintype.card C:=by rw [nielsenCappedPresentation_faces_length] at hk;omega
    refine ⟨(Fintype.equivFin C).symm ⟨k,hk'⟩,?_⟩
    simp only [FiniteCyclicPresentation.boundary,nielsenCappedPresentation,nielsenCapFaceOccurrences,List.map_cons,
      List.get_eq_getElem,List.getElem_cons_succ,List.getElem_map,List.getElem_ofFn]

theorem nielsenCappedPresentation_cap_adjacent (f:(Pcap).Face) (hf:f≠f₀) :
    (Pcap).FaceAdjacent f (f₀) := by
  obtain ⟨c,hcf⟩:=nielsenCappedPresentation_other_boundary hD hNE hFG hfin w hwD hwN J hc hv f hf
  obtain ⟨b,hb⟩:=List.exists_mem_of_ne_nil _ (nielsenBoundaryCapList_ne_nil hD hNE hFG hfin w hwD hwN J hc hv c)
  have hcap:d (Sum.inr b)∈(Pcap).boundary f := by
    rw [hcf]
    exact List.mem_map.mpr ⟨Sum.inr b,
      (nielsenCapBoundaryOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv c _).mpr ⟨b,rfl,hb⟩,rfl⟩
  have hold:d (Sum.inl b.val)∈(Pcap).boundary (f₀) := by
    rw [nielsenCappedPresentation_original_boundary]
    exact List.mem_map.mpr ⟨Sum.inl b.val,
      (nielsenCapOriginalOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv _).mpr ⟨b.val,rfl⟩,rfl⟩
  have hflip:d (Sum.inl b.val)=(d (Sum.inr b)).flip :=
    nielsenCapFiniteDartEquiv_pair hD hNE hFG hfin w hwD hwN J hc hv (Sum.inr b)
  refine ⟨edgeOfDart (d (Sum.inr b)),List.mem_map_of_mem hcap,?_⟩
  have hsame:edgeOfDart (d (Sum.inl b.val))=edgeOfDart (d (Sum.inr b)):=by rw [hflip,edgeOfDart_flip]
  exact hsame ▸ List.mem_map_of_mem hold

theorem nielsenCappedPresentation_connected : (Pcap).IsConnected := by
  refine ⟨⟨f₀⟩,?_⟩
  intro f g
  have hf:Relation.ReflTransGen (Pcap).FaceAdjacent f (f₀) := by
    by_cases he:f=f₀
    · subst f
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        (nielsenCappedPresentation_cap_adjacent hD hNE hFG hfin w hwD hwN J hc hv f he)
  have hg:Relation.ReflTransGen (Pcap).FaceAdjacent (f₀) g := by
    by_cases he:g=f₀
    · subst g
      exact Relation.ReflTransGen.refl
    · obtain ⟨a,ha,hb⟩:=nielsenCappedPresentation_cap_adjacent hD hNE hFG hfin w hwD hwN J hc hv g he
      exact Relation.ReflTransGen.single ⟨a,hb,ha⟩
  exact hf.trans hg

/-- The exact capped word is a validity-bundled orientable closed surface presentation. -/
def nielsenCappedValidPresentation : ValidPresentation :=
  ⟨Pcap,nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv⟩

/-- Genus and Euler characteristic of the actual derived capped word, with no assigned genus or Euler hypothesis. -/
theorem nielsenCappedPresentation_genus :
    ∃g,Surfaces.HasTopologicalGenus ((Pcap).PolygonalRealization
      (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      Surfaces.CyclicSurface.eulerCharacteristic (Pcap)=2-2*(g:ℤ) :=
  Surfaces.CyclicSurface.closed_coherent_connected_genus
    (nielsenCappedValidPresentation hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCappedPresentation_connected hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCappedPresentation_closed hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCappedPresentation_coherent hD hNE hFG hfin w hwD hwN J hc hv)

end NielsenCappedGenus


section NielsenCoreRawCornerChains
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "σ" => nielsenCyclicCornerEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "τ" => nielsenCyclicBoundaryReturnTime hD hNE hFG hfin w hwD hwN J hc hv
local notation "R" => nielsenCyclicBoundaryNext hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "tag" => nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv

/-- Literal original-pairing corner identifications; traversing a genuine boundary edge is not an identification. -/
def nielsenCoreRawCornerStep (i j:ZMod J.n) : Prop := pairIndex i≠i ∧ j=σ i
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCoreRawCornerSetoid : Setoid (ZMod J.n) where
  r:=Relation.EqvGen step
  iseqv:=Relation.EqvGen.is_equivalence step

/-- Each derived cap joins the terminal corner of an unpaired edge only to its actual next boundary corner. -/
theorem nielsenCyclicBoundaryNext_corner_chain (b:B) :
    Relation.EqvGen step (b.val+1) (R b).val := by
  have aux : ∀m:ℕ,1≤m→m≤τ b→Relation.EqvGen step (σ b.val) ((σ^m) b.val) := by
    intro m
    induction m with
    | zero => intro hm;omega
    | succ m ih =>
      intro _hm hmk
      by_cases hm:m=0
      · subst m
        simpa only [Nat.zero_add,pow_one] using (Relation.EqvGen.refl (r:=step) (σ b.val))
      · have hmpos:0<m:=Nat.pos_of_ne_zero hm
        have hn:pairIndex ((σ^m) b.val)≠(σ^m) b.val := by
          intro he
          have hmin:=nielsenCyclicBoundaryReturnTime_le hD hNE hFG hfin w hwD hwN J hc hv b m hmpos he
          omega
        have hpath:=ih hmpos (by omega)
        apply Relation.EqvGen.trans _ _ _ hpath
        apply Relation.EqvGen.rel
        refine ⟨hn,?_⟩
        rw [pow_succ',Equiv.Perm.mul_apply]
  have hb:σ b.val=b.val+1:=by change pairIndex b.val+1=b.val+1;rw [b.property]
  change Relation.EqvGen step (b.val+1) ((σ^(τ b)) b.val)
  simpa only [hb] using aux (τ b)
    (nielsenCyclicBoundaryReturnTime_spec hD hNE hFG hfin w hwD hwN J hc hv b).1 le_rfl

/-- Every raw corner generator is a true element of the original whole group acting on the physical sphere. -/
theorem nielsenCoreRawCornerStep_sphereOrbit {i j:ZMod J.n} (hij:step i j) :
    ∃g:H,g.val.val (Hyperbolic.closedDiscToExtended (vertex i))=Hyperbolic.closedDiscToExtended (vertex j) := by
  obtain ⟨hne,rfl⟩:=hij
  cases hi:tag i with
  | inr b => exact False.elim (hne (nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv i b hi))
  | inl v =>
    have he:=(nielsenCyclicPairIndex_endpoint_reverse hD hNE hFG hfin w hwD hwN J hc hv i v hi).1
    refine ⟨(fuchsianSideElement hD v.val.val.1)⁻¹,?_⟩
    exact (P.compactifiedAction_sphere _ _).symm.trans (congrArg Hyperbolic.closedDiscToExtended he)

theorem nielsenCoreRawCornerChain_sphereOrbit {i j:ZMod J.n}
    (hij:Relation.EqvGen step i j) :
    ∃g:H,g.val.val (Hyperbolic.closedDiscToExtended (vertex i))=Hyperbolic.closedDiscToExtended (vertex j) := by
  induction hij with
  | rel i j h => exact nielsenCoreRawCornerStep_sphereOrbit hD hNE hFG hfin w hwD hwN J hc hv h
  | refl i => exact ⟨1,rfl⟩
  | symm i j _ ih =>
    obtain ⟨g,hg⟩:=ih
    refine ⟨g⁻¹,?_⟩
    change g.val.val.symm _=_
    rw [←hg,g.val.val.symm_apply_apply]
  | trans i j k _ _ ih1 ih2 =>
    obtain ⟨g,hg⟩:=ih1
    obtain ⟨h,hh⟩:=ih2
    refine ⟨h*g,?_⟩
    change h.val.val (g.val.val _)=_
    rw [hg,hh]

theorem nielsenCyclicBoundaryNext_endpoint_sphereOrbit (b:B) :
    ∃g:H,g.val.val (Hyperbolic.closedDiscToExtended (vertex (b.val+1)))=
      Hyperbolic.closedDiscToExtended (vertex (R b).val) :=
  nielsenCoreRawCornerChain_sphereOrbit hD hNE hFG hfin w hwD hwN J hc hv
    (nielsenCyclicBoundaryNext_corner_chain hD hNE hFG hfin w hwD hwN J hc hv b)

end NielsenCoreRawCornerChains


/-- From only the original non-elementary finitely generated group, construct the actual finite
Nielsen polygon with its derived caps, and obtain genus and Euler characteristic of that exact
faithful realization. Identification with the geometric capped quotient is a separate obligation. -/
theorem finitelyGenerated_nielsen_capped_word_genus
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG) :
    ∃w:P.domain.carrier,∃hw:IsDirichletCenter P w,∃hwN:w∈fuchsianNielsenCore P hNE,
      let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
      let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
      let hwD:=dirichletDomain_center_mem P w hw
      ∃J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle,
        ∃hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier),
        ∃hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG,
        ∃g,Surfaces.HasTopologicalGenus
          ((nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).PolygonalRealization
            (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
          Surfaces.CyclicSurface.eulerCharacteristic (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)=2-2*(g:ℤ) := by
  obtain ⟨w,hw,hwN⟩:=exists_dirichlet_center_in_nielsenCore P hNE
  let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD:=dirichletDomain_center_mem P w hw
  obtain ⟨J,hc,hv⟩:=nielsenCore_actual_marked_cyclic_boundary hD hNE hFG hfin w hwD hwN
  exact ⟨w,hw,hwN,J,hc,hv,nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv⟩



section NielsenCappedOccurrenceIndex
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv
local notation "d" => nielsenCapFiniteDartEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "p" => nielsenCapOccurrencePair hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOccurrence_dart_injective :
    Function.Injective (BoundaryOccurrence.dart (P:=Pcap)) := by
  rintro ⟨f,i⟩ ⟨g,j⟩ he
  change ((Pcap).boundary f).get i=((Pcap).boundary g).get j at he
  by_cases hfg:f=g
  · subst g
    have hn:((Pcap).boundary f).Nodup:=
      (List.nodup_flatten.mp (nielsenCappedPresentation_flatten_nodup hD hNE hFG hfin w hwD hwN J hc hv)).1
        _ (List.get_mem _ f)
    have hij:i=j:=(List.nodup_iff_injective_get.mp hn) he
    subst j
    rfl
  · have hx:((Pcap).boundary f).get i∈(Pcap).boundary f:=List.get_mem _ i
    have hy:((Pcap).boundary g).get j∈(Pcap).boundary g:=List.get_mem _ j
    rw [←he] at hy
    exact False.elim (List.disjoint_left.mp
      (nielsenCappedPresentation_boundary_disjoint hD hNE hFG hfin w hwD hwN J hc hv f g hfg) hx hy)

theorem nielsenCappedOccurrence_dart_surjective :
    Function.Surjective (BoundaryOccurrence.dart (P:=Pcap)) := by
  intro a
  obtain ⟨l,hl,ha⟩:=List.mem_flatten.mp (nielsenCappedPresentation_flatten_mem hD hNE hFG hfin w hwD hwN J hc hv a)
  obtain ⟨f,hf⟩:=List.mem_iff_get.mp hl
  have ha':a∈(Pcap).boundary f:=by
    change a∈(Pcap).faces.get f
    rwa [hf]
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp ha'
  exact ⟨⟨f,i⟩,hi⟩

/-- Every actual stored occurrence, including cap faces, has its unique genuine original/cap label. -/
def nielsenCappedOccurrenceIndex : (Pcap).BoundaryOccurrence≃O :=
  (Equiv.ofBijective (FiniteCyclicPresentation.BoundaryOccurrence.dart (P:=Pcap))
    ⟨nielsenCappedOccurrence_dart_injective hD hNE hFG hfin w hwD hwN J hc hv,
      nielsenCappedOccurrence_dart_surjective hD hNE hFG hfin w hwD hwN J hc hv⟩).trans (d).symm
local notation "index" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOccurrenceIndex_dart (o:(Pcap).BoundaryOccurrence) : d (index o)=o.dart :=
  (d).apply_symm_apply o.dart

def nielsenCappedOccurrencePartner (o:(Pcap).BoundaryOccurrence) : (Pcap).BoundaryOccurrence :=
  (index).symm (p (index o))
local notation "partner" => nielsenCappedOccurrencePartner hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOccurrencePartner_dart (o:(Pcap).BoundaryOccurrence) :
    (partner o).dart=o.dart.flip := by
  rw [←nielsenCappedOccurrenceIndex_dart, nielsenCappedOccurrencePartner,Equiv.apply_symm_apply,
    nielsenCapFiniteDartEquiv_pair,nielsenCappedOccurrenceIndex_dart]

theorem nielsenCappedOccurrencePartner_involutive : Function.Involutive partner := by
  intro o
  apply (index).injective
  simp only [nielsenCappedOccurrencePartner,Equiv.apply_symm_apply]
  exact nielsenCapOccurrencePair_involutive hD hNE hFG hfin w hwD hwN J hc hv (index o)

theorem nielsenCappedOccurrencePartner_ne (o:(Pcap).BoundaryOccurrence) : partner o≠o := by
  intro he
  have h:=congrArg index he
  rw [nielsenCappedOccurrencePartner,Equiv.apply_symm_apply] at h
  exact nielsenCapOccurrencePair_ne_self hD hNE hFG hfin w hwD hwN J hc hv (index o) h

end NielsenCappedOccurrenceIndex


private theorem nielsen_cycle_chain_reverse {A:Type} {r:A→A→Prop} (s:Cycle A) (hs:s.Chain r) :
    s.reverse.Chain (fun x y=>r y x) := by
  induction s using Quotient.inductionOn with
  | h l =>
    cases l with
    | nil => trivial
    | cons a l =>
      have hh:List.IsChain r (a::l++[a]):=hs
      have hr:List.IsChain (fun x y=>r y x) (a::l++[a]).reverse:=List.isChain_reverse.mpr hh
      change (Cycle.reverse ((a::l):Cycle A)).Chain (fun x y=>r y x)
      rw [Cycle.reverse_coe,List.reverse_cons,←Cycle.coe_cons_eq_coe_append]
      apply (Cycle.chain_coe_cons _ _ _).mpr
      simpa only [List.reverse_cons,List.reverse_append,List.reverse_singleton,List.reverse_nil,List.nil_append,List.singleton_append] using hr

private theorem nielsen_cycle_chain_get_finRotate {A:Type} {r:A→A→Prop} (l:List A)
    (hs:(l:Cycle A).Chain r) (i:Fin l.length) : r (l.get i) (l.get (finRotate l.length i)) := by
  cases l with
  | nil => exact Fin.elim0 i
  | cons a l =>
    have hh:List.IsChain r ((a::l)++[a]):=hs
    have hb:i.val+1<((a::l)++[a]).length:=by simp only [List.length_append,List.length_singleton];omega
    have hr:=(List.isChain_iff_getElem.mp hh) i.val hb
    rw [List.getElem_append_left i.isLt] at hr
    by_cases hi:i.val+1<(a::l).length
    · rw [List.getElem_append_left hi] at hr
      simpa only [List.get_eq_getElem,Surfaces.CyclicSurface.finRotate_val_of_succ_lt i hi] using hr
    · have hlast:i.val+1=(a::l).length:=by omega
      rw [List.getElem_append_right (by omega)] at hr
      simpa only [hlast,Nat.sub_self,List.getElem_cons_zero,List.get_eq_getElem,Surfaces.CyclicSurface.finRotate_val_of_last i hlast] using hr

section NielsenCapCycleCorners
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "capList" => nielsenBoundaryCapList hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenBoundaryCapList_reverse_chain (c:C) :
    (((capList c).reverse):Cycle B).Chain (fun x y:B=>ρ y=x) := by
  have h:((capList c):Cycle B).Chain (fun x y:B=>ρ x=y):=by
    rw [nielsenBoundaryCapList_coe]
    exact nielsenBoundaryCapCycle_chain hD hNE hFG hfin w hwD hwN J hc hv c
  simpa only [Cycle.reverse_coe] using nielsen_cycle_chain_reverse _ h

theorem nielsenBoundaryCapList_reverse_next (c:C) (i:Fin (capList c).reverse.length) :
    ρ ((capList c).reverse.get (finRotate (capList c).reverse.length i))=(capList c).reverse.get i :=
  nielsen_cycle_chain_get_finRotate _ (nielsenBoundaryCapList_reverse_chain hD hNE hFG hfin w hwD hwN J hc hv c) i

end NielsenCapCycleCorners


private theorem nielsen_cycle_chain_iff_get_finRotate {A:Type} {r:A→A→Prop} (l:List A) :
    (l:Cycle A).Chain r ↔ ∀i:Fin l.length,r (l.get i) (l.get (finRotate l.length i)) := by
  constructor
  · exact fun h i=>nielsen_cycle_chain_get_finRotate l h i
  · intro h
    cases l with
    | nil => trivial
    | cons a l =>
      apply (Cycle.chain_coe_cons _ _ _).mpr
      apply List.isChain_iff_getElem.mpr
      intro i hi
      have hib:i<(a::l).length:=by simp only [List.length_cons,List.length_append,List.length_nil] at hi ⊢;omega
      have hr:=h ⟨i,hib⟩
      change r (((a::l)++[a])[i]'(Nat.lt_of_succ_lt hi)) (((a::l)++[a])[i+1]'hi)
      rw [List.getElem_append_left hib]
      by_cases hs:i+1<(a::l).length
      · rw [List.getElem_append_left hs]
        simpa only [List.get_eq_getElem,Surfaces.CyclicSurface.finRotate_val_of_succ_lt (⟨i,hib⟩:Fin (a::l).length)
          hs] using hr
      · have he:i+1=(a::l).length:=by omega
        rw [List.getElem_append_right (by omega)]
        simpa only [List.get_eq_getElem,Surfaces.CyclicSurface.finRotate_val_of_last (⟨i,hib⟩:Fin (a::l).length)
          he,he,Nat.sub_self,List.getElem_cons_zero] using hr

section NielsenCapFaceCycles
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "capList" => nielsenBoundaryCapList hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldFace" => nielsenCapOriginalOccurrences hD hNE hFG hfin w hwD hwN J hc hv
local notation "capFace" => nielsenCapBoundaryOccurrences hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCapFaceNext : O→O
  | .inl i=>.inl (i+1)
  | .inr b=>.inr ((ρ)⁻¹ b)
local notation "nextO" => nielsenCapFaceNext hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCapOriginalOccurrences_chain :
    ((oldFace):Cycle O).Chain (fun x y:O=>nextO x=y) := by
  apply (nielsen_cycle_chain_iff_get_finRotate _).mpr
  intro i
  have hlen:(oldFace).length=J.n:=List.length_ofFn
  have hi:i.val<J.n:=by simpa only [hlen] using i.isLt
  have hr:(finRotate (oldFace).length i).val=(finRotate J.n ⟨i.val,hi⟩).val := by
    rw [Surfaces.CyclicSurface.finRotate_val_mod,Surfaces.CyclicSurface.finRotate_val_mod]
    exact congrArg (fun n:ℕ=>(i.val+1)%n) hlen
  have hrot:(ZMod.finEquiv J.n) ⟨(finRotate (oldFace).length i).val,by simpa only [hlen] using (finRotate (oldFace).length i).isLt⟩=
      (ZMod.finEquiv J.n) ⟨i.val,hi⟩+1 := by
    calc
      _=(ZMod.finEquiv J.n) (finRotate J.n ⟨i.val,hi⟩):=congrArg (ZMod.finEquiv J.n) (Fin.ext hr)
      _=_:=by simp only [finRotate_apply,map_add,map_one]
  simp only [nielsenCapOriginalOccurrences,List.get_eq_getElem,List.getElem_ofFn]
  exact congrArg Sum.inl hrot.symm

theorem nielsenCapBoundaryOccurrences_chain (c:C) :
    ((capFace c):Cycle O).Chain (fun x y:O=>nextO x=y) := by
  change Cycle.Chain _ (Cycle.ofList ((capList c).reverse.map (fun b:B=>(Sum.inr b:O))))
  rw [←Cycle.map_coe,Cycle.chain_map]
  apply (nielsenBoundaryCapList_reverse_chain hD hNE hFG hfin w hwD hwN J hc hv c).imp
  intro x y h
  exact congrArg Sum.inr ((ρ).symm_apply_eq.mpr h.symm)

end NielsenCapFaceCycles


section NielsenCappedRawLabels
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "nextO" => nielsenCapFaceNext hD hNE hFG hfin w hwD hwN J hc hv
local notation "facesO" => nielsenCapFaceOccurrences hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "d" => nielsenCapFiniteDartEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "partner" => nielsenCappedOccurrencePartner hD hNE hFG hfin w hwD hwN J hc hv
local notation "p" => nielsenCapOccurrencePair hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCapFaceOccurrences_chain (l:List O) (hl:l∈facesO) :
    (l:Cycle O).Chain (fun x y:O=>nextO x=y) := by
  rcases List.mem_cons.mp hl with he|hl
  · subst l
    exact nielsenCapOriginalOccurrences_chain hD hNE hFG hfin w hwD hwN J hc hv
  · obtain ⟨k,rfl⟩:=List.mem_ofFn.mp hl
    exact nielsenCapBoundaryOccurrences_chain hD hNE hFG hfin w hwD hwN J hc hv _

theorem nielsenCappedOccurrenceIndex_next (o:(Pcap).BoundaryOccurrence) :
    index (Surfaces.CyclicSurface.cornerNext (Pcap) o)=nextO (index o) := by
  have hf:(Pcap).boundary o.1∈(Pcap).faces:=List.get_mem _ o.1
  obtain ⟨l,hl,he⟩:=List.mem_map.mp hf
  have hchain:((Pcap).boundary o.1:Cycle (Pcap).Dart).Chain
      (fun a b=>nextO ((d).symm a)=(d).symm b) := by
    rw [←he,←Cycle.map_coe,Cycle.chain_map]
    simpa only [Equiv.symm_apply_apply] using nielsenCapFaceOccurrences_chain hD hNE hFG hfin w hwD hwN J hc hv l hl
  have hh:=nielsen_cycle_chain_get_finRotate _ hchain o.2
  exact hh.symm

abbrev NielsenCoreRawCornerClasses := Quotient (nielsenCoreRawCornerSetoid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCapRawVertexLabel : O→V
  | .inl i=>Quotient.mk _ i
  | .inr b=>Quotient.mk _ (b.val+1)
local notation "label" => nielsenCapRawVertexLabel hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCapRawNextVertexLabel : O→V
  | .inl i=>Quotient.mk _ (i+1)
  | .inr b=>Quotient.mk _ b.val
local notation "nextLabel" => nielsenCapRawNextVertexLabel hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCappedOccurrenceRawLabel (o:(Pcap).BoundaryOccurrence) : V := label (index o)
local notation "f" => nielsenCappedOccurrenceRawLabel hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOccurrenceRawLabel_next (o:(Pcap).BoundaryOccurrence) :
    f (Surfaces.CyclicSurface.cornerNext (Pcap) o)=nextLabel (index o) := by
  unfold nielsenCappedOccurrenceRawLabel
  rw [nielsenCappedOccurrenceIndex_next]
  cases hi:index o with
  | inl i => rfl
  | inr b =>
    change (Quotient.mk _ (((ρ).symm b).val+1):V)=Quotient.mk _ b.val
    have h:=nielsenCyclicBoundaryNext_corner_chain hD hNE hFG hfin w hwD hwN J hc hv ((ρ).symm b)
    have he:nielsenCyclicBoundaryNext hD hNE hFG hfin w hwD hwN J hc hv ((ρ).symm b)=b:=
      (ρ).apply_symm_apply b
    rw [he] at h
    exact Quotient.sound h

theorem nielsenCapRawVertexLabel_pair (x:O) : label x=nextLabel (p x) := by
  cases x with
  | inl i =>
    by_cases hi:pairIndex i=i
    · rw [nielsenCapOccurrencePair,dite_eq_left hi]
      rfl
    · rw [nielsenCapOccurrencePair,dite_eq_right hi]
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ ⟨hi,rfl⟩
  | inr b => rfl

theorem nielsenCapRawNextVertexLabel_pair (x:O) : nextLabel x=label (p x) := by
  have h:=nielsenCapRawVertexLabel_pair hD hNE hFG hfin w hwD hwN J hc hv (p x)
  rw [nielsenCapOccurrencePair_involutive hD hNE hFG hfin w hwD hwN J hc hv] at h
  exact h.symm

theorem nielsenCappedOccurrenceRawLabel_paired_left (o:(Pcap).BoundaryOccurrence) :
    f o=f (Surfaces.CyclicSurface.cornerNext (Pcap) (partner o)) := by
  rw [nielsenCappedOccurrenceRawLabel_next]
  change label (index o)=nextLabel (index ((index).symm (p (index o))))
  rw [Equiv.apply_symm_apply]
  exact nielsenCapRawVertexLabel_pair hD hNE hFG hfin w hwD hwN J hc hv _

theorem nielsenCappedOccurrenceRawLabel_paired_right (o:(Pcap).BoundaryOccurrence) :
    f (Surfaces.CyclicSurface.cornerNext (Pcap) o)=f (partner o) := by
  rw [nielsenCappedOccurrenceRawLabel_next]
  change nextLabel (index o)=label (index ((index).symm (p (index o))))
  rw [Equiv.apply_symm_apply]
  exact nielsenCapRawNextVertexLabel_pair hD hNE hFG hfin w hwD hwN J hc hv _

end NielsenCappedRawLabels


section NielsenCappedVertexKernel
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "partner" => nielsenCappedOccurrencePartner hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "f" => nielsenCappedOccurrenceRawLabel hD hNE hFG hfin w hwD hwN J hc hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOccurrence_edge_eq_iff (o q:(Pcap).BoundaryOccurrence) :
    o.edge=q.edge ↔ q=o ∨ q=partner o := by
  have hedge:(partner o).edge=o.edge := by
    unfold FiniteCyclicPresentation.BoundaryOccurrence.edge
    rw [nielsenCappedOccurrencePartner_dart,edgeOfDart_flip]
  have hnot:¬(Pcap).IsBoundaryEdge o.edge := by
    intro h
    have h2:=nielsenCappedPresentation_closed hD hNE hFG hfin w hwD hwN J hc hv o.edge
    change (Pcap).edgeMultiplicity o.edge=1 at h
    omega
  constructor
  · intro hoq
    by_cases hqo:q=o
    · exact Or.inl hqo
    obtain ⟨r,_hr,hunique⟩:=(nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc
      hv).exists_unique_partner o hnot
    exact Or.inr ((hunique q ⟨Ne.symm hqo,hoq.symm⟩).trans
      (hunique (partner o) ⟨Ne.symm (nielsenCappedOccurrencePartner_ne hD hNE hFG hfin w hwD hwN J hc hv
        o),hedge⟩).symm)
  · rintro (rfl|rfl)
    · rfl
    · exact hedge.symm

theorem nielsenCappedRawLabel_initial (o q:(Pcap).BoundaryOccurrence) (he:o.edge=q.edge) :
    f (Surfaces.CyclicSurface.occurrenceInitial (Pcap) o)=f (Surfaces.CyclicSurface.occurrenceInitial (Pcap) q) := by
  rcases (nielsenCappedOccurrence_edge_eq_iff hD hNE hFG hfin w hwD hwN J hc hv o q).mp he with rfl|rfl
  · rfl
  · have hp:=nielsenCappedOccurrencePartner_dart hD hNE hFG hfin w hwD hwN J hc hv o
    cases hd:o.dart with
    | pos a =>
      have hq:(partner o).dart=.neg a:=by simpa only [hd,SignedDart.flip] using hp
      simpa only [Surfaces.CyclicSurface.occurrenceInitial,hd,hq] using
        nielsenCappedOccurrenceRawLabel_paired_left hD hNE hFG hfin w hwD hwN J hc hv o
    | neg a =>
      have hq:(partner o).dart=.pos a:=by simpa only [hd,SignedDart.flip] using hp
      simpa only [Surfaces.CyclicSurface.occurrenceInitial,hd,hq] using
        nielsenCappedOccurrenceRawLabel_paired_right hD hNE hFG hfin w hwD hwN J hc hv o

theorem nielsenCappedRawLabel_terminal (o q:(Pcap).BoundaryOccurrence) (he:o.edge=q.edge) :
    f (Surfaces.CyclicSurface.occurrenceTerminal (Pcap) o)=f (Surfaces.CyclicSurface.occurrenceTerminal (Pcap) q) := by
  rcases (nielsenCappedOccurrence_edge_eq_iff hD hNE hFG hfin w hwD hwN J hc hv o q).mp he with rfl|rfl
  · rfl
  · have hp:=nielsenCappedOccurrencePartner_dart hD hNE hFG hfin w hwD hwN J hc hv o
    cases hd:o.dart with
    | pos a =>
      have hq:(partner o).dart=.neg a:=by simpa only [hd,SignedDart.flip] using hp
      simpa only [Surfaces.CyclicSurface.occurrenceTerminal,hd,hq] using
        nielsenCappedOccurrenceRawLabel_paired_right hD hNE hFG hfin w hwD hwN J hc hv o
    | neg a =>
      have hq:(partner o).dart=.pos a:=by simpa only [hd,SignedDart.flip] using hp
      simpa only [Surfaces.CyclicSurface.occurrenceTerminal,hd,hq] using
        nielsenCappedOccurrenceRawLabel_paired_left hD hNE hFG hfin w hwD hwN J hc hv o

def nielsenCappedVertexToRaw : Surfaces.CyclicSurface.Vertex (Pcap)→V :=
  Surfaces.CyclicSurface.vertexLift f (nielsenCappedRawLabel_initial hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCappedRawLabel_terminal hD hNE hFG hfin w hwD hwN J hc hv)
local notation "toRaw" => nielsenCappedVertexToRaw hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedVertexToRaw_mk (o:(Pcap).BoundaryOccurrence) : toRaw (Surfaces.CyclicSurface.vertexClass (Pcap)
  o)=f o := rfl

def nielsenCappedOriginalCorner (i:ZMod J.n) : (Pcap).BoundaryOccurrence := (index).symm (Sum.inl i)
local notation "oldCorner" => nielsenCappedOriginalCorner hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOriginalCorner_next
    (i:ZMod J.n) : Surfaces.CyclicSurface.cornerNext (Pcap)
    (oldCorner i)=oldCorner (i+1) := by
  apply (index).injective
  rw [nielsenCappedOccurrenceIndex_next]
  simp only [nielsenCappedOriginalCorner,Equiv.apply_symm_apply,nielsenCapFaceNext]

theorem nielsenCappedOriginalCorner_partner (i:ZMod J.n) (hi:pairIndex i≠i) :
    partner (oldCorner i)=oldCorner (pairIndex i) := by
  apply (index).injective
  simp only [nielsenCappedOccurrencePartner,nielsenCappedOriginalCorner,Equiv.apply_symm_apply,
    nielsenCapOccurrencePair,dite_eq_right hi]

theorem nielsenCappedOccurrence_vertex_paired_left (o:(Pcap).BoundaryOccurrence) :
    Surfaces.CyclicSurface.vertexClass (Pcap) o=Surfaces.CyclicSurface.vertexClass (Pcap) (Surfaces.CyclicSurface.cornerNext (Pcap) (partner o)) := by
  have hflip:=nielsenCappedOccurrencePartner_dart hD hNE hFG hfin w hwD hwN J hc hv o
  have hedge:o.edge=(partner o).edge:=
    (nielsenCappedOccurrence_edge_eq_iff hD hNE hFG hfin w hwD hwN J hc hv o _).mpr (Or.inr rfl)
  cases hd:o.dart with
  | pos a =>
    have hp:(partner o).dart=.neg a:=by simpa only [hd,SignedDart.flip] using hflip
    simpa only [Surfaces.CyclicSurface.occurrenceInitial,hd,hp] using Surfaces.CyclicSurface.vertexClass_initial (Pcap) o (partner o) hedge
  | neg a =>
    have hp:(partner o).dart=.pos a:=by simpa only [hd,SignedDart.flip] using hflip
    simpa only [Surfaces.CyclicSurface.occurrenceTerminal,hd,hp] using Surfaces.CyclicSurface.vertexClass_terminal (Pcap) o (partner o) hedge

theorem nielsenRawCornerStep_cappedVertex {i j:ZMod J.n} (hij:step i j) :
    Surfaces.CyclicSurface.vertexClass (Pcap) (oldCorner i)=Surfaces.CyclicSurface.vertexClass (Pcap) (oldCorner j) := by
  obtain ⟨hi,rfl⟩:=hij
  have h:=nielsenCappedOccurrence_vertex_paired_left hD hNE hFG hfin w hwD hwN J hc hv (oldCorner i)
  rw [nielsenCappedOriginalCorner_partner hD hNE hFG hfin w hwD hwN J hc hv i hi,nielsenCappedOriginalCorner_next] at h
  exact h

def nielsenRawToCappedVertex : V→Surfaces.CyclicSurface.Vertex
    (Pcap) := Quotient.lift
  (fun i=>Surfaces.CyclicSurface.vertexClass (Pcap) (oldCorner i)) (by
    intro i j hij
    induction hij with
    | rel i j h => exact nielsenRawCornerStep_cappedVertex hD hNE hFG hfin w hwD hwN J hc hv h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)
local notation "fromRaw" => nielsenRawToCappedVertex hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedVertex_raw_leftInverse : Function.LeftInverse fromRaw toRaw := by
  intro v
  refine Quotient.inductionOn v ?_
  intro o
  change fromRaw (toRaw (Surfaces.CyclicSurface.vertexClass (Pcap) o))=Surfaces.CyclicSurface.vertexClass (Pcap) o
  rw [nielsenCappedVertexToRaw_mk]
  unfold nielsenCappedOccurrenceRawLabel
  cases hi:index o with
  | inl i =>
    have ho:o=oldCorner i:=by apply (index).injective;rw [nielsenCappedOriginalCorner,Equiv.apply_symm_apply,hi]
    subst o
    change Surfaces.CyclicSurface.vertexClass (Pcap) (oldCorner i)=Surfaces.CyclicSurface.vertexClass (Pcap) (oldCorner
      i)
    rfl
  | inr b =>
    change Surfaces.CyclicSurface.vertexClass (Pcap) (oldCorner (b.val+1))=Surfaces.CyclicSurface.vertexClass (Pcap) o
    have hp:partner o=oldCorner b.val:=by
      apply (index).injective
      rw [nielsenCappedOccurrencePartner,Equiv.apply_symm_apply,hi,nielsenCappedOriginalCorner,Equiv.apply_symm_apply]
      rfl
    have h:=nielsenCappedOccurrence_vertex_paired_left hD hNE hFG hfin w hwD hwN J hc hv o
    rw [hp,nielsenCappedOriginalCorner_next] at h
    exact h.symm

theorem nielsenCappedVertex_raw_rightInverse : Function.RightInverse fromRaw toRaw := by
  intro v
  refine Quotient.inductionOn v ?_
  intro i
  change nielsenCapRawVertexLabel hD hNE hFG hfin w hwD hwN J hc hv (index ((index).symm (Sum.inl i)))=Quotient.mk _ i
  rw [Equiv.apply_symm_apply]
  rfl

/-- The cap attachment imposes exactly the original actual partial-pairing corner kernel. -/
def nielsenCappedVertexRawEquiv : Surfaces.CyclicSurface.Vertex (Pcap)≃V where
  toFun:=toRaw
  invFun:=fromRaw
  left_inv:=nielsenCappedVertex_raw_leftInverse hD hNE hFG hfin w hwD hwN J hc hv
  right_inv:=nielsenCappedVertex_raw_rightInverse hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedVertex_count : Nat.card
    (Surfaces.CyclicSurface.Vertex (Pcap))=Nat.card V :=
  Nat.card_congr (nielsenCappedVertexRawEquiv hD hNE hFG hfin w hwD hwN J hc hv)

end NielsenCappedVertexKernel


section NielsenCappedRawEuler
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedPresentation_rawEuler : Surfaces.CyclicSurface.eulerCharacteristic (Pcap)=
    (Nat.card V:ℤ)-(Pcap).edgeCount+1+(Fintype.card C:ℤ) := by
  rw [Surfaces.CyclicSurface.eulerCharacteristic,nielsenCappedVertex_count,nielsenCappedPresentation_faces_length,Nat.cast_add,Nat.cast_one]
  ring

/-- The derived capped genus satisfies the literal original-corner, edge-pair and actual cap-cycle count. -/
theorem nielsenCappedPresentation_genus_rawEuler :
    ∃g,Surfaces.HasTopologicalGenus ((Pcap).PolygonalRealization
      (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      (Nat.card V:ℤ)-(Pcap).edgeCount+1+(Fintype.card C:ℤ)=2-2*(g:ℤ) := by
  obtain ⟨g,hg,hχ⟩:=nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv
  exact ⟨g,hg,(nielsenCappedPresentation_rawEuler hD hNE hFG hfin w hwD hwN J hc hv).symm.trans hχ⟩

end NielsenCappedRawEuler

end LowDimensionalTopology.Geometry.Fuchsian
