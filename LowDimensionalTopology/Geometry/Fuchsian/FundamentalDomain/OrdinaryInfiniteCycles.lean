/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonFreeSideArcs
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSupportingHalfPlanes
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.OrdinaryDirichletCycles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonTranslateDiameters
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactifiedPolygonSides
public import LowDimensionalTopology.Geometry.Polygon.Euclidean.EuclideanPolygonAngles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonLocalGeometry
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Ordinary ideal cycles and local polygon geometry

An ordinary sphere neighborhood meets only finitely many closed polygon tiles.
Their Klein half-plane germs determine the inward directions and Euclidean ideal
angles. The finite incident fan gives the angle sum over an ordinary ideal cycle.

Tangential circle traces then distinguish free-side interiors, proper ideal
vertices and improper ideal vertices. The final classification uses these actual
side incidences. Separate namespace blocks retain local measurable structures and
classical or geometric notation scopes used by the intermediate constructions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual sphere orbit transporters into a compact ordinary neighborhood are finite. -/
theorem ordinary_compact_orbit_transporters_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hU :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H U)
    (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hK : IsCompact K) (hKU : K⊆U) (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    {g:H | g•z∈K}.Finite := by
  by_cases he : ∃k:H,k•z∈K
  · obtain ⟨k,hk⟩:=he
    apply ((hU K hK hKU).image (fun g:H=>g*k)).subset
    intro g hg
    refine ⟨g*k⁻¹,?_,by simp⟩
    refine ⟨g•z,⟨k•z,hk,?_⟩,hg⟩
    change (g*k⁻¹)•(k•z)=g•z
    rw [mul_smul,inv_smul_smul]
  · exact (Set.finite_empty.subset (by
      intro g hg
      exact False.elim (he ⟨g,hg⟩)))

/-- The actual closed Euclidean tile, including its genuine ideal boundary. -/
def fuchsianPolygonClosedPlaneTile {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (g:H) : Set ℂ:=
  closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' fuchsianDomainTile P D g)

/-- Ordinary ideal points have a genuine finite Euclidean neighborhood star for every original convex locally finite polygon. -/
theorem IsConvexFuchsianPolygon.ordinary_closedPlaneTiles_neighborhood_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃ε:ℝ,0<ε ∧ {g:H | (fuchsianPolygonClosedPlaneTile P D g∩Metric.ball ξ ε).Nonempty}.Finite := by
  obtain ⟨U,hU,hξU,hdisc⟩:=hOrd
  have hOp:IsOpen ((OnePoint.some:ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' U):=
    hU.preimage OnePoint.continuous_coe
  obtain ⟨ε,hε,hball⟩:=Metric.isOpen_iff.mp hOp ξ hξU
  let K:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=OnePoint.some '' Metric.closedBall ξ (ε/2)
  have hK:IsCompact K:=(isCompact_closedBall ξ (ε/2)).image OnePoint.continuous_coe
  have hKU:K⊆U:=by
    rintro _ ⟨z,hz,rfl⟩
    exact hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
  obtain ⟨w,hw⟩:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hF: {g:H | g•w.val∈K}.Finite:=ordinary_compact_orbit_transporters_finite U hdisc K hK hKU w.val
  have hsmall:∀ᶠg:H in cofinite,
      Metric.diam ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' fuchsianDomainTile P D g)<ε/4:=
    hD.euclidean_closed_tile_diam_tendsto.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/4))
  have hBad: {g:H | ¬Metric.diam ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) ''
      fuchsianDomainTile P D g)<ε/4}.Finite:=Filter.mem_cofinite.mp hsmall
  refine ⟨ε/4,by linarith,(hBad.union hF).subset ?_⟩
  rintro g ⟨z,hzg,hzξ⟩
  by_cases hg:g∈{g:H | ¬Metric.diam ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) ''
      fuchsianDomainTile P D g)<ε/4}
  · exact Or.inl hg
  · right
    have hd:Metric.diam ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) ''
        fuchsianDomainTile P D g)<ε/4:=not_not.mp hg
    have hbounded:Bornology.IsBounded ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) ''
        fuchsianDomainTile P D g):=by
      apply (Metric.isBounded_ball (x:=(0:ℂ)) (r:=1)).subset
      rintro _ ⟨x,hx,rfl⟩
      exact mem_ball_zero_iff.mpr (P.finiteCoordinate x).norm_lt_one
    have hwg:g•w∈fuchsianDomainTile P D g:=⟨w,subset_closure hw,rfl⟩
    have hdist:dist (P.finiteCoordinate (g•w):ℂ) z≤Metric.diam
        ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' fuchsianDomainTile P D g):=by
      rw [←Metric.diam_closure]
      exact Metric.dist_le_diam_of_mem hbounded.closure
        (subset_closure ⟨g•w,hwg,rfl⟩) hzg
    have hclose:dist (P.finiteCoordinate (g•w):ℂ) ξ≤ε/2:=by
      have ht:=dist_triangle (P.finiteCoordinate (g•w):ℂ) z ξ
      have hzdist:dist z ξ<ε/4:=Metric.mem_ball.mp hzξ
      linarith
    exact ⟨(P.finiteCoordinate (g•w):ℂ),Metric.mem_closedBall.mpr hclose,
      P.finiteCoordinate_extended (g•w)⟩

/-- Original ideal points transport into the genuine ideal boundary of the translated domain. -/
theorem UnitDiscFuchsianGroup.idealBoundary_smul {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (g:H) (ξ η:ℂ)
    (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (he:g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    η∈fuchsianPolygonIdealBoundary P (g•D) := by
  have hnorm:‖η‖=1:=by
    obtain ⟨a,ha,hga⟩:=P.unitCircle_image g ξ ((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
    have hh:η=a:=OnePoint.coe_injective (he.symm.trans hga)
    exact hh ▸ ha
  apply (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P _ η).mpr
  refine ⟨hnorm,?_⟩
  have hx:=(mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D ξ).mp hξ |>.2
  have hmap:=mem_closure_image (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    g.val).continuous.continuousAt hx
  change g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈closure (g.val.val ''
    ((Subtype.val:P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D)) at hmap
  rw [he] at hmap
  convert hmap using 1
  congr 1
  ext z
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨y.val,⟨y,hy,rfl⟩,rfl⟩
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨g•y,⟨y,hy,rfl⟩,rfl⟩

/-- The ideal closure of a translated open polygon lies in its actual closed Euclidean tile. -/
theorem UnitDiscFuchsianGroup.idealBoundary_subset_closedPlaneTile
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (D:Set P.domain.carrier) (g:H) :
    fuchsianPolygonIdealBoundary P (g•D)⊆fuchsianPolygonClosedPlaneTile P D g := by
  intro ξ hξ
  apply closure_mono _ ((mem_fuchsianPolygonIdealBoundary P (g•D) ξ).mp hξ).1
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨x,Set.smul_set_mono subset_closure hx,rfl⟩

/-- Only finitely many actual closed tiles meet a fixed ordinary ideal point. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_incident_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    {g:H | ξ∈fuchsianPolygonClosedPlaneTile P D g}.Finite := by
  obtain ⟨ε,hε,hf⟩:=hD.ordinary_closedPlaneTiles_neighborhood_finite ξ hOrd
  exact hf.subset (fun g hg=>⟨ξ,hg,Metric.mem_ball_self hε⟩)

/-- Every original ordinary ideal cycle is finite, with no generic Dirichlet or finite-generation restriction. -/
theorem IsConvexFuchsianPolygon.ordinary_idealCycle_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    (fuchsianPolygonIdealCycle P D (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).Finite := by
  apply ((hD.ordinary_ideal_incident_finite ξ hOrd).image
    (fun g:H=>g⁻¹•(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))).subset
  rintro _ ⟨⟨η,hη,rfl⟩,g,hg⟩
  have hback:g⁻¹.val.val (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    change g⁻¹•(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [←hg,inv_smul_smul]
  have hξ:=P.idealBoundary_smul D g⁻¹ η ξ hη hback
  exact ⟨g⁻¹,P.idealBoundary_subset_closedPlaneTile D g⁻¹ hξ,by
    change (g⁻¹)⁻¹•(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    simpa only [inv_inv] using hg⟩

/-- An ordinary ideal point has trivial stabilizer in the whole original group. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_stabilizer_trivial
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∀g:H,g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→g=1 := by
  intro g hfix
  by_contra hg
  have hpar:=hD.nonidentity_ideal_fixer_parabolic g hg ξ hξ hfix
  exact ordinaryNeighborhood_not_parabolic_fixed (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hOrd g hpar hfix

/-- The order of every genuine ordinary ideal cycle is one. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_stabilizer_card
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    Nat.card (MulAction.stabilizer H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=1 := by
  have hfree:=hD.ordinary_ideal_stabilizer_trivial ξ hξ hOrd
  let : Subsingleton (MulAction.stabilizer H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)):=⟨fun a b=>by
    apply Subtype.ext
    exact (hfree a.val (MulAction.mem_stabilizer_iff.mp a.property)).trans
      (hfree b.val (MulAction.mem_stabilizer_iff.mp b.property)).symm⟩
  let : Unique (MulAction.stabilizer H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)):=
    { default:=1,
      uniq:=fun _=>Subsingleton.elim _ _ }
  exact Nat.card_unique

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The genuine finite star at an ordinary ideal point determines the original tile by actual affine cuts relative to the closed unit disc. -/
theorem ordinary_finite_convex_relative_germ {ι:Type*} (s:Finset ι) (i₀:ι) (hi₀:i₀∈s)
    (U:ι→Set ℂ) (hc:∀i∈s,Convex ℝ (U i)) (ho:∀i∈s,IsOpen (U i))
    (hn:∀i∈s,(U i).Nonempty) (hd:∀i∈s,i≠i₀→Disjoint (U i₀) (U i))
    (hball:∀i∈s,U i⊆Metric.ball (0:ℂ) 1) (ξ:ℂ) (_hξ:‖ξ‖=1)
    (hz:∀i∈s,ξ∈closure (U i)) (N:Set ℂ) (hN:IsOpen N) (_hξN:ξ∈N)
    (hcover:N∩Metric.ball (0:ℂ) 1⊆⋃i∈s,closure (U i)) :
    ∃n:{i // i∈s∧i≠i₀}→ℂ,
      (∀i,n i≠0 ∧ (∀z∈U i₀,inner ℝ (n i) (z-ξ)<0) ∧
        (∀z∈U i.val,0 < inner ℝ (n i) (z-ξ))) ∧
      closure (U i₀)∩N∩Metric.closedBall (0:ℂ) 1=
        {z | ∀i,inner ℝ (n i) (z-ξ)≤0}∩N∩Metric.closedBall (0:ℂ) 1 := by
  have hsep (i:{i // i∈s∧i≠i₀}) :
      ∃n:ℂ,n≠0 ∧ (∀z∈U i₀,inner ℝ n (z-ξ)<0) ∧
        (∀z∈U i.val,0 < inner ℝ n (z-ξ)) := by
    obtain ⟨n,t,hnn,hl,hr⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator
      (hc i₀ hi₀) (ho i₀ hi₀) (hn i₀ hi₀) (hc i.val i.property.1)
      (ho i.val i.property.1) (hn i.val i.property.1) (hd i.val i.property.1 i.property.2)
    have hbase:inner ℝ n ξ=t:=_root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hl hr ⟨hz i₀
      hi₀,hz i.val i.property.1⟩
    refine ⟨n,hnn,fun z hz=>?_,fun z hz=>?_⟩
    · rw [inner_sub_right,hbase]
      exact sub_neg.mpr (hl z hz)
    · rw [inner_sub_right,hbase]
      exact sub_pos.mpr (hr z hz)
  choose n hn' using hsep
  refine ⟨n,hn',?_⟩
  apply subset_antisymm
  · rintro z ⟨⟨hzU,hzN⟩,hzB⟩
    refine ⟨⟨fun i=>?_,hzN⟩,hzB⟩
    exact (closure_minimal (fun u hu=>((hn' i).2.1 u hu).le)
      (isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const)) hzU
  · rintro z ⟨⟨hzQ,hzN⟩,hzB⟩
    refine ⟨⟨?_,hzN⟩,hzB⟩
    obtain ⟨a,ha⟩:=hn i₀ hi₀
    have han:‖a‖<1:=mem_ball_zero_iff.mp (hball i₀ hi₀ ha)
    have hzn:‖z‖≤1:=mem_closedBall_zero_iff.mp hzB
    let f:ℝ→ℂ:=fun t=>(1-t)•z+t•a
    have hf:Continuous f:=(continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const)
    have hlim:Tendsto f (𝓝[>] (0:ℝ)) (𝓝 z):=by
      convert hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
      simp only [f,sub_zero,one_smul,zero_smul,add_zero]
    have hNevent:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),f t∈N:=hlim.eventually (hN.mem_nhds hzN)
    have hpos:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),0<t:=self_mem_nhdsWithin
    have hlt:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),t<1:=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))
    have hmem:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),f t∈closure (U i₀):=by
      filter_upwards [hNevent,hpos,hlt] with t htN ht0 ht1
      have htB:f t∈Metric.ball (0:ℂ) 1:=by
        apply mem_ball_zero_iff.mpr
        have hnorm:=norm_add_le ((1-t)•z) (t•a)
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_pos (sub_pos.mpr ht1),abs_of_pos ht0] at hnorm
        change ‖(1-t)•z+t•a‖<1
        nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hzn),
          mul_pos ht0 (sub_pos.mpr han)]
      obtain ⟨i,hi,hfi⟩:=mem_iUnion₂.mp (hcover ⟨htN,htB⟩)
      by_cases hie:i=i₀
      · simpa only [hie] using hfi
      · let j:{i // i∈s∧i≠i₀}:=⟨i,hi,hie⟩
        have hright:0 ≤ inner ℝ (n j) (f t-ξ):=
          (closure_minimal (fun u hu=>((hn' j).2.2 u hu).le)
            (isClosed_le continuous_const
              (continuous_const.inner (continuous_id.sub continuous_const)))) hfi
        have he:inner ℝ (n j) (f t-ξ)=
            (1-t)*inner ℝ (n j) (z-ξ)+t*inner ℝ (n j) (a-ξ):=by
          simp only [f,inner_sub_right,inner_add_right,real_inner_smul_right]
          ring
        have hneg:=mul_neg_of_pos_of_neg ht0 ((hn' j).2.1 a ha)
        have hnonpos:=mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1.le) (hzQ j)
        rw [he] at hright
        exact (by linarith : False).elim
    exact isClosed_closure.mem_of_tendsto hlim hmem

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal Euclidean closed tile is the image of its true compact disc closure. -/
theorem fuchsianPolygonClosedPlaneTile_model {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (g:H) :
    (fun p:𝕔𝔻=>(p:ℂ)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate ''
      fuchsianDomainTile P D g)=
      fuchsianPolygonClosedPlaneTile P D g := by
  have hc:Topology.IsClosedEmbedding (fun p:𝕔𝔻=>(p:ℂ)):=
    Complex.UnitClosedDisc.continuous_coe.isClosedEmbedding Complex.UnitClosedDisc.isEmbedding_coe.injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,←hc.closure_image_eq,image_image,image_image]
  rfl

/-- The same compact tile maps to the closure of the actual open Klein tile. -/
theorem fuchsianPolygonClosedPlaneTile_klein {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (g:H) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' fuchsianDomainTile P D g)=
      closure (P.kleinCoordinate '' (g•D)) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
  change closure (P.kleinCoordinate '' fuchsianDomainTile P D g)=_
  apply subset_antisymm
  · exact closure_minimal (P.klein_closed_tile_subset_closure D g) isClosed_closure
  · exact closure_mono (image_mono (Set.smul_set_mono subset_closure))

/-- The actual ordinary finite star remains finite in the boundary-compatible Klein model. -/
theorem IsConvexFuchsianPolygon.ordinary_klein_neighborhood_finite
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:‖ξ‖=1) (hOrd:HasMobiusOrdinaryNeighborhood H
      (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃N:Set ℂ,IsOpen N ∧ ξ∈N ∧
      {g:H | (closure (P.kleinCoordinate '' (g•D))∩N).Nonempty}.Finite := by
  obtain ⟨ε,hε,hf⟩:=hD.ordinary_closedPlaneTiles_neighborhood_finite ξ hOrd
  let W:Set 𝕔𝔻:=(fun p:𝕔𝔻=>(p:ℂ)) ⁻¹' Metric.ball ξ ε
  have hW:IsOpen W:=Metric.isOpen_ball.preimage Complex.UnitClosedDisc.continuous_coe
  obtain ⟨N,hN,hNW⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.isInducing.isOpen_iff.mp hW
  let p:𝕔𝔻:=Complex.UnitClosedDisc.mk ξ hξ.le
  have hpf:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p=ξ:=
    congrArg (fun z:𝕔𝔻=>(z:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p
      hξ)
  have hpW:p∈W:=Metric.mem_ball_self hε
  have hξN:ξ∈N:=by
    rw [←hpf]
    change p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ⁻¹' N
    rw [hNW]
    exact hpW
  refine ⟨N,hN,hξN,hf.subset ?_⟩
  rintro g ⟨z,hzg,hzN⟩
  obtain ⟨q,hq,hqz⟩:=(fuchsianPolygonClosedPlaneTile_klein P D g).symm ▸ hzg
  have hqW:q∈W:=by
    rw [←hNW]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q∈N
    exact hqz.symm ▸ hzN
  exact ⟨(q:ℂ),(fuchsianPolygonClosedPlaneTile_model P D g) ▸ ⟨q,hq,rfl⟩,hqW⟩

/-- Every ordinary ideal point of the actual original polygon has a finite affine-support germ relative to the genuine closed unit disc. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_finite_halfplanes
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃ (s:Finset H) (n:{g // g∈s∧g≠1}→ℂ) (N:Set ℂ),
      IsOpen N ∧ ξ∈N ∧
      (∀g∈s,ξ∈closure (P.kleinCoordinate '' (g•D))) ∧
      (∀i,n i≠0 ∧ (∀z∈P.kleinCoordinate '' D,inner ℝ (n i) (z-ξ)<0) ∧
        (∀z∈P.kleinCoordinate '' (i.val•D),0 < inner ℝ (n i) (z-ξ))) ∧
      closure (P.kleinCoordinate '' D)∩N∩Metric.closedBall (0:ℂ) 1=
        {z | ∀i,inner ℝ (n i) (z-ξ)≤0}∩N∩Metric.closedBall (0:ℂ) 1 := by
  classical
  obtain ⟨hξcl,hξnorm⟩:=(mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ
  have hξK:ξ∈closure (P.kleinCoordinate '' D):=by
    have hcl:ξ∈closure ((fun z:𝔻=>(z:ℂ)) '' (P.finiteCoordinate '' D)):=by
      simpa only [image_image] using hξcl
    have hh:=disc_ideal_closure_klein ξ hξnorm hcl
    simpa only [image_image,_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.kleinCoordinate] using hh
  obtain ⟨N,hN,hξN,hf⟩:=hD.ordinary_klein_neighborhood_finite ξ hξnorm hOrd
  let U:H→Set ℂ:=fun g=>P.kleinCoordinate '' (g•D)
  let F:=hf.toFinset
  have hF (g:H) : g∈F ↔ (closure (U g)∩N).Nonempty:=Set.Finite.mem_toFinset _
  let B:=⋃g∈F.filter (fun g=>ξ∉closure (U g)),closure (U g)
  have hBc:IsClosed B:=isClosed_biUnion_finset (fun _ _=>isClosed_closure)
  have hξB:ξ∉B:=by
    intro hh
    obtain ⟨g,hg,hξg⟩:=mem_iUnion₂.mp hh
    exact (Finset.mem_filter.mp hg).2 hξg
  let O:=N∩Bᶜ
  have hOo:IsOpen O:=hN.inter hBc.isOpen_compl
  have hξO:ξ∈O:=⟨hξN,hξB⟩
  let s:=F.filter (fun g=>ξ∈closure (U g))
  have hs (g:H) : g∈s ↔ g∈F∧ξ∈closure (U g):=Finset.mem_filter
  have hUone:U 1=P.kleinCoordinate '' D:=by simp only [U,one_smul]
  have h1s:(1:H)∈s:=by
    apply (hs 1).mpr
    refine ⟨(hF 1).mpr ⟨ξ,?_,hξN⟩,?_⟩ <;> simpa only [hUone] using hξK
  have hDo:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hUc (g:H) : Convex ℝ (U g):=by
    change Convex ℝ ((fun x=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x))
      '' (g•D))
    rw [←image_image]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp (hD.smul_convex g)
  have hUo (g:H) : IsOpen (U g):=
    P.kleinCoordinate_isOpenEmbedding.isOpenMap _ ((Homeomorph.smul g).isOpenMap D hDo)
  have hUn (g:H) : (U g).Nonempty:=(hDn.image (fun x=>g•x)).image P.kleinCoordinate
  have hUd (g:H) (_hg:g∈s) (hg:g≠1) : Disjoint (U 1) (U g):=by
    rw [hUone]
    exact (hD.locallyFinite.fundamental.disjoint_image hg).symm.image
      P.kleinCoordinate_isOpenEmbedding.injective.injOn (subset_univ _) (subset_univ _)
  have hUb (g:H) : U g⊆Metric.ball (0:ℂ) 1:=by
    rintro _ ⟨x,hx,rfl⟩
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact mem_range_self (P.finiteCoordinate x)
  have hcover:O∩Metric.ball (0:ℂ) 1⊆⋃g∈s,closure (U g):=by
    rintro z ⟨hzO,hzball⟩
    have hzrange:z∈range P.kleinCoordinate:=by
      change z∈range (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ∘ P.finiteCoordinate)
      rw [range_comp,P.finiteCoordinate.surjective.range_eq,image_univ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
      exact hzball
    obtain ⟨x,rfl⟩:=hzrange
    have hcov:=hD.locallyFinite.fundamental.closure_cover
    have hx:x∈⋃g:H,fuchsianDomainTile P D g:=by
      change x∈⋃g:H,(fun y:P.domain.carrier=>g•y) '' closure D
      rw [hcov]
      trivial
    obtain ⟨g,hg⟩:=mem_iUnion.mp hx
    have hxcl:P.kleinCoordinate x∈closure (U g):=
      P.klein_closed_tile_subset_closure D g ⟨x,hg,rfl⟩
    have hgF:g∈F:=(hF g).mpr ⟨P.kleinCoordinate x,hxcl,hzO.1⟩
    have hξg:ξ∈closure (U g):=by
      by_contra hnot
      exact hzO.2 (mem_iUnion₂.mpr ⟨g,Finset.mem_filter.mpr ⟨hgF,hnot⟩,hxcl⟩)
    exact mem_iUnion₂.mpr ⟨g,(hs g).mpr ⟨hgF,hξg⟩,hxcl⟩
  obtain ⟨n,hn,he⟩:=ordinary_finite_convex_relative_germ s 1 h1s U
    (fun g _=>hUc g) (fun g _=>hUo g) (fun g _=>hUn g) hUd
    (fun g _=>hUb g) ξ hξnorm (fun g hg=>(hs g).mp hg |>.2) O hOo hξO hcover
  rw [hUone] at he hn
  exact ⟨s,n,O,hOo,hξO,fun g hg=>(hs g).mp hg |>.2,hn,he⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A true separator between two nonempty disc tiles cannot have zero tangential derivative at their common ideal point. -/
theorem ordinary_support_tangent_normal_ne_zero (n ξ a b:ℂ) (hξ:‖ξ‖=1)
    (ha:‖a‖<1) (hb:‖b‖<1)
    (hl:inner ℝ n (a-ξ)<0) (hr:0 < inner ℝ n (b-ξ)) :
    n-(inner ℝ n ξ)•ξ≠0 := by
  intro he
  have hn:n=(inner ℝ n ξ)•ξ:=sub_eq_zero.mp he
  have hxa:inner ℝ ξ a<1:=lt_of_le_of_lt (real_inner_le_norm ξ a)
    (by simpa only [hξ,one_mul] using ha)
  have hxb:inner ℝ ξ b<1:=lt_of_le_of_lt (real_inner_le_norm ξ b)
    (by simpa only [hξ,one_mul] using hb)
  have hself:inner ℝ ξ ξ=1:=by rw [real_inner_self_eq_norm_sq,hξ,one_pow]
  have hl':inner ℝ n ξ*(inner ℝ ξ a-1)<0:=by
    conv_lhs at hl => rw [hn]
    simp only [real_inner_smul_left,inner_sub_right,hself] at hl
    nlinarith only [hl]
  have hr':0 < inner ℝ n ξ*(inner ℝ ξ b-1):=by
    conv_rhs at hr => rw [hn]
    simp only [real_inner_smul_left,inner_sub_right,hself] at hr
    nlinarith only [hr]
  have ht:0 < inner ℝ n ξ:=by
    by_contra hnot
    have hprod:=mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hnot) (sub_nonpos.mpr hxa.le)
    exact hl'.not_ge hprod
  have hprod:=mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr hxb.le)
  exact hr'.not_ge hprod

/-- The actual affine Klein cut pulls back to its genuine orthogonal circle inequality. -/
theorem ordinary_klein_support_cut_le (n ξ z:ℂ) :
    inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z-ξ)≤0 ↔
      2*inner ℝ n z-(inner ℝ n ξ)*(1+‖z‖^2)≤0 := by
  have hd:0 < 1+‖z‖^2:=by positivity
  have he:inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z-ξ)=
      (2*inner ℝ n z-(inner ℝ n ξ)*(1+‖z‖^2))/(1+‖z‖^2):=by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,←Complex.real_smul,inner_sub_right,real_inner_smul_right]
    field_simp [hd.ne']
  rw [he]
  rw [div_le_iff₀ hd,zero_mul]

/-- Along a true straight Euclidean direction at the ideal point, the genuine circle cut has the actual first-order tangential normal. -/
theorem ordinary_klein_support_cut_ray (n ξ v:ℂ) (hξ:‖ξ‖=1) (t:ℝ) (ht:0<t) :
    inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (ξ+t•v)-ξ)≤0 ↔
      2*(inner ℝ n v-(inner ℝ n ξ)*inner ℝ ξ v)-
        (inner ℝ n ξ)*t*‖v‖^2≤0 := by
  rw [ordinary_klein_support_cut_le]
  have hnorm:‖ξ+t•v‖^2=1+2*t*inner ℝ ξ v+t^2*‖v‖^2:=by
    rw [norm_add_sq_real,hξ,one_pow,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs]
    ring
  rw [hnorm,inner_add_right,real_inner_smul_right]
  have he:2*(inner ℝ n ξ+t*inner ℝ n v)-
      inner ℝ n ξ*(1+(1+2*t*inner ℝ ξ v+t^2*‖v‖^2))=
      t*(2*(inner ℝ n v-inner ℝ n ξ*inner ℝ ξ v)-inner ℝ n ξ*t*‖v‖^2):=by ring
  rw [he]
  simpa only [mul_zero] using (mul_le_mul_iff_right₀ ht (b:=
    2*(inner ℝ n v-(inner ℝ n ξ)*inner ℝ ξ v)-(inner ℝ n ξ)*t*‖v‖^2) (c:=0))

/-- Away from its two actual tangent directions a genuine ideal geodesic cut has stable angular membership. -/
theorem ordinary_klein_support_cut_eventual (n ξ v:ℂ) (hξ:‖ξ‖=1)
    (hne:inner ℝ n v-(inner ℝ n ξ)*inner ℝ ξ v≠0) :
    ∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
      (inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (ξ+t•v)-ξ)≤0 ↔
        inner ℝ n v-(inner ℝ n ξ)*inner ℝ ξ v<0) := by
  let q:=inner ℝ n v-(inner ℝ n ξ)*inner ℝ ξ v
  let F:ℝ→ℝ:=fun t=>2*q-(inner ℝ n ξ)*t*‖v‖^2
  have hc:Continuous F:=by fun_prop
  have h0:F 0=2*q:=by simp only [F,mul_zero,zero_mul,sub_zero]
  rcases lt_or_gt_of_ne hne with hneg|hpos
  · have hneg':F 0<0:=by rw [h0];exact mul_neg_of_pos_of_neg (by norm_num) hneg
    have hevent:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),F t<0:=
      nhdsWithin_le_nhds (hc.continuousAt.eventually (gt_mem_nhds hneg'))
    filter_upwards [self_mem_nhdsWithin,hevent] with t ht hFt
    rw [ordinary_klein_support_cut_ray n ξ v hξ t ht]
    exact iff_of_true hFt.le hneg
  · have hpos':0<F 0:=by rw [h0];exact mul_pos (by norm_num) hpos
    have hevent:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),0<F t:=
      nhdsWithin_le_nhds (hc.continuousAt.eventually (lt_mem_nhds hpos'))
    filter_upwards [self_mem_nhdsWithin,hevent] with t ht hFt
    rw [ordinary_klein_support_cut_ray n ξ v hξ t ht]
    exact iff_of_false (not_le_of_gt hFt) (not_lt_of_ge hpos.le)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The true inward half-circle is the eventual Euclidean radial trace of the actual closed unit disc. -/
theorem ordinary_unitDisc_cut_eventual (ξ:ℂ) (hξ:‖ξ‖=1) (u:Circle)
    (hne:inner ℝ ξ (u:ℂ)≠0) :
    ∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
      (‖ξ+t•(u:ℂ)‖≤1 ↔ inner ℝ ξ (u:ℂ)<0) := by
  let F:ℝ→ℝ:=fun t=>2*inner ℝ ξ (u:ℂ)+t
  have hc:Continuous F:=continuous_const.add continuous_id
  have hnorm (t:ℝ) : ‖ξ+t•(u:ℂ)‖^2=1+t*(2*inner ℝ ξ (u:ℂ)+t):=by
    rw [norm_add_sq_real,hξ,one_pow,real_inner_smul_right,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs,Circle.norm_coe,one_pow,mul_one]
    ring
  rcases lt_or_gt_of_ne hne with hneg|hpos
  · have he:F 0<0:=by dsimp only [F];linarith
    have hE:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),F t<0:=
      nhdsWithin_le_nhds (hc.continuousAt.eventually (gt_mem_nhds he))
    filter_upwards [self_mem_nhdsWithin,hE] with t ht hFt
    have hs:=mul_neg_of_pos_of_neg ht hFt
    have hnorm':‖ξ+t•(u:ℂ)‖≤1:=by nlinarith [hnorm t,norm_nonneg (ξ+t•(u:ℂ))]
    exact iff_of_true hnorm' hneg
  · have he:0<F 0:=by dsimp only [F];linarith
    have hE:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),0<F t:=
      nhdsWithin_le_nhds (hc.continuousAt.eventually (lt_mem_nhds he))
    filter_upwards [self_mem_nhdsWithin,hE] with t ht hFt
    have hs:=mul_pos ht hFt
    have hnorm':¬‖ξ+t•(u:ℂ)‖≤1:=by
      intro hh
      have hh0:=norm_nonneg (ξ+t•(u:ℂ))
      nlinarith [hnorm t]
    exact iff_of_false hnorm' (not_lt_of_ge hpos.le)

/-- The actual finite circle inequalities have stable membership along almost every genuine ideal ray direction. -/
theorem ordinary_finite_cut_point_eventual_ae {ι:Type*} [Finite ι] (ξ:ℂ) (hξ:‖ξ‖=1)
    (n:ι→ℂ) (hn:∀i,n i-(inner ℝ (n i) ξ)•ξ≠0) :
    ∀ᵐu:Circle ∂polygonDirectionMeasure,∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
      ((‖ξ+t•(u:ℂ)‖≤1 ∧ ∀i,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
        (ξ+t•(u:ℂ))-ξ)≤0) ↔
        inner ℝ ξ (u:ℂ)<0 ∧
          ∀i,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0) := by
  have hξne:ξ≠0:=by intro h;rw [h,norm_zero] at hξ;norm_num at hξ
  have hA:∀ᵐu:Circle ∂polygonDirectionMeasure,inner ℝ ξ (u:ℂ)≠0:=by
    have hz:polygonDirectionMeasure {u:Circle | inner ℝ (u:ℂ) ξ=0}=0:=
      (finite_circle_orthogonal ξ hξne).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with u hu
    change inner ℝ (u:ℂ) ξ≠0 at hu
    simpa only [real_inner_comm] using hu
  have hB:∀ᵐu:Circle ∂polygonDirectionMeasure,
      ∀i,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)≠0:=by
    apply ae_all_iff.mpr
    intro i
    have hz:polygonDirectionMeasure {u:Circle | inner ℝ (u:ℂ) (n i-(inner ℝ (n i) ξ)•ξ)=0}=0:=
      (finite_circle_orthogonal _ (hn i)).measure_zero _
    have he:∀u:Circle,inner ℝ (u:ℂ) (n i-(inner ℝ (n i) ξ)•ξ)=
        inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ):=by
      intro u
      rw [inner_sub_right,real_inner_smul_right,real_inner_comm (u:ℂ) (n i),
        real_inner_comm (u:ℂ) ξ]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with u hu
    change inner ℝ (u:ℂ) (n i-(inner ℝ (n i) ξ)•ξ)≠0 at hu
    rw [he] at hu
    exact hu
  filter_upwards [hA,hB] with u huξ hun
  have hball:=ordinary_unitDisc_cut_eventual ξ hξ u huξ
  have hcuts:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),∀i,
      (inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (ξ+t•(u:ℂ))-ξ)≤0 ↔
        inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0):=
    Filter.eventually_all.mpr (fun i=>ordinary_klein_support_cut_eventual (n i) ξ (u:ℂ) hξ (hun i))
  have hE:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
      ((‖ξ+t•(u:ℂ)‖≤1 ∧ ∀i,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
        (ξ+t•(u:ℂ))-ξ)≤0) ↔
        (inner ℝ ξ (u:ℂ)<0 ∧
          ∀i,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0)):=by
    filter_upwards [hball,hcuts] with t htB htC
    exact and_congr htB (forall_congr' htC)
  exact hE

/-- The actual local directions of a finite family of true ideal geodesic cuts agree almost everywhere with its inward tangent cone. -/
theorem ordinary_finite_cut_directions_ae {ι:Type*} [Finite ι] (ξ:ℂ) (hξ:‖ξ‖=1)
    (n:ι→ℂ) (hn:∀i,n i-(inner ℝ (n i) ξ)•ξ≠0) :
    ∀ᵐu:Circle ∂polygonDirectionMeasure,
      (u∈_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
        {z:ℂ | ‖z‖≤1 ∧ ∀i,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z-ξ)≤0} ξ ↔
        inner ℝ ξ (u:ℂ)<0 ∧
          ∀i,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0) := by
  filter_upwards [ordinary_finite_cut_point_eventual_ae ξ hξ n hn] with u hu
  change (∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
    ‖ξ+t•(u:ℂ)‖≤1 ∧ ∀i,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      (ξ+t•(u:ℂ))-ξ)≤0) ↔ _
  rw [eventually_congr hu]
  exact eventually_const

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual Euclidean local angle of the original polygon at its ideal point, measured from the original closed region germ. -/
def fuchsianPolygonEuclideanIdealAngle {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (ξ:ℂ) : ℝ:=
  _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (closure ((fun
    x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) ξ

/-- Actual Euclidean closure and actual closed Klein closure describe the same original finite-or-ideal points. -/
theorem fuchsianPolygon_euclideanClosure_klein_iff {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (z:ℂ) :
    z∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D) ↔
      ‖z‖≤1 ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈closure (P.kleinCoordinate '' D) := by
  let S:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)
  have hc:Topology.IsClosedEmbedding (fun p:𝕔𝔻=>(p:ℂ)):=
    Complex.UnitClosedDisc.continuous_coe.isClosedEmbedding Complex.UnitClosedDisc.isEmbedding_coe.injective
  have hPlane:(fun p:𝕔𝔻=>(p:ℂ)) '' S=
      closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D):=by
    dsimp only [S,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure]
    rw [←hc.closure_image_eq,image_image,image_image]
    rfl
  have hKlein:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' S=closure (P.kleinCoordinate '' D):=by
    dsimp only [S,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
    rfl
  constructor
  · intro hz
    obtain ⟨p,hp,hpz⟩:=hPlane.symm ▸ hz
    refine ⟨hpz ▸ p.norm_le_one,?_⟩
    rw [←hKlein]
    refine ⟨p,hp,?_⟩
    change (p:ℂ)=z at hpz
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (p:ℂ)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z
    rw [hpz]
  · rintro ⟨hzn,hzK⟩
    let p:𝕔𝔻:=Complex.UnitClosedDisc.mk z hzn
    have hpK:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' S:=by
      rw [hKlein]
      exact hzK
    obtain ⟨q,hq,hqp⟩:=hpK
    have he:q=p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective hqp
    rw [←hPlane]
    exact ⟨p,he ▸ hq,rfl⟩

/-- The original closed polygon has a true finite polynomial-inequality germ at every ordinary ideal point. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_polynomial_germ
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃ (s:Finset H) (n:{g // g∈s∧g≠1}→ℂ),
      (∀i,n i-(inner ℝ (n i) ξ)•ξ≠0) ∧
      ∀ᶠz:ℂ in 𝓝 ξ,
        (z∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D) ↔
          (‖z‖≤1 ∧ ∀i,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z-ξ)≤0)) := by
  obtain ⟨s,n,N,hN,hξN,_hs,hn,he⟩:=hD.ordinary_ideal_finite_halfplanes ξ hξ hOrd
  have hξnorm:‖ξ‖=1:=((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  let I:={g:H // g∈s∧g≠1}
  let : Finite I:=Finite.of_injective (fun i:I=>(⟨i.val,i.property.1⟩:s)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun i:s=>i.val) h))
  have hnorm (x:P.domain.carrier) : ‖P.kleinCoordinate x‖<1:=by
    apply mem_ball_zero_iff.mp
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact mem_range_self (P.finiteCoordinate x)
  obtain ⟨w,hw⟩:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hnq (i:I) : n i-(inner ℝ (n i) ξ)•ξ≠0:=by
    apply ordinary_support_tangent_normal_ne_zero (n i) ξ (P.kleinCoordinate w)
      (P.kleinCoordinate (i.val•w)) hξnorm (hnorm w) (hnorm (i.val•w))
    · exact (hn i).2.1 _ ⟨w,hw,rfl⟩
    · exact (hn i).2.2 _ ⟨i.val•w,⟨w,hw,rfl⟩,rfl⟩
  have hk:Continuous _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula:=by
    have hd:∀z:ℂ,1+‖z‖^2≠0:=fun z=>ne_of_gt (by positivity)
    exact (Complex.continuous_ofReal.comp
      (continuous_const.div (continuous_const.add (continuous_norm.pow 2)) hd)).mul continuous_id
  have hξfixed:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula ξ=ξ:=by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,hξnorm,one_pow]
    norm_num
  have hNe:∀ᶠz:ℂ in 𝓝 ξ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈N:=
    hk.continuousAt.eventually (hN.mem_nhds (hξfixed.symm ▸ hξN))
  have hGerm:∀ᶠz:ℂ in 𝓝 ξ,
      (z∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D) ↔
        (‖z‖≤1 ∧ ∀i:I,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z-ξ)≤0)):=by
    filter_upwards [hNe] with z hzN
    rw [fuchsianPolygon_euclideanClosure_klein_iff]
    by_cases hzn:‖z‖≤1
    · have hzB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈Metric.closedBall (0:ℂ) 1:=
        mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_mem_closedDisc
          (Complex.UnitClosedDisc.mk z hzn))
      constructor
      · rintro ⟨_,hzK⟩
        have hh:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈closure (P.kleinCoordinate ''
          D)∩N∩Metric.closedBall (0:ℂ) 1:=
          ⟨⟨hzK,hzN⟩,hzB⟩
        rw [he] at hh
        exact ⟨hzn,hh.1.1⟩
      · rintro ⟨_,hcut⟩
        have hh:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈{z:ℂ | ∀i:I,inner ℝ (n i)
          (z-ξ)≤0}∩N∩Metric.closedBall (0:ℂ) 1:=
          ⟨⟨hcut,hzN⟩,hzB⟩
        rw [←he] at hh
        exact ⟨hzn,hh.1.1⟩
    · exact iff_of_false (fun h=>hzn h.1) (fun h=>hzn h.1)
  exact ⟨s,n,hnq,hGerm⟩

/-- Every ordinary ideal angle of the original polygon is the genuine angular measure of the tangent cone derived from its actual finite local tile star. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_angle_tangent_cone
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃ (s:Finset H) (n:{g // g∈s∧g≠1}→ℂ),
      (∀i,n i-(inner ℝ (n i) ξ)•ξ≠0) ∧
      fuchsianPolygonEuclideanIdealAngle P D ξ=
        2*Real.pi*(polygonDirectionMeasure {u:Circle | inner ℝ ξ (u:ℂ)<0 ∧
          ∀i,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0}).toReal := by
  obtain ⟨s,n,hnq,hGerm⟩:=hD.ordinary_ideal_polynomial_germ ξ hξ hOrd
  have hξnorm:‖ξ‖=1:=((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  let I:={g:H // g∈s∧g≠1}
  let : Finite I:=Finite.of_injective (fun i:I=>(⟨i.val,i.property.1⟩:s)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun i:s=>i.val) h))
  have hdir:=_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections_congr_germ hGerm
  have hAE:=ordinary_finite_cut_directions_ae ξ hξnorm n hnq
  have hmeasure:polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
      {z:ℂ | ‖z‖≤1 ∧ ∀i:I,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z-ξ)≤0} ξ)=
      polygonDirectionMeasure {u:Circle | inner ℝ ξ (u:ℂ)<0 ∧
        ∀i:I,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0}:=
    by
      apply measure_congr
      filter_upwards [hAE] with u hu
      apply propext
      exact hu
  refine ⟨s,n,hnq,?_⟩
  unfold fuchsianPolygonEuclideanIdealAngle _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle
  exact congrArg (fun r:ENNReal=>2*Real.pi*r.toReal)
    ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure hdir).trans hmeasure)

/-- Membership in the actual original closed polygon stabilizes along almost every genuine Euclidean direction at an ordinary ideal point. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_ray_membership_eventual_ae
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∀ᵐu:Circle ∂polygonDirectionMeasure,∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
      ((ξ+t•(u:ℂ)∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) ↔
        u∈_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
          (closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) ξ) := by
  obtain ⟨s,n,hnq,hGerm⟩:=hD.ordinary_ideal_polynomial_germ ξ hξ hOrd
  have hξnorm:‖ξ‖=1:=((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  let I:={g:H // g∈s∧g≠1}
  let : Finite I:=Finite.of_injective (fun i:I=>(⟨i.val,i.property.1⟩:s)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun i:s=>i.val) h))
  have hdir:=_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections_congr_germ hGerm
  have hPoint:=ordinary_finite_cut_point_eventual_ae ξ hξnorm n hnq
  have hAngle:=ordinary_finite_cut_directions_ae ξ hξnorm n hnq
  filter_upwards [hPoint,hAngle] with u huP huA
  have hAlong:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
      ((ξ+t•(u:ℂ)∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) ↔
        (‖ξ+t•(u:ℂ)‖≤1 ∧ ∀i:I,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
          (ξ+t•(u:ℂ))-ξ)≤0)):=
    (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanRay_tendsto ξ u).eventually hGerm
  have hDirA:(u∈_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
      (closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) ξ) ↔
        inner ℝ ξ (u:ℂ)<0 ∧
          ∀i:I,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0:=by
    rw [hdir]
    exact huA
  filter_upwards [hAlong,huP] with t htA htP
  exact htA.trans (htP.trans hDirA.symm)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance ordinaryIdealAnglesSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance ordinaryIdealAnglesSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- Translating the actual original selector does not change its orbit-selector property. -/
theorem IsFuchsianFundamentalSet.smul_selector {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {F:Set P.domain.carrier}
    (hF:IsFuchsianFundamentalSet P F) (g:H) : IsFuchsianFundamentalSet P (g•F) := by
  intro x
  obtain ⟨y,hy,hyuniq⟩:=hF x
  refine ⟨g•y,⟨⟨y,hy.1,rfl⟩,?_⟩,?_⟩
  · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul H P.domain.carrier g
    y).trans hy.2
  · rintro z ⟨⟨v,hv,hgv⟩,hz⟩
    change g•v=z at hgv
    have hq:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier v=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier x:=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul H P.domain.carrier g
        v).symm.trans (hgv ▸ hz)
    rw [hyuniq v ⟨hv,hq⟩] at hgv
    exact hgv.symm

/-- Every actual translated polygon is again a convex locally finite polygon for the same original action. -/
theorem IsConvexFuchsianPolygon.smul_polygon {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (g:H) : IsConvexFuchsianPolygon P (g•D) := by
  have hf:=hD.locallyFinite.fundamental
  have hcl:closure (g•D)=g•closure D:=((Homeomorph.smul g).image_closure D).symm
  have hfnew:IsFuchsianFundamentalDomain P (g•D):=by
    refine ⟨(Homeomorph.smul g).isOpenMap _ hf.isOpen,
      (Homeomorph.smul g).isConnected_image.mpr hf.isConnected,?_,?_⟩
    · obtain ⟨F,hF,hDF,hFC⟩:=hf.exists_fundamentalSet
      refine ⟨g•F,_root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalSet.smul_selector (P:=P) hF
        g,Set.smul_set_mono hDF,?_⟩
      rw [hcl]
      exact Set.smul_set_mono hFC
    · have he:frontier (g•D)=(fun x:P.domain.carrier=>g•x) '' frontier D:=
        ((Homeomorph.smul g).image_frontier D).symm
      rw [he,P.area_image g _ isClosed_frontier.measurableSet]
      exact hf.null_frontier
  refine ⟨⟨hfnew,?_⟩,hD.smul_convex g⟩
  intro K hK
  have ht (h:H) : fuchsianDomainTile P (g•D) h=fuchsianDomainTile P D (h*g):=by
    change h•closure (g•D)=(h*g)•closure D
    rw [hcl,mul_smul]
  let S:={h:H | (fuchsianDomainTile P D h∩K).Nonempty}
  have hS:S.Finite:=hD.locallyFinite.compact_hits_finite K hK
  apply (hS.image (fun h:H=>h*g⁻¹)).subset
  intro h hh
  refine ⟨h*g,?_,?_⟩
  · change (fuchsianDomainTile P D (h*g)∩K).Nonempty
    rw [←ht h]
    exact hh
  · simp only [mul_inv_cancel_right]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The ordinary ideal star consists of finitely many actual incident closed tiles and covers a genuine relative neighborhood. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_klein_finite_star
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃ (s:Finset H) (N:Set ℂ), IsOpen N ∧ ξ∈N ∧
      (∀g:H,g∈s ↔ ξ∈closure (P.kleinCoordinate '' (g•D))) ∧
      N∩Metric.ball (0:ℂ) 1⊆⋃g∈s,closure (P.kleinCoordinate '' (g•D)) := by
  classical
  have hξnorm:‖ξ‖=1:=((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  obtain ⟨N,hN,hξN,hf⟩:=hD.ordinary_klein_neighborhood_finite ξ hξnorm hOrd
  let U:H→Set ℂ:=fun g=>P.kleinCoordinate '' (g•D)
  let F:=hf.toFinset
  have hF (g:H) : g∈F ↔ (closure (U g)∩N).Nonempty:=Set.Finite.mem_toFinset _
  let B:=⋃g∈F.filter (fun g=>ξ∉closure (U g)),closure (U g)
  have hBc:IsClosed B:=isClosed_biUnion_finset (fun _ _=>isClosed_closure)
  have hξB:ξ∉B:=by
    intro hh
    obtain ⟨g,hg,hξg⟩:=mem_iUnion₂.mp hh
    exact (Finset.mem_filter.mp hg).2 hξg
  let O:=N∩Bᶜ
  have hOo:IsOpen O:=hN.inter hBc.isOpen_compl
  have hξO:ξ∈O:=⟨hξN,hξB⟩
  let s:=F.filter (fun g=>ξ∈closure (U g))
  have hs (g:H) : g∈s ↔ g∈F∧ξ∈closure (U g):=Finset.mem_filter
  have hcover:O∩Metric.ball (0:ℂ) 1⊆⋃g∈s,closure (U g):=by
    rintro z ⟨hzO,hzball⟩
    have hzrange:z∈range P.kleinCoordinate:=by
      change z∈range (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ∘ P.finiteCoordinate)
      rw [range_comp,P.finiteCoordinate.surjective.range_eq,image_univ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
      exact hzball
    obtain ⟨x,rfl⟩:=hzrange
    have hcov:=hD.locallyFinite.fundamental.closure_cover
    have hx:x∈⋃g:H,fuchsianDomainTile P D g:=by
      change x∈⋃g:H,(fun y:P.domain.carrier=>g•y) '' closure D
      rw [hcov]
      trivial
    obtain ⟨g,hg⟩:=mem_iUnion.mp hx
    have hxcl:P.kleinCoordinate x∈closure (U g):=
      P.klein_closed_tile_subset_closure D g ⟨x,hg,rfl⟩
    have hgF:g∈F:=(hF g).mpr ⟨P.kleinCoordinate x,hxcl,hzO.1⟩
    have hξg:ξ∈closure (U g):=by
      by_contra hnot
      exact hzO.2 (mem_iUnion₂.mpr ⟨g,Finset.mem_filter.mpr ⟨hgF,hnot⟩,hxcl⟩)
    exact mem_iUnion₂.mpr ⟨g,(hs g).mpr ⟨hgF,hξg⟩,hxcl⟩
  refine ⟨s,O,hOo,hξO,?_,hcover⟩
  intro g
  constructor
  · exact fun hg=>(hs g).mp hg |>.2
  · intro hg
    exact (hs g).mpr ⟨(hF g).mpr ⟨ξ,hg,hξN⟩,hg⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Two actual disjoint convex Klein tiles have only finitely many common Euclidean directions at a shared ideal point. -/
theorem ordinary_klein_regions_common_directions_finite {U V:Set ℂ} (ξ:ℂ) (hξ:‖ξ‖=1)
    (hUc:Convex ℝ U) (hUo:IsOpen U) (hUn:U.Nonempty)
    (hVc:Convex ℝ V) (hVo:IsOpen V) (hVn:V.Nonempty) (hd:Disjoint U V)
    (hUb:U⊆Metric.ball (0:ℂ) 1) (hVb:V⊆Metric.ball (0:ℂ) 1)
    (hξU:ξ∈closure U) (hξV:ξ∈closure V) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections {z:ℂ |
      ‖z‖≤1∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈closure U} ξ ∩
      _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections {z:ℂ | ‖z‖≤1∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈closure V} ξ).Finite := by
  obtain ⟨n,t,_hn,hl,hr⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator hUc hUo hUn hVc hVo hVn hd
  have hbase:inner ℝ n ξ=t:=_root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hl hr ⟨hξU,hξV⟩
  have hl':∀z∈U,inner ℝ n (z-ξ)<0:=by
    intro z hz
    rw [inner_sub_right,hbase]
    exact sub_neg.mpr (hl z hz)
  have hr':∀z∈V,0 < inner ℝ n (z-ξ):=by
    intro z hz
    rw [inner_sub_right,hbase]
    exact sub_pos.mpr (hr z hz)
  obtain ⟨a,ha⟩:=hUn
  obtain ⟨b,hb⟩:=hVn
  have hqn:=ordinary_support_tangent_normal_ne_zero n ξ a b hξ
    (mem_ball_zero_iff.mp (hUb ha)) (mem_ball_zero_iff.mp (hVb hb)) (hl' a ha) (hr' b hb)
  have hclU:∀z∈closure U,inner ℝ n (z-ξ)≤0:=by
    exact fun z hz=>(closure_minimal (fun w hw=>(hl' w hw).le)
      (isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const)) hz
  have hclV:∀z∈closure V,inner ℝ (-n) (z-ξ)≤0:=by
    intro z hz
    have hneg:∀w∈V,inner ℝ (-n) (w-ξ)≤0:=by
      intro w hw
      rw [inner_neg_left]
      exact neg_nonpos.mpr (hr' w hw).le
    have hC:IsClosed {w:ℂ | inner ℝ (-n) (w-ξ)≤0}:=
      isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const
    exact closure_minimal (s:=V) (t:={w:ℂ | inner ℝ (-n) (w-ξ)≤0}) hneg hC hz
  apply (finite_circle_orthogonal (n-(inner ℝ n ξ)•ξ) hqn).subset
  rintro u ⟨hu,hv⟩
  by_contra hnot
  change inner ℝ (u:ℂ) (n-(inner ℝ n ξ)•ξ)≠0 at hnot
  change ∀ᶠr:ℝ in 𝓝[>] (0:ℝ), ‖ξ+r•(u:ℂ)‖≤1∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (ξ+r•(u:ℂ))∈closure U at hu
  change ∀ᶠr:ℝ in 𝓝[>] (0:ℝ), ‖ξ+r•(u:ℂ)‖≤1∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (ξ+r•(u:ℂ))∈closure V at hv
  have hq:inner ℝ n (u:ℂ)-(inner ℝ n ξ)*inner ℝ ξ (u:ℂ)≠0:=by
    simpa only [inner_sub_right,real_inner_smul_right,real_inner_comm (u:ℂ) n,
      real_inner_comm (u:ℂ) ξ] using hnot
  have hqn':inner ℝ (-n) (u:ℂ)-(inner ℝ (-n) ξ)*inner ℝ ξ (u:ℂ)≠0:=by
    simp only [inner_neg_left]
    intro h
    apply hq
    linarith
  have he:=ordinary_klein_support_cut_eventual n ξ (u:ℂ) hξ hq
  have he':=ordinary_klein_support_cut_eventual (-n) ξ (u:ℂ) hξ hqn'
  obtain ⟨r,⟨⟨huR,hvR⟩,heR⟩,heR'⟩:=(((hu.and hv).and he).and he').exists
  have hlt:inner ℝ n (u:ℂ)-(inner ℝ n ξ)*inner ℝ ξ (u:ℂ)<0:=
    heR.mp (hclU _ huR.2)
  have hlt':inner ℝ (-n) (u:ℂ)-(inner ℝ (-n) ξ)*inner ℝ ξ (u:ℂ)<0:=
    heR'.mp (hclV _ hvR.2)
  simp only [inner_neg_left] at hlt'
  linarith

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The real Euclidean ordinary star is finite, contains exactly the incident tiles, and covers a true inward neighborhood. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_euclidean_finite_star
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃ (s:Finset H) (O:Set ℂ), IsOpen O ∧ ξ∈O ∧
      (∀g:H,g∈s ↔ ξ∈fuchsianPolygonIdealBoundary P (g•D)) ∧
      O∩Metric.ball (0:ℂ) 1⊆⋃g∈s,
        closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' (g•D)) := by
  obtain ⟨s,N,hN,hξN,hs,hcover⟩:=hD.ordinary_ideal_klein_finite_star ξ hξ hOrd
  have hξnorm:‖ξ‖=1:=((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  have hk:Continuous _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula:=by
    have hd:∀z:ℂ,1+‖z‖^2≠0:=fun z=>ne_of_gt (by positivity)
    exact (Complex.continuous_ofReal.comp
      (continuous_const.div (continuous_const.add (continuous_norm.pow 2))
        hd)).mul continuous_id
  have hξfixed:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula ξ=ξ:=by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,hξnorm,one_pow]
    norm_num
  refine ⟨s,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula ⁻¹' N,hN.preimage hk,?_,?_,?_⟩
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula ξ∈N
    rw [hξfixed]
    exact hξN
  · intro g
    rw [hs g,mem_fuchsianPolygonIdealBoundary,fuchsianPolygon_euclideanClosure_klein_iff,
      hξfixed]
    exact ⟨fun h=>⟨⟨hξnorm.le,h⟩,hξnorm⟩,fun h=>h.1.2⟩
  · rintro z ⟨hzN,hzn⟩
    have hzb:‖z‖<1:=mem_ball_zero_iff.mp hzn
    have hzK:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈N∩Metric.ball (0:ℂ) 1:=
      ⟨hzN,mem_ball_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_mem_disc
        (Complex.UnitDisc.mk z hzb))⟩
    obtain ⟨g,hgs,hgK⟩:=mem_iUnion₂.mp (hcover hzK)
    exact mem_iUnion₂.mpr ⟨g,hgs,
      (fuchsianPolygon_euclideanClosure_klein_iff P (g•D) z).mpr ⟨hzb.le,hgK⟩⟩

/-- Actual local directions at an ordinary ideal corner are null measurable, as derived from their finite genuine support cone. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_directions_nullMeasurable
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    NullMeasurableSet (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
      (closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) ξ) polygonDirectionMeasure := by
  obtain ⟨s,n,hnq,hGerm⟩:=hD.ordinary_ideal_polynomial_germ ξ hξ hOrd
  have hξnorm:‖ξ‖=1:=((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  let I:={g:H // g∈s∧g≠1}
  let : Finite I:=Finite.of_injective (fun i:I=>(⟨i.val,i.property.1⟩:s)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun i:s=>i.val) h))
  let C:Set Circle:={u | inner ℝ ξ (u:ℂ)<0∧
    ∀i:I,inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0}
  have hCeq:C={u:Circle | inner ℝ ξ (u:ℂ)<0}∩
      ⋂i:I,{u:Circle | inner ℝ (n i) (u:ℂ)-(inner ℝ (n i) ξ)*inner ℝ ξ (u:ℂ)<0}:=by
    ext u
    simp only [C,mem_ofPred_eq,mem_inter_iff,mem_iInter]
  have hCm:MeasurableSet C:=by
    rw [hCeq]
    apply MeasurableSet.inter
    · exact (isOpen_lt (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
    · apply MeasurableSet.iInter
      intro i
      exact (isOpen_lt ((continuous_const.inner continuous_subtype_val).sub
        (continuous_const.mul (continuous_const.inner continuous_subtype_val))) continuous_const).measurableSet
  have hdir:=_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections_congr_germ hGerm
  have hAE:=ordinary_finite_cut_directions_ae ξ hξnorm n hnq
  apply hCm.nullMeasurableSet.congr
  filter_upwards [hAE] with u hu
  apply propext
  rw [hdir]
  exact hu.symm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance ordinaryIdealTraceSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance ordinaryIdealTraceSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- A genuinely inward Euclidean direction enters the actual open disc. -/
theorem ordinary_unitDisc_inward_ray_eventually (ξ:ℂ) (hξ:‖ξ‖=1) (u:Circle)
    (hu:inner ℝ ξ (u:ℂ)<0) :
    ∀ᶠt:ℝ in 𝓝[>] (0:ℝ),‖ξ+t•(u:ℂ)‖<1 := by
  have hc:Continuous (fun t:ℝ=>2*inner ℝ ξ (u:ℂ)+t):=continuous_const.add continuous_id
  have hneg:2*inner ℝ ξ (u:ℂ)+(0:ℝ)<0:=by linarith
  have he:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),2*inner ℝ ξ (u:ℂ)+t<0:=
    nhdsWithin_le_nhds (hc.continuousAt.eventually (gt_mem_nhds hneg))
  filter_upwards [self_mem_nhdsWithin,he] with t ht hneg
  have hn:‖ξ+t•(u:ℂ)‖^2=1+t*(2*inner ℝ ξ (u:ℂ)+t):=by
    rw [norm_add_sq_real,hξ,one_pow,real_inner_smul_right,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs,Circle.norm_coe,one_pow,mul_one]
    ring
  have hmul:=mul_neg_of_pos_of_neg ht hneg
  nlinarith [norm_nonneg (ξ+t•(u:ℂ))]

/-- At an ordinary ideal point, the actual angles of all incident original closed tiles add to a straight angle. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_incident_angle_sum
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ξ:ℂ) (hξ:ξ∈fuchsianPolygonIdealBoundary P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃s:Finset H,(∀g:H,g∈s ↔ ξ∈fuchsianPolygonIdealBoundary P (g•D)) ∧
      ∑g∈s,fuchsianPolygonEuclideanIdealAngle P (g•D) ξ=Real.pi := by
  classical
  obtain ⟨s,O,hO,hξO,hs,hCover⟩:=hD.ordinary_ideal_euclidean_finite_star ξ hξ hOrd
  let A:H→Set ℂ:=fun g=>closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' (g•D))
  let f:H→Set Circle:=fun g=>_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections (A g) ξ
  have hξnorm:‖ξ‖=1:=((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  have hξne:ξ≠0:=by intro h;rw [h,norm_zero] at hξnorm;norm_num at hξnorm
  have hInc (g:H) (hg:g∈s):ξ∈fuchsianPolygonIdealBoundary P (g•D):=(hs g).mp hg
  have hStable:∀ᵐu:Circle ∂polygonDirectionMeasure,∀g:s,
      ∀ᶠt:ℝ in 𝓝[>] (0:ℝ),(ξ+t•(u:ℂ)∈A g.val ↔ u∈f g.val):=by
    apply ae_all_iff.mpr
    intro g
    exact (hD.smul_polygon g.val).ordinary_ideal_ray_membership_eventual_ae ξ
      (hInc g.val g.property) hOrd
  have hNotTangent:∀ᵐu:Circle ∂polygonDirectionMeasure,inner ℝ ξ (u:ℂ)≠0:=by
    have hz:polygonDirectionMeasure {u:Circle | inner ℝ (u:ℂ) ξ=0}=0:=
      (finite_circle_orthogonal ξ hξne).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with u hu
    change inner ℝ (u:ℂ) ξ≠0 at hu
    simpa only [real_inner_comm] using hu
  have hUnion:(⋃g∈s,f g) =ᵐ[polygonDirectionMeasure]
      {u:Circle | 0 ≤ inner ℝ (u:ℂ) (-ξ)}:=by
    filter_upwards [hStable,hNotTangent] with u hu hutan
    apply propext
    have hIff:((u∈⋃g∈s,f g) ↔ inner ℝ ξ (u:ℂ)<0):=by
      constructor
      · intro hum
        obtain ⟨g,hgs,hug⟩:=mem_iUnion₂.mp hum
        have hRay:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),ξ+t•(u:ℂ)∈A g:=by
          filter_upwards [hu ⟨g,hgs⟩] with t ht
          exact ht.mpr hug
        have hUnit:=ordinary_unitDisc_cut_eventual ξ hξnorm u hutan
        obtain ⟨t,htA,htU⟩:=(hRay.and hUnit).exists
        have hn:‖ξ+t•(u:ℂ)‖≤1:=
          ((fuchsianPolygon_euclideanClosure_klein_iff P (g•D) _).mp htA).1
        exact htU.mp hn
      · intro huin
        have hRayO:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),ξ+t•(u:ℂ)∈O:=
          (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanRay_tendsto ξ u).eventually (hO.mem_nhds hξO)
        have hRayB:=ordinary_unitDisc_inward_ray_eventually ξ hξnorm u huin
        have hAll:=Filter.eventually_all.mpr hu
        obtain ⟨t,⟨htO,htB⟩,htAll⟩:=((hRayO.and hRayB).and hAll).exists
        obtain ⟨g,hgs,hgA⟩:=mem_iUnion₂.mp (hCover ⟨htO,mem_ball_zero_iff.mpr htB⟩)
        exact mem_iUnion₂.mpr ⟨g,hgs,(htAll ⟨g,hgs⟩).mp hgA⟩
    change (u∈⋃g∈s,f g) ↔ 0 ≤ inner ℝ (u:ℂ) (-ξ)
    rw [hIff,inner_neg_right,neg_nonneg,real_inner_comm]
    exact lt_iff_le_and_ne.trans ⟨fun h=>h.1,fun h=>⟨h,by simpa only [real_inner_comm] using hutan⟩⟩
  have hNull (g:H) (hg:g∈s):NullMeasurableSet (f g) polygonDirectionMeasure:=
    (hD.smul_polygon g).ordinary_ideal_directions_nullMeasurable ξ (hInc g hg) hOrd
  have hDis:(s:Set H).Pairwise (fun g h=>polygonDirectionMeasure (f g∩f h)=0):=by
    intro g hg h hh hgh
    have hDo:=hD.locallyFinite.fundamental.isOpen
    have hDn:=hD.locallyFinite.fundamental.isConnected.nonempty
    have hKInc (g:H) (hg:g∈s):ξ∈closure (P.kleinCoordinate '' (g•D)):=by
      have hξg:=((mem_fuchsianPolygonIdealBoundary P (g•D) ξ).mp (hInc g hg)).1
      have hK:=(fuchsianPolygon_euclideanClosure_klein_iff P (g•D) ξ).mp hξg
      have hfix:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula ξ=ξ:=by simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,hξnorm,one_pow];norm_num
      exact hfix ▸ hK.2
    have hB (g:H):P.kleinCoordinate '' (g•D)⊆Metric.ball (0:ℂ) 1:=by
      rintro _ ⟨x,hx,rfl⟩
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
      exact mem_range_self (P.finiteCoordinate x)
    have hfin:=ordinary_klein_regions_common_directions_finite ξ hξnorm
      (hD.klein_smul_convex g)
      (P.kleinCoordinate_isOpenEmbedding.isOpenMap _ ((Homeomorph.smul g).isOpenMap _ hDo))
      ((hDn.image (fun x=>g•x)).image P.kleinCoordinate)
      (hD.klein_smul_convex h)
      (P.kleinCoordinate_isOpenEmbedding.isOpenMap _ ((Homeomorph.smul h).isOpenMap _ hDo))
      ((hDn.image (fun x=>h•x)).image P.kleinCoordinate)
      (hD.locallyFinite.fundamental.klein_images_disjoint hgh) (hB g) (hB h)
      (hKInc g hg) (hKInc h hh)
    have he (k:H):A k={z:ℂ | ‖z‖≤1∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z∈closure (P.kleinCoordinate '' (k•D))}:=by
      ext z
      exact fuchsianPolygon_euclideanClosure_klein_iff P (k•D) z
    change polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections (A g) ξ∩
      _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections (A h) ξ)=0
    rw [he g,he h]
    exact hfin.measure_zero _
  have hm:=measure_biUnion_finset₀ (μ:=polygonDirectionMeasure) (s:=s) (f:=f) hDis hNull
  have hUnionMeasure:=measure_congr hUnion
  have hAngle:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonDirectionMeasure_hemisphere (-ξ) (neg_ne_zero.mpr
    hξne)
  refine ⟨s,hs,?_⟩
  change (∑g∈s,2*Real.pi*(polygonDirectionMeasure (f g)).toReal)=Real.pi
  rw [←Finset.mul_sum,←ENNReal.toReal_sum (fun g hg=>measure_ne_top polygonDirectionMeasure _),←hm,
    hUnionMeasure]
  exact hAngle

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual normal and tangent form the genuine orthonormal coordinate frame at a unit ideal point. -/
theorem ordinary_circle_frame (ξ:ℂ) (hξ:‖ξ‖=1) (n:ℂ) :
    n=(inner ℝ n ξ)•ξ+(inner ℝ n (Complex.I*ξ))•(Complex.I*ξ) := by
  have hsq:ξ.re^2+ξ.im^2=1:=by
    have h:=Complex.sq_norm ξ
    rw [hξ,one_pow,Complex.normSq_apply] at h
    nlinarith
  have hr:=congrArg (fun r:ℝ=>n.re*r) hsq
  have hi:=congrArg (fun r:ℝ=>n.im*r) hsq
  apply Complex.ext <;> simp [Complex.inner,Complex.real_smul] <;> nlinarith [hr,hi]

/-- A true support separating two disc tiles has a nonzero derivative along the actual boundary circle. -/
theorem ordinary_tangent_coefficient_ne_zero (ξ:ℂ) (hξ:‖ξ‖=1) (n:ℂ)
    (hn:n-(inner ℝ n ξ)•ξ≠0) : inner ℝ n (Complex.I*ξ)≠0 := by
  intro hc
  apply hn
  have he:=ordinary_circle_frame ξ hξ n
  rw [hc,zero_smul,add_zero] at he
  exact sub_eq_zero.mpr he

/-- A literal rational circle path, used only for the ideal-boundary germ of the original polygon. -/
def ordinaryIdealCirclePath (ξ:ℂ) (t:ℝ) : ℂ:=
  ((1-t^2)/(1+t^2))•ξ+(2*t/(1+t^2))•(Complex.I*ξ)

theorem ordinaryIdealCirclePath_norm (ξ:ℂ) (hξ:‖ξ‖=1) (t:ℝ) :
    ‖ordinaryIdealCirclePath ξ t‖=1 := by
  have horth:inner ℝ ξ (Complex.I*ξ)=0:=by
    simp [Complex.inner,Complex.mul_re,Complex.mul_im]
    ring
  have hI:‖Complex.I*ξ‖=1:=by rw [norm_mul,Complex.norm_I,hξ,one_mul]
  have he:‖ordinaryIdealCirclePath ξ t‖^2=1:=by
    simp only [ordinaryIdealCirclePath,norm_add_sq_real,norm_smul,real_inner_smul_left,
      real_inner_smul_right,horth,hξ,hI,Real.norm_eq_abs,sq_abs,
      mul_zero,add_zero,mul_one]
    have hd:1+t^2≠0:=ne_of_gt (by positivity)
    field_simp [hd]
    ring
  nlinarith [norm_nonneg (ordinaryIdealCirclePath ξ t)]

theorem ordinaryIdealCirclePath_inner (ξ n:ℂ) (t:ℝ) :
    inner ℝ n (ordinaryIdealCirclePath ξ t-ξ)=
      2*t*(inner ℝ n (Complex.I*ξ)-(inner ℝ n ξ)*t)/(1+t^2) := by
  rw [ordinaryIdealCirclePath,inner_sub_right,inner_add_right,real_inner_smul_right,
    real_inner_smul_right]
  have hd:1+t^2≠0:=ne_of_gt (by positivity)
  field_simp [hd]
  ring

theorem ordinaryIdealCirclePath_continuous (ξ:ℂ) : Continuous (ordinaryIdealCirclePath ξ) := by
  have hd:∀t:ℝ,1+t^2≠0:=fun t=>ne_of_gt (by positivity)
  apply Continuous.add
  · exact ((continuous_const.sub (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 2)) hd).smul continuous_const
  · exact ((continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) hd).smul continuous_const

theorem ordinaryIdealCirclePath_zero (ξ:ℂ) : ordinaryIdealCirclePath ξ 0=ξ := by
  simp [ordinaryIdealCirclePath]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine separating circle cut cannot contain a full neighborhood of its ideal point on the boundary circle. -/
theorem ordinary_circle_support_not_nhds (ξ:ℂ) (hξ:‖ξ‖=1) (n:ℂ)
    (hn:n-(inner ℝ n ξ)•ξ≠0) :
    ¬∀ᶠt:ℝ in 𝓝 (0:ℝ),inner ℝ n (ordinaryIdealCirclePath ξ t-ξ)≤0 := by
  intro h
  let b:=inner ℝ n ξ
  let c:=inner ℝ n (Complex.I*ξ)
  let F:ℝ→ℝ:=fun t=>2*t*(c-b*t)/(1+t^2)
  have hF0:F 0=0:=by simp [F]
  have hLocal:IsLocalMax F 0:=by
    filter_upwards [h] with t ht
    rw [hF0]
    rw [ordinaryIdealCirclePath_inner] at ht
    exact ht
  have hDer:HasDerivAt F (2*c) 0:=by
    dsimp only [F]
    convert ((((hasDerivAt_id (0:ℝ)).const_mul 2).mul
      ((hasDerivAt_const 0 c).sub ((hasDerivAt_id 0).const_mul b))).div
      ((hasDerivAt_const 0 1).add ((hasDerivAt_id 0).pow 2)) (by norm_num)) using 1 <;> norm_num
    funext t
    rfl
  have hc:c=0:=by linarith [hLocal.hasDerivAt_eq_zero hDer]
  exact ordinary_tangent_coefficient_ne_zero ξ hξ n hn hc

/-- The actual free-side interior yields a genuine closed-disc germ for the original polygon. -/
theorem IsConvexFuchsianPolygon.ordinary_free_interior_closed_germ
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈interior (fuchsianPolygonIdealCircle P D))
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∀ᶠz:ℂ in 𝓝 (u:ℂ),
      (z∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D) ↔ ‖z‖≤1) := by
  have huE:(u:ℂ)∈fuchsianPolygonIdealBoundary P D:=show u∈fuchsianPolygonIdealCircle P D from interior_subset hu
  obtain ⟨s,n,hnq,hGerm⟩:=hD.ordinary_ideal_polynomial_germ (u:ℂ) huE hOrd
  let I:={g:H // g∈s∧g≠1}
  let γ:ℝ→Circle:=fun t=>⟨ordinaryIdealCirclePath (u:ℂ) t,
    mem_sphere_zero_iff_norm.mpr (ordinaryIdealCirclePath_norm (u:ℂ) u.norm_coe t)⟩
  have hγ:Continuous γ:=(ordinaryIdealCirclePath_continuous (u:ℂ)).subtype_mk _
  have hγ0:γ 0=u:=Subtype.ext (ordinaryIdealCirclePath_zero _)
  have hTrace:∀ᶠt:ℝ in 𝓝 (0:ℝ),γ t∈fuchsianPolygonIdealCircle P D:=by
    have hh:Tendsto γ (𝓝 (0:ℝ)) (𝓝 u):=hγ0 ▸ hγ.continuousAt.tendsto
    exact hh.eventually (mem_interior_iff_mem_nhds.mp hu)
  have hPath:Tendsto (ordinaryIdealCirclePath (u:ℂ)) (𝓝 (0:ℝ)) (𝓝 (u:ℂ)):=by
    simpa only [ordinaryIdealCirclePath_zero] using
      (ordinaryIdealCirclePath_continuous (u:ℂ)).continuousAt.tendsto (x:=(0:ℝ))
  have hAlong:=hPath.eventually hGerm
  have hEmpty:IsEmpty I:=by
    constructor
    intro i
    apply ordinary_circle_support_not_nhds (u:ℂ) u.norm_coe (n i) (hnq i)
    filter_upwards [hTrace,hAlong] with t htE htG
    have hzE:(ordinaryIdealCirclePath (u:ℂ) t)∈fuchsianPolygonIdealBoundary P D:=htE
    have hzCl:=((mem_fuchsianPolygonIdealBoundary P D _).mp hzE).1
    have hcut:inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (ordinaryIdealCirclePath
      (u:ℂ) t)-(u:ℂ))≤0:=
      (htG.mp hzCl).2 i
    have hfix:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (ordinaryIdealCirclePath (u:ℂ) t)=ordinaryIdealCirclePath (u:ℂ) t:=by
      simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,ordinaryIdealCirclePath_norm (u:ℂ)
        u.norm_coe t,one_pow]
      norm_num
    rw [hfix] at hcut
    exact hcut
  let : IsEmpty I:=hEmpty
  filter_upwards [hGerm] with z hz
  simpa only [IsEmpty.forall_iff,and_true] using hz

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A real closed-disc germ excludes every other genuine incident polygon tile. -/
theorem IsConvexFuchsianPolygon.ideal_closed_disc_germ_no_other_tile
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ξ:ℂ)
    (hGerm:∀ᶠz:ℂ in 𝓝 ξ,
      (z∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D) ↔ ‖z‖≤1))
    (g:H) (hg:ξ∈fuchsianPolygonIdealBoundary P (g•D)) : g=1 := by
  by_contra hgne
  have hcl:=((mem_fuchsianPolygonIdealBoundary P (g•D) ξ).mp hg).1
  obtain ⟨z,hzG,y,hy,hyz⟩:=(mem_closure_iff_nhds.mp hcl) _ hGerm
  have hyNorm:‖(P.finiteCoordinate y:ℂ)‖≤1:=(P.finiteCoordinate y).norm_lt_one.le
  have hyCl:(P.finiteCoordinate y:ℂ)∈closure
      ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D):=by
    apply (hyz ▸ hzG).mpr hyNorm
  have hF:Topology.IsEmbedding (fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)):=
    Complex.UnitDisc.isEmbedding_coe.comp P.finiteCoordinate.isEmbedding
  have hyD:y∈closure D:=by
    rw [hF.closure_eq_preimage_closure_image]
    exact hyCl
  exact Set.disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image_closure hgne) hy hyD

/-- The actual ordinary cycle of a free-side interior point is the literal singleton. -/
theorem IsConvexFuchsianPolygon.ordinary_free_interior_cycle_singleton
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈interior (fuchsianPolygonIdealCircle P D))
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    fuchsianPolygonIdealCycle P D ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)={((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} := by
  have huE:(u:ℂ)∈fuchsianPolygonIdealBoundary P D:=
    show u∈fuchsianPolygonIdealCircle P D from interior_subset hu
  have hGerm:=hD.ordinary_free_interior_closed_germ u hu hOrd
  ext ζ
  constructor
  · rintro ⟨⟨η,hη,rfl⟩,g,hg⟩
    change g•((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hg
    have hback:g⁻¹.val.val (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
      change g⁻¹•(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      rw [←hg,inv_smul_smul]
    have hξ:=P.idealBoundary_smul D g⁻¹ η (u:ℂ) hη hback
    have hInv:g⁻¹=1:=hD.ideal_closed_disc_germ_no_other_tile (u:ℂ) hGerm g⁻¹ hξ
    have hg1:g=1:=inv_eq_one.mp hInv
    rw [hg1,one_smul] at hg
    exact mem_singleton_iff.mpr hg.symm
  · intro hζ
    rw [mem_singleton_iff] at hζ
    subst ζ
    exact ⟨⟨(u:ℂ),huE,rfl⟩,1,one_smul _ _⟩

/-- A literal interior point of a genuine free side has the same singleton ordinary cycle. -/
theorem IsConvexFuchsianPolygon.ordinary_free_side_interior_cycle_singleton
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (F:Set Circle)
    (hF:IsFuchsianFreeSide P D F) (u:Circle) (hu:u∈interior F)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    fuchsianPolygonIdealCycle P D ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)={((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} := by
  have hFE:F⊆fuchsianPolygonIdealCircle P D:=by
    obtain ⟨⟨v,_hv,rfl⟩,_⟩:=hF
    exact connectedComponentIn_subset _ _
  exact hD.ordinary_free_interior_cycle_singleton u (interior_mono hFE hu) hOrd

/-- The actual Euclidean angle of an ordinary free-side interior point is a straight angle. -/
theorem IsConvexFuchsianPolygon.ordinary_free_interior_angle
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈interior (fuchsianPolygonIdealCircle P D))
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=Real.pi := by
  classical
  have huE:(u:ℂ)∈fuchsianPolygonIdealBoundary P D:=
    show u∈fuchsianPolygonIdealCircle P D from interior_subset hu
  have hGerm:=hD.ordinary_free_interior_closed_germ u hu hOrd
  obtain ⟨s,hs,hSum⟩:=hD.ordinary_ideal_incident_angle_sum (u:ℂ) huE hOrd
  have hsOne:s={1}:=by
    ext g
    constructor
    · intro hg
      exact Finset.mem_singleton.mpr
        (hD.ideal_closed_disc_germ_no_other_tile (u:ℂ) hGerm g ((hs g).mp hg))
    · intro hg
      have hg1:g=1:=Finset.mem_singleton.mp hg
      subst g
      exact (hs 1).mpr (by simpa only [one_smul] using huE)
  rw [hsOne] at hSum
  simpa only [Finset.sum_singleton,one_smul] using hSum

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Squared normal and tangential coordinates of a genuine circle point satisfy the actual circle equation. -/
theorem ordinary_circle_coordinates_sq (ξ z:ℂ) (hξ:‖ξ‖=1) (hz:‖z‖=1) :
    (inner ℝ ξ z)^2+(inner ℝ (Complex.I*ξ) z)^2=1 := by
  have he:=ordinary_circle_frame ξ hξ z
  have hnorm:inner ℝ z z=1:=by rw [real_inner_self_eq_norm_sq,hz,one_pow]
  calc
    _ = inner ℝ ((inner ℝ z ξ)•ξ+(inner ℝ z (Complex.I*ξ))•(Complex.I*ξ)) z := by
      rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
      rw [real_inner_comm z ξ,real_inner_comm z (Complex.I*ξ)]
      ring
    _ = inner ℝ z z := congrArg (fun w:ℂ=>inner ℝ w z) he.symm
    _ = 1 := hnorm

/-- The exact circle restriction of a genuine affine support cut factors through its tangential coordinate. -/
theorem ordinary_circle_support_factor (ξ n z:ℂ) (hξ:‖ξ‖=1) (hz:‖z‖=1)
    (hd:1+inner ℝ ξ z≠0) :
    inner ℝ n (z-ξ)=inner ℝ (Complex.I*ξ) z*
      (inner ℝ n (Complex.I*ξ)-(inner ℝ n ξ)*inner ℝ (Complex.I*ξ) z/(1+inner ℝ ξ z)) := by
  have he:=ordinary_circle_frame ξ hξ n
  have hsq:=ordinary_circle_coordinates_sq ξ z hξ hz
  have hs (w:ℂ):inner ℝ n w=(inner ℝ n ξ)*inner ℝ ξ w+
      (inner ℝ n (Complex.I*ξ))*inner ℝ (Complex.I*ξ) w:=by
    conv_lhs => rw [he]
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
  have hleft:inner ℝ n (z-ξ)=(inner ℝ n ξ)*(inner ℝ ξ z-1)+
      (inner ℝ n (Complex.I*ξ))*inner ℝ (Complex.I*ξ) z:=by
    rw [inner_sub_right,hs z]
    ring
  rw [hleft]
  have hsqb:=congrArg (fun r:ℝ=>(inner ℝ n ξ)*r) hsq
  field_simp [hd]
  nlinarith [hsqb]

/-- Along the actual unit circle, each true support inequality has the sign of its nonzero tangential derivative. -/
theorem ordinary_circle_support_trace_germ (u:Circle) (n:ℂ)
    (hn:n-(inner ℝ n (u:ℂ))•(u:ℂ)≠0) :
    ∀ᶠz:Circle in 𝓝 u,
      (inner ℝ n ((z:ℂ)-(u:ℂ))≤0 ↔
        (inner ℝ n (Complex.I*(u:ℂ)))*inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)≤0) := by
  let ξ:ℂ:=(u:ℂ)
  let b:=inner ℝ n ξ
  let c:=inner ℝ n (Complex.I*ξ)
  let x:Circle→ℝ:=fun z=>inner ℝ ξ (z:ℂ)
  let y:Circle→ℝ:=fun z=>inner ℝ (Complex.I*ξ) (z:ℂ)
  have hxu:x u=1:=by dsimp only [x,ξ];rw [real_inner_self_eq_norm_sq,u.norm_coe,one_pow]
  have hyu:y u=0:=by
    dsimp only [y,ξ]
    simp [Complex.inner]
    ring
  have hxc:Continuous x:=continuous_const.inner continuous_subtype_val
  have hyc:Continuous y:=continuous_const.inner continuous_subtype_val
  have hden:1+x u≠0:=by rw [hxu];norm_num
  let d:Circle→ℝ:=fun z=>c-b*y z/(1+x z)
  have hdc:ContinuousAt d u:=continuousAt_const.sub
    ((continuousAt_const.mul hyc.continuousAt).div (continuousAt_const.add hxc.continuousAt) hden)
  have hdu:d u=c:=by simp only [d,hyu,mul_zero,zero_div,sub_zero]
  have hc:c≠0:=ordinary_tangent_coefficient_ne_zero ξ u.norm_coe n hn
  have hDn:∀ᶠz:Circle in 𝓝 u,1+x z≠0:=
    (continuous_const.add hxc).continuousAt.eventually (isOpen_ne.mem_nhds hden)
  have hfactor (z:Circle) (hz:1+x z≠0):inner ℝ n ((z:ℂ)-ξ)=y z*d z:=
    ordinary_circle_support_factor ξ n (z:ℂ) u.norm_coe z.norm_coe hz
  rcases lt_or_gt_of_ne hc with hc|hc
  · have hDneg:∀ᶠz:Circle in 𝓝 u,d z<0:=
      hdc.eventually (gt_mem_nhds (hdu ▸ hc))
    filter_upwards [hDn,hDneg] with z hdz hneg
    rw [hfactor z hdz]
    change y z*d z≤0 ↔ c*y z≤0
    exact ⟨fun h=>mul_nonpos_of_nonpos_of_nonneg hc.le (nonneg_of_mul_nonpos_left h hneg),
      fun h=>mul_nonpos_of_nonneg_of_nonpos (nonneg_of_mul_nonpos_right h hc) hneg.le⟩
  · have hDpos:∀ᶠz:Circle in 𝓝 u,0<d z:=
      hdc.eventually (lt_mem_nhds (hdu ▸ hc))
    filter_upwards [hDn,hDpos] with z hdz hpos
    rw [hfactor z hdz]
    change y z*d z≤0 ↔ c*y z≤0
    exact ⟨fun h=>mul_nonpos_of_nonneg_of_nonpos hc.le (nonpos_of_mul_nonpos_left h hpos),
      fun h=>mul_nonpos_of_nonpos_of_nonneg (nonpos_of_mul_nonpos_right h hc) hpos.le⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory InnerProductGeometry
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine orthonormal inward quadrant has its actual quarter-circle angle. -/
theorem ordinary_orthonormal_quadrant_angle (n m:ℂ) (hn:‖n‖=1) (hm:‖m‖=1)
    (ho:inner ℝ n m=0)
    (hframe:∀z:ℂ,z=(inner ℝ z n)•n+(inner ℝ z m)•m) :
    2*Real.pi*(polygonDirectionMeasure {u:Circle |
      inner ℝ n (u:ℂ)<0∧inner ℝ m (u:ℂ)<0}).toReal=Real.pi/2 := by
  have hn0:n≠0:=by intro h;rw [h,norm_zero] at hn;norm_num at hn
  have hm0:m≠0:=by intro h;rw [h,norm_zero] at hm;norm_num at hm
  have hnn:inner ℝ n n=1:=by rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have hmm:inner ℝ m m=1:=by rw [real_inner_self_eq_norm_sq,hm,one_pow]
  have hmn:inner ℝ m n=0:=by rw [real_inner_comm,ho]
  have hCone:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPositiveCone (-n) (-m))=
      {u:Circle | inner ℝ n (u:ℂ)≤0∧inner ℝ m (u:ℂ)≤0}:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_positiveCone]
    ext u
    change ((u:ℂ)∈Submodule.span NNReal {-n,-m}) ↔ _
    rw [Submodule.mem_span_pair]
    constructor
    · rintro ⟨a,b,he⟩
      have he':(u:ℂ)=(a:ℝ)•(-n)+(b:ℝ)•(-m):=he.symm
      change inner ℝ n (u:ℂ)≤0∧inner ℝ m (u:ℂ)≤0
      rw [he']
      simp only [inner_add_right,real_inner_smul_right,inner_neg_right,hnn,hmm,ho,hmn,
        neg_zero,mul_zero,mul_neg,mul_one,zero_add,add_zero,neg_nonpos]
      exact ⟨a.property,b.property⟩
    · rintro ⟨hu,hv⟩
      refine ⟨⟨-inner ℝ n (u:ℂ),neg_nonneg.mpr hu⟩,
        ⟨-inner ℝ m (u:ℂ),neg_nonneg.mpr hv⟩,?_⟩
      change (-inner ℝ n (u:ℂ))•(-n)+(-inner ℝ m (u:ℂ))•(-m)=(u:ℂ)
      simpa only [neg_smul,smul_neg,neg_neg,real_inner_comm] using (hframe (u:ℂ)).symm
  have hθ:angle (-n) (-m)=Real.pi/2:=by
    apply (inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp
    simpa only [inner_neg_left,inner_neg_right,neg_neg] using ho
  have hAngle:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_positiveCone (neg_ne_zero.mpr
    hn0) (neg_ne_zero.mpr hm0)
    (show angle (-n) (-m)<Real.pi by rw [hθ];linarith [Real.pi_pos])
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_zero,hCone,hθ] at hAngle
  have hAE:{u:Circle | inner ℝ n (u:ℂ)<0∧inner ℝ m (u:ℂ)<0} =ᵐ[polygonDirectionMeasure]
      {u:Circle | inner ℝ n (u:ℂ)≤0∧inner ℝ m (u:ℂ)≤0}:=by
    have hN:polygonDirectionMeasure {u:Circle | inner ℝ (u:ℂ) n=0}=0:=
      (finite_circle_orthogonal n hn0).measure_zero _
    have hM:polygonDirectionMeasure {u:Circle | inner ℝ (u:ℂ) m=0}=0:=
      (finite_circle_orthogonal m hm0).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN,measure_eq_zero_iff_ae_notMem.mp hM] with u hu hv
    change inner ℝ (u:ℂ) n≠0 at hu
    change inner ℝ (u:ℂ) m≠0 at hv
    apply propext
    have hu':inner ℝ n (u:ℂ)≠0:=by simpa only [real_inner_comm] using hu
    have hv':inner ℝ m (u:ℂ)≠0:=by simpa only [real_inner_comm] using hv
    exact ⟨fun h=>⟨h.1.le,h.2.le⟩,
      fun h=>⟨lt_of_le_of_ne h.1 hu',lt_of_le_of_ne h.2 hv'⟩⟩
  rw [measure_congr hAE]
  exact hAngle

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual first-order support form is exactly its tangential coefficient in the ideal orthonormal frame. -/
theorem ordinary_tangent_support_form (ξ n v:ℂ) (hξ:‖ξ‖=1) :
    inner ℝ n v-(inner ℝ n ξ)*inner ℝ ξ v=
      (inner ℝ n (Complex.I*ξ))*inner ℝ (Complex.I*ξ) v := by
  have he:=ordinary_circle_frame ξ hξ n
  conv_lhs => lhs; rw [he]
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
  ring

/-- A true ordinary corner has both its actual circle trace and its actual angular directions in the same derived finite tangential coordinates. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_tangential_trace
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃ (s:Finset H) (c:{g // g∈s∧g≠1}→ℝ),
      (∀i,c i≠0) ∧
      (∀ᶠz:Circle in 𝓝 u,(z∈fuchsianPolygonIdealCircle P D ↔
        ∀i,c i*inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)≤0)) ∧
      (∀ᵐv:Circle ∂polygonDirectionMeasure,
        (v∈_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
          (closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) (u:ℂ) ↔
          inner ℝ (u:ℂ) (v:ℂ)<0∧∀i,c i*inner ℝ (Complex.I*(u:ℂ)) (v:ℂ)<0)) := by
  obtain ⟨s,n,hnq,hGerm⟩:=hD.ordinary_ideal_polynomial_germ (u:ℂ) hu hOrd
  let I:={g:H // g∈s∧g≠1}
  let : Finite I:=Finite.of_injective (fun i:I=>(⟨i.val,i.property.1⟩:s)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun i:s=>i.val) h))
  let c:I→ℝ:=fun i=>inner ℝ (n i) (Complex.I*(u:ℂ))
  refine ⟨s,c,fun i=>ordinary_tangent_coefficient_ne_zero (u:ℂ) u.norm_coe (n i) (hnq i),?_,?_⟩
  · have hAlong:∀ᶠz:Circle in 𝓝 u,
        ((z:ℂ)∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D) ↔
          ‖(z:ℂ)‖≤1∧∀i:I,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z:ℂ)-(u:ℂ))≤0):=
      continuous_subtype_val.continuousAt.tendsto.eventually hGerm
    have hCuts:∀ᶠz:Circle in 𝓝 u,∀i:I,
        (inner ℝ (n i) ((z:ℂ)-(u:ℂ))≤0 ↔ c i*inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)≤0):=
      Filter.eventually_all.mpr (fun i=>ordinary_circle_support_trace_germ u (n i) (hnq i))
    filter_upwards [hAlong,hCuts] with z hz hzCuts
    have hfix:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z:ℂ)=(z:ℂ):=by
      simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,z.norm_coe,one_pow]
      norm_num
    change ((z:ℂ)∈fuchsianPolygonIdealBoundary P D) ↔ _
    rw [mem_fuchsianPolygonIdealBoundary,hz,hfix,z.norm_coe]
    simp only [le_refl,true_and,and_true]
    exact forall_congr' hzCuts
  · have hDir:=_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections_congr_germ hGerm
    have hAE:=ordinary_finite_cut_directions_ae (u:ℂ) u.norm_coe n hnq
    filter_upwards [hAE] with v hv
    rw [hDir]
    exact hv.trans (and_congr_right (fun _=>forall_congr' (fun i=>by
      rw [ordinary_tangent_support_form (u:ℂ) (n i) (v:ℂ) u.norm_coe])))

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The ordinary ideal cone has exactly the three possible actual Euclidean angle values. -/
theorem ordinary_tangential_cone_angle_profile {ι:Type*} (u:Circle) (c:ι→ℝ)
    (hc:∀i,c i≠0) :
    let a:=2*Real.pi*(polygonDirectionMeasure {v:Circle |
      inner ℝ (u:ℂ) (v:ℂ)<0∧∀i,c i*inner ℝ (Complex.I*(u:ℂ)) (v:ℂ)<0}).toReal
    (IsEmpty ι∧a=Real.pi) ∨ ((∃i j,0<c i∧c j<0)∧a=0) ∨
      (Nonempty ι∧((∀i,0<c i)∨(∀i,c i<0))∧a=Real.pi/2) := by
  classical
  let ξ:ℂ:=(u:ℂ)
  let τ:ℂ:=Complex.I*ξ
  have hτ:‖τ‖=1:=by dsimp only [τ];rw [norm_mul,Complex.norm_I,u.norm_coe,one_mul]
  have horth:inner ℝ ξ τ=0:=by
    dsimp only [τ]
    simp [Complex.inner]
    ring
  let C:Set Circle:={v | inner ℝ ξ (v:ℂ)<0∧∀i,c i*inner ℝ τ (v:ℂ)<0}
  change (IsEmpty ι∧2*Real.pi*(polygonDirectionMeasure C).toReal=Real.pi) ∨
    ((∃i j,0<c i∧c j<0)∧2*Real.pi*(polygonDirectionMeasure C).toReal=0) ∨
    (Nonempty ι∧((∀i,0<c i)∨(∀i,c i<0))∧2*Real.pi*(polygonDirectionMeasure C).toReal=Real.pi/2)
  by_cases hEmpty:IsEmpty ι
  · let : IsEmpty ι:=hEmpty
    refine Or.inl ⟨hEmpty,?_⟩
    have hC:C={v:Circle | 0 ≤ inner ℝ (v:ℂ) (-ξ)} \ {v:Circle | inner ℝ (v:ℂ) ξ=0}:=by
      ext v
      simp only [C,IsEmpty.forall_iff,and_true,mem_ofPred_eq,Set.mem_sdiff,inner_neg_right,
        neg_nonneg]
      change inner ℝ ξ (v:ℂ)<0 ↔ inner ℝ (v:ℂ) ξ≤0∧inner ℝ (v:ℂ) ξ≠0
      simpa only [real_inner_comm] using
        (show inner ℝ ξ (v:ℂ)<0 ↔ inner ℝ ξ (v:ℂ)≤0∧inner ℝ ξ (v:ℂ)≠0 from lt_iff_le_and_ne)
    have hξne:ξ≠0:=u.coe_ne_zero
    have hAE:C =ᵐ[polygonDirectionMeasure] {v:Circle | 0 ≤ inner ℝ (v:ℂ) (-ξ)}:=by
      rw [hC]
      exact sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right
          ((finite_circle_orthogonal ξ hξne).measure_zero _))
    exact (congrArg (fun r:ENNReal=>2*Real.pi*r.toReal) (measure_congr hAE)).trans
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonDirectionMeasure_hemisphere (-ξ) (neg_ne_zero.mpr hξne))
  · have hne:Nonempty ι:=not_isEmpty_iff.mp hEmpty
    obtain ⟨i₀⟩:=hne
    by_cases hOpp:∃i j,0<c i∧c j<0
    · refine Or.inr (Or.inl ⟨hOpp,?_⟩)
      have hC:C=∅:=by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨i,j,hpi,hnj⟩:=hOpp
        have hi:=hv.2 i
        have hj:=hv.2 j
        have hyneg:inner ℝ τ (v:ℂ)<0:=neg_of_mul_neg_right hi hpi.le
        have hypos:0 < inner ℝ τ (v:ℂ):=pos_of_mul_neg_right hj hnj.le
        exact hyneg.not_gt hypos
      rw [hC,measure_empty,ENNReal.toReal_zero,mul_zero]
    · have hSign:(∀i,0<c i)∨(∀i,c i<0):=by
        rcases lt_or_gt_of_ne (hc i₀) with hn|hp
        · right
          intro i
          rcases lt_or_gt_of_ne (hc i) with hi|hi
          · exact hi
          · exact False.elim (hOpp ⟨i,i₀,hi,hn⟩)
        · left
          intro i
          rcases lt_or_gt_of_ne (hc i) with hi|hi
          · exact False.elim (hOpp ⟨i₀,i,hp,hi⟩)
          · exact hi
      refine Or.inr (Or.inr ⟨⟨i₀⟩,hSign,?_⟩)
      rcases hSign with hpos|hneg
      · have hC:C={v:Circle | inner ℝ ξ (v:ℂ)<0∧inner ℝ τ (v:ℂ)<0}:=by
          ext v
          exact and_congr_right (fun _=>⟨fun h=>neg_of_mul_neg_right (h i₀) (hpos i₀).le,
            fun h i=>mul_neg_of_pos_of_neg (hpos i) h⟩)
        rw [hC]
        exact ordinary_orthonormal_quadrant_angle ξ τ u.norm_coe hτ horth
          (ordinary_circle_frame ξ u.norm_coe)
      · have hC:C={v:Circle | inner ℝ ξ (v:ℂ)<0∧inner ℝ (-τ) (v:ℂ)<0}:=by
          ext v
          change (inner ℝ ξ (v:ℂ)<0∧∀i,c i*inner ℝ τ (v:ℂ)<0) ↔
            (inner ℝ ξ (v:ℂ)<0∧inner ℝ (-τ) (v:ℂ)<0)
          rw [inner_neg_left,neg_lt_zero]
          exact and_congr_right (fun _=>⟨fun h=>pos_of_mul_neg_right (h i₀) (hneg i₀).le,
            fun h i=>mul_neg_of_neg_of_pos (hneg i) h⟩)
        rw [hC]
        apply ordinary_orthonormal_quadrant_angle ξ (-τ) u.norm_coe
          (by rw [norm_neg];exact hτ) (by rw [inner_neg_right,horth,neg_zero])
        intro z
        simpa only [inner_neg_right,smul_neg,neg_smul,neg_neg] using
          ordinary_circle_frame ξ u.norm_coe z

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal circle path through the original ideal point. -/
def ordinaryIdealCircleCurve (u:Circle) (t:ℝ) : Circle:=
  ⟨ordinaryIdealCirclePath (u:ℂ) t,
    mem_sphere_zero_iff_norm.mpr (ordinaryIdealCirclePath_norm (u:ℂ) u.norm_coe t)⟩

theorem ordinaryIdealCircleCurve_continuous (u:Circle) : Continuous (ordinaryIdealCircleCurve u):=
  (ordinaryIdealCirclePath_continuous (u:ℂ)).subtype_mk _

theorem ordinaryIdealCircleCurve_zero (u:Circle) : ordinaryIdealCircleCurve u 0=u:=
  Subtype.ext (ordinaryIdealCirclePath_zero _)

theorem ordinaryIdealCircleCurve_tangent (u:Circle) (t:ℝ) :
    inner ℝ (Complex.I*(u:ℂ)) (ordinaryIdealCircleCurve u t:ℂ)=2*t/(1+t^2) := by
  have horth:inner ℝ (Complex.I*(u:ℂ)) (u:ℂ)=0:=by
    simp [Complex.inner]
    ring
  have hnorm:inner ℝ (Complex.I*(u:ℂ)) (Complex.I*(u:ℂ))=1:=by
    rw [real_inner_self_eq_norm_sq,norm_mul,Complex.norm_I,u.norm_coe,one_mul,one_pow]
  have he:=ordinaryIdealCirclePath_inner (u:ℂ) (Complex.I*(u:ℂ)) t
  change inner ℝ (Complex.I*(u:ℂ)) (ordinaryIdealCirclePath (u:ℂ) t)=2*t/(1+t^2)
  simpa only [inner_sub_right,horth,hnorm,zero_mul,sub_zero,mul_one] using he

theorem ordinaryIdealCircleCurve_eq_iff (u:Circle) (t:ℝ) :
    ordinaryIdealCircleCurve u t=u ↔ t=0 := by
  constructor
  · intro he
    have h:=congrArg (fun z:Circle=>inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)) he
    rw [ordinaryIdealCircleCurve_tangent] at h
    have horth:inner ℝ (Complex.I*(u:ℂ)) (u:ℂ)=0:=by
      simp [Complex.inner]
      ring
    rw [horth] at h
    have hd:1+t^2≠0:=ne_of_gt (by positivity)
    field_simp [hd] at h
    linarith
  · rintro rfl
    exact ordinaryIdealCircleCurve_zero u

/-- Near the actual unit point, zero tangential coordinate identifies that point uniquely. -/
theorem ordinary_circle_tangent_zero_germ (u:Circle) :
    ∀ᶠz:Circle in 𝓝 u,(inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)=0 ↔ z=u) := by
  have hself:inner ℝ (u:ℂ) (u:ℂ)=1:=by rw [real_inner_self_eq_norm_sq,u.norm_coe,one_pow]
  have hx:∀ᶠz:Circle in 𝓝 u,0 < inner ℝ (u:ℂ) (z:ℂ):=
    (continuous_const.inner continuous_subtype_val).continuousAt.eventually
      (lt_mem_nhds (show 0 < inner ℝ (u:ℂ) (u:ℂ) by rw [hself];norm_num))
  filter_upwards [hx] with z hz
  constructor
  · intro hy
    have hsq:=ordinary_circle_coordinates_sq (u:ℂ) (z:ℂ) u.norm_coe z.norm_coe
    rw [hy,zero_pow (by norm_num),add_zero] at hsq
    have hx1:inner ℝ (u:ℂ) (z:ℂ)=1:=by nlinarith
    have he:=ordinary_circle_frame (u:ℂ) u.norm_coe (z:ℂ)
    have hzξ:inner ℝ (z:ℂ) (u:ℂ)=1:=(real_inner_comm _ _).trans hx1
    have hzτ:inner ℝ (z:ℂ) (Complex.I*(u:ℂ))=0:=(real_inner_comm _ _).trans hy
    rw [hzξ,hzτ,one_smul,zero_smul,add_zero] at he
    exact Subtype.ext he
  · rintro rfl
    simp [Complex.inner]
    ring

/-- A genuine one-sided boundary-circle germ is neither interior nor isolated. -/
theorem ordinary_half_circle_trace_types (E:Set Circle) (u:Circle) (σ:ℝ) (hσ:σ≠0)
    (hE:∀ᶠz:Circle in 𝓝 u,(z∈E ↔ σ*inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)≤0)) :
    u∉interior E ∧ u∈closure (E\{u}) := by
  let p:ℝ→Circle:=fun r=>ordinaryIdealCircleCurve u (σ*r)
  let q:ℝ→Circle:=fun r=>ordinaryIdealCircleCurve u (-σ*r)
  have hp:Continuous p:=(ordinaryIdealCircleCurve_continuous u).comp (continuous_const.mul continuous_id)
  have hq:Continuous q:=(ordinaryIdealCircleCurve_continuous u).comp (continuous_const.mul continuous_id)
  have hp0:p 0=u:=by simp [p,ordinaryIdealCircleCurve_zero]
  have hq0:q 0=u:=by simp [q,ordinaryIdealCircleCurve_zero]
  have hpLim:Tendsto p (𝓝[>] (0:ℝ)) (𝓝 u):=by
    rw [←hp0]
    exact hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hqLim:Tendsto q (𝓝[>] (0:ℝ)) (𝓝 u):=by
    rw [←hq0]
    exact hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · intro hu
    have hpE:=hpLim.eventually (mem_interior_iff_mem_nhds.mp hu)
    have hpTrace:=hpLim.eventually hE
    obtain ⟨r,⟨hrE,hrTrace⟩,hr⟩:=((hpE.and hpTrace).and self_mem_nhdsWithin).exists
    have hle:=hrTrace.mp hrE
    change σ*inner ℝ (Complex.I*(u:ℂ)) (ordinaryIdealCircleCurve u (σ*r):ℂ)≤0 at hle
    rw [ordinaryIdealCircleCurve_tangent,←mul_div_assoc] at hle
    have hnum:0<σ*(2*(σ*r)):=by
      have hh:=mul_pos (sq_pos_of_ne_zero hσ) hr
      nlinarith
    have hpos:0<σ*(2*(σ*r))/(1+(σ*r)^2):=div_pos hnum (by positivity)
    exact not_lt_of_ge hle hpos
  · apply isClosed_closure.mem_of_tendsto hqLim
    have hqTrace:=hqLim.eventually hE
    filter_upwards [hqTrace,self_mem_nhdsWithin] with r hrTrace hr
    apply subset_closure
    refine ⟨hrTrace.mpr ?_,?_⟩
    · change σ*inner ℝ (Complex.I*(u:ℂ)) (ordinaryIdealCircleCurve u (-σ*r):ℂ)≤0
      rw [ordinaryIdealCircleCurve_tangent,←mul_div_assoc]
      have hnum:σ*(2*(-σ*r))<0:=by
        have hh:=mul_pos (sq_pos_of_ne_zero hσ) hr
        nlinarith
      exact (div_neg_of_neg_of_pos hnum (by positivity)).le
    · change q r≠u
      dsimp only [q]
      intro he
      exact (mul_ne_zero (neg_ne_zero.mpr hσ) hr.ne')
        ((ordinaryIdealCircleCurve_eq_iff u (-σ*r)).mp he)

/-- A genuine singleton boundary-circle germ is neither interior nor an accumulation point. -/
theorem ordinary_isolated_circle_trace_types (E:Set Circle) (u:Circle)
    (hE:∀ᶠz:Circle in 𝓝 u,(z∈E ↔ z=u)) :
    u∉interior E ∧ u∉closure (E\{u}) := by
  constructor
  · intro hu
    have hlim:Tendsto (ordinaryIdealCircleCurve u) (𝓝[>] (0:ℝ)) (𝓝 u):=by
      have hlim':Tendsto (ordinaryIdealCircleCurve u) (𝓝[>] (0:ℝ))
          (𝓝 (ordinaryIdealCircleCurve u 0)):=
        (ordinaryIdealCircleCurve_continuous u).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [ordinaryIdealCircleCurve_zero] using hlim'
    have hmem:=hlim.eventually (mem_interior_iff_mem_nhds.mp hu)
    have hTrace:=hlim.eventually hE
    obtain ⟨t,⟨htE,htTrace⟩,ht⟩:=((hmem.and hTrace).and self_mem_nhdsWithin).exists
    exact ht.ne' ((ordinaryIdealCircleCurve_eq_iff u t).mp (htTrace.mp htE))
  · intro hu
    obtain ⟨z,hzTrace,hzE,hzne⟩:=(mem_closure_iff_nhds.mp hu) _ hE
    exact hzne (hzTrace.mp hzE)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual Euclidean ideal angle is determined by the genuine local topology of the polygon's original circle trace. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_angle_topology
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=
      if u∈interior (fuchsianPolygonIdealCircle P D) then Real.pi
      else if u∉closure (fuchsianPolygonIdealCircle P D\{u}) then 0 else Real.pi/2 := by
  classical
  obtain ⟨s,c,hc,hTrace,hDir⟩:=hD.ordinary_ideal_tangential_trace u hu hOrd
  let I:={g:H // g∈s∧g≠1}
  let E:=fuchsianPolygonIdealCircle P D
  let C:Set Circle:={v | inner ℝ (u:ℂ) (v:ℂ)<0∧
    ∀i:I,c i*inner ℝ (Complex.I*(u:ℂ)) (v:ℂ)<0}
  have hAngle:fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=
      2*Real.pi*(polygonDirectionMeasure C).toReal:=by
    have hm:polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
        (closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) (u:ℂ))=
        polygonDirectionMeasure C:=by
      apply measure_congr
      filter_upwards [hDir] with v hv
      exact propext hv
    exact congrArg (fun r:ENNReal=>2*Real.pi*r.toReal) hm
  have hProfile:=ordinary_tangential_cone_angle_profile u c hc
  change (IsEmpty I∧2*Real.pi*(polygonDirectionMeasure C).toReal=Real.pi)∨
    ((∃i j,0<c i∧c j<0)∧2*Real.pi*(polygonDirectionMeasure C).toReal=0)∨
    (Nonempty I∧((∀i,0<c i)∨(∀i,c i<0))∧2*Real.pi*(polygonDirectionMeasure C).toReal=Real.pi/2) at hProfile
  rcases hProfile with ⟨hEmpty,hval⟩|⟨hOpp,hval⟩|⟨hNonempty,hSign,hval⟩
  · let : IsEmpty I:=hEmpty
    have hInt:u∈interior E:=by
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [hTrace] with z hz
      exact hz.mpr (fun i=>isEmptyElim i)
    rw [ite_eq_left hInt]
    exact hAngle.trans hval
  · obtain ⟨i,j,hi,hj⟩:=hOpp
    have hIso:∀ᶠz:Circle in 𝓝 u,(z∈E ↔ z=u):=by
      filter_upwards [hTrace,ordinary_circle_tangent_zero_germ u] with z hz hzero
      rw [hz]
      constructor
      · intro h
        have hyneg:=nonpos_of_mul_nonpos_right (h i) hi
        have hypos:=nonneg_of_mul_nonpos_right (h j) hj
        exact hzero.mp (le_antisymm hyneg hypos)
      · intro he
        have hy:=hzero.mpr he
        intro k
        rw [hy,mul_zero]
    have ht:=ordinary_isolated_circle_trace_types E u hIso
    rw [ite_eq_right ht.1,ite_eq_left ht.2]
    exact hAngle.trans hval
  · obtain ⟨i₀⟩:=hNonempty
    have hHalf:∀ᶠz:Circle in 𝓝 u,(z∈E ↔
        c i₀*inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)≤0):=by
      filter_upwards [hTrace] with z hz
      rw [hz]
      constructor
      · exact fun h=>h i₀
      · intro hi i
        rcases hSign with hpos|hneg
        · exact mul_nonpos_of_nonneg_of_nonpos (hpos i).le
            (nonpos_of_mul_nonpos_right hi (hpos i₀))
        · exact mul_nonpos_of_nonpos_of_nonneg (hneg i).le
            (nonneg_of_mul_nonpos_right hi (hneg i₀))
    have ht:=ordinary_half_circle_trace_types E u (c i₀) (hc i₀) hHalf
    rw [ite_eq_right ht.1,ite_eq_right (not_not.mpr ht.2)]
    exact hAngle.trans hval

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual ordinary-neighborhood property is invariant under the original whole group. -/
theorem HasMobiusOrdinaryNeighborhood.smul_ordinary {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hξ:HasMobiusOrdinaryNeighborhood H ξ) (g:H) :
    HasMobiusOrdinaryNeighborhood H (g•ξ) := by
  let : ContinuousConstSMul H _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
    ⟨fun h=>(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph h.val).continuous⟩
  obtain ⟨U,hU,hξU,hd⟩:=hξ
  refine ⟨g•U,(Homeomorph.smul g).isOpenMap U hU,⟨ξ,hξU,rfl⟩,?_⟩
  intro K hK hKU
  let L:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=g⁻¹•K
  have hL:IsCompact L:=hK.image (continuous_const_smul g⁻¹)
  have hLU:L⊆U:=by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨y,hy,hgy⟩:=hKU hz
    change g•y=z at hgy
    change g⁻¹•z∈U
    rw [←hgy,inv_smul_smul]
    exact hy
  apply ((hd L hL hLU).image (fun h:H=>g*h*g⁻¹)).subset
  rintro h ⟨z,⟨y,hy,hhy⟩,hz⟩
  change h•y=z at hhy
  refine ⟨g⁻¹*h*g,?_,by group⟩
  refine ⟨g⁻¹•z,⟨g⁻¹•y,⟨y,hy,rfl⟩,?_⟩,⟨z,hz,rfl⟩⟩
  change (g⁻¹*h*g)•(g⁻¹•y)=g⁻¹•z
  rw [mul_smul,mul_smul,smul_inv_smul,hhy]

/-- The literal circle point in the actual closed-disc model. -/
def ordinaryCircleClosedModel (u:Circle) : 𝕔𝔻:=Complex.UnitClosedDisc.mk (u:ℂ) u.norm_coe.le

theorem ordinaryCircleClosedModel_continuous : Continuous ordinaryCircleClosedModel:=
  continuous_subtype_val.subtype_mk _

/-- A genuine closed-disc isometry acts by a genuine homeomorphism on the actual ideal circle. -/
def ordinaryClosedDiscCircleHomeomorph (e:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry) : Circle≃ₜCircle := by
  let f:Circle→Circle:=fun u=>⟨(e.closedMap (ordinaryCircleClosedModel u):ℂ),
    mem_sphere_zero_iff_norm.mpr ((e.ideal_iff _).mpr u.norm_coe)⟩
  let f':Circle→Circle:=fun u=>⟨(e.symm.closedMap (ordinaryCircleClosedModel u):ℂ),
    mem_sphere_zero_iff_norm.mpr ((e.symm.ideal_iff _).mpr u.norm_coe)⟩
  have hf (u:Circle):ordinaryCircleClosedModel (f u)=e.closedMap (ordinaryCircleClosedModel u):=
    Subtype.ext rfl
  have hf' (u:Circle):ordinaryCircleClosedModel (f' u)=e.closedMap.symm (ordinaryCircleClosedModel u):=
    Subtype.ext rfl
  refine { toFun:=f,invFun:=f',left_inv:=?_,right_inv:=?_,continuous_toFun:=?_,continuous_invFun:=?_ }
  · intro u
    apply Subtype.ext
    change (e.closedMap.symm (ordinaryCircleClosedModel (f u)):ℂ)=(u:ℂ)
    rw [hf,e.closedMap.symm_apply_apply]
    rfl
  · intro u
    apply Subtype.ext
    change (e.closedMap (ordinaryCircleClosedModel (f' u)):ℂ)=(u:ℂ)
    rw [hf',e.closedMap.apply_symm_apply]
    rfl
  · exact ((Complex.UnitClosedDisc.continuous_coe.comp e.closedMap.continuous).comp
      ordinaryCircleClosedModel_continuous).subtype_mk _
  · exact ((Complex.UnitClosedDisc.continuous_coe.comp e.closedMap.symm.continuous).comp
      ordinaryCircleClosedModel_continuous).subtype_mk _

/-- The real original circle action is the boundary restriction of its actual compactified action. -/
def UnitDiscFuchsianGroup.ordinaryCircleAction {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (g:H) : Circle≃ₜCircle:=
  ordinaryClosedDiscCircleHomeomorph (P.compactifiedAction g)

/-- The actual ideal-circle homeomorphism agrees with the original whole-group sphere action. -/
theorem UnitDiscFuchsianGroup.ordinaryCircleAction_sphere {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (g:H) (u:Circle) :
    (((P.ordinaryCircleAction g u:Circle):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=g•((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended ((P.compactifiedAction g).closedMap
    (ordinaryCircleClosedModel u))=
    g.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (ordinaryCircleClosedModel u))
  exact P.compactifiedAction_sphere g (ordinaryCircleClosedModel u)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine original boundary action transports the actual whole ideal-circle trace exactly. -/
theorem UnitDiscFuchsianGroup.ordinaryCircleAction_image_idealCircle {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (g:H) :
    P.ordinaryCircleAction g '' fuchsianPolygonIdealCircle P D=
      fuchsianPolygonIdealCircle P (g•D) := by
  let e:=P.ordinaryCircleAction g
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact P.idealBoundary_smul D g (u:ℂ) (e u:ℂ) hu (P.ordinaryCircleAction_sphere g u).symm
  · intro hv
    let u:=e.symm v
    have he:e u=v:=e.apply_symm_apply v
    have hback:g⁻¹.val.val ((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
      change g⁻¹•((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      have hSphere:=P.ordinaryCircleAction_sphere g u
      change (((e u:Circle):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=g•((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hSphere
      rw [he] at hSphere
      rw [hSphere,inv_smul_smul]
    have hU:=P.idealBoundary_smul (g•D) g⁻¹ (v:ℂ) (u:ℂ) hv hback
    have hu:u∈fuchsianPolygonIdealCircle P D:=by
      change (u:ℂ)∈fuchsianPolygonIdealBoundary P D
      simpa only [inv_smul_smul] using hU
    exact ⟨u,hu,he⟩

/-- Actual local Euclidean ideal angles are preserved by the original conformal polygon transport. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_angle_smul
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (g:H) (u:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    fuchsianPolygonEuclideanIdealAngle P (g•D) (P.ordinaryCircleAction g u:ℂ)=
      fuchsianPolygonEuclideanIdealAngle P D (u:ℂ) := by
  let e:=P.ordinaryCircleAction g
  let E:=fuchsianPolygonIdealCircle P D
  let E':=fuchsianPolygonIdealCircle P (g•D)
  have hE:e '' E=E':=P.ordinaryCircleAction_image_idealCircle D g
  have hu':e u∈E':=hE ▸ mem_image_of_mem e hu
  have hOrd':HasMobiusOrdinaryNeighborhood H (((e u:Circle):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [P.ordinaryCircleAction_sphere g u]
    exact hOrd.smul_ordinary g
  have hInt:(e u∈interior E') ↔ u∈interior E:=by
    rw [←hE,←e.image_interior]
    exact e.injective.mem_set_image
  have hsd:e '' (E\{u})=E'\{e u}:=by
    rw [Set.image_sdiff e.injective,image_singleton,hE]
  have hAcc:(e u∈closure (E'\{e u})) ↔ u∈closure (E\{u}):=by
    rw [←hsd,←e.image_closure]
    exact e.injective.mem_set_image
  rw [(hD.smul_polygon g).ordinary_ideal_angle_topology (e u) hu' hOrd',
    hD.ordinary_ideal_angle_topology u hu hOrd,hInt,hAcc]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual original ideal cycle, in its literal circle coordinate. -/
def fuchsianPolygonIdealCircleCycle {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (u:Circle) : Set Circle:=
  {v | v∈fuchsianPolygonIdealCircle P D ∧ ∃g:H,g•((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}

/-- The circle presentation is exactly the geometric original whole-sphere ideal cycle. -/
theorem fuchsianPolygonIdealCircleCycle_sphere {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (u:Circle) :
    (fun v:Circle=>((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' fuchsianPolygonIdealCircleCycle P D u=
      fuchsianPolygonIdealCycle P D ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  ext ζ
  constructor
  · rintro ⟨v,⟨hv,g,hg⟩,rfl⟩
    exact ⟨⟨(v:ℂ),hv,rfl⟩,g,hg⟩
  · rintro ⟨⟨z,hz,rfl⟩,g,hg⟩
    have hnorm:‖z‖=1:=((mem_fuchsianPolygonIdealBoundary P D z).mp hz).2
    let v:Circle:=⟨z,mem_sphere_zero_iff_norm.mpr hnorm⟩
    exact ⟨v,⟨hz,g,hg⟩,rfl⟩

/-- The actual whole-group circle action cancels inverses at every original ideal point. -/
theorem UnitDiscFuchsianGroup.ordinaryCircleAction_inv {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (g:H) (u:Circle) :
    P.ordinaryCircleAction g (P.ordinaryCircleAction g⁻¹ u)=u := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  rw [P.ordinaryCircleAction_sphere,P.ordinaryCircleAction_sphere,smul_inv_smul]

/-- Ordinary original ideal cycles are genuinely finite in their literal circle coordinates. -/
theorem IsConvexFuchsianPolygon.ordinary_idealCircleCycle_finite
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    (fuchsianPolygonIdealCircleCycle P D u).Finite := by
  have hinj:Function.Injective (fun v:Circle=>((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)):=by
    intro v w h
    exact Subtype.ext (OnePoint.coe_injective h)
  exact (Set.finite_image_iff hinj.injOn).mp
    ((fuchsianPolygonIdealCircleCycle_sphere P D u).symm ▸ hD.ordinary_idealCycle_finite (u:ℂ) hOrd)

/-- The actual ordinary circle-cycle angles, including zero-angle proper vertices, add to a straight angle. -/
theorem IsConvexFuchsianPolygon.ordinary_idealCircleCycle_angle_sum
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∑v∈(hD.ordinary_idealCircleCycle_finite u hOrd).toFinset,
      fuchsianPolygonEuclideanIdealAngle P D (v:ℂ)=Real.pi := by
  classical
  obtain ⟨s,hs,hSum⟩:=hD.ordinary_ideal_incident_angle_sum (u:ℂ) hu hOrd
  let t:Finset Circle:=(hD.ordinary_idealCircleCycle_finite u hOrd).toFinset
  let f:H→Circle:=fun g=>P.ordinaryCircleAction g⁻¹ u
  have hMember (g:H) (hg:g∈s):f g∈fuchsianPolygonIdealCircle P D:=by
    have hξ:=P.idealBoundary_smul (g•D) g⁻¹ (u:ℂ) (f g:ℂ) ((hs g).mp hg)
      (P.ordinaryCircleAction_sphere g⁻¹ u).symm
    change (f g:ℂ)∈fuchsianPolygonIdealBoundary P D
    simpa only [inv_smul_smul] using hξ
  have hOrdF (g:H):HasMobiusOrdinaryNeighborhood H (((f g:Circle):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [P.ordinaryCircleAction_sphere g⁻¹ u]
    exact hOrd.smul_ordinary g⁻¹
  have hAngles (g:H) (hg:g∈s):
      fuchsianPolygonEuclideanIdealAngle P (g•D) (u:ℂ)=
        fuchsianPolygonEuclideanIdealAngle P D (f g:ℂ):=by
    have hA:=hD.ordinary_ideal_angle_smul g (f g) (hMember g hg) (hOrdF g)
    rw [P.ordinaryCircleAction_inv] at hA
    exact hA
  have hBijection:(∑g∈s,fuchsianPolygonEuclideanIdealAngle P (g•D) (u:ℂ))=
      ∑v∈t,fuchsianPolygonEuclideanIdealAngle P D (v:ℂ):=by
    apply Finset.sum_bij (fun g _=>f g)
    · intro g hg
      apply (Set.Finite.mem_toFinset _).mpr
      refine ⟨hMember g hg,g⁻¹,?_⟩
      exact (P.ordinaryCircleAction_sphere g⁻¹ u).symm
    · intro g hg h hh he
      have hSph: g⁻¹•((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=h⁻¹•((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
        rw [←P.ordinaryCircleAction_sphere,←P.ordinaryCircleAction_sphere]
        exact congrArg (fun v:Circle=>((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he
      have hFix:(h*g⁻¹)•((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
        rw [mul_smul,hSph,smul_inv_smul]
      have hOne:=hD.ordinary_ideal_stabilizer_trivial (u:ℂ) hu hOrd (h*g⁻¹) hFix
      exact (mul_inv_eq_one.mp hOne).symm
    · intro v hv
      have hv':v∈fuchsianPolygonIdealCircleCycle P D u:=(Set.Finite.mem_toFinset _).mp hv
      obtain ⟨hvE,h,hvH⟩:=hv'
      have hback:h⁻¹.val.val ((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
        change h⁻¹•((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
        rw [←hvH,inv_smul_smul]
      have hξ:=P.idealBoundary_smul D h⁻¹ (v:ℂ) (u:ℂ) hvE hback
      refine ⟨h⁻¹,(hs _).mpr hξ,?_⟩
      apply Subtype.ext
      apply OnePoint.coe_injective
      change (((P.ordinaryCircleAction (h⁻¹)⁻¹ u:Circle):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      rw [inv_inv,P.ordinaryCircleAction_sphere]
      exact hvH
    · exact hAngles
  exact hBijection ▸ hSum

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The two actual support contacts force proportional supports when their tangential signs agree. -/
theorem ordinary_same_sign_support_determinant (a b c d x y s t:ℝ)
    (hx:x<0) (hy:y<0) (hcd:0<c*d)
    (ha:a*x+c*s=0) (hb:b*y+d*t=0) (hma:b*x+d*s≤0) (hnb:a*y+c*t≤0) :
    a*d-b*c=0 := by
  have hcne:c≠0:=by intro h;rw [h,zero_mul] at hcd;exact lt_irrefl 0 hcd
  rcases lt_or_gt_of_ne hcne with hc|hc
  · have hd:d<0:=by
      by_contra hn
      have hprod:=mul_nonpos_of_nonpos_of_nonneg hc.le (le_of_not_gt hn)
      exact hcd.not_ge hprod
    have hma':0≤c*(b*x+d*s):=mul_nonneg_of_nonpos_of_nonpos hc.le hma
    have hnb':0≤d*(a*y+c*t):=mul_nonneg_of_nonpos_of_nonpos hd.le hnb
    have hδx:(a*d-b*c)*x≤0:=by
      nlinarith [congrArg (fun r:ℝ=>d*r) ha]
    have hδy:0≤(a*d-b*c)*y:=by
      nlinarith [congrArg (fun r:ℝ=>c*r) hb]
    have hδge:0≤a*d-b*c:=nonneg_of_mul_nonpos_left hδx hx
    have hδle:a*d-b*c≤0:=by
      by_contra hn
      have hprod:=mul_neg_of_pos_of_neg (lt_of_not_ge hn) hy
      exact hprod.not_ge hδy
    exact le_antisymm hδle hδge
  · have hd:0<d:=by
      by_contra hn
      have hprod:=mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt hn)
      exact hcd.not_ge hprod
    have hma':c*(b*x+d*s)≤0:=mul_nonpos_of_nonneg_of_nonpos hc.le hma
    have hnb':d*(a*y+c*t)≤0:=mul_nonpos_of_nonneg_of_nonpos hd.le hnb
    have hδx:0≤(a*d-b*c)*x:=by
      nlinarith [congrArg (fun r:ℝ=>d*r) ha]
    have hδy:(a*d-b*c)*y≤0:=by
      nlinarith [congrArg (fun r:ℝ=>c*r) hb]
    have hδge:0≤a*d-b*c:=nonneg_of_mul_nonpos_left hδy hy
    have hδle:a*d-b*c≤0:=by
      by_contra hn
      have hprod:=mul_neg_of_pos_of_neg (lt_of_not_ge hn) hx
      exact hprod.not_ge hδx
    exact le_antisymm hδle hδge

/-- Two true supporting lines reaching the same ideal point and supporting real finite contacts agree if their tangential signs agree. -/
theorem ordinary_same_sign_support_lines (ξ n m a b:ℂ) (hξ:‖ξ‖=1)
    (ha:‖a‖<1) (hb:‖b‖<1)
    (hna:inner ℝ n (a-ξ)=0) (hmb:inner ℝ m (b-ξ)=0)
    (hma:inner ℝ m (a-ξ)≤0) (hnb:inner ℝ n (b-ξ)≤0)
    (hc:0<(inner ℝ n (Complex.I*ξ))*(inner ℝ m (Complex.I*ξ))) :
    ∀z:ℂ,inner ℝ n (z-ξ)=0 ↔ inner ℝ m (z-ξ)=0 := by
  have hxa:inner ℝ ξ a-1<0:=by
    have hh:=lt_of_le_of_lt (real_inner_le_norm ξ a) (by simpa only [hξ,one_mul] using ha)
    linarith
  have hxb:inner ℝ ξ b-1<0:=by
    have hh:=lt_of_le_of_lt (real_inner_le_norm ξ b) (by simpa only [hξ,one_mul] using hb)
    linarith
  have hForm (k z:ℂ):inner ℝ k (z-ξ)=(inner ℝ k ξ)*(inner ℝ ξ z-1)+
      (inner ℝ k (Complex.I*ξ))*inner ℝ (Complex.I*ξ) z:=by
    rw [inner_sub_right]
    have hh:=ordinary_tangent_support_form ξ k z hξ
    linarith
  have hδ:=ordinary_same_sign_support_determinant (inner ℝ n ξ) (inner ℝ m ξ)
    (inner ℝ n (Complex.I*ξ)) (inner ℝ m (Complex.I*ξ))
    (inner ℝ ξ a-1) (inner ℝ ξ b-1) (inner ℝ (Complex.I*ξ) a) (inner ℝ (Complex.I*ξ) b)
    hxa hxb hc (hForm n a ▸ hna) (hForm m b ▸ hmb) (hForm m a ▸ hma) (hForm n b ▸ hnb)
  have hcn:inner ℝ n (Complex.I*ξ)≠0:=by intro h;rw [h,zero_mul] at hc;exact lt_irrefl 0 hc
  have hcm:inner ℝ m (Complex.I*ξ)≠0:=by intro h;rw [h,mul_zero] at hc;exact lt_irrefl 0 hc
  intro z
  have hCross:(inner ℝ m (Complex.I*ξ))*inner ℝ n (z-ξ)=
      (inner ℝ n (Complex.I*ξ))*inner ℝ m (z-ξ):=by
    rw [hForm n z,hForm m z]
    have hh:=congrArg (fun r:ℝ=>r*(inner ℝ ξ z-1)) hδ
    nlinarith
  constructor
  · intro hz
    rw [hz,mul_zero] at hCross
    exact (mul_eq_zero.mp hCross.symm).resolve_left hcn
  · intro hz
    rw [hz,mul_zero] at hCross
    exact (mul_eq_zero.mp hCross).resolve_left hcm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Three genuine disjoint convex tiles meeting an ideal point cannot support two positive finite contacts on the same tangential side. -/
theorem ordinary_three_tile_tangents_opposite {U V W:Set ℂ} (ξ n m a b:ℂ)
    (hξ:‖ξ‖=1) (ha:‖a‖<1) (hb:‖b‖<1)
    (hUc:Convex ℝ U) (hUo:IsOpen U) (hUn:U.Nonempty)
    (hVc:Convex ℝ V) (hVo:IsOpen V) (hVn:V.Nonempty)
    (hWc:Convex ℝ W) (hWo:IsOpen W) (hWn:W.Nonempty)
    (hUV:Disjoint U V) (hUW:Disjoint U W) (hVW:Disjoint V W)
    (hξU:ξ∈closure U) (hξV:ξ∈closure V) (hξW:ξ∈closure W)
    (haU:a∈closure U) (haV:a∈closure V) (hbU:b∈closure U) (hbW:b∈closure W)
    (hn:n≠0) (hl:∀z∈U,inner ℝ n (z-ξ)<0) (hr:∀z∈V,0 < inner ℝ n (z-ξ))
    (_hm:m≠0) (hl':∀z∈U,inner ℝ m (z-ξ)<0) (hr':∀z∈W,0 < inner ℝ m (z-ξ))
    (hcn:inner ℝ n (Complex.I*ξ)≠0) (hcm:inner ℝ m (Complex.I*ξ)≠0) :
    (inner ℝ n (Complex.I*ξ))*(inner ℝ m (Complex.I*ξ))<0 := by
  have hleft:∀z∈closure U,inner ℝ n (z-ξ)≤0:=fun z hz=>
    closure_minimal (fun w hw=>(hl w hw).le)
      (isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const) hz
  have hright:∀z∈closure V,0 ≤ inner ℝ n (z-ξ):=fun z hz=>
    closure_minimal (fun w hw=>(hr w hw).le)
      (isClosed_le continuous_const (continuous_const.inner (continuous_id.sub continuous_const))) hz
  have hleft':∀z∈closure U,inner ℝ m (z-ξ)≤0:=fun z hz=>
    closure_minimal (fun w hw=>(hl' w hw).le)
      (isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const) hz
  have hright':∀z∈closure W,0 ≤ inner ℝ m (z-ξ):=fun z hz=>
    closure_minimal (fun w hw=>(hr' w hw).le)
      (isClosed_le continuous_const (continuous_const.inner (continuous_id.sub continuous_const))) hz
  have hna:inner ℝ n (a-ξ)=0:=le_antisymm (hleft a haU) (hright a haV)
  have hmb:inner ℝ m (b-ξ)=0:=le_antisymm (hleft' b hbU) (hright' b hbW)
  have hprodne:(inner ℝ n (Complex.I*ξ))*(inner ℝ m (Complex.I*ξ))≠0:=mul_ne_zero hcn hcm
  by_contra hnot
  have hprod:0<(inner ℝ n (Complex.I*ξ))*(inner ℝ m (Complex.I*ξ)):=
    lt_of_le_of_ne (le_of_not_gt hnot) hprodne.symm
  have hLine:=ordinary_same_sign_support_lines ξ n m a b hξ ha hb hna hmb
    (hleft' a haU) (hleft b hbU) hprod
  have hnb:inner ℝ n (b-ξ)=0:=(hLine b).mpr hmb
  have hcol:Collinear ℝ ({a,ξ,b}:Set ℂ):=by
    apply _root_.LowDimensionalTopology.Geometry.Polygon.polygonComplex_hyperplane_collinear n ξ hn (by simp)
    rintro z (rfl|rfl|rfl)
    · exact sub_eq_zero.mp (by simpa only [inner_sub_right] using hna)
    · rfl
    · exact sub_eq_zero.mp (by simpa only [inner_sub_right] using hnb)
  have hSub: (closure U∩closure V∩closure W).Subsingleton:=
    _root_.LowDimensionalTopology.Geometry.Euclidean.three_disjoint_open_convex_closures_subsingleton hUc hUo hUn hVc hVo hVn hWc hWo hWn hUV hUW hVW
  have hξAll:ξ∈closure U∩closure V∩closure W:=⟨⟨hξU,hξV⟩,hξW⟩
  rcases hcol.wbtw_or_wbtw_or_wbtw with h|h|h
  · have hξball:ξ∈Metric.ball (0:ℂ) 1:=(convex_ball (0:ℂ) 1).segment_subset
      (mem_ball_zero_iff.mpr ha) (mem_ball_zero_iff.mpr hb) h.mem_segment
    exact (mem_ball_zero_iff.mp hξball).ne hξ
  · have hbV:b∈closure V:=hVc.closure.segment_subset hξV haV h.mem_segment
    have hbξ:b=ξ:=hSub ⟨⟨hbU,hbV⟩,hbW⟩ hξAll
    rw [hbξ,hξ] at hb
    exact lt_irrefl 1 hb
  · have haW:a∈closure W:=hWc.closure.segment_subset hbW hξW h.mem_segment
    have haξ:a=ξ:=hSub ⟨⟨haU,haV⟩,haW⟩ hξAll
    rw [haξ,hξ] at ha
    exact lt_irrefl 1 ha

/-- Two actual supports with opposite tangential signs leave only a null set of real corner directions. -/
theorem ordinary_opposite_supports_angle_zero {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (ξ n m:ℂ) (hξ:‖ξ‖=1)
    (hn:∀z∈closure (P.kleinCoordinate '' D),inner ℝ n (z-ξ)≤0)
    (hm:∀z∈closure (P.kleinCoordinate '' D),inner ℝ m (z-ξ)≤0)
    (hprod:(inner ℝ n (Complex.I*ξ))*(inner ℝ m (Complex.I*ξ))<0) :
    fuchsianPolygonEuclideanIdealAngle P D ξ=0 := by
  let A:=closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)
  let τ:=Complex.I*ξ
  have hτ:τ≠0:=mul_ne_zero Complex.I_ne_zero (by intro h;rw [h,norm_zero] at hξ;norm_num at hξ)
  have hcn:inner ℝ n τ≠0:=by intro h;rw [h,zero_mul] at hprod;exact lt_irrefl 0 hprod
  have hcm:inner ℝ m τ≠0:=by intro h;rw [h,mul_zero] at hprod;exact lt_irrefl 0 hprod
  have hfin:(_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections A ξ).Finite:=by
    apply (finite_circle_orthogonal τ hτ).subset
    intro u hu
    by_contra hy
    change inner ℝ (u:ℂ) τ≠0 at hy
    have hy':inner ℝ τ (u:ℂ)≠0:=by simpa only [real_inner_comm] using hy
    have hnq:inner ℝ n (u:ℂ)-(inner ℝ n ξ)*inner ℝ ξ (u:ℂ)≠0:=by
      rw [ordinary_tangent_support_form ξ n (u:ℂ) hξ]
      exact mul_ne_zero hcn hy'
    have hmq:inner ℝ m (u:ℂ)-(inner ℝ m ξ)*inner ℝ ξ (u:ℂ)≠0:=by
      rw [ordinary_tangent_support_form ξ m (u:ℂ) hξ]
      exact mul_ne_zero hcm hy'
    change ∀ᶠt:ℝ in 𝓝[>] (0:ℝ),ξ+t•(u:ℂ)∈A at hu
    obtain ⟨t,⟨htA,htn⟩,htm⟩:=((hu.and (ordinary_klein_support_cut_eventual n ξ (u:ℂ) hξ hnq)).and
      (ordinary_klein_support_cut_eventual m ξ (u:ℂ) hξ hmq)).exists
    have htK:=((fuchsianPolygon_euclideanClosure_klein_iff P D _).mp htA).2
    have hnneg:=htn.mp (hn _ htK)
    have hmneg:=htm.mp (hm _ htK)
    rw [ordinary_tangent_support_form ξ n (u:ℂ) hξ] at hnneg
    rw [ordinary_tangent_support_form ξ m (u:ℂ) hξ] at hmneg
    have hpos:=mul_pos_of_neg_of_neg hnneg hmneg
    have hneg:=mul_neg_of_neg_of_pos hprod (sq_pos_of_ne_zero hy')
    nlinarith
  change 2*Real.pi*(polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections A
    ξ)).toReal=0
  rw [hfin.measure_zero polygonDirectionMeasure,ENNReal.toReal_zero,mul_zero]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance ordinaryProperVertexSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance ordinaryProperVertexSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- A true original ideal side endpoint remains in the literal closed Klein side. -/
theorem fuchsian_side_ideal_endpoint_klein {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (S:Set P.domain.carrier) (u:Circle)
    (hu:IsFuchsianSideIdealEndpoint P S u) :
    (u:ℂ)∈closure (P.kleinCoordinate '' S) := by
  change (u:ℂ)∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' S) at hu
  have hh:=disc_ideal_closure_klein (u:ℂ) u.norm_coe (S:=P.finiteCoordinate '' S) (by
    simpa only [image_image] using hu)
  simpa only [image_image,_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.kleinCoordinate] using hh

/-- Proper ideal vertices have genuine zero Euclidean angle, for the original polygon with no ordinary or generic-centre restriction. -/
theorem IsConvexFuchsianPolygon.proper_ideal_angle_zero
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:IsProperFuchsianInfiniteVertex P D u) :
    fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=0 := by
  obtain ⟨_huE,S,T,hS,hT,hST,huS,huT⟩:=hu
  obtain ⟨g,hg,hSg⟩:=hS.1
  obtain ⟨h,hh,hTh⟩:=hT.1
  have hgh:g≠h:=by
    intro he
    apply hST
    rw [hSg,hTh,he]
  let U:=P.kleinCoordinate '' D
  let V:=P.kleinCoordinate '' (g•D)
  let W:=P.kleinCoordinate '' (h•D)
  have hDo:=hD.locallyFinite.fundamental.isOpen
  have hDn:=hD.locallyFinite.fundamental.isConnected.nonempty
  have hOpen (k:H):IsOpen (P.kleinCoordinate '' (k•D)):=
    P.kleinCoordinate_isOpenEmbedding.isOpenMap _ ((Homeomorph.smul k).isOpenMap _ hDo)
  have hNonempty (k:H):(P.kleinCoordinate '' (k•D)).Nonempty:=
    (hDn.image (fun x=>k•x)).image P.kleinCoordinate
  have hNorm (x:P.domain.carrier):‖P.kleinCoordinate x‖<1:=by
    apply mem_ball_zero_iff.mp
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact mem_range_self (P.finiteCoordinate x)
  have hSideCl (A:Set P.domain.carrier) (k:H) (he:A=closure D∩fuchsianDomainTile P D k):
      closure (P.kleinCoordinate '' A)⊆closure U∩closure (P.kleinCoordinate '' (k•D)):=by
    apply closure_minimal _ (isClosed_closure.inter isClosed_closure)
    rintro _ ⟨x,hx,rfl⟩
    rw [he] at hx
    exact ⟨mem_closure_image P.kleinCoordinate_isOpenEmbedding.continuous.continuousAt hx.1,
      P.klein_closed_tile_subset_closure D k ⟨x,hx.2,rfl⟩⟩
  have hξS:=hSideCl S g hSg (fuchsian_side_ideal_endpoint_klein P S u huS)
  have hξT:=hSideCl T h hTh (fuchsian_side_ideal_endpoint_klein P T u huT)
  obtain ⟨a₀,ha₀⟩:=hS.2.2.nonempty
  obtain ⟨b₀,hb₀⟩:=hT.2.2.nonempty
  let a:=P.kleinCoordinate a₀
  let b:=P.kleinCoordinate b₀
  have haS:a∈closure (P.kleinCoordinate '' S):=subset_closure ⟨a₀,ha₀,rfl⟩
  have hbT:b∈closure (P.kleinCoordinate '' T):=subset_closure ⟨b₀,hb₀,rfl⟩
  have haUV:=hSideCl S g hSg haS
  have hbUW:=hSideCl T h hTh hbT
  obtain ⟨n,t,hn,hnL,hnR⟩:=hD.exists_global_tile_separator g hg
  obtain ⟨m,s,hm,hmL,hmR⟩:=hD.exists_global_tile_separator h hh
  have hnL':∀z∈U,inner ℝ n z<t:=by rintro _ ⟨x,hx,rfl⟩;exact hnL x hx
  have hnR':∀z∈V,t < inner ℝ n z:=by rintro _ ⟨x,hx,rfl⟩;exact hnR x hx
  have hmL':∀z∈U,inner ℝ m z<s:=by rintro _ ⟨x,hx,rfl⟩;exact hmL x hx
  have hmR':∀z∈W,s < inner ℝ m z:=by rintro _ ⟨x,hx,rfl⟩;exact hmR x hx
  have hnξ:inner ℝ n (u:ℂ)=t:=_root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hnL' hnR' hξS
  have hmξ:inner ℝ m (u:ℂ)=s:=_root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hmL' hmR' hξT
  have hLn:∀z∈U,inner ℝ n (z-(u:ℂ))<0:=by
    intro z hz;rw [inner_sub_right,hnξ];exact sub_neg.mpr (hnL' z hz)
  have hRn:∀z∈V,0 < inner ℝ n (z-(u:ℂ)):=by
    intro z hz;rw [inner_sub_right,hnξ];exact sub_pos.mpr (hnR' z hz)
  have hLm:∀z∈U,inner ℝ m (z-(u:ℂ))<0:=by
    intro z hz;rw [inner_sub_right,hmξ];exact sub_neg.mpr (hmL' z hz)
  have hRm:∀z∈W,0 < inner ℝ m (z-(u:ℂ)):=by
    intro z hz;rw [inner_sub_right,hmξ];exact sub_pos.mpr (hmR' z hz)
  obtain ⟨w,hw⟩:=hDn
  have hqn:=ordinary_support_tangent_normal_ne_zero n (u:ℂ) (P.kleinCoordinate w)
    (P.kleinCoordinate (g•w)) u.norm_coe (hNorm w) (hNorm (g•w))
    (hLn _ ⟨w,hw,rfl⟩) (hRn _ ⟨g•w,⟨w,hw,rfl⟩,rfl⟩)
  have hqm:=ordinary_support_tangent_normal_ne_zero m (u:ℂ) (P.kleinCoordinate w)
    (P.kleinCoordinate (h•w)) u.norm_coe (hNorm w) (hNorm (h•w))
    (hLm _ ⟨w,hw,rfl⟩) (hRm _ ⟨h•w,⟨w,hw,rfl⟩,rfl⟩)
  have hprod:=ordinary_three_tile_tangents_opposite (u:ℂ) n m a b u.norm_coe (hNorm a₀) (hNorm b₀)
    hD.klein_convex (P.kleinCoordinate_isOpenEmbedding.isOpenMap _ hDo) (show U.Nonempty from ⟨P.kleinCoordinate
      w,w,hw,rfl⟩)
    (hD.klein_smul_convex g) (hOpen g) (hNonempty g)
    (hD.klein_smul_convex h) (hOpen h) (hNonempty h)
    (by simpa only [one_smul] using hD.locallyFinite.fundamental.klein_images_disjoint (Ne.symm hg))
    (by simpa only [one_smul] using hD.locallyFinite.fundamental.klein_images_disjoint (Ne.symm hh))
    (hD.locallyFinite.fundamental.klein_images_disjoint hgh)
    hξS.1 hξS.2 hξT.2 haUV.1 haUV.2 hbUW.1 hbUW.2 hn hLn hRn hm hLm hRm
    (ordinary_tangent_coefficient_ne_zero (u:ℂ) u.norm_coe n hqn)
    (ordinary_tangent_coefficient_ne_zero (u:ℂ) u.norm_coe m hqm)
  apply ordinary_opposite_supports_angle_zero P D (u:ℂ) n m u.norm_coe _ _ hprod
  · exact fun z hz=>closure_minimal (fun w hw=>(hLn w hw).le)
      (isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const) hz
  · exact fun z hz=>closure_minimal (fun w hw=>(hLm w hw).le)
      (isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const) hz

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine side endpoint belongs to both actual ideal closures of its paired tiles. -/
theorem fuchsian_side_ideal_endpoint_paired_tile {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D S:Set P.domain.carrier) (g:H)
    (hS:S=closure D∩fuchsianDomainTile P D g) (u:Circle)
    (hu:IsFuchsianSideIdealEndpoint P S u) :
    (u:ℂ)∈fuchsianPolygonIdealBoundary P (g•D) := by
  have hF:Continuous (fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)):=
    Complex.UnitDisc.continuous_coe.comp P.finiteCoordinate.continuous
  have hcl:closure (g•D)=g•closure D:=((Homeomorph.smul g).image_closure D).symm
  have hSub:(fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' S⊆
      closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' (g•D)):=by
    rintro _ ⟨x,hx,rfl⟩
    have hxG:x∈closure (g•D):=by rw [hcl];exact (hS ▸ hx).2
    exact mem_closure_image hF.continuousAt hxG
  exact (mem_fuchsianPolygonIdealBoundary P (g•D) (u:ℂ)).mpr
    ⟨closure_minimal hSub isClosed_closure hu,u.norm_coe⟩

/-- A real side endpoint cannot be interior to the ideal-circle trace at an ordinary point. -/
theorem IsConvexFuchsianPolygon.ordinary_side_endpoint_not_free_interior
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D S:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hS:IsFuchsianPolygonSide P D S) (u:Circle) (hu:IsFuchsianSideIdealEndpoint P S u)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    u∉interior (fuchsianPolygonIdealCircle P D) := by
  intro huInt
  obtain ⟨g,hg,hSg⟩:=hS.1
  have hTile:=fuchsian_side_ideal_endpoint_paired_tile P D S g hSg u hu
  exact hg (hD.ideal_closed_disc_germ_no_other_tile (u:ℂ)
    (hD.ordinary_free_interior_closed_germ u huInt hOrd) g hTile)

/-- An actual improper ordinary vertex has a genuine right Euclidean angle. -/
theorem IsConvexFuchsianPolygon.ordinary_improper_ideal_angle
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:IsImproperFuchsianInfiniteVertex P D u)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=Real.pi/2 := by
  obtain ⟨huE,S,F,hS,huS,hF,huF⟩:=hu
  have hInt:=hD.ordinary_side_endpoint_not_free_interior hS u huS hOrd
  have huFin:u∈F:=hF.isClosed.closure_eq ▸ frontier_subset_closure huF
  have hFE:F⊆fuchsianPolygonIdealCircle P D:=by
    obtain ⟨⟨v,_hv,rfl⟩,_⟩:=hF
    exact connectedComponentIn_subset _ _
  have hAccF:u∈closure (F\{u}):=by
    have hAcc:=IsPreconnected.preperfect_of_nontrivial hF.nontrivial hF.isConnected.isPreconnected u huFin
    rw [accPt_principal_iff_clusterPt,←mem_closure_iff_clusterPt] at hAcc
    exact hAcc
  have hAcc:u∈closure (fuchsianPolygonIdealCircle P D\{u}):=
    closure_mono (sdiff_subset_sdiff_left hFE) hAccF
  rw [hD.ordinary_ideal_angle_topology u huE hOrd,ite_eq_right hInt,
    ite_eq_right (not_not.mpr hAcc)]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine nontrivial compact connected circle interval has positive actual angular measure. -/
theorem ordinary_connected_circle_positive {F:Set Circle} (hc:IsConnected F) (hcl:IsClosed F)
    (hn:F.Nontrivial) : 0<polygonDirectionMeasure F := by
  obtain ⟨a,b,hab,_hlen,he⟩:=circle_compact_connected_arc hc hcl.isCompact hn
  have hExp:IsOpenMap (fun t:ℝ=>Circle.exp t):=by
    have hcomp:(fun t:ℝ=>AddCircle.homeomorphCircle' (t:AddCircle (2*Real.pi)))=
        (fun t:ℝ=>Circle.exp t):=by ext t;rfl
    rw [←hcomp]
    exact AddCircle.homeomorphCircle'.isOpenMap.comp QuotientAddGroup.isOpenMap_coe
  have hOp:IsOpen (Circle.exp '' Ioo a b):=hExp _ isOpen_Ioo
  have hNe:(Circle.exp '' Ioo a b).Nonempty:=(nonempty_Ioo.mpr hab).image _
  have hPos:=IsOpen.measure_pos polygonDirectionMeasure hOp hNe
  apply lt_of_lt_of_le hPos
  rw [he]
  exact measure_mono (image_mono Ioo_subset_Icc_self)

/-- A genuine one-sided ideal-circle germ produces a true positive-length free component with the original point on its frontier. -/
theorem ordinary_half_trace_free_endpoint {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (u:Circle) (σ:ℝ) (hσ:σ≠0)
    (hTrace:∀ᶠz:Circle in 𝓝 u,(z∈fuchsianPolygonIdealCircle P D ↔
      σ*inner ℝ (Complex.I*(u:ℂ)) (z:ℂ)≤0)) :
    ∃F:Set Circle,IsFuchsianFreeSide P D F∧u∈frontier F := by
  let E:=fuchsianPolygonIdealCircle P D
  let q:ℝ→Circle:=fun r=>ordinaryIdealCircleCurve u (-σ*r)
  have hq:Continuous q:=(ordinaryIdealCircleCurve_continuous u).comp (continuous_const.mul continuous_id)
  have hq0:q 0=u:=by simp [q,ordinaryIdealCircleCurve_zero]
  have hAlong:∀ᶠr:ℝ in 𝓝 (0:ℝ),(q r∈E ↔
      σ*inner ℝ (Complex.I*(u:ℂ)) (q r:ℂ)≤0):=by
    have hlim:Tendsto q (𝓝 (0:ℝ)) (𝓝 u):=by
      have hh:=hq.continuousAt.tendsto (x:=(0:ℝ))
      simpa only [hq0] using hh
    exact hlim.eventually hTrace
  obtain ⟨δ,hδ,hAll⟩:=Metric.mem_nhds_iff.mp hAlong
  let ε:ℝ:=δ/2
  have hε:0<ε:=half_pos hδ
  have hqE:q '' Icc (0:ℝ) ε⊆E:=by
    rintro _ ⟨r,hr,rfl⟩
    have hrB:r∈Metric.ball (0:ℝ) δ:=by
      rw [mem_ball_zero_iff,Real.norm_eq_abs,abs_of_nonneg hr.1]
      exact lt_of_le_of_lt hr.2 (by dsimp only [ε];linarith)
    apply (hAll hrB).mpr
    change σ*inner ℝ (Complex.I*(u:ℂ)) (ordinaryIdealCircleCurve u (-σ*r):ℂ)≤0
    rw [ordinaryIdealCircleCurve_tangent,←mul_div_assoc]
    have hnum:σ*(2*(-σ*r))≤0:=by
      have hh:=mul_nonneg (sq_nonneg σ) hr.1
      nlinarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  have hQU:u∈q '' Icc (0:ℝ) ε:=⟨0,⟨le_rfl,hε.le⟩,hq0⟩
  have hQC:IsConnected (q '' Icc (0:ℝ) ε):=
    (isConnected_Icc hε.le).image q hq.continuousOn
  have hQN:(q '' Icc (0:ℝ) ε).Nontrivial:=by
    refine ⟨u,hQU,q ε,⟨ε,⟨hε.le,le_rfl⟩,rfl⟩,?_⟩
    intro he
    have hzero: -σ*ε=0:=(ordinaryIdealCircleCurve_eq_iff u (-σ*ε)).mp he.symm
    exact (mul_ne_zero (neg_ne_zero.mpr hσ) hε.ne') hzero
  have huE:u∈E:=hqE hQU
  let F:=connectedComponentIn E u
  have hFsub:F⊆E:=connectedComponentIn_subset _ _
  have hQF:q '' Icc (0:ℝ) ε⊆F:=
    hQC.isPreconnected.subset_connectedComponentIn hQU hqE
  have hFC:IsConnected F:=isConnected_connectedComponentIn_iff.mpr huE
  have hFcl:IsClosed F:=isClosed_connectedComponentIn_of_isClosed (fuchsianPolygonIdealCircle_isClosed P D) huE
  have hFPos:0<polygonDirectionMeasure F:=ordinary_connected_circle_positive hFC hFcl (hQN.mono hQF)
  have hF:IsFuchsianFreeSide P D F:=⟨⟨u,huE,rfl⟩,hFPos⟩
  have hNoInt:u∉interior E:=(ordinary_half_circle_trace_types E u σ hσ hTrace).1
  have huF:u∈F:=mem_connectedComponentIn huE
  have hNoIntF:u∉interior F:=fun h=>hNoInt (interior_mono hFsub h)
  exact ⟨F,hF,⟨hFcl.closure_eq.symm ▸ huF,hNoIntF⟩⟩

/-- Every ordinary ideal point with an actual right angle is a genuine free-side endpoint. -/
theorem IsConvexFuchsianPolygon.ordinary_right_angle_free_endpoint
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hAngle:fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=Real.pi/2) :
    ∃F:Set Circle,IsFuchsianFreeSide P D F∧u∈frontier F := by
  obtain ⟨s,c,hc,hTrace,hDir⟩:=hD.ordinary_ideal_tangential_trace u hu hOrd
  let I:={g:H // g∈s∧g≠1}
  let C:Set Circle:={v | inner ℝ (u:ℂ) (v:ℂ)<0∧
    ∀i:I,c i*inner ℝ (Complex.I*(u:ℂ)) (v:ℂ)<0}
  have hA:2*Real.pi*(polygonDirectionMeasure C).toReal=Real.pi/2:=by
    have hM:polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalDirections
        (closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' D)) (u:ℂ))=
        polygonDirectionMeasure C:=by
      apply measure_congr
      filter_upwards [hDir] with v hv
      exact propext hv
    exact (congrArg (fun r:ENNReal=>2*Real.pi*r.toReal) hM).symm.trans hAngle
  have hProfile:=ordinary_tangential_cone_angle_profile u c hc
  change (IsEmpty I∧2*Real.pi*(polygonDirectionMeasure C).toReal=Real.pi)∨
    ((∃i j,0<c i∧c j<0)∧2*Real.pi*(polygonDirectionMeasure C).toReal=0)∨
    (Nonempty I∧((∀i,0<c i)∨(∀i,c i<0))∧2*Real.pi*(polygonDirectionMeasure C).toReal=Real.pi/2) at hProfile
  rcases hProfile with ⟨_,hval⟩|⟨_,hval⟩|⟨⟨i₀⟩,hSign,_hval⟩
  · exfalso;linarith [Real.pi_pos]
  · exfalso;linarith [Real.pi_pos]
  · apply ordinary_half_trace_free_endpoint P D u (c i₀) (hc i₀)
    filter_upwards [hTrace] with z hz
    rw [hz]
    constructor
    · exact fun h=>h i₀
    · intro hi i
      rcases hSign with hpos|hneg
      · exact mul_nonpos_of_nonneg_of_nonpos (hpos i).le
          (nonpos_of_mul_nonpos_right hi (hpos i₀))
      · exact mul_nonpos_of_nonpos_of_nonneg (hneg i).le
          (nonneg_of_mul_nonpos_right hi (hneg i₀))

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine two-point ordinary cycle consists of right-angle free-side endpoints; the original point is a common endpoint for the original polygon and a nonidentity translate. -/
theorem IsConvexFuchsianPolygon.ordinary_two_point_cycle_free_endpoints
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u v:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D) (huv:u≠v)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hCycle:fuchsianPolygonIdealCircleCycle P D u={u,v}) :
    fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=Real.pi/2 ∧
      fuchsianPolygonEuclideanIdealAngle P D (v:ℂ)=Real.pi/2 ∧
      ∃g:H,g≠1∧∃F G:Set Circle,IsFuchsianFreeSide P D F∧
        IsFuchsianFreeSide P (g•D) G∧u∈frontier F∧u∈frontier G := by
  have hvC:v∈fuchsianPolygonIdealCircleCycle P D u:=hCycle.symm ▸ (by simp)
  obtain ⟨hv,g,hgv⟩:=hvC
  have hOrdV:HasMobiusOrdinaryNeighborhood H ((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=
    hgv ▸ hOrd.smul_ordinary g
  have hback:g⁻¹•((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [←hgv,inv_smul_smul]
  have hNoIntU:u∉interior (fuchsianPolygonIdealCircle P D):=by
    intro hInt
    have hvExt:((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈fuchsianPolygonIdealCycle P D ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=
      ⟨⟨(v:ℂ),hv,rfl⟩,g,hgv⟩
    rw [hD.ordinary_free_interior_cycle_singleton u hInt hOrd] at hvExt
    exact huv (Subtype.ext (OnePoint.coe_injective (mem_singleton_iff.mp hvExt)).symm)
  have hNoIntV:v∉interior (fuchsianPolygonIdealCircle P D):=by
    intro hInt
    have huExt:((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈fuchsianPolygonIdealCycle P D ((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=
      ⟨⟨(u:ℂ),hu,rfl⟩,g⁻¹,hback⟩
    rw [hD.ordinary_free_interior_cycle_singleton v hInt hOrdV] at huExt
    exact huv (Subtype.ext (OnePoint.coe_injective (mem_singleton_iff.mp huExt)))
  have hAu:fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)≤Real.pi/2:=by
    rw [hD.ordinary_ideal_angle_topology u hu hOrd,ite_eq_right hNoIntU]
    split_ifs <;> linarith [Real.pi_pos]
  have hAv:fuchsianPolygonEuclideanIdealAngle P D (v:ℂ)≤Real.pi/2:=by
    rw [hD.ordinary_ideal_angle_topology v hv hOrdV,ite_eq_right hNoIntV]
    split_ifs <;> linarith [Real.pi_pos]
  have hSum:=hD.ordinary_idealCircleCycle_angle_sum u hu hOrd
  have ht:(hD.ordinary_idealCircleCycle_finite u hOrd).toFinset={u,v}:=by
    apply Finset.coe_injective
    simpa only [Set.Finite.coe_toFinset,Finset.coe_pair] using hCycle
  rw [ht,Finset.sum_pair huv] at hSum
  have hAuEq:fuchsianPolygonEuclideanIdealAngle P D (u:ℂ)=Real.pi/2:=by linarith
  have hAvEq:fuchsianPolygonEuclideanIdealAngle P D (v:ℂ)=Real.pi/2:=by linarith
  have hg:g≠1:=by
    intro he
    rw [he,one_smul] at hgv
    exact huv (Subtype.ext (OnePoint.coe_injective hgv))
  have huTile:u∈fuchsianPolygonIdealCircle P (g⁻¹•D):=
    P.idealBoundary_smul D g⁻¹ (v:ℂ) (u:ℂ) hv hback
  have hInv:P.ordinaryCircleAction g⁻¹ v=u:=by
    apply Subtype.ext
    apply OnePoint.coe_injective
    rw [P.ordinaryCircleAction_sphere]
    exact hback
  have hTileAngle:=hD.ordinary_ideal_angle_smul g⁻¹ v hv hOrdV
  rw [hInv] at hTileAngle
  obtain ⟨F,hF,huF⟩:=hD.ordinary_right_angle_free_endpoint u hu hOrd hAuEq
  obtain ⟨G,hG,huG⟩:=(hD.smul_polygon g⁻¹).ordinary_right_angle_free_endpoint u huTile hOrd
    (hTileAngle.trans hAvEq)
  exact ⟨hAuEq,hAvEq,g⁻¹,inv_ne_one.mpr hg,F,G,hF,hG,huF,huG⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise Complex.UnitDisc Classical
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A finite system of actual support cuts has an attained upper boundary whenever one tangential coefficient is positive. -/
theorem ordinary_finite_cuts_upper {ι:Type*} [Finite ι] (a c:ι→ℝ) (k₀:ℝ)
    (hstrict:∀i,c i*k₀<a i) (hpos:∃i,0<c i) :
    ∃k:ℝ,k₀<k ∧ (∀i,c i*k≤a i) ∧ ∃i,0<c i ∧ c i*k=a i := by
  classical
  let I:={i:ι // 0<c i}
  let : Nonempty I:=⟨⟨hpos.choose,hpos.choose_spec⟩⟩
  obtain ⟨i,hi⟩:=Finite.exists_min (fun i:I=>a i.val/c i.val)
  let k:=a i.val/c i.val
  have hk:k₀<k:=(lt_div_iff₀ i.property).mpr (by simpa only [mul_comm] using hstrict i.val)
  refine ⟨k,hk,?_,i.val,i.property,?_⟩
  · intro j
    by_cases hj:0<c j
    · have hb:k≤a j/c j:=hi ⟨j,hj⟩
      simpa only [mul_comm] using (le_div_iff₀ hj).mp hb
    · have hc:c j≤0:=le_of_not_gt hj
      exact (mul_le_mul_of_nonpos_left hk.le hc).trans (hstrict j).le
  · dsimp only [k]
    field_simp [i.property.ne']

/-- The lower boundary follows by reversing the true tangential coordinate. -/
theorem ordinary_finite_cuts_lower {ι:Type*} [Finite ι] (a c:ι→ℝ) (k₀:ℝ)
    (hstrict:∀i,c i*k₀<a i) (hneg:∃i,c i<0) :
    ∃k:ℝ,k<k₀ ∧ (∀i,c i*k≤a i) ∧ ∃i,c i<0 ∧ c i*k=a i := by
  obtain ⟨k,hk,hall,i,hi,he⟩:=ordinary_finite_cuts_upper a (fun i=>-c i) (-k₀)
    (by simpa only [neg_mul_neg] using hstrict) (by simpa only [neg_pos] using hneg)
  refine ⟨-k,by linarith,?_,i,by linarith,?_⟩
  · intro j
    simpa only [neg_mul,mul_neg] using hall j
  · simpa only [neg_mul,mul_neg] using he

/-- An actual boundary ray approaching an ordinary ideal point belongs to the compactified endpoint of a genuine original side. -/
theorem IsConvexFuchsianPolygon.ordinary_boundary_ray_side
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (u:Circle) (hOrd:HasMobiusOrdinaryNeighborhood H
      ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (v:ℂ) (_hv:v≠0)
    (hRay:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),
      (u:ℂ)+t•v∈P.kleinCoordinate '' frontier D) :
    ∃S:Set P.domain.carrier,IsFuchsianPolygonSide P D S ∧
      IsFuchsianSideIdealEndpoint P S u ∧
      ∃x∈S,∃t:ℝ,0<t ∧ P.kleinCoordinate x=(u:ℂ)+t•v := by
  classical
  obtain ⟨N,hN,huN,hfin⟩:=hD.ordinary_klein_neighborhood_finite (u:ℂ) u.norm_coe hOrd
  let F:=hfin.toFinset.filter (fun g:H=>g≠1)
  let R:Set ℂ:={z | ∃t:ℝ,0<t ∧ z=(u:ℂ)+t•v}
  let A:H→Set ℂ:=fun g=>(P.kleinCoordinate '' (closure D∩fuchsianDomainTile P D g))∩R
  have hcont:Continuous (fun t:ℝ=>(u:ℂ)+t•v):=continuous_const.add (continuous_id.smul continuous_const)
  have hlim:Tendsto (fun t:ℝ=>(u:ℂ)+t•v) (𝓝[>] (0:ℝ)) (𝓝 (u:ℂ)):=by
    convert hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp only [zero_smul,add_zero]
  have hUnion:∀ᶠt:ℝ in 𝓝[>] (0:ℝ),(u:ℂ)+t•v∈⋃g∈F,A g:=by
    filter_upwards [hRay,hlim.eventually (hN.mem_nhds huN),self_mem_nhdsWithin] with t ht htN htpos
    obtain ⟨x,hx,hxe⟩:=ht
    obtain ⟨S,hS,hxS⟩:=hD.boundary_mem_side hx
    obtain ⟨g,hg,heS,_⟩:=hD.side_iff.mp hS
    have hxS':x∈closure D∩fuchsianDomainTile P D g:=heS ▸ hxS
    have hgF:g∈F:=Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr
      ⟨P.kleinCoordinate x,P.klein_closed_tile_subset_closure D g ⟨x,hxS'.2,rfl⟩,
        hxe.symm ▸ htN⟩,hg⟩
    exact mem_iUnion₂.mpr ⟨g,hgF,⟨⟨x,hxS',hxe⟩,t,htpos,rfl⟩⟩
  have hucl:(u:ℂ)∈closure (⋃g∈F,A g):=mem_closure_of_tendsto hlim hUnion
  rw [F.closure_biUnion] at hucl
  obtain ⟨g,hgF,hug⟩:=mem_iUnion₂.mp hucl
  have hg:g≠1:=(Finset.mem_filter.mp hgF).2
  let S:=closure D∩fuchsianDomainTile P D g
  have huK:(u:ℂ)∈closure (P.kleinCoordinate '' S):=
    closure_mono inter_subset_left hug
  have hnot:(u:ℂ)∉P.kleinCoordinate '' S:=by
    rintro ⟨x,_hx,he⟩
    have hxnorm:‖P.kleinCoordinate x‖<1:=by
      exact mem_ball_zero_iff.mp (show P.kleinCoordinate x∈Metric.ball (0:ℂ) 1 from by
        rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate];exact mem_range_self (P.finiteCoordinate x))
    rw [he,u.norm_coe] at hxnorm
    exact lt_irrefl _ hxnorm
  have hnontr:S.Nontrivial:=by
    by_contra hn
    have hsing:S.Subsingleton:=Set.not_nontrivial_iff.mp hn
    exact hnot ((hsing.image P.kleinCoordinate).isClosed.closure_eq ▸ huK)
  have hS:IsFuchsianPolygonSide P D S:=hD.side_of_nontrivial_intersection hg hnontr
  have huE:IsFuchsianSideIdealEndpoint P S u:=by
    change (u:ℂ)∈closure ((fun x:P.domain.carrier=>(P.finiteCoordinate x:ℂ)) '' S)
    have he:closure (P.kleinCoordinate '' S)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ''
        fuchsianSideClosedModel (⟨S,hS⟩:FuchsianPolygonSides P D):=
      (fuchsianSideClosedModel_klein_image (⟨S,hS⟩:FuchsianPolygonSides P D)).symm
    obtain ⟨q,hq,hqu⟩:=he ▸ huK
    have hq:q=Complex.UnitClosedDisc.mk (u:ℂ) u.norm_coe.le:=by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.injective
      exact hqu.trans (congrArg (fun z:𝕔𝔻=>(z:ℂ))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed (Complex.UnitClosedDisc.mk
          (u:ℂ) u.norm_coe.le) u.norm_coe)).symm
    subst q
    have ham:=(fuchsianSideClosedModel_ambient (⟨S,hS⟩:FuchsianPolygonSides P D)) ▸
      mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended hq
    exact ((mem_fuchsianPolygonIdealBoundary P S (u:ℂ)).mp
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P S (u:ℂ)).mpr ⟨u.norm_coe,ham⟩)).1
  obtain ⟨z,hz⟩:=closure_nonempty_iff.mp ⟨(u:ℂ),hug⟩
  obtain ⟨x,hx,hxz⟩:=hz.1
  obtain ⟨t,ht,hzt⟩:=hz.2
  exact ⟨S,hS,huE,x,hx,t,ht,hxz.trans hzt⟩

/-- A true inward straight ray at the unit circle enters the actual disc for all sufficiently small positive parameters. -/
theorem ordinary_inward_ray_ball (u:Circle) (v:ℂ)
    (hv:inner ℝ (u:ℂ) v=-1) :
    ∀ᶠt:ℝ in 𝓝[>] (0:ℝ),(u:ℂ)+t•v∈Metric.ball (0:ℂ) 1 := by
  have hbound:0<1/(‖v‖^2+1):=by positivity
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds hbound)] with t ht htbound
  have hb:t*(‖v‖^2+1)<1:=(lt_div_iff₀ (by positivity : 0<‖v‖^2+1)).mp htbound
  have he:‖(u:ℂ)+t•v‖^2=1-2*t+t^2*‖v‖^2:=by
    rw [norm_add_sq_real,u.norm_coe,real_inner_smul_right,hv,norm_smul,Real.norm_eq_abs]
    rw [mul_pow,sq_abs]
    ring
  apply mem_ball_zero_iff.mpr
  have hmul:=mul_lt_mul_of_pos_left (show t*‖v‖^2<1 by nlinarith) ht
  nlinarith [norm_nonneg ((u:ℂ)+t•v)]

/-- A genuine active affine support ray is an actual polygon-frontier ray. -/
theorem IsConvexFuchsianPolygon.ordinary_active_cut_ray
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    {ι:Type*} (u:Circle) (n:ι→ℂ) (N:Set ℂ) (hN:IsOpen N) (huN:(u:ℂ)∈N)
    (hstrict:∀i,∀z∈P.kleinCoordinate '' D,inner ℝ (n i) (z-(u:ℂ))<0)
    (hGerm:closure (P.kleinCoordinate '' D)∩N∩Metric.closedBall (0:ℂ) 1=
      {z | ∀i,inner ℝ (n i) (z-(u:ℂ))≤0}∩N∩Metric.closedBall (0:ℂ) 1)
    (v:ℂ) (hv:inner ℝ (u:ℂ) v=-1)
    (hweak:∀i,inner ℝ (n i) v≤0) (heq:∃i,inner ℝ (n i) v=0) :
    ∀ᶠt:ℝ in 𝓝[>] (0:ℝ),(u:ℂ)+t•v∈P.kleinCoordinate '' frontier D := by
  have hcont:Continuous (fun t:ℝ=>(u:ℂ)+t•v):=continuous_const.add (continuous_id.smul continuous_const)
  have hlim:Tendsto (fun t:ℝ=>(u:ℂ)+t•v) (𝓝[>] (0:ℝ)) (𝓝 (u:ℂ)):=by
    convert hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp only [zero_smul,add_zero]
  filter_upwards [ordinary_inward_ray_ball u v hv,hlim.eventually (hN.mem_nhds huN),
    self_mem_nhdsWithin] with t htBall htN ht
  let z:ℂ:=(u:ℂ)+t•v
  have hzcl:z∈closure (P.kleinCoordinate '' D):=by
    have hh:z∈{z | ∀i,inner ℝ (n i) (z-(u:ℂ))≤0}∩N∩Metric.closedBall (0:ℂ) 1:=by
      refine ⟨⟨?_,htN⟩,Metric.ball_subset_closedBall htBall⟩
      intro i
      dsimp only [z]
      rw [add_sub_cancel_left,real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hweak i)
    exact ((hGerm ▸ hh : z∈closure (P.kleinCoordinate '' D)∩N∩Metric.closedBall (0:ℂ) 1)).1.1
  have hznot:z∉P.kleinCoordinate '' D:=by
    intro hmem
    obtain ⟨i,hi⟩:=heq
    have hlt:=hstrict i z hmem
    dsimp only [z] at hlt
    rw [add_sub_cancel_left,real_inner_smul_right,hi,mul_zero] at hlt
    exact lt_irrefl _ hlt
  have hzRange:z∈range P.kleinCoordinate:=by
    change z∈range (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ∘ P.finiteCoordinate)
    rw [range_comp,P.finiteCoordinate.surjective.range_eq,image_univ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact htBall
  obtain ⟨x,hxz⟩:=hzRange
  refine ⟨x,?_,hxz⟩
  have hDo:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  rw [frontier,hDo.interior_eq]
  refine ⟨?_,fun hx=>hznot (hxz ▸ mem_image_of_mem P.kleinCoordinate hx)⟩
  rw [P.kleinCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
  change P.kleinCoordinate x∈closure (P.kleinCoordinate '' D)
  rwa [hxz]

/-- Distinct inward slopes at the same actual ideal endpoint cannot lie on one original geodesic side. -/
theorem IsConvexFuchsianPolygon.ordinary_ray_sides_distinct
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (u:Circle) (k l:ℝ) (hkl:k≠l) (S T:Set P.domain.carrier)
    (hS:IsFuchsianPolygonSide P D S) (hT:IsFuchsianPolygonSide P D T)
    (huS:IsFuchsianSideIdealEndpoint P S u)
    (hxS:∃x∈S,∃t:ℝ,0<t ∧ P.kleinCoordinate x=(u:ℂ)+t•(-(u:ℂ)+k•(Complex.I*(u:ℂ))))
    (hxT:∃x∈T,∃t:ℝ,0<t ∧ P.kleinCoordinate x=(u:ℂ)+t•(-(u:ℂ)+l•(Complex.I*(u:ℂ)))) : S≠T := by
  intro he
  subst T
  obtain ⟨n,a,hn,_hl,_hcl,hline⟩:=hD.side_global_support hS
  have huLine:inner ℝ n (u:ℂ)=a:=by
    have hsub:closure (P.kleinCoordinate '' S)⊆{z:ℂ | inner ℝ n z=a}:=
      closure_minimal (by rintro _ ⟨x,hx,rfl⟩;exact hline x hx)
        (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    exact hsub (fuchsian_side_ideal_endpoint_klein P S u huS)
  have horth (q:ℝ)
      (hq:∃x∈S,∃t:ℝ,0<t ∧ P.kleinCoordinate x=(u:ℂ)+t•(-(u:ℂ)+q•(Complex.I*(u:ℂ)))) :
      -(inner ℝ n (u:ℂ))+q*inner ℝ n (Complex.I*(u:ℂ))=0:=by
    obtain ⟨x,hx,t,ht,hxt⟩:=hq
    have hh:=hline x hx
    rw [hxt,inner_add_right,real_inner_smul_right,inner_add_right,inner_neg_right,
      real_inner_smul_right,huLine] at hh
    simpa only [huLine] using
      (mul_eq_zero.mp (by linarith : t*(-a+q*inner ℝ n (Complex.I*(u:ℂ)))=0)).resolve_left ht.ne'
  have hk:=horth k hxS
  have hl:=horth l hxT
  have hc:inner ℝ n (Complex.I*(u:ℂ))=0:=by
    have heq:(k-l)*inner ℝ n (Complex.I*(u:ℂ))=0:=by nlinarith
    exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hkl)
  have ha:inner ℝ n (u:ℂ)=0:=by rw [hc,mul_zero] at hk;linarith
  apply hn
  rw [ordinary_circle_frame (u:ℂ) u.norm_coe n,ha,hc,zero_smul,zero_smul,add_zero]

/-- Every ordinary ideal point outside the actual free-circle interior is a genuine proper or improper infinite vertex, with original side incidences. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_vertex_classification
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hInt:u∉interior (fuchsianPolygonIdealCircle P D)) :
    IsProperFuchsianInfiniteVertex P D u ∨ IsImproperFuchsianInfiniteVertex P D u := by
  classical
  obtain ⟨s,n,N,hN,huN,_hs,hn,hGerm⟩:=hD.ordinary_ideal_finite_halfplanes (u:ℂ) hu hOrd
  let I:={g:H // g∈s∧g≠1}
  let : Finite I:=Finite.of_injective (fun i:I=>(⟨i.val,i.property.1⟩:s)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun i:s=>i.val) h))
  let ξ:ℂ:=(u:ℂ)
  let τ:ℂ:=Complex.I*ξ
  let a:I→ℝ:=fun i=>inner ℝ (n i) ξ
  let c:I→ℝ:=fun i=>inner ℝ (n i) τ
  have hnorm (x:P.domain.carrier):‖P.kleinCoordinate x‖<1:=by
    apply mem_ball_zero_iff.mp
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact mem_range_self (P.finiteCoordinate x)
  obtain ⟨w,hw⟩:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hnq (i:I):n i-(inner ℝ (n i) ξ)•ξ≠0:=by
    apply ordinary_support_tangent_normal_ne_zero (n i) ξ (P.kleinCoordinate w)
      (P.kleinCoordinate (i.val•w)) u.norm_coe (hnorm w) (hnorm (i.val•w))
    · exact (hn i).2.1 _ ⟨w,hw,rfl⟩
    · exact (hn i).2.2 _ ⟨i.val•w,⟨w,hw,rfl⟩,rfl⟩
  have hc:∀i,c i≠0:=fun i=>ordinary_tangent_coefficient_ne_zero ξ u.norm_coe (n i) (hnq i)
  have hTrace:∀ᶠz:Circle in 𝓝 u,(z∈fuchsianPolygonIdealCircle P D ↔
      ∀i:I,c i*inner ℝ τ (z:ℂ)≤0):=by
    have hNear:∀ᶠz:Circle in 𝓝 u,(z:ℂ)∈N:=
      continuous_subtype_val.continuousAt.tendsto.eventually (hN.mem_nhds huN)
    have hCuts:∀ᶠz:Circle in 𝓝 u,∀i:I,
        (inner ℝ (n i) ((z:ℂ)-ξ)≤0 ↔ c i*inner ℝ τ (z:ℂ)≤0):=
      Filter.eventually_all.mpr (fun i=>ordinary_circle_support_trace_germ u (n i) (hnq i))
    filter_upwards [hNear,hCuts] with z hzN hzCuts
    have hzB:(z:ℂ)∈Metric.closedBall (0:ℂ) 1:=mem_closedBall_zero_iff.mpr z.norm_coe.le
    have hfix:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z:ℂ)=(z:ℂ):=by
      simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,z.norm_coe,one_pow];norm_num
    change (z:ℂ)∈fuchsianPolygonIdealBoundary P D ↔ _
    rw [mem_fuchsianPolygonIdealBoundary,fuchsianPolygon_euclideanClosure_klein_iff,
      hfix,z.norm_coe]
    simp only [le_refl,and_true,true_and]
    have hh:((z:ℂ)∈closure (P.kleinCoordinate '' D)) ↔
        ∀i:I,inner ℝ (n i) ((z:ℂ)-ξ)≤0:=by
      constructor
      · intro hz
        exact ((hGerm ▸ (show (z:ℂ)∈closure (P.kleinCoordinate '' D)∩N∩Metric.closedBall (0:ℂ) 1 from
          ⟨⟨hz,hzN⟩,hzB⟩))).1.1
      · intro hz
        exact ((hGerm ▸ (show (z:ℂ)∈{z | ∀i:I,inner ℝ (n i) (z-ξ)≤0}∩N∩Metric.closedBall (0:ℂ) 1 from
          ⟨⟨hz,hzN⟩,hzB⟩) : (z:ℂ)∈closure (P.kleinCoordinate '' D)∩N∩Metric.closedBall (0:ℂ) 1)).1.1
    exact hh.trans (forall_congr' hzCuts)
  have hI:Nonempty I:=by
    by_contra hne
    have : IsEmpty I:=not_nonempty_iff.mp hne
    apply hInt
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hTrace] with z hz
    exact hz.mpr (fun i=>isEmptyElim i)
  let k₀:ℝ:=inner ℝ τ (P.kleinCoordinate w)/(1-inner ℝ ξ (P.kleinCoordinate w))
  have hd:0<1-inner ℝ ξ (P.kleinCoordinate w):=by
    have hle:=real_inner_le_norm ξ (P.kleinCoordinate w)
    have hξn:‖ξ‖=1:=u.norm_coe
    rw [hξn,one_mul] at hle
    linarith [hnorm w]
  have hstrict:∀i,c i*k₀<a i:=by
    intro i
    have hlt:inner ℝ (n i) (P.kleinCoordinate w-ξ)<0:=(hn i).2.1 _ ⟨w,hw,rfl⟩
    have hframe:=ordinary_circle_frame ξ u.norm_coe (n i)
    have he:inner ℝ (n i) (P.kleinCoordinate w-ξ)=
        a i*(inner ℝ ξ (P.kleinCoordinate w)-1)+c i*inner ℝ τ (P.kleinCoordinate w):=by
      conv_lhs => rw [hframe]
      simp only [inner_add_left,real_inner_smul_left,inner_sub_right]
      have hξself:inner ℝ ξ ξ=1:=by rw [real_inner_self_eq_norm_sq,u.norm_coe,one_pow]
      have hτξ:inner ℝ τ ξ=0:=by simp [τ,ξ,Complex.inner];ring
      rw [hξself,hτξ]
      dsimp only [a,c,τ]
      ring
    rw [he] at hlt
    dsimp only [k₀]
    rw [←mul_div_assoc,div_lt_iff₀ hd]
    nlinarith
  have hinner (k:ℝ):inner ℝ ξ (-ξ+k•τ)=-1:=by
    have hξself:inner ℝ ξ ξ=1:=by rw [real_inner_self_eq_norm_sq,u.norm_coe,one_pow]
    have hξτ:inner ℝ ξ τ=0:=by simp [τ,ξ,Complex.inner];ring
    rw [inner_add_right,inner_neg_right,real_inner_smul_right,hξself,hξτ,mul_zero,add_zero]
  have hSide (k:ℝ) (hall:∀i,c i*k≤a i) (heq:∃i,c i*k=a i) :
      ∃S:Set P.domain.carrier,IsFuchsianPolygonSide P D S ∧ IsFuchsianSideIdealEndpoint P S u ∧
        ∃x∈S,∃t:ℝ,0<t ∧ P.kleinCoordinate x=ξ+t•(-ξ+k•τ):=by
    have hform (i:I):inner ℝ (n i) (-ξ+k•τ)=-a i+k*c i:=by
      rw [inner_add_right,inner_neg_right,real_inner_smul_right]
    apply hD.ordinary_boundary_ray_side u hOrd (-ξ+k•τ)
      (by intro hv;have hh:=hinner k;rw [hv,inner_zero_right] at hh;norm_num at hh)
    apply hD.ordinary_active_cut_ray u n N hN huN (fun i=>(hn i).2.1) hGerm
      (-ξ+k•τ) (hinner k)
    · intro i;rw [hform];nlinarith [hall i]
    · obtain ⟨i,hi⟩:=heq
      exact ⟨i,by rw [hform];nlinarith⟩
  have hFree (i₀:I) (hsign:(∀i,0<c i)∨(∀i,c i<0)) :
      ∃F:Set Circle,IsFuchsianFreeSide P D F∧u∈frontier F:=by
    apply ordinary_half_trace_free_endpoint P D u (c i₀) (hc i₀)
    filter_upwards [hTrace] with z hz
    rw [hz]
    constructor
    · exact fun h=>h i₀
    · intro hi i
      rcases hsign with hpos|hneg
      · exact mul_nonpos_of_nonneg_of_nonpos (hpos i).le
          (nonpos_of_mul_nonpos_right hi (hpos i₀))
      · exact mul_nonpos_of_nonpos_of_nonneg (hneg i).le
          (nonneg_of_mul_nonpos_right hi (hneg i₀))
  by_cases hpos:∃i,0<c i
  · obtain ⟨k,hk,hall,i,hi,heq⟩:=ordinary_finite_cuts_upper a c k₀ hstrict hpos
    obtain ⟨S,hS,huS,hxS⟩:=hSide k hall ⟨i,heq⟩
    by_cases hneg:∃i,c i<0
    · obtain ⟨l,hl,hlall,j,_hj,hjeq⟩:=ordinary_finite_cuts_lower a c k₀ hstrict hneg
      obtain ⟨T,hT,huT,hxT⟩:=hSide l hlall ⟨j,hjeq⟩
      exact Or.inl ⟨hu,S,T,hS,hT,hD.ordinary_ray_sides_distinct u k l (by linarith) S T hS hT huS hxS hxT,huS,huT⟩
    · have hsign:∀j,0<c j:=by
        intro j
        exact lt_of_le_of_ne (le_of_not_gt (fun h=>hneg ⟨j,h⟩)) (Ne.symm (hc j))
      obtain ⟨F,hF,huF⟩:=hFree i (Or.inl hsign)
      exact Or.inr ⟨hu,S,F,hS,huS,hF,huF⟩
  · obtain ⟨i₀⟩:=hI
    have hsign:∀j,c j<0:=by
      intro j
      exact lt_of_le_of_ne (le_of_not_gt (fun h=>hpos ⟨j,h⟩)) (hc j)
    obtain ⟨k,_hk,hall,i,_hi,heq⟩:=ordinary_finite_cuts_lower a c k₀ hstrict ⟨i₀,hsign i₀⟩
    obtain ⟨S,hS,huS,_hxS⟩:=hSide k hall ⟨i,heq⟩
    obtain ⟨F,hF,huF⟩:=hFree i (Or.inr hsign)
    exact Or.inr ⟨hu,S,F,hS,huS,hF,huF⟩

/-- A literal circle-interior point of the actual ideal trace is interior to a genuine positive-length free side. -/
theorem ordinary_ideal_interior_free_side {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (D:Set P.domain.carrier) (u:Circle)
    (hu:u∈interior (fuchsianPolygonIdealCircle P D)) :
    ∃F:Set Circle,IsFuchsianFreeSide P D F∧u∈interior F := by
  have hExp:IsOpenMap (fun t:ℝ=>Circle.exp t):=by
    have hcomp:(fun t:ℝ=>AddCircle.homeomorphCircle' (t:AddCircle (2*Real.pi)))=
        (fun t:ℝ=>Circle.exp t):=by ext t;rfl
    rw [←hcomp]
    exact AddCircle.homeomorphCircle'.isOpenMap.comp QuotientAddGroup.isOpenMap_coe
  let : LocallyConnectedSpace Circle:=
    (hExp.isQuotientMap Circle.exp.continuous Circle.exp_surjective).isCoinducing.locallyConnectedSpace
  let E:=fuchsianPolygonIdealCircle P D
  let F:=connectedComponentIn E u
  have hN:F∈𝓝 u:=connectedComponentIn_mem_nhds (mem_interior_iff_mem_nhds.mp hu)
  have hFi:u∈interior F:=mem_interior_iff_mem_nhds.mpr hN
  have hp:0<polygonDirectionMeasure F:=
    (IsOpen.measure_pos polygonDirectionMeasure isOpen_interior ⟨u,hFi⟩).trans_le
      (measure_mono interior_subset)
  exact ⟨F,⟨⟨u,interior_subset hu,rfl⟩,hp⟩,hFi⟩

/-- An ordinary ideal point lies in a free-side interior or is a proper or improper infinite vertex. -/
theorem IsConvexFuchsianPolygon.ordinary_ideal_point_classification
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (u:Circle)
    (hu:u∈fuchsianPolygonIdealCircle P D)
    (hOrd:HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    (∃F:Set Circle,IsFuchsianFreeSide P D F∧u∈interior F) ∨
      IsProperFuchsianInfiniteVertex P D u ∨ IsImproperFuchsianInfiniteVertex P D u := by
  by_cases hInt:u∈interior (fuchsianPolygonIdealCircle P D)
  · exact Or.inl (ordinary_ideal_interior_free_side P D u hInt)
  · exact Or.inr (hD.ordinary_ideal_vertex_classification u hu hOrd hInt)

end LowDimensionalTopology.Geometry.Fuchsian
