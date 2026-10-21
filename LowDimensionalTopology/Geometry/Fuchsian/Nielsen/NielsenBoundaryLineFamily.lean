/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenGapLines
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenBoundaryCharts
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreCriterion

/-!
# Actual finite Nielsen-core polygon geometry
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance nielsenBoundaryLineFamilySphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenBoundaryLineFamilySphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

theorem nielsen_discLine_carrier_injective : Function.Injective Hyperbolic.DiscLine.carrier := by
  intro L M h
  apply Hyperbolic.DiscLine.toHalfPlane_injective
  apply Hyperbolic.HalfPlaneLine.carrier_injective
  have he:=congrArg (fun S:Set 𝔻=>Hyperbolic.discToHalfPlane '' S) h
  rw [L.carrier_eq_cayley_image_halfPlane,M.carrier_eq_cayley_image_halfPlane,image_image,image_image] at he
  simpa only [Hyperbolic.discToHalfPlane_halfPlaneToDisc,Set.image_id'] using he

def nielsenBoundaryDiscLineFamily {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hNE : DiscreteGroups.IsNonElementary H) : Set Hyperbolic.DiscLine :=
  {L | ∃G:Hyperbolic.NielsenHalfPlaneGap,G.carrier∈Auxiliary.Topology.nielsenRealGapFamily
    (Hyperbolic.nielsenHalfPlaneRealSet
    (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
      (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))) ∧
    P.finiteCoordinate '' ((nielsenHalfPlaneChart P hNE).symm '' G.line.carrier)=L.carrier}

theorem nielsenBoundaryDiscLineFamily_subset_frontier
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) :
    L.carrier⊆P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE) := by
  obtain ⟨G,hG,hGL⟩:=hL
  let A:=Hyperbolic.nielsenHalfPlaneRealSet
    (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
      (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))
  have ho : IsOpen (Hyperbolic.nielsenRealArcRegion A) := by
    rw [←nielsenHalfPlaneChart_core_image P hNE]
    exact (nielsenHalfPlaneChart P hNE).isOpenMap _ (fuchsianNielsenCore_isOpen P hNE)
  have hnCore : (fuchsianNielsenCore P hNE).Nonempty := by
    obtain ⟨x,hx⟩:=(P.asFuchsianDisc.nielsenRegion_properties hNE).2.1
    exact ⟨⟨x,(P.asFuchsianDisc.nielsenRegion_properties hNE).1 hx⟩,hx⟩
  have hn : (Hyperbolic.nielsenRealArcRegion A).Nonempty := by
    rw [←nielsenHalfPlaneChart_core_image P hNE]
    exact hnCore.image _
  rw [←hGL]
  apply image_mono
  rintro x ⟨z,hz,rfl⟩
  have hf := nielsenGap_line_subset_frontier A ho hn G hG hz
  rw [←nielsenHalfPlaneChart_frontier_image P hNE] at hf
  obtain ⟨y,hy,hye⟩:=hf
  simpa only [←hye,Homeomorph.symm_apply_apply] using hy

theorem nielsenBoundaryDiscLineFamily_frontier_cover
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hNE : DiscreteGroups.IsNonElementary H) :
    P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE)=
      ⋃L:Hyperbolic.DiscLine,⋃_:L∈nielsenBoundaryDiscLineFamily P hNE,L.carrier := by
  apply subset_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    let A:=Hyperbolic.nielsenHalfPlaneRealSet
      (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
        (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))
    have ho : IsOpen (Hyperbolic.nielsenRealArcRegion A) := by
      rw [←nielsenHalfPlaneChart_core_image P hNE]
      exact (nielsenHalfPlaneChart P hNE).isOpenMap _ (fuchsianNielsenCore_isOpen P hNE)
    have hxF : nielsenHalfPlaneChart P hNE x∈frontier (Hyperbolic.nielsenRealArcRegion A) := by
      rw [←nielsenHalfPlaneChart_frontier_image P hNE]
      exact mem_image_of_mem _ hx
    obtain ⟨G,hG,hxG⟩:=nielsenRealArcRegion_frontier_exists_gap A ho _ hxF
    obtain ⟨L,hL⟩:=nielsenGap_original_native_line P hNE G
    refine mem_iUnion.mpr ⟨L,mem_iUnion.mpr ⟨⟨G,hG,hL⟩,?_⟩⟩
    rw [←hL]
    exact mem_image_of_mem _ ⟨nielsenHalfPlaneChart P hNE x,hxG,
      (nielsenHalfPlaneChart P hNE).symm_apply_apply x⟩
  · intro z hz
    obtain ⟨L,hz⟩:=mem_iUnion.mp hz
    obtain ⟨hL,hzL⟩:=mem_iUnion.mp hz
    exact nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hzL

theorem nielsenBoundaryDiscLineFamily_pairwise_disjoint
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hNE : DiscreteGroups.IsNonElementary H) :
    (nielsenBoundaryDiscLineFamily P hNE).PairwiseDisjoint Hyperbolic.DiscLine.carrier := by
  intro L hL M hM hne
  obtain ⟨G,hG,hGL⟩:=hL
  obtain ⟨J,hJ,hJM⟩:=hM
  have hneG : G.carrier≠J.carrier := by
    intro he
    have hline := nielsenGap_line_eq_of_carrier_eq G J he
    have heC : L.carrier=M.carrier := hGL.symm.trans (hline ▸ hJM)
    exact hne (nielsen_discLine_carrier_injective heC)
  have hdG := Auxiliary.Topology.nielsenRealGapFamily_pairwiseDisjoint _ hG hJ hneG
  rcases Hyperbolic.nielsen_gap_lines_eq_or_disjoint G J hdG with he | hd
  · exact False.elim (hne (nielsen_discLine_carrier_injective (hGL.symm.trans (he ▸ hJM))))
  · change Disjoint L.carrier M.carrier
    rw [←hGL,←hJM]
    apply disjoint_left.mpr
    rintro z ⟨x,⟨u,hu,rfl⟩,hx⟩ ⟨y,⟨v,hv,rfl⟩,hy⟩
    have he : u=v := (nielsenHalfPlaneChart P hNE).symm.injective
      (P.finiteCoordinate.injective (hx.trans hy.symm))
    exact disjoint_left.mp hd hu (he.symm ▸ hv)

theorem nielsenBoundaryDiscLineFamily_compact_hits_finite
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H)
    (K:Set P.domain.carrier) (hK:IsCompact K) :
    {L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧
      (L.carrier∩P.finiteCoordinate '' K).Nonempty}.Finite := by
  let A:=Hyperbolic.nielsenHalfPlaneRealSet
    (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
      (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))
  let E:=nielsenHalfPlaneChart P hNE
  let F:= {S:Set ℝ | S∈Auxiliary.Topology.nielsenRealGapFamily A ∧ ∃G:Hyperbolic.NielsenHalfPlaneGap,
    G.carrier=S ∧ (G.line.carrier∩E '' K).Nonempty}
  have hF:F.Finite:=nielsenRealGapFamily_compact_line_hits_finite A
    (Hyperbolic.nielsenHalfPlaneRealSet_isClosed _ (DiscreteGroups.mobiusLimitSet_isClosed _)) (E '' K)
      (hK.image E.continuous)
  let B (S:Set ℝ):Set Hyperbolic.DiscLine:={L | ∃G:Hyperbolic.NielsenHalfPlaneGap,G.carrier=S ∧
    P.finiteCoordinate '' (E.symm '' G.line.carrier)=L.carrier}
  have hB (S:Set ℝ): (B S).Finite := by
    apply Set.Subsingleton.finite
    rintro L ⟨G,hGS,hGL⟩ M ⟨J,hJS,hJM⟩
    have he:=nielsenGap_line_eq_of_carrier_eq G J (hGS.trans hJS.symm)
    exact nielsen_discLine_carrier_injective (hGL.symm.trans (he ▸ hJM))
  apply (hF.biUnion (fun S _=>hB S)).subset
  rintro L ⟨⟨G,hG,hGL⟩,z,hzL,x,hxK,hxz⟩
  have hzIm : z∈P.finiteCoordinate '' (E.symm '' G.line.carrier) := hGL.symm ▸ hzL
  obtain ⟨u,⟨v,hv,rfl⟩,hu⟩:=hzIm
  have hux : E.symm v=x:=P.finiteCoordinate.injective (hu.trans hxz.symm)
  have hEx : E x=v := by rw [←hux,E.apply_symm_apply]
  have hFS : G.carrier∈F:=⟨hG,G,rfl,v,hv,x,hxK,hEx⟩
  exact mem_iUnion₂.mpr ⟨G.carrier,hFS,G,rfl,hGL⟩

theorem nielsenBoundaryDiscLineFamily_finite_hits
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H)
    (V:Set 𝔻) (hV:V.Finite) :
    {L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧ (L.carrier∩V).Nonempty}.Finite := by
  have hAt (x:𝔻) : {L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧ x∈L.carrier}.Finite := by
    apply Set.Subsingleton.finite
    rintro L ⟨hL,hxL⟩ M ⟨hM,hxM⟩
    by_contra hne
    have hd:=nielsenBoundaryDiscLineFamily_pairwise_disjoint P hNE hL hM hne
    exact disjoint_left.mp hd hxL hxM
  apply (hV.biUnion (fun x _=>hAt x)).subset
  rintro L ⟨hL,x,hxL,hxV⟩
  exact mem_iUnion₂.mpr ⟨x,hxV,hL,hxL⟩

theorem finite_nielsenCore_boundary_lines
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    {L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧
      (L.carrier∩P.finiteCoordinate '' closure (D∩fuchsianNielsenCore P hNE)).Nonempty}.Finite := by
  let N:=fuchsianNielsenCore P hNE
  let Q:=D∩N
  by_cases hi:(Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' Q)).Nonempty
  · obtain ⟨p,hp⟩:=hi
    let V:=frontier D∩frontier N
    have hV:V.Finite:=finite_nielsenCore_boundary_crossings_of_ideal hD hNE ha w hwD hwN p hp
    have hMeet:=nielsenBoundaryDiscLineFamily_finite_hits P hNE (P.finiteCoordinate '' V)
      (hV.image P.finiteCoordinate)
    have hWhole:=finite_ideal_boundary_whole_lines P Q (finite_nielsenCore_idealBoundary hD hNE ha)
    apply (hMeet.union hWhole).subset
    rintro L ⟨hL,z,hzL,x,hxQ,hxz⟩
    by_cases hcross:(L.carrier∩P.finiteCoordinate '' frontier D).Nonempty
    · left
      refine ⟨hL,?_⟩
      obtain ⟨a,haL,b,hbD,hba⟩:=hcross
      have haN:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL haL
      obtain ⟨c,hcN,hca⟩:=haN
      have hcb:c=b:=P.finiteCoordinate.injective (hca.trans hba.symm)
      refine ⟨a,haL,b,⟨hbD,?_⟩,hba⟩
      exact hcb ▸ hcN
    · right
      let S:=P.finiteCoordinate.symm '' L.carrier
      have hpre:IsPreconnected S:=L.hConvex.isPreconnected.image _ P.finiteCoordinate.symm.continuous.continuousOn
      have havoid:Disjoint S (frontier D) := by
        apply disjoint_left.mpr
        rintro y ⟨v,hv,rfl⟩ hy
        exact hcross ⟨v,hv,P.finiteCoordinate.symm v,hy,P.finiteCoordinate.apply_symm_apply v⟩
      have hxS:x∈S:=⟨z,hzL,(P.finiteCoordinate.eq_symm_apply.mpr hxz).symm⟩
      have hxclD:x∈closure D:=closure_mono inter_subset_left hxQ
      have hxD:x∈D := by
        by_contra hn
        exact disjoint_left.mp havoid hxS
          ((hD.locallyFinite.fundamental.isOpen.frontier_eq).symm ▸ ⟨hxclD,hn⟩)
      have hSD:S⊆D:=preconnected_subset_open_of_avoids_frontier hpre
        hD.locallyFinite.fundamental.isOpen ⟨x,hxS,hxD⟩ havoid
      intro v hvL
      let y:=P.finiteCoordinate.symm v
      have hyS:y∈S:=⟨v,hvL,rfl⟩
      have hyN:y∈frontier N := by
        obtain ⟨u,hu,huv⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hvL
        have huy:u=y:=P.finiteCoordinate.injective (huv.trans (P.finiteCoordinate.apply_symm_apply v).symm)
        exact huy ▸ hu
      refine ⟨y,?_,P.finiteCoordinate.apply_symm_apply v⟩
      rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
      exact ⟨subset_closure (hSD hyS),frontier_subset_closure hyN⟩
  · have hc:=Fuchsian.native_closure_compact_of_idealTrace_empty (P.finiteCoordinate '' Q) hi
    rw [←P.finiteCoordinate.image_closure] at hc
    exact nielsenBoundaryDiscLineFamily_compact_hits_finite P hNE (closure Q)
      (P.finiteCoordinate.isEmbedding.isCompact_iff.mpr hc)

end LowDimensionalTopology.Geometry.Fuchsian
