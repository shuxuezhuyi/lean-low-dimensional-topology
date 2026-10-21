/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenNormalizedRegion
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenModelGeometry
@[expose] public section
open Set
open scoped Topology OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
noncomputable section

/-- The actual source maximal-arc construction transported by a genuine whole-domain chart. -/
def nielsenRegionInChart
    (H : Subgroup Mobius.complexMobiusGroup)
    (q : Mobius.complexMobiusGroup) : Set (OnePoint ℂ):=
  nielsenModelSet q (Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet
    (DiscreteGroups.Action.Actions.subgroupConjugate q H)))

theorem FuchsianDisc.nielsenRegionInChart_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet) :
    nielsenRegionInChart H q⊆D.carrier:=nielsen_modelSet_subset q hq _

theorem FuchsianDisc.nielsenRegionInChart_isOpen
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H) (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet
      (DiscreteGroups.Action.Actions.subgroupConjugate q H)) :
    IsOpen (nielsenRegionInChart H q) :=
  nielsen_modelSet_isOpen q _ ((D.nielsenConjugate q).nielsenHalfPlaneArcRegion_isOpen hq (hH.conjugation q) hinf)

theorem FuchsianDisc.nielsenRegionInChart_nonempty
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H) (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet
      (DiscreteGroups.Action.Actions.subgroupConjugate q H)) :
    (nielsenRegionInChart H q).Nonempty :=
  (((D.nielsenConjugate q).nielsenHalfPlaneArcRegion_nonempty hq (hH.conjugation q) hinf).image _).image _

theorem FuchsianDisc.nielsenRegionInChart_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H) (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet
      (DiscreteGroups.Action.Actions.subgroupConjugate q H)) :
    D.HyperbolicallyConvex (nielsenRegionInChart H q) := by
  apply (D.hyperbolicallyConvex_iff_chart q hq _ (D.nielsenRegionInChart_subset q hq)).mpr
  rw [nielsenRegionInChart,nielsen_modelSet_coordinate]
  exact (D.nielsenConjugate q).nielsenHalfPlaneArcRegion_hConvex hq (hH.conjugation q) hinf

theorem FuchsianDisc.nielsenRegionInChart_invariant
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H) (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet
      (DiscreteGroups.Action.Actions.subgroupConjugate q H)) :
    ∀g : H,∀p∈nielsenRegionInChart H q,g • p∈nielsenRegionInChart H q := by
  intro g p hp
  obtain ⟨w,⟨z,hz,rfl⟩,rfl⟩:=hp
  let k : DiscreteGroups.Action.Actions.subgroupConjugate q H:=⟨q*g.val*q⁻¹,
    (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g.val,g.property,rfl⟩⟩
  have hi:=(D.nielsenConjugate q).nielsenHalfPlaneArcRegion_invariant hq (hH.conjugation q) hinf
    k (Hyperbolic.extendedHalfPlanePoint z) (mem_image_of_mem _ hz)
  obtain ⟨u,hu,hue⟩:=hi
  refine ⟨Hyperbolic.extendedHalfPlanePoint u,mem_image_of_mem _ hu,?_⟩
  change q⁻¹ • Hyperbolic.extendedHalfPlanePoint u=g.val • (q⁻¹ • Hyperbolic.extendedHalfPlanePoint z)
  rw [hue]
  change q⁻¹ • ((q*g.val*q⁻¹) • Hyperbolic.extendedHalfPlanePoint z)=g.val • (q⁻¹ • Hyperbolic.extendedHalfPlanePoint z)
  simp only [mul_smul,inv_smul_smul]

theorem FuchsianDisc.nielsenRegionInChart_minimal
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H) (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet
      (DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (S : Set (OnePoint ℂ)) (hSD : S⊆D.carrier) (hopen : IsOpen S) (hne : S.Nonempty)
    (hc : D.HyperbolicallyConvex S) (hi : ∀g : H,∀p∈S,g • p∈S) : nielsenRegionInChart H q⊆S := by
  let T:=nielsenModelCoordinateSet q S
  have hSimage : q.val '' S⊆Hyperbolic.openHalfPlaneSet:=by rw [←hq];exact image_mono hSD
  have hTimage:=nielsen_modelCoordinate_image q S hSimage
  have hTi : ∀k : DiscreteGroups.Action.Actions.subgroupConjugate q H,∀p∈Hyperbolic.extendedHalfPlanePoint '' T,
      k • p∈Hyperbolic.extendedHalfPlanePoint '' T:=by
    intro k p hp
    rw [hTimage] at hp ⊢
    obtain ⟨s,hs,rfl⟩:=hp
    obtain ⟨g,hg,hgk⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H k.val).mp k.property
    refine ⟨g • s,hi ⟨g,hg⟩ s hs,?_⟩
    change q • (g • s)=k.val • (q • s)
    rw [←hgk]
    simp only [mul_smul,inv_smul_smul]
  have hm:=(D.nielsenConjugate q).nielsenHalfPlaneArcRegion_minimal hq (hH.conjugation q) hinf T
    (nielsen_modelCoordinate_isOpen q S hopen) (nielsen_modelCoordinate_nonempty q S hSimage hne)
    ((D.hyperbolicallyConvex_iff_chart q hq S hSD).mp hc) hTi
  have hh:=image_mono (image_mono hm (f:=Hyperbolic.extendedHalfPlanePoint)) (f:=q⁻¹.val)
  change nielsenRegionInChart H q⊆nielsenModelSet q (nielsenModelCoordinateSet q S) at hh
  rwa [nielsen_modelSet_coordinate_inverse q S hSimage] at hh

/-- Independence from the genuine boundary point and whole-disc chart used in the actual arc construction. -/
theorem FuchsianDisc.nielsenRegionInChart_independent
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (q r : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hr : r.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H) (hiq : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet
      (DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (hir : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate r H)) :
    nielsenRegionInChart H q=nielsenRegionInChart H r := by
  apply Set.Subset.antisymm
  · exact D.nielsenRegionInChart_minimal q hq hH hiq _ (D.nielsenRegionInChart_subset r hr)
      (D.nielsenRegionInChart_isOpen r hr hH hir) (D.nielsenRegionInChart_nonempty r hr hH hir)
      (D.nielsenRegionInChart_convex r hr hH hir) (D.nielsenRegionInChart_invariant r hr hH hir)
  · exact D.nielsenRegionInChart_minimal r hr hH hir _ (D.nielsenRegionInChart_subset q hq)
      (D.nielsenRegionInChart_isOpen q hq hH hiq) (D.nielsenRegionInChart_nonempty q hq hH hiq)
      (D.nielsenRegionInChart_convex q hq hH hiq) (D.nielsenRegionInChart_invariant q hq hH hiq)

/-- A genuine chart from the proved original-domain normalization, with no additional assumption. -/
def FuchsianDisc.nielsenArcNormalizer {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : DiscreteGroups.IsNonElementary H) : Mobius.complexMobiusGroup:=
  Classical.choose (D.nielsenNormalizer_exists hH)

theorem FuchsianDisc.nielsenArcNormalizer_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : DiscreteGroups.IsNonElementary H) :
    (D.nielsenArcNormalizer hH).val '' D.carrier=Hyperbolic.openHalfPlaneSet:=
  (Classical.choose_spec (D.nielsenNormalizer_exists hH)).1

theorem FuchsianDisc.nielsenArcNormalizer_limit
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : DiscreteGroups.IsNonElementary H) :
    (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
      (D.nielsenArcNormalizer hH) H):=
  (Classical.choose_spec (D.nielsenNormalizer_exists hH)).2

/--
The actual maximal complementary-arc open-halfplane construction
in the original geometric disc. Its geometric properties and least-set theorem are proved below.
-/
def FuchsianDisc.nielsenRegion {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hH : DiscreteGroups.IsNonElementary H) : Set (OnePoint ℂ):=
  nielsenRegionInChart H (D.nielsenArcNormalizer hH)


/-- All original geometric hypotheses are retained in the original disc. -/
theorem FuchsianDisc.nielsenRegion_properties
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : DiscreteGroups.IsNonElementary H) :
    D.nielsenRegion hH⊆D.carrier ∧ (D.nielsenRegion hH).Nonempty ∧ IsOpen (D.nielsenRegion hH) ∧
      D.HyperbolicallyConvex (D.nielsenRegion hH) ∧
      (∀g : H,∀p∈D.nielsenRegion hH,g • p∈D.nielsenRegion hH) :=
  ⟨D.nielsenRegionInChart_subset _ (D.nielsenArcNormalizer_image hH),
    D.nielsenRegionInChart_nonempty _ (D.nielsenArcNormalizer_image hH) hH (D.nielsenArcNormalizer_limit hH),
    D.nielsenRegionInChart_isOpen _ (D.nielsenArcNormalizer_image hH) hH (D.nielsenArcNormalizer_limit hH),
    D.nielsenRegionInChart_convex _ (D.nielsenArcNormalizer_image hH) hH (D.nielsenArcNormalizer_limit hH),
    D.nielsenRegionInChart_invariant _ (D.nielsenArcNormalizer_image hH) hH (D.nielsenArcNormalizer_limit hH)⟩

/-- For the independently defined genuine source arc construction. -/
theorem FuchsianDisc.nielsenRegion_isLeast_nonempty_open_invariant_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : DiscreteGroups.IsNonElementary H) :
    IsLeast {S : Set (OnePoint ℂ) | S⊆D.carrier ∧ S.Nonempty ∧ IsOpen S ∧ D.HyperbolicallyConvex S ∧
      (∀g : H,∀p∈S,g • p∈S)} (D.nielsenRegion hH) := by
  refine ⟨D.nielsenRegion_properties hH,?_⟩
  rintro S ⟨hSD,hne,hopen,hc,hi⟩
  exact D.nielsenRegionInChart_minimal _ (D.nielsenArcNormalizer_image hH) hH
    (D.nielsenArcNormalizer_limit hH) S hSD hopen hne hc hi

theorem nielsenHalfPlaneArcRegion_full_boundary : Hyperbolic.nielsenHalfPlaneArcRegion Hyperbolic.halfPlaneIdealBoundary=univ := by
  apply Set.eq_univ_of_forall
  intro z G hG
  obtain ⟨p,hp,_⟩:=hG
  exact (hp.2 hp.1).elim

/-- The original first-kind convention follows from the actual empty complementary-arc family. -/
theorem FuchsianDisc.nielsenRegionInChart_firstKind
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hfirst : D.IsFirstKind) : nielsenRegionInChart H q=D.carrier := by
  have hLim : DiscreteGroups.mobiusLimitSet H=frontier D.carrier:=by
    rw [←fuchsianLimitSet_eq_nonElementary H hH]
    exact hfirst
  have hqfront : q.val '' frontier D.carrier=Hyperbolic.halfPlaneIdealBoundary:=by
    change (Mobius.mobiusBoundaryHomeomorph q) '' frontier D.carrier=_
    rw [Homeomorph.image_frontier]
    change frontier (q.val '' D.carrier)=_
    rw [hq,nielsen_openHalfPlane_frontier]
  have hK : DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)=Hyperbolic.halfPlaneIdealBoundary:=by
    rw [←nielsen_mobiusLimitSet_conjugation H q,hLim,hqfront]
  change nielsenModelSet q (Hyperbolic.nielsenHalfPlaneArcRegion _)=D.carrier
  rw [hK,nielsenHalfPlaneArcRegion_full_boundary,nielsenModelSet,image_univ,nielsen_halfPlanePoint_range]
  rw [←hq,nielsen_mobius_inverse_image]

theorem FuchsianDisc.nielsenRegion_firstKind
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hH : DiscreteGroups.IsNonElementary H)
    (hfirst : D.IsFirstKind) :
    D.nielsenRegion hH=D.carrier :=
  D.nielsenRegionInChart_firstKind _ (D.nielsenArcNormalizer_image hH) hH hfirst


/-- The original maximal complementary arcs of the true invariant boundary circle. -/
def FuchsianDisc.nielsenArcFamily
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    Set (Set (OnePoint ℂ)):=
  {J | ∃p∈frontier D.carrier\DiscreteGroups.mobiusLimitSet H,J=connectedComponentIn (frontier
    D.carrier\DiscreteGroups.mobiusLimitSet H) p}

theorem FuchsianDisc.nielsen_ordinaryBoundary_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet) :
    q.val '' (frontier D.carrier\DiscreteGroups.mobiusLimitSet H)=
      Hyperbolic.halfPlaneIdealBoundary\DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  rw [image_sdiff q.val.injective,nielsen_mobiusLimitSet_conjugation]
  congr 1
  change (Mobius.mobiusBoundaryHomeomorph q) '' frontier D.carrier=_
  rw [Homeomorph.image_frontier]
  change frontier (q.val '' D.carrier)=_
  rw [hq,nielsen_openHalfPlane_frontier]

theorem FuchsianDisc.nielsenArcFamily_chart_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet) :
    (fun J : Set (OnePoint ℂ)=>q.val '' J) '' D.nielsenArcFamily=
      Hyperbolic.nielsenHalfPlaneArcFamily (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)) := by
  ext J
  constructor
  · rintro ⟨S,⟨p,hp,rfl⟩,rfl⟩
    refine ⟨q.val p,?_,?_⟩
    · rw [←D.nielsen_ordinaryBoundary_image q hq]
      exact mem_image_of_mem _ hp
    · change (Mobius.mobiusBoundaryHomeomorph q) '' connectedComponentIn _ p=_
      rw [(Mobius.mobiusBoundaryHomeomorph q).image_connectedComponentIn hp]
      change connectedComponentIn (q.val '' _) (q.val p)=_
      rw [D.nielsen_ordinaryBoundary_image q hq]
  · rintro ⟨p,hp,rfl⟩
    rw [←D.nielsen_ordinaryBoundary_image q hq] at hp
    obtain ⟨s,hs,rfl⟩:=hp
    refine ⟨connectedComponentIn (frontier D.carrier\DiscreteGroups.mobiusLimitSet H) s,⟨s,hs,rfl⟩,?_⟩
    change (Mobius.mobiusBoundaryHomeomorph q) '' connectedComponentIn _ s=_
    rw [(Mobius.mobiusBoundaryHomeomorph q).image_connectedComponentIn hs]
    change connectedComponentIn (q.val '' _) (q.val s)=_
    rw [D.nielsen_ordinaryBoundary_image q hq]

theorem FuchsianDisc.nielsenArcFamily_chart_mem
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (J : Set (OnePoint ℂ)) :
    J∈D.nielsenArcFamily ↔ q.val '' J∈Hyperbolic.nielsenHalfPlaneArcFamily (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)) := by
  rw [←D.nielsenArcFamily_chart_image q hq]
  exact q.val.injective.image_injective.mem_set_image.symm

theorem FuchsianDisc.nielsenArcFamily_gap_mem
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (G : Hyperbolic.NielsenHalfPlaneGap) :
    q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈D.nielsenArcFamily ↔
      Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈Hyperbolic.nielsenHalfPlaneArcFamily
        (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)) := by
  rw [D.nielsenArcFamily_chart_mem q hq]
  rw [show q.val '' (q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier))=Hyperbolic.nielsenRealBoundaryPoint
    '' G.carrier from
    q.val.image_symm_image _]

/-- No original maximal complementary arc is omitted from the genuine geodesic construction. -/
theorem FuchsianDisc.nielsenArcFamily_exists_gap
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H) (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet
      (DiscreteGroups.Action.Actions.subgroupConjugate q H))
    {J : Set (OnePoint ℂ)} (hJ : J∈D.nielsenArcFamily) :
    ∃G : Hyperbolic.NielsenHalfPlaneGap,q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=J := by
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hK : DiscreteGroups.IsNonElementary K:=hH.conjugation q
  have hB:=(D.nielsenConjugate q).nielsenHalfPlane_limit_subset hq
  have hi : (DiscreteGroups.mobiusLimitSet
    K).Infinite:=fun hf=>DiscreteGroups.mobiusLimitSet_not_countable K hK hf.countable
  obtain ⟨G,hG⟩:=Hyperbolic.nielsenHalfPlaneArcFamily_exists_gap (DiscreteGroups.mobiusLimitSet
    K) (DiscreteGroups.mobiusLimitSet_isClosed K)
    (Hyperbolic.nielsenHalfPlaneRealSet_infinite _ hi hB hinf).nonempty hinf
    ((D.nielsenArcFamily_chart_mem q hq J).mp hJ)
  exact ⟨G,by rw [hG,nielsen_mobius_inverse_image]⟩

/-- Exact original-disc intersection formula using all actual maximal complementary arcs
and the opposite actual open geodesic half-planes, excluding their boundary geodesics. -/
theorem FuchsianDisc.nielsenRegionInChart_eq_arc_intersection
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet) :
    nielsenRegionInChart H q={p | p∈D.carrier ∧ ∀G : Hyperbolic.NielsenHalfPlaneGap,
      q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈D.nielsenArcFamily →
      p∈nielsenModelSet q G.keptSide} := by
  ext p
  constructor
  · intro hp
    refine ⟨D.nielsenRegionInChart_subset q hq hp,?_⟩
    obtain ⟨w,⟨z,hz,rfl⟩,rfl⟩:=hp
    intro G hG
    apply (nielsen_modelSet_point_mem q G.keptSide z).mpr
    exact hz G ((D.nielsenArcFamily_gap_mem q hq G).mp hG)
  · rintro ⟨hp,hside⟩
    have hpH : q.val p∈Hyperbolic.openHalfPlaneSet:=by rw [←hq];exact mem_image_of_mem _ hp
    obtain ⟨z,hz⟩:=nielsen_halfPlanePoint_range.symm ▸ hpH
    have he : q⁻¹.val (Hyperbolic.extendedHalfPlanePoint z)=p:=by
      change q.val.symm (Hyperbolic.extendedHalfPlanePoint z)=p
      rw [hz,q.val.symm_apply_apply]
    refine ⟨Hyperbolic.extendedHalfPlanePoint z,⟨z,?_,rfl⟩,he⟩
    intro G hG
    apply (nielsen_modelSet_point_mem q G.keptSide z).mp
    rw [he]
    exact hside G ((D.nielsenArcFamily_gap_mem q hq G).mpr hG)

/-- These are the actual complementary components in the original geometric disc. -/
theorem FuchsianDisc.nielsenArcSide_eq_component
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (G : Hyperbolic.NielsenHalfPlaneGap) (z : ℍ) (hz : z∈G.keptSide) :
    nielsenModelSet q G.keptSide=
      connectedComponentIn (D.carrier\nielsenModelSet q G.line.carrier) (q⁻¹.val (Hyperbolic.extendedHalfPlanePoint z)) := by
  rw [G.keptSide_eq_openHalfPlane z hz]
  exact nielsen_modelSet_openHalfPlane q hq G.line z
    (Set.disjoint_left.mp G.keptSide_disjoint_line hz)


theorem nielsen_gap_idealEndpoints_limit_subset (Λ : Set (OnePoint ℂ))
    (hinf : (∞ : OnePoint ℂ)∈Λ) (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈Hyperbolic.nielsenHalfPlaneArcFamily Λ) : G.line.idealEndpoints⊆Λ := by
  have hm : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet Λ):=by
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage Λ hinf] at hG
    exact Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.injective.image_injective.mem_set_image.mp hG
  obtain ⟨x,hx,hGx⟩:=hm
  have hend (y : ℝ) (hy : y∈closure G.carrier) (hyn : y∉G.carrier) : Hyperbolic.nielsenRealBoundaryPoint y∈Λ:=by
    apply Auxiliary.Topology.nielsen_realGap_endpoint_mem hx
    · rwa [←hGx]
    · rwa [←hGx]
  cases G with
  | bounded a b hab =>
    have ha : Hyperbolic.nielsenRealBoundaryPoint a∈Λ:=hend a
      (by change a∈closure (Ioo a b);rw [closure_Ioo hab.ne];exact ⟨le_refl _,hab.le⟩)
      (by change a∉Ioo a b;exact fun hh=>lt_irrefl a hh.1)
    have hb : Hyperbolic.nielsenRealBoundaryPoint b∈Λ:=hend b
      (by change b∈closure (Ioo a b);rw [closure_Ioo hab.ne];exact ⟨hab.le,le_refl _⟩)
      (by change b∉Ioo a b;exact fun hh=>lt_irrefl b hh.2)
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    exact Set.pair_subset ha hb
  | left b =>
    have hb : Hyperbolic.nielsenRealBoundaryPoint b∈Λ:=hend b
      (by change b∈closure (Iio b);rw [closure_Iio];exact le_refl _)
      (by change b∉Iio b;exact lt_irrefl b)
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    exact Set.pair_subset hb hinf
  | right a =>
    have ha : Hyperbolic.nielsenRealBoundaryPoint a∈Λ:=hend a
      (by change a∈closure (Ioi a);rw [closure_Ioi];exact le_refl _)
      (by change a∉Ioi a;exact lt_irrefl a)
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    exact Set.pair_subset ha hinf

theorem FuchsianDisc.nielsenArcGeodesic_idealEndpoints
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (G : Hyperbolic.NielsenHalfPlaneGap) :
    closure (nielsenModelSet q G.line.carrier)∩frontier D.carrier=q⁻¹.val '' G.line.idealEndpoints := by
  have hcancel (S : Set (OnePoint ℂ)) : q.val '' (q⁻¹.val '' S)=S:=q.val.image_symm_image S
  have hfront : q.val '' frontier D.carrier=Hyperbolic.halfPlaneIdealBoundary:=by
    change (Mobius.mobiusBoundaryHomeomorph q) '' frontier D.carrier=_
    rw [Homeomorph.image_frontier]
    change frontier (q.val '' D.carrier)=_
    rw [hq,nielsen_openHalfPlane_frontier]
  have hc : q.val '' closure (nielsenModelSet q G.line.carrier)=closure (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier):=by
    change (Mobius.mobiusBoundaryHomeomorph q) '' closure (nielsenModelSet q G.line.carrier)=_
    rw [Homeomorph.image_closure]
    change closure (q.val '' (q⁻¹.val '' (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)))=_
    rw [hcancel]
  apply q.val.injective.image_injective
  rw [image_inter q.val.injective,hc,hfront,hcancel]
  rfl

theorem FuchsianDisc.nielsenArcGeodesic_endpoints_subset_limit
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)) (G :
      Hyperbolic.NielsenHalfPlaneGap)
    (hG : q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)∈D.nielsenArcFamily) :
    closure (nielsenModelSet q G.line.carrier)∩frontier D.carrier⊆DiscreteGroups.mobiusLimitSet H := by
  rw [D.nielsenArcGeodesic_idealEndpoints q hq G]
  have hh:=image_mono (nielsen_gap_idealEndpoints_limit_subset _ hinf G
    ((D.nielsenArcFamily_gap_mem q hq G).mp hG)) (f:=q⁻¹.val)
  rw [←nielsen_mobiusLimitSet_conjugation H q,nielsen_mobius_inverse_image] at hh
  exact hh


theorem FuchsianDisc.nielsenArcFamily_sUnion
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    ⋃₀ D.nielsenArcFamily=frontier D.carrier\DiscreteGroups.mobiusLimitSet H := by
  ext p
  constructor
  · rintro ⟨J,⟨q,_,rfl⟩,hp⟩
    exact connectedComponentIn_subset _ _ hp
  · intro hp
    exact ⟨connectedComponentIn (frontier D.carrier\DiscreteGroups.mobiusLimitSet H)
      p,⟨p,hp,rfl⟩,mem_connectedComponentIn hp⟩

theorem FuchsianDisc.nielsenArcFamily_pairwiseDisjoint
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    D.nielsenArcFamily.PairwiseDisjoint id := by
  intro S hS T hT hne
  apply Set.disjoint_left.mpr
  intro p hpS hpT
  obtain ⟨x,_,rfl⟩:=hS
  obtain ⟨y,_,rfl⟩:=hT
  exact hne ((connectedComponentIn_eq hpS).trans (connectedComponentIn_eq hpT).symm)

theorem FuchsianDisc.nielsenArcFamily_countable
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hH : DiscreteGroups.IsNonElementary H) : D.nielsenArcFamily.Countable := by
  let q:=D.nielsenArcNormalizer hH
  let F : Set (OnePoint ℂ) → Set (OnePoint ℂ):=fun S=>q.val '' S
  have hF : Function.Injective F:=q.val.injective.image_injective
  have hc : (F '' D.nielsenArcFamily).Countable:=by
    change ((fun S=>q.val '' S) '' D.nielsenArcFamily).Countable
    rw [D.nielsenArcFamily_chart_image q (D.nielsenArcNormalizer_image hH)]
    exact Hyperbolic.nielsenHalfPlaneArcFamily_countable _ (DiscreteGroups.mobiusLimitSet_isClosed _)
      (D.nielsenArcNormalizer_limit hH)
  have hh:=hc.preimage hF
  rwa [hF.preimage_image] at hh

end
end LowDimensionalTopology.Geometry.Fuchsian
