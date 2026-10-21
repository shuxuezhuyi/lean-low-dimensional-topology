module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreFiniteness
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianCharts
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedFundamentalDomains
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology MeasureTheory
open scoped OnePoint Complex.UnitDisc UpperHalfPlane ENNReal
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
local instance nielsenConjugateSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance nielsenConjugateSphereBorelSpace : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- Genuine original-disc hyperbolic convexity is preserved and reflected by
an actual whole-group and whole-domain Mobius conjugacy. -/
theorem hyperbolicallyConvex_conjugation_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (hS : S⊆D.carrier) :
    (D.nielsenConjugate q).HyperbolicallyConvex (q.val '' S) ↔ D.HyperbolicallyConvex S := by
  let E := D.nielsenConjugate q
  let r := E.halfPlaneNormalizer
  have hr : (r*q).val '' D.carrier=Hyperbolic.openHalfPlaneSet := by
    rw [nielsen_mobius_image_mul]
    exact E.halfPlaneNormalizer_image
  rw [D.hyperbolicallyConvex_iff_chart (r*q) hr S hS]
  change Hyperbolic.HConvex (nielsenModelCoordinateSet r (q.val '' S)) ↔
    Hyperbolic.HConvex (nielsenModelCoordinateSet (r*q) S)
  rw [nielsenModelCoordinateSet,nielsenModelCoordinateSet,nielsen_mobius_image_mul]

/-- Source minimality gives inclusion of the new actual Nielsen region in
the actual conjugate of the original one. -/
theorem nielsenRegion_conjugate_subset_image
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup) :
    (D.nielsenConjugate q).nielsenRegion (hNE.conjugation q) ⊆ q.val '' D.nielsenRegion hNE := by
  let E := D.nielsenConjugate q
  obtain ⟨hsub,hne,ho,hc,hi⟩ := D.nielsenRegion_properties hNE
  apply (E.nielsenRegion_isLeast_nonempty_open_invariant_convex (hNE.conjugation q)).2
  refine ⟨image_mono hsub,hne.image q.val,?_,?_,?_⟩
  · exact (Mobius.mobiusBoundaryHomeomorph q).isOpenMap _ ho
  · exact (hyperbolicallyConvex_conjugation_iff D q _ hsub).mpr hc
  · intro g p hp
    obtain ⟨z,hz,rfl⟩ := hp
    obtain ⟨f,hf,hfg⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H g.val).mp g.property
    refine ⟨f.val z,hi ⟨f,hf⟩ z hz,?_⟩
    change q.val (f.val z)=g.val.val (q.val z)
    rw [←hfg]
    change q.val (f.val z)=q.val (f.val (q.val.symm (q.val z)))
    rw [Equiv.symm_apply_apply]

/-- The actual source Nielsen region is exactly natural under a genuine
Mobius conjugacy of the entire original group and geometric disc. -/
theorem nielsenRegion_conjugation_image
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup) :
    q.val '' D.nielsenRegion hNE = (D.nielsenConjugate q).nielsenRegion (hNE.conjugation q) := by
  let E := D.nielsenConjugate q
  let S := q.val.symm '' E.nielsenRegion (hNE.conjugation q)
  obtain ⟨hsub,hne,ho,hc,hi⟩ := E.nielsenRegion_properties (hNE.conjugation q)
  have hSD : S⊆D.carrier := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨v,hv,he⟩ := hsub hz
    rw [←he,Equiv.symm_apply_apply]
    exact hv
  have hqS : q.val '' S=E.nielsenRegion (hNE.conjugation q) := q.val.image_symm_image _
  have hNS : D.nielsenRegion hNE⊆S := by
    apply (D.nielsenRegion_isLeast_nonempty_open_invariant_convex hNE).2
    refine ⟨hSD,hne.image q.val.symm,?_,?_,?_⟩
    · exact (Mobius.mobiusBoundaryHomeomorph q).symm.isOpenMap _ ho
    · apply (hyperbolicallyConvex_conjugation_iff D q S hSD).mp
      rw [hqS]
      exact hc
    · intro g p hp
      obtain ⟨z,hz,rfl⟩ := hp
      let k : DiscreteGroups.Action.Actions.subgroupConjugate q H :=
        ⟨q*g.val*q⁻¹,(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g.val,g.property,rfl⟩⟩
      refine ⟨k.val.val z,hi k z hz,?_⟩
      change q.val.symm (q.val (g.val.val (q.val.symm z)))=g.val.val (q.val.symm z)
      rw [Equiv.symm_apply_apply]
  apply subset_antisymm
  · rw [←hqS]
    exact image_mono hNS
  · exact nielsenRegion_conjugate_subset_image D hNE q

/-- The actual Nielsen-core area in an arbitrary original geometric disc,
using the existing genuine density measure on that original model. -/
def geometricNielsenCoreArea
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (S : Set (fuchsianGeometricDomain D).carrier) : ℝ≥0∞ :=
  geometricModelArea D (S ∩ (Subtype.val ⁻¹' D.nielsenRegion hNE))

/-- A genuine whole-group Mobius conjugacy preserves the actual density area
inside the source-defined original Nielsen region. -/
theorem geometricNielsenCoreArea_conjugate_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup)
    (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : MeasurableSet S) :
    geometricNielsenCoreArea (D.nielsenConjugate q) (hNE.conjugation q)
      (geometricConjugateHomeomorph D q '' S)=geometricNielsenCoreArea D hNE S := by
  let e := geometricConjugateHomeomorph D q
  let E := D.nielsenConjugate q
  have hsub := (D.nielsenRegion_properties hNE).1
  have hmap : e '' (Subtype.val ⁻¹' D.nielsenRegion hNE) =
      (Subtype.val : (fuchsianGeometricDomain E).carrier→Mobius.ExtendedComplex) ⁻¹'
        E.nielsenRegion (hNE.conjugation q) := by
    apply subset_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change q.val x.val∈E.nielsenRegion (hNE.conjugation q)
      rw [←nielsenRegion_conjugation_image D hNE q]
      exact ⟨x.val,hx,rfl⟩
    · intro y hy
      obtain ⟨z,hz,hzy⟩ := (nielsenRegion_conjugation_image D hNE q).symm ▸ hy
      let x : (fuchsianGeometricDomain D).carrier := ⟨z,hsub hz⟩
      exact ⟨x,hz,Subtype.ext hzy⟩
  have himage : e '' (S ∩ (Subtype.val ⁻¹' D.nielsenRegion hNE)) =
      e '' S ∩ (Subtype.val ⁻¹' E.nielsenRegion (hNE.conjugation q)) := by
    rw [Set.image_inter e.injective,hmap]
  have hN : IsOpen ((Subtype.val : (fuchsianGeometricDomain D).carrier→Mobius.ExtendedComplex) ⁻¹'
      D.nielsenRegion hNE) :=
    (D.nielsenRegion_properties hNE).2.2.1.preimage continuous_subtype_val
  unfold geometricNielsenCoreArea
  rw [←himage]
  exact geometricModelArea_conjugate_image D q _ (hS.inter hN.measurableSet)

/-- An original genuine fundamental domain maps to a genuine fundamental
domain of the entire actually normalized group, including its null frontier
and the original density measure. -/
theorem geometric_fundamentalDomain_to_disc
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    {S : Set (fuchsianGeometricDomain D).carrier}
    (hS : DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) S) :
    IsFuchsianFundamentalDomain (geometricDiscData D) (geometricDiscHomeomorph D '' S) := by
  let P := geometricDiscData D
  let f := geometricDiscHomeomorph D
  let e := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (geometricDiscNormalizer D) H
  have he (g : geometricDiscGroup D) (x : P.domain.carrier) :
      f.symm (g • x)=e.symm g • f.symm x := by
    apply f.injective
    rw [f.apply_symm_apply,geometricDiscHomeomorph_equivariant,e.apply_symm_apply,f.apply_symm_apply]
  have hMap : Measure.map f (geometricModelArea D)=P.area := by
    rw [geometricModelArea,Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have hh : f ∘ f.symm=id := funext f.apply_symm_apply
    rw [hh,Measure.map_id]
  have hfd := DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm f.symm he hS
  change DiscreteGroups.Action.IsFundamentalDomain _ _ (Measure.map f (geometricModelArea D)) (f.symm ⁻¹' S) at hfd
  rw [hMap] at hfd
  have hset : f.symm ⁻¹' S=f '' S := (f.toEquiv.image_eq_preimage_symm S).symm
  rwa [hset] at hfd

/-- The true original Nielsen-core area equals the actual standard-disc core
area after the proved original whole-model normalization. -/
theorem geometricNielsenCoreArea_eq_disc
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (S : Set (fuchsianGeometricDomain D).carrier) (hS : MeasurableSet S) :
    geometricNielsenCoreArea D hNE S =
      fuchsianNielsenCoreArea (geometricDiscData D) (hNE.conjugation (geometricDiscNormalizer D))
        (geometricDiscHomeomorph D '' S) := by
  let P := geometricDiscData D
  let q := geometricDiscNormalizer D
  let f := geometricDiscHomeomorph D
  have hNEq : DiscreteGroups.IsNonElementary (geometricDiscGroup D) := hNE.conjugation q
  have hN : q.val '' D.nielsenRegion hNE = P.asFuchsianDisc.nielsenRegion hNEq := by
    rw [geometricDiscData_asFuchsianDisc]
    exact nielsenRegion_conjugation_image D hNE q
  have hsub := (D.nielsenRegion_properties hNE).1
  have hmap : f '' (Subtype.val ⁻¹' D.nielsenRegion hNE)=fuchsianNielsenCore P hNEq := by
    apply subset_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change q.val x.val∈P.asFuchsianDisc.nielsenRegion hNEq
      rw [←hN]
      exact ⟨x.val,hx,rfl⟩
    · intro y hy
      change y.val∈P.asFuchsianDisc.nielsenRegion hNEq at hy
      obtain ⟨z,hz,hzy⟩ := hN.symm ▸ hy
      let x : (fuchsianGeometricDomain D).carrier := ⟨z,hsub hz⟩
      exact ⟨x,hz,Subtype.ext hzy⟩
  have hm : MeasurableSet (S ∩ (Subtype.val ⁻¹' D.nielsenRegion hNE)) :=
    hS.inter ((D.nielsenRegion_properties hNE).2.2.1.preimage continuous_subtype_val).measurableSet
  unfold geometricNielsenCoreArea fuchsianNielsenCoreArea
  rw [geometricModelArea,Measure.map_apply f.symm.continuous.measurable hm]
  have himage : f.symm ⁻¹' (S ∩ (Subtype.val ⁻¹' D.nielsenRegion hNE))=
      f '' S ∩ fuchsianNielsenCore P hNEq := by
    calc
      _ = f '' (S ∩ (Subtype.val ⁻¹' D.nielsenRegion hNE)) :=
        (f.toEquiv.image_eq_preimage_symm _).symm
      _ = _ := by rw [Set.image_inter f.injective,hmap]
  exact congrArg P.area himage

/-- Finite generation implies finite actual Nielsen-core area on every
genuine fundamental domain in an arbitrary original invariant geometric
disc. Both the original group and original density measure are retained. -/
theorem finitelyGenerated_geometricNielsenCoreArea_ne_top
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    {S : Set (fuchsianGeometricDomain D).carrier}
    (hS : DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) S) :
    geometricNielsenCoreArea D hNE S≠⊤ := by
  let P := geometricDiscData D
  let e := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (geometricDiscNormalizer D) H
  have : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hFG
  have : Group.FG (geometricDiscGroup D) := Group.fg_of_surjective (f:=e.toMonoidHom) e.surjective
  have hFG' : (geometricDiscGroup D).FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  rw [geometricNielsenCoreArea_eq_disc D hNE S hS.isOpen.measurableSet]
  exact finitelyGenerated_nielsenCoreArea_ne_top P (hNE.conjugation (geometricDiscNormalizer D)) hFG'
    (geometric_fundamentalDomain_to_disc D hS)

/-- The original invariant Nielsen-core area theorem is valid on arbitrary
original geometric discs, including fundamental domains with infinite area. -/
theorem geometricNielsenCoreArea_independent
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    {S T : Set (fuchsianGeometricDomain D).carrier}
    (hS : DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) S)
    (hT : DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) T) :
    geometricNielsenCoreArea D hNE S=geometricNielsenCoreArea D hNE T := by
  rw [geometricNielsenCoreArea_eq_disc D hNE S hS.isOpen.measurableSet,
    geometricNielsenCoreArea_eq_disc D hNE T hT.isOpen.measurableSet]
  exact fuchsianNielsenCoreArea_independent _ _ (geometric_fundamentalDomain_to_disc D hS)
    (geometric_fundamentalDomain_to_disc D hT)

end LowDimensionalTopology.Geometry.Fuchsian
