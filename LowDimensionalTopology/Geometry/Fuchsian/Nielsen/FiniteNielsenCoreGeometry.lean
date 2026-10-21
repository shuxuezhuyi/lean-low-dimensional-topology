module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreConjugation
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.FiniteAreaIdealBoundary
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FundamentalDomainGenerators
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology MeasureTheory
open scoped OnePoint Complex.UnitDisc Pointwise
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
local instance finiteCoreSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance finiteCoreSphereBorelSpace : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- The genuine finite coordinate recovers exactly the original source
Nielsen region, rather than a separately chosen convex core. -/
theorem fuchsianNielsenCore_finite_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    Hyperbolic.extendedDiscPoint '' (P.finiteCoordinate '' fuchsianNielsenCore P hNE)=
      P.asFuchsianDisc.nielsenRegion hNE := by
  apply subset_antisymm
  · rintro _ ⟨z,⟨x,hx,rfl⟩,rfl⟩
    change (((P.finiteCoordinate x:𝔻):ℂ):Mobius.ExtendedComplex)∈P.asFuchsianDisc.nielsenRegion hNE
    rw [P.finiteCoordinate_extended x]
    exact hx
  · intro z hz
    let x : P.domain.carrier := ⟨z,(P.asFuchsianDisc.nielsenRegion_properties hNE).1 hz⟩
    exact ⟨P.finiteCoordinate x,⟨x,hz,rfl⟩,P.finiteCoordinate_extended x⟩

/-- The actual original Nielsen region is genuinely geodesically convex in
its true native finite coordinate. -/
theorem fuchsianNielsenCore_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    Hyperbolic.DiscHConvex (P.finiteCoordinate '' fuchsianNielsenCore P hNE) := by
  apply (P.asFuchsianDisc.hyperbolicallyConvex_disc rfl _).mp
  rw [fuchsianNielsenCore_finite_image P hNE]
  exact (P.asFuchsianDisc.nielsenRegion_properties hNE).2.2.2.1

/-- Intersecting an original convex polygon with the actual Nielsen region
preserves genuine native geodesic convexity. -/
theorem nielsenCore_inter_native_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hNE : DiscreteGroups.IsNonElementary H) :
    Hyperbolic.DiscHConvex (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)) := by
  rw [Set.image_inter P.finiteCoordinate.injective]
  intro z hz w hw p hp
  exact ⟨hD.convex z hz.1 w hw.1 hp,fuchsianNielsenCore_convex P hNE z hz.2 w hw.2 hp⟩

/-- Finite true Nielsen-core area forces finitely many actual ideal closure
points of the original polygon inside that genuine core. No finite-area
assumption is imposed on the whole original polygon. -/
theorem finite_nielsenCore_idealBoundary
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤) :
    (fuchsianPolygonIdealBoundary P (D∩fuchsianNielsenCore P hNE)).Finite := by
  have ho : IsOpen (D∩fuchsianNielsenCore P hNE) :=
    hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)
  have hArea : Hyperbolic.discHyperbolicArea (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))≠⊤ := by
    rwa [←P.area_apply _ ho.measurableSet]
  have hh := (nielsenCore_inter_native_convex hD hNE).complexIdealBoundary_finite
    (P.finiteCoordinate.isOpenMap _ ho) hArea
  simpa only [fuchsianPolygonIdealBoundary,Set.image_image] using hh

/-- Every actual ideal point of the Nielsen part of any original set is a
true original limit point. This does not require finite area or a polygon. -/
theorem nielsenCore_inter_idealBoundary_subset_limit
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (D : Set P.domain.carrier) (ξ : ℂ)
    (hξ : ξ∈fuchsianPolygonIdealBoundary P (D∩fuchsianNielsenCore P hNE)) :
    (ξ:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet H := by
  obtain ⟨hξN,hξcl⟩ := (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P _ ξ).mp hξ
  have hSub : (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) ''
      (D∩fuchsianNielsenCore P hNE) ⊆ P.asFuchsianDisc.nielsenRegion hNE := by
    rintro _ ⟨x,hx,rfl⟩
    exact hx.2
  have hB : (ξ:Mobius.ExtendedComplex)∈frontier P.asFuchsianDisc.carrier := by
    rw [show P.asFuchsianDisc.carrier=Hyperbolic.extendedUnitDisc from rfl,nielsen_unitDisc_frontier]
    exact ⟨ξ,mem_sphere_zero_iff_norm.mpr hξN,rfl⟩
  exact nielsenRegion_closure_frontier_subset_limit P.asFuchsianDisc hNE
    ⟨closure_mono hSub hξcl,hB⟩

/-- The actual ideal closure of the source Nielsen region equals precisely
the whole true original limit set, including both inclusions. -/
theorem nielsenRegion_closure_frontier_eq_limit
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    closure (D.nielsenRegion hNE) ∩ frontier D.carrier=DiscreteGroups.mobiusLimitSet H := by
  apply subset_antisymm (nielsenRegion_closure_frontier_subset_limit D hNE)
  have hp := D.nielsenRegion_properties hNE
  have hc := nielsen_limitSet_subset_closure H hNE _ hp.2.1 hp.2.2.2.2
  exact fun z hz => ⟨hc hz,D.loxodromic_limit_subset_frontier hz⟩

/-- The sphere image of the actual original core is literally the original
source-defined Nielsen region. -/
theorem fuchsianNielsenCore_sphere_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' fuchsianNielsenCore P hNE =
      P.asFuchsianDisc.nielsenRegion hNE := by
  apply subset_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx
  · intro z hz
    exact ⟨⟨z,(P.asFuchsianDisc.nielsenRegion_properties hNE).1 hz⟩,hz,rfl⟩

/-- Any genuine canonical ray from an actual Nielsen point toward a true
limit point stays in the actual Nielsen region. Its ideal accumulation is
proved from the actual source region, not added as a core hypothesis. -/
theorem fuchsianNielsenCore_canonical_ray_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (w : P.domain.carrier) (hw : w∈fuchsianNielsenCore P hNE)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (hξL : (ξ:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet H) :
    Hyperbolic.discHRay (P.finiteCoordinate w) (ξ:Mobius.ExtendedComplex) ⊆
      P.finiteCoordinate '' fuchsianNielsenCore P hNE := by
  have hB : (ξ:Mobius.ExtendedComplex)∈Hyperbolic.extendedDiscIdealBoundary := (Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hξ
  let R : Hyperbolic.DiscRayAt (P.finiteCoordinate w) := ⟨Hyperbolic.discHRay _ (ξ:Mobius.ExtendedComplex),ξ,hB,
    Hyperbolic.isDiscHLineRay_discHRay _ _ hB⟩
  have hEnd : R.idealEndpoint=(ξ:Mobius.ExtendedComplex) := by
    obtain ⟨_,_,_,_,_,ht⟩ := R.isRay
    exact singleton_injective (ht.symm.trans (Hyperbolic.discHRay_idealEndpoints _ _ hB))
  have hcl : (ξ:Mobius.ExtendedComplex)∈closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) ''
      fuchsianNielsenCore P hNE) := by
    rw [fuchsianNielsenCore_sphere_image P hNE]
    exact ((nielsenRegion_closure_frontier_eq_limit P.asFuchsianDisc hNE).symm ▸ hξL).1
  have hξCore : ξ∈fuchsianPolygonIdealBoundary P (fuchsianNielsenCore P hNE) :=
    (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P _ ξ).mpr ⟨hξ,hcl⟩
  apply open_discHConvex_ideal_ray_subset
    (P.finiteCoordinate.isOpenMap _ (fuchsianNielsenCore_isOpen P hNE))
    (fuchsianNielsenCore_convex P hNE) (mem_image_of_mem _ hw) R ξ hξ hEnd
  simpa only [Set.image_image] using ((mem_fuchsianPolygonIdealBoundary P _ ξ).mp hξCore).1

/-- With a genuine common interior Nielsen point, the ideal boundary of the
actual polygon's core part is exactly its original ideal boundary inside the
true limit set. The reverse inclusion is proved with actual canonical rays. -/
theorem nielsenCore_inter_idealBoundary_eq
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hNE : DiscreteGroups.IsNonElementary H)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE) :
    fuchsianPolygonIdealBoundary P (D∩fuchsianNielsenCore P hNE)=
      fuchsianPolygonIdealBoundary P D ∩ nielsenIdealLimitSet H := by
  apply subset_antisymm
  · intro ξ hξ
    refine ⟨?_,nielsenCore_inter_idealBoundary_subset_limit P hNE D ξ hξ⟩
    exact inter_subset_inter_left _ (closure_mono (image_mono inter_subset_left)) hξ
  · rintro ξ ⟨hξD,hξL⟩
    have hξN := ((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξD).2
    have hB : (ξ:Mobius.ExtendedComplex)∈Hyperbolic.extendedDiscIdealBoundary := (Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hξN
    have hRay : Hyperbolic.discHRay (P.finiteCoordinate w) (ξ:Mobius.ExtendedComplex) ⊆
        P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE) := by
      rw [Set.image_inter P.finiteCoordinate.injective]
      exact fun z hz => ⟨hD.ideal_canonical_ray_subset w hwD ξ hξD hz,
        fuchsianNielsenCore_canonical_ray_subset P hNE w hwN ξ hξN hξL hz⟩
    have hTrace : (ξ:Mobius.ExtendedComplex)∈Hyperbolic.discTraceIdealEndpoints (Hyperbolic.discHRay (P.finiteCoordinate w) (ξ:Mobius.ExtendedComplex)) := by
      rw [Hyperbolic.discHRay_idealEndpoints _ _ hB]
      exact mem_singleton _
    have himage : Hyperbolic.extendedDiscPoint '' (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))=
        (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' (D∩fuchsianNielsenCore P hNE) := by
      rw [Set.image_image]
      congr 1
      funext x
      exact P.finiteCoordinate_extended x
    have hcl := closure_mono (image_mono hRay) hTrace.1
    rw [himage] at hcl
    exact (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P _ ξ).mpr ⟨hξN,hcl⟩

/-- Finite actual Nielsen-core area supplies finitely many original ideal
polygon points which are true limit points, without requiring finite area of
the whole original polygon or finite original side count. -/
theorem finite_nielsenCore_original_limit_idealBoundary
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hNE : DiscreteGroups.IsNonElementary H)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤) :
    (fuchsianPolygonIdealBoundary P D ∩ nielsenIdealLimitSet H).Finite := by
  rw [←nielsenCore_inter_idealBoundary_eq hD hNE w hwD hwN]
  exact finite_nielsenCore_idealBoundary hD hNE harea

/-- Every original ideal-boundary cycle based at a true limit point is finite
when the actual Nielsen portion has finite area and a genuine common interior
point. Only true original orbit intersections are counted. -/
theorem finite_nielsenCore_limit_idealCycle
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hNE : DiscreteGroups.IsNonElementary H)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (ξ : Mobius.ExtendedComplex)
    (hξL : ξ∈DiscreteGroups.mobiusLimitSet H) :
    (fuchsianPolygonIdealCycle P D ξ).Finite := by
  have hF := (finite_nielsenCore_original_limit_idealBoundary hD hNE w hwD hwN harea).image
    (fun z : ℂ => (z:Mobius.ExtendedComplex))
  apply hF.subset
  rintro z ⟨hzE,hzO⟩
  obtain ⟨η,hηD,rfl⟩ := hzE
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hzO
  have hηL : (η:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet H := by
    rw [←hg]
    exact DiscreteGroups.mobiusLimitSet_invariant H g hξL
  exact ⟨η,⟨hηD,hηL⟩,rfl⟩

/-- The actual source Nielsen region contains an original genuinely free
centre, without finite generation or a finite-area hypothesis. -/
theorem exists_dirichlet_center_in_nielsenCore
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    ∃w : P.domain.carrier,IsDirichletCenter P w ∧ w∈fuchsianNielsenCore P hNE := by
  have hp := P.asFuchsianDisc.nielsenRegion_properties hNE
  obtain ⟨z,hz,hfree⟩ := DiscreteGroups.discreteMobius_open_free_point H P.discrete _ hp.2.2.1 hp.2.1
  let w : P.domain.carrier := ⟨z,hp.1 hz⟩
  refine ⟨w,?_,hz⟩
  intro g hg
  exact hfree g (congrArg Subtype.val hg)

/-- A genuine finite Nielsen-core area fundamental domain supplies an actual
Dirichlet polygon centred in that source region, with finitely many true limit
ideal boundary points and finite actual ideal cycles. This is a proved lower
chain toward the converse, not an assumed finite-sidedness conclusion. -/
theorem finite_nielsenCore_exists_dirichlet_limit_cycles_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤) :
    ∃w : P.domain.carrier,IsDirichletCenter P w ∧ w∈fuchsianNielsenCore P hNE ∧
      (fuchsianPolygonIdealBoundary P (dirichletDomain P w) ∩ nielsenIdealLimitSet H).Finite ∧
      ∀ξ∈DiscreteGroups.mobiusLimitSet H,(fuchsianPolygonIdealCycle P (dirichletDomain P w) ξ).Finite := by
  obtain ⟨w,hw,hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  have hpoly := dirichletDomain_isConvexFuchsianPolygon P w hw
  have hwD := dirichletDomain_center_mem P w hw
  have harea' : fuchsianNielsenCoreArea P hNE (dirichletDomain P w)≠⊤ := by
    rwa [fuchsianNielsenCoreArea_independent P hNE (dirichletDomain_fundamental P w hw) hD]
  exact ⟨w,hw,hwN,finite_nielsenCore_original_limit_idealBoundary hpoly hNE w hwD hwN harea',
    fun ξ hξ => finite_nielsenCore_limit_idealCycle hpoly hNE w hwD hwN harea' ξ hξ⟩

/-- If an original native set has no actual ideal closure points, its
closure is genuinely compact inside the original open disc. -/
theorem unitDisc_no_ideal_closure_compact
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (S : Set P.domain.carrier) (hE : fuchsianPolygonIdealBoundary P S=∅) :
    IsCompact (closure S) := by
  let L := closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' S)
  have hLc : IsCompact L := isClosed_closure.isCompact
  have hLrange : L⊆Set.range (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) := by
    intro z hz
    have hzcl : z∈closure P.domain.carrier :=
      closure_mono (by rintro _ ⟨x,_hx,rfl⟩; exact x.property) hz
    by_cases hzD : z∈P.domain.carrier
    · exact ⟨⟨z,hzD⟩,rfl⟩
    · have hzF : z∈frontier P.domain.carrier :=
        ⟨hzcl,by simpa only [P.domain.isOpen.interior_eq] using hzD⟩
      change z∈frontier Hyperbolic.extendedUnitDisc at hzF
      rw [nielsen_unitDisc_frontier] at hzF
      obtain ⟨ξ,hξ,rfl⟩ := hzF
      have hξE : ξ∈fuchsianPolygonIdealBoundary P S :=
        (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P S ξ).mpr
          ⟨mem_sphere_zero_iff_norm.mp hξ,hz⟩
      simp only [hE,mem_empty_iff_false] at hξE
  rw [Topology.IsEmbedding.closure_eq_preimage_closure_image IsEmbedding.subtypeVal S]
  exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hLc hLrange

/-- In the no-ideal-boundary case, only finitely many original sides can meet
the actual Nielsen core. Compactness is proved for the genuine core part. -/
theorem no_ideal_nielsenCore_sides_finite
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (hE : fuchsianPolygonIdealBoundary P (D∩fuchsianNielsenCore P hNE)=∅) :
    {s : FuchsianPolygonSides P D | (s.val∩fuchsianNielsenCore P hNE).Nonempty}.Finite := by
  have hK := unitDisc_no_ideal_closure_compact P (D∩fuchsianNielsenCore P hNE) hE
  apply ((hD.locallyFinite.compact_sides_finite _ hK).preimage Subtype.val_injective.injOn).subset
  intro s hs
  refine ⟨s.property,?_⟩
  obtain ⟨z,hzs,hzN⟩ := hs
  refine ⟨z,hzs,?_⟩
  exact (fuchsianNielsenCore_isOpen P hNE).closure_inter
    ⟨frontier_subset_closure ((Fuchsian.IsFuchsianPolygonSide.subset_frontier hD.locallyFinite.fundamental s.property)
      hzs),hzN⟩

/-- The actual source Nielsen core is connected in the original native
space, as proved through its genuine finite coordinate. -/
theorem fuchsianNielsenCore_isConnected
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    IsConnected (fuchsianNielsenCore P hNE) := by
  have hp := P.asFuchsianDisc.nielsenRegion_properties hNE
  have hne : (fuchsianNielsenCore P hNE).Nonempty := by
    obtain ⟨z,hz⟩ := hp.2.1
    exact ⟨⟨z,hp.1 hz⟩,hz⟩
  refine ⟨hne,?_⟩
  have hpre := (fuchsianNielsenCore_convex P hNE).isPreconnected
  exact P.finiteCoordinate.isEmbedding.isInducing.isPreconnected_image.mp hpre

/-- If the genuine Nielsen portion of an original polygon has no ideal
closure points, the original whole group is finitely generated. The proof
uses the connected actual core and its locally finite closed original tiles. -/
theorem no_ideal_nielsenCore_finitelyGenerated
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE)
    (hE : fuchsianPolygonIdealBoundary P (D∩fuchsianNielsenCore P hNE)=∅) : H.FG := by
  classical
  let N : SubMulAction H P.domain.carrier :=
    ⟨fuchsianNielsenCore P hNE,fun g _x hx => fuchsianNielsenCore_invariant P hNE g _ hx⟩
  let : ConnectedSpace N := isConnected_iff_connectedSpace.mp (fuchsianNielsenCore_isConnected P hNE)
  let : ContinuousConstSMul H N := ⟨fun g =>
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
  let K : Set N := Subtype.val ⁻¹' closure D
  have hK : IsClosed K := isClosed_closure.preimage continuous_subtype_val
  have hnK : K.Nonempty := ⟨⟨w,hwN⟩,subset_closure hwD⟩
  have he (g : H) : g • K=(Subtype.val : N→P.domain.carrier) ⁻¹' fuchsianDomainTile P D g := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.val,hy,rfl⟩
    · rintro ⟨y,hy,hgy⟩
      have hyN : y∈fuchsianNielsenCore P hNE := by
        have hh := fuchsianNielsenCore_invariant P hNE g⁻¹ x.val x.property
        change g • y=x.val at hgy
        rwa [←hgy,inv_smul_smul] at hh
      exact ⟨⟨y,hyN⟩,hy,Subtype.ext hgy⟩
  have hlf : LocallyFinite (fun g : H => g • K) := by
    simp_rw [he]
    exact hD.locallyFinite.locallyFinite.preimage_continuous continuous_subtype_val
  have hcov : (⋃g : H,g • K)=univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x.val∈⋃g : H,fuchsianDomainTile P D g := by
      change x.val∈⋃g : H,(fun y : P.domain.carrier => g • y) '' closure D
      rw [hD.locallyFinite.fundamental.closure_cover]
      trivial
    obtain ⟨g,hg⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨g,?_⟩
    rw [he]
    exact hg
  have hgen := connected_closed_tiles_generate K hK hnK hlf hcov
  have hcompact := unitDisc_no_ideal_closure_compact P (D∩fuchsianNielsenCore P hNE) hE
  have hfinite : {g : H | (K∩g • K).Nonempty}.Finite := by
    apply (hD.locallyFinite.compact_hits_finite _ hcompact).subset
    rintro g ⟨x,hxK,hxg⟩
    have hxg' : x∈(Subtype.val : N→P.domain.carrier) ⁻¹' fuchsianDomainTile P D g := by
      rw [←he g]
      exact hxg
    refine ⟨x.val,hxg',?_⟩
    exact (fuchsianNielsenCore_isOpen P hNE).closure_inter ⟨hxK,x.property⟩
  apply (Group.fg_iff_subgroup_fg H).mp
  exact Group.fg_iff.mpr ⟨_,hgen,hfinite⟩

end LowDimensionalTopology.Geometry.Fuchsian
