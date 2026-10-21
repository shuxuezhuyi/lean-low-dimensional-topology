/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCoreEquality
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCorePolygonArea
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.Classification
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise
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
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance targetAreaSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance targetAreaSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- Closed copies need only cover the invariant core. Their null boundaries
then give the genuine measure-theoretic fundamental domain for restricted
area, without asserting an ambient pointwise fundamental domain. -/
theorem nielsen_measureFundamentalDomain_of_closed_cover
    {G X : Type*} [Group G] [Countable G] [MulAction G X]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [ContinuousConstSMul G X] [MeasurableConstSMul G X]
    {μ : Measure X} [SMulInvariantMeasure G X μ]
    (N Q : Set X) (hN : MeasurableSet N) (hQ : IsOpen Q)
    (hnull : μ (frontier Q) = 0)
    (hpack : Pairwise fun a b : G => Disjoint (a • Q) (b • Q))
    (hcover : N ⊆ ⋃ a : G, a • closure Q) :
    MeasureTheory.IsFundamentalDomain G Q (μ.restrict N) := by
  have hboundary : ∀ᵐ x ∂μ, x ∈ closure Q → x ∈ Q := by
    apply ae_le_set.mpr
    rwa [← hQ.frontier_eq]
  have hall : ∀ᵐ x ∂μ, ∀ a : G, a • x ∈ closure Q → a • x ∈ Q := by
    apply ae_all_iff.mpr
    intro a
    exact (measurePreserving_smul a μ).quasiMeasurePreserving.ae hboundary
  have hac : μ.restrict N ≪ μ := Measure.restrict_le_self.absolutelyContinuous
  refine ⟨hQ.measurableSet.nullMeasurableSet, ?_, fun a b hab => (hpack hab).aedisjoint⟩
  filter_upwards [ae_restrict_mem hN, hac hall] with x hx hxall
  obtain ⟨a, y, hy, hay⟩ := mem_iUnion.mp (hcover hx)
  refine ⟨a⁻¹, hxall a⁻¹ ?_⟩
  rw [← hay, inv_smul_smul]
  exact hy

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "Qcore" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "Pcore" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Qcore
local notation "Saux" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "Htarget" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "Ktarget" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "Ptarget" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb

/-- The actual retained whole projective group has disjoint original tile
interiors, inherited from its proved auxiliary developing map. -/
theorem generalCoreTarget_interior_tiles_disjoint :
    letI := (Ptarget).nativeAction
    Pairwise fun a b : Ktarget => Disjoint (a • (Pcore).interior) (b • (Pcore).interior) := by
  let targetAreaAction := (Ptarget).nativeAction
  let E := generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb
  let inc : Ktarget → (Saux).Generated := fun a =>
    ⟨(E.symm a).val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb
      (E.symm a).property⟩
  have hact (a : Ktarget) (x : ℍ) : a • x = (inc a).val x := by
    have h := generalCoreTargetMobiusEquiv_action g orders s t ho hdef d hd hb (E.symm a) x
    change E (E.symm a) • x = (E.symm a).val x at h
    change a • x = (E.symm a).val x
    rwa [E.apply_symm_apply] at h
  have himage (a : Ktarget) : a • (Pcore).interior =
      (fun x : ℍ => inc a • x) '' (Pcore).interior := by
    change (fun x : ℍ => a • x) '' (Pcore).interior = _
    exact image_congr (fun x _ => hact a x)
  intro a b hab
  rw [himage, himage]
  apply (Saux).original_interior_tiles_disjoint_of_evaluation_injective
    (generalCoreAux_evaluation_injective g orders s t ho hdef d hd hb)
  intro he
  apply hab
  apply E.symm.injective
  exact Subtype.ext (congrArg (fun c : (Saux).Generated => c.val) he)

/-- Every actual Nielsen point is covered by a closed original tile of the
same retained projective group. This is the proved core equality, transported
only through the faithful original point action. -/
theorem generalCoreTarget_nielsen_closed_tile_cover
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    letI := (Ptarget).nativeAction
    (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (Ptarget).asFuchsianDisc.nielsenRegion hNE) ⊆
      ⋃ a : Ktarget, a • closure (Pcore).interior := by
  let targetAreaAction := (Ptarget).nativeAction
  intro x hx
  have hxS : x ∈ generalCoreTargetTileSaturation g orders s t ho hdef d hd hb := by
    rw [generalCoreTargetTileSaturation_eq_nielsen_closure g orders s t ho hdef d hd hb hNE]
    exact subset_closure hx
  obtain ⟨a, ha, y, hy, hay⟩ := mem_iUnion₂.mp hxS
  let f : Htarget := ⟨a, ha⟩
  refine mem_iUnion.mpr ⟨generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb f,
    y, ?_, ?_⟩
  · rw [← _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
    exact hy
  · exact (generalCoreTargetMobiusEquiv_action g orders s t ho hdef d hd hb f y).trans hay

/-- The original core tile is an actual a.e. fundamental domain for the true
canonical Nielsen region, measured by the original hyperbolic density. -/
theorem generalCoreTarget_nielsen_measureFundamentalDomain
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    letI := (Ptarget).nativeAction
    MeasureTheory.IsFundamentalDomain Ktarget (Pcore).interior
      (volume.restrict (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (Ptarget).asFuchsianDisc.nielsenRegion hNE)) := by
  let targetAreaAction := (Ptarget).nativeAction
  let targetAreaCountable : Countable Ktarget := _root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable _ (Ptarget).discrete
  let targetAreaContinuous : ContinuousConstSMul Ktarget ℍ :=
    ⟨fun a => ((Ptarget).nativeHom a).continuous⟩
  let targetAreaInvariant : SMulInvariantMeasure Ktarget ℍ volume := ⟨by
    intro a T hT
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeIsometry_measurePreserving ((Ptarget).nativeHom a)).measure_preimage
      hT.nullMeasurableSet⟩
  have hQ := (generalCore_auxiliary_poincare g orders s t ho hdef d hd hb).2
  apply nielsen_measureFundamentalDomain_of_closed_cover
  · exact (((Ptarget).asFuchsianDisc.nielsenRegion_properties hNE).2.2.1.preimage
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous).measurableSet
  · exact hQ.isOpen
  · exact hQ.null_frontier
  · exact generalCoreTarget_interior_tiles_disjoint g orders s t ho hdef d hd hb
  · exact generalCoreTarget_nielsen_closed_tile_cover g orders s t ho hdef d hd hb hNE

/-- Area inside the original target Nielsen core agrees with the original
core tile area for every genuine ambient fundamental domain of that target. -/
theorem generalCoreTarget_fundamental_inter_nielsen_area
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) (F : Set ℍ) :
    letI := (Ptarget).nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain Ktarget ℍ volume F →
      volume (F ∩ (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (Ptarget).asFuchsianDisc.nielsenRegion hNE)) =
        volume (Pcore).interior := by
  let targetAreaAction := (Ptarget).nativeAction
  let targetAreaCountable : Countable Ktarget := _root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable _ (Ptarget).discrete
  let targetAreaContinuous : ContinuousConstSMul Ktarget ℍ :=
    ⟨fun a => ((Ptarget).nativeHom a).continuous⟩
  let targetAreaInvariant : SMulInvariantMeasure Ktarget ℍ volume := ⟨by
    intro a T hT
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeIsometry_measurePreserving ((Ptarget).nativeHom a)).measure_preimage
      hT.nullMeasurableSet⟩
  intro hF
  let N := _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (Ptarget).asFuchsianDisc.nielsenRegion hNE
  have hN : MeasurableSet N :=
    (((Ptarget).asFuchsianDisc.nielsenRegion_properties hNE).2.2.1.preimage
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous).measurableSet
  have hInv (a : Ktarget) (x : ℍ) (hx : x ∈ N) : a • x ∈ N := by
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (a • x) ∈ (Ptarget).asFuchsianDisc.nielsenRegion hNE
    rw [← (Ptarget).nativeAction_boundary]
    exact ((Ptarget).asFuchsianDisc.nielsenRegion_properties hNE).2.2.2.2 a _ hx
  have hiff (a : Ktarget) (x : ℍ) : a • x ∈ N ↔ x ∈ N :=
    ⟨fun hx => by simpa only [inv_smul_smul] using hInv a⁻¹ (a • x) hx, hInv a x⟩
  let ν := volume.restrict N
  let targetAreaRestrictedInvariant : SMulInvariantMeasure Ktarget ℍ ν := ⟨by
    intro a T hT
    change volume.restrict N ((fun x : ℍ => a • x) ⁻¹' T) = volume.restrict N T
    rw [Measure.restrict_apply (hT.preimage (measurable_const_smul a)), Measure.restrict_apply hT]
    have he : ((fun x : ℍ => a • x) ⁻¹' T) ∩ N =
        (fun x : ℍ => a • x) ⁻¹' (T ∩ N) := by
      ext x
      change (a • x ∈ T ∧ x ∈ N) ↔ (a • x ∈ T ∧ a • x ∈ N)
      rw [hiff]
    rw [he]
    exact SMulInvariantMeasure.measure_preimage_smul a (hT.inter hN)⟩
  have hac : ν ≪ volume := Measure.restrict_le_self.absolutelyContinuous
  have hFD := (native_geometric_fundamental_measureDomain (Ptarget) F hF).mono hac
  have hQD := generalCoreTarget_nielsen_measureFundamentalDomain g orders s t ho hdef d hd hb hNE
  have he : ν F = ν (Pcore).interior := hFD.measure_eq hQD
  have hQ := (generalCore_auxiliary_poincare g orders s t ho hdef d hd hb).2
  have hQmeas : MeasurableSet (Pcore).interior := hQ.isOpen.measurableSet
  change volume.restrict N F = volume.restrict N (Pcore).interior at he
  rw [Measure.restrict_apply hF.isOpen.measurableSet,
    Measure.restrict_apply hQmeas,
    inter_eq_left.mpr (generalCoreTarget_base_interior_subset_nielsen
      g orders s t ho hdef d hd hb hNE)] at he
  exact he

/-- The actual canonical Nielsen area of every actual Cayley-model
fundamental domain is the original polygon's explicitly computed angle
defect. The ambient domain is arbitrary; no signature or area is assumed. -/
theorem generalCoreTarget_cayley_nielsen_area
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget)
    (F : Set (Ptarget).cayleyData.domain.carrier)
    (hF : IsFuchsianFundamentalDomain (Ptarget).cayleyData F) :
    fuchsianNielsenCoreArea (Ptarget).cayleyData (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) F =
      ENNReal.ofReal (2 * Real.pi * generalCoreDeficit g orders s t) := by
  let targetAreaAction := (Ptarget).nativeAction
  let e := (Ptarget).cayleyCoordinate
  let E := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius Ktarget
  have hmap : Measure.map e.symm (Ptarget).cayleyData.area = (volume : Measure ℍ) := by
    rw [← (Ptarget).cayleyCoordinate_area_map]
    rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    simp only [Function.comp_def, e.symm_apply_apply, Measure.map_id']
  have hback : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain Ktarget ℍ volume (e ⁻¹' F) := by
    have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage E e
      (fun a x => (Ptarget).cayleyCoordinate_equivariant a x) hF
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain Ktarget ℍ (Measure.map e.symm (Ptarget).cayleyData.area)
      (e ⁻¹' F) at h
    rwa [hmap] at h
  have himage : e '' (e ⁻¹' F) = F := e.surjective.image_preimage F
  calc
    _ = fuchsianNielsenCoreArea (Ptarget).cayleyData (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
        (e '' (e ⁻¹' F)) := congrArg _ himage.symm
    _ = volume ((e ⁻¹' F) ∩
        (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (Ptarget).asFuchsianDisc.nielsenRegion hNE)) :=
      halfTurn_cayley_nielsen_core_area (Ptarget) hNE _
        (hF.isOpen.preimage e.continuous).measurableSet
    _ = volume (Pcore).interior :=
      generalCoreTarget_fundamental_inter_nielsen_area g orders s t ho hdef d hd hb hNE _ hback
    _ = _ := generalCorePolygon_native_volume g orders s t ho hdef d hd hb

/-- For every allowed positive-boundary construction, the unchanged actual
target has this genuine Nielsen area. Non-elementarity is derived from the
actual retained boundary translations and actual auxiliary finite area. -/
theorem generalCoreTarget_positive_boundary_nielsen_area (ht : 0 < t)
    (F : Set (Ptarget).cayleyData.domain.carrier)
    (hF : IsFuchsianFundamentalDomain (Ptarget).cayleyData F) :
    fuchsianNielsenCoreArea (Ptarget).cayleyData
      ((generalCoreTargetMobius_nonElementary g orders s t ho hdef d hd hb ht).conjugation
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) F =
      ENNReal.ofReal (2 * Real.pi * generalCoreDeficit g orders s t) :=
  generalCoreTarget_cayley_nielsen_area g orders s t ho hdef d hd hb
    (generalCoreTargetMobius_nonElementary g orders s t ho hdef d hd hb ht) F hF

end LowDimensionalTopology.Geometry.Fuchsian
