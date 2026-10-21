/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryComponents
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCutAxisSeparation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set Topology
open scoped UpperHalfPlane Pointwise
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

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

local notation "Qcore" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "Saux" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "Htarget" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "Ktarget" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "Ptarget" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb
local notation "Pdisc" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.cayleyData Ptarget
local notation "Edisc" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.cayleyCoordinate Ptarget
local notation "Kdisc" => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius Ktarget
local notation "Ucore" => generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I
local notation "idx" => generalCoreBoundarySideIndex g orders s t
local notation "Kcut" => (fun j : Fin t => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (idx j 1)))

/-- The same entire native target group in its actual Cayley representation. -/
def generalCoreBoundaryCayleyEquiv : Htarget ≃* Kdisc :=
  (generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius Ktarget)

/-- The actual full-group equivalence preserves every original native point. -/
theorem generalCoreBoundaryCayleyEquiv_action (a : Htarget) (z : ℍ) :
    generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb a • Edisc z = Edisc (a.val z) := by
  have h := (Ptarget).cayleyCoordinate_equivariant
    (generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb a) z
  change _ = generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb a • Edisc z at h
  rw [generalCoreTargetMobiusEquiv_action g orders s t ho hdef d hd hb a z] at h
  exact h.symm

/-- Finite generation concerns the whole actual Cayley target group. -/
theorem generalCoreTargetCayley_fg : (Kdisc).FG := by
  let originalTargetFG : Group.FG Htarget := (Group.fg_iff_subgroup_fg _).mpr
    (generalCoreTargetGroup_fg g orders s t ho hdef d hd hb)
  apply (Group.fg_iff_subgroup_fg _).mp
  exact Group.fg_of_surjective
    (f := (generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb).toMonoidHom)
    (generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb).surjective

/-- The actual source-defined Nielsen core transports by the genuine Cayley
coordinate, without replacing it with a chosen polygon or an assigned core. -/
theorem generalCoreTargetCayley_nielsen_image
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    Edisc '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (Ptarget).asFuchsianDisc.nielsenRegion hNE) =
      fuchsianNielsenCore Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) := by
  have hdisc : (Pdisc).asFuchsianDisc = (Ptarget).asFuchsianDisc.nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius := by
    apply _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianDisc_eq_of_carrier_eq
    exact cayleyMobius_image_openHalfPlane.symm
  have hpoint (z : ℍ) : (Edisc z).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) := by
    have he := _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)
    change _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (((z : ℂ) : Mobius.ExtendedComplex))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane]
    exact he
  have hN : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' (Ptarget).asFuchsianDisc.nielsenRegion hNE =
      (Pdisc).asFuchsianDisc.nielsenRegion (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) := by
    rw [hdisc]
    exact nielsenRegion_conjugation_image (Ptarget).asFuchsianDisc hNE _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
  apply subset_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change (Edisc z).val ∈ (Pdisc).asFuchsianDisc.nielsenRegion (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    rw [hpoint, ← hN]
    exact ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z, hz, rfl⟩
  · intro y hy
    change y.val ∈ (Pdisc).asFuchsianDisc.nielsenRegion (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) at hy
    obtain ⟨x, hx, hxy⟩ := hN.symm ▸ hy
    have hxR : x ∈ range _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
      exact ((Ptarget).asFuchsianDisc.nielsenRegion_properties hNE).1 hx
    obtain ⟨z, rfl⟩ := hxR
    exact ⟨z, hx, Subtype.ext ((hpoint z).trans hxy)⟩

/-- The actual open cut chamber maps onto the canonical Nielsen core of
the same actual Cayley target group. -/
theorem generalCoreTargetCayley_chamber_image
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    Edisc '' Ucore = fuchsianNielsenCore Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) := by
  rw [generalCoreTarget_chamber_eq_nielsen g orders s t ho hdef d hd hb hNE]
  exact generalCoreTargetCayley_nielsen_image g orders s t ho hdef d hd hb hNE

/-- Each prescribed boundary support as a genuine native disc line. -/
def generalCoreBoundaryDiscLine (j : Fin t) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (idx j 1)).toDiscLine

/-- Its original physical carrier is exactly the genuine Cayley image of
the complete original native cut axis. -/
theorem generalCoreBoundaryDiscLine_carrier (j : Fin t) :
    (generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j).carrier =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' Kcut j :=
  (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (idx j 1)).discCarrier_eq_cayley_image

/-- Every original complete cut support belongs to the source-defined whole
Nielsen boundary-line family; no family membership premise is supplied. -/
theorem generalCoreBoundaryDiscLine_mem_family
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget)
    (j : Fin t) :
    generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j ∈
      nielsenBoundaryDiscLineFamily Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) := by
  apply nielsenBoundary_full_line_mem_family
  rw [generalCoreBoundaryDiscLine_carrier]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hxFront := generalCoreCutAxis_subset_target_frontier g orders s t ho hdef d hd hb j hx
  have hxU : x ∈ frontier Ucore := by
    rw [generalCoreCutChamber_frontier_eq_axes]
    rw [generalCoreTargetTileSaturation_frontier_eq_axes] at hxFront
    exact hxFront
  have himage := (Edisc).image_frontier Ucore
  rw [generalCoreTargetCayley_chamber_image g orders s t ho hdef d hd hb hNE] at himage
  have hxDisc : Edisc x ∈ frontier (fuchsianNielsenCore Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)) :=
    himage ▸ mem_image_of_mem Edisc hxU
  exact ⟨Edisc x, hxDisc, (Ptarget).cayleyCoordinate_finite x⟩

/-- Each original boundary label determines its genuine whole-group maximal
boundary-hyperbolic cyclic conjugacy class. -/
def generalCoreBoundaryCyclicClass
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget)
    (j : Fin t) :
    FuchsianBoundaryHyperbolicCyclicConjugacyClasses (Pdisc).asFuchsianDisc :=
  nielsenBoundaryLineCyclicClass Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (generalCoreTargetCayley_fg g orders s t ho hdef d hd hb)
    (generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j)
    (generalCoreBoundaryDiscLine_mem_family g orders s t ho hdef d hd hb hNE j)

/-- The entire original-domain base line is exactly the image of its
complete original native support, with the same actual Cayley coordinate. -/
theorem generalCoreBoundaryDiscLine_original_carrier (j : Fin t) :
    (Pdisc).finiteCoordinate.symm ''
      (generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j).carrier = Edisc '' Kcut j := by
  rw [generalCoreBoundaryDiscLine_carrier, image_image]
  rfl

/-- Original-domain membership on a prescribed complete boundary line is
exactly native membership on its original complete cut axis. -/
theorem generalCoreBoundaryDiscLine_original_mem (j : Fin t) (x : ℍ) :
    Edisc x ∈ (Pdisc).finiteCoordinate.symm ''
      (generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j).carrier ↔ x ∈ Kcut j := by
  rw [generalCoreBoundaryDiscLine_original_carrier]
  constructor
  · rintro ⟨z, hz, he⟩
    exact (Edisc).injective he ▸ hz
  · intro hx
    exact mem_image_of_mem Edisc hx

/-- Different original prescribed boundary labels give distinct actual
whole-group maximal boundary-cyclic conjugacy classes. The proof uses the
whole original group orbit, followed by the actual complete-axis incidence. -/
theorem generalCoreBoundaryCyclicClass_injective
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    Function.Injective (generalCoreBoundaryCyclicClass g orders s t ho hdef d hd hb hNE) := by
  intro j k hclass
  let Lj := generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j
  let Lk := generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb k
  have hpEq := nielsenBoundaryLine_projection_eq_of_class_eq Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (generalCoreTargetCayley_fg g orders s t ho hdef d hd hb) Lj Lk
    (generalCoreBoundaryDiscLine_mem_family g orders s t ho hdef d hd hb hNE j)
    (generalCoreBoundaryDiscLine_mem_family g orders s t ho hdef d hd hb hNE k) hclass
  obtain ⟨z, _w, hz, _hw, _hne⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (idx j 1)).exists_two_points
  have hzJ : Edisc z ∈ (Pdisc).finiteCoordinate.symm '' Lj.carrier :=
    (generalCoreBoundaryDiscLine_original_mem g orders s t ho hdef d hd hb j z).mpr hz
  have hpJ : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain (Edisc z) ∈
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain '' ((Pdisc).finiteCoordinate.symm '' Lj.carrier) :=
    mem_image_of_mem _ hzJ
  have hpK := hpEq ▸ hpJ
  obtain ⟨y0, hy0, hproj⟩ := hpK
  obtain ⟨y, rfl⟩ := (Edisc).surjective y0
  have hyK := (generalCoreBoundaryDiscLine_original_mem g orders s t ho hdef d hd hb k y).mp hy0
  have horb := Quotient.exact hproj
  change Edisc y ∈ MulAction.orbit Kdisc (Edisc z) at horb
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp horb
  let b : Htarget := (generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb).symm a
  have hact := generalCoreBoundaryCayleyEquiv_action g orders s t ho hdef d hd hb b z
  rw [show generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb b = a from
    (generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb).apply_symm_apply a] at hact
  have hnative : b.val z = y := (Edisc).injective (hact.symm.trans ha)
  let γ : (Saux).Generated := ⟨b.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb b.property⟩
  exact (generalCoreCutAxis_translated_incidence g orders s t ho hdef d hd hb γ 1 j k y
    ⟨z, hz, hnative⟩ ⟨y, hyK, rfl⟩).1

/-- Every genuine original maximal boundary-hyperbolic cyclic class is
represented by one of the prescribed cut supports. This ranges over the
whole actual source-defined class type rather than selected generators. -/
theorem generalCoreBoundaryCyclicClass_surjective
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    Function.Surjective (generalCoreBoundaryCyclicClass g orders s t ho hdef d hd hb hNE) := by
  intro q
  induction q using Quotient.inductionOn with
  | h K =>
    obtain ⟨f, hfK, hf⟩ := K.property.2
    obtain ⟨M⟩ := (Pdisc).asFuchsianDisc.axisModel_exists f.val f.property hf.hyperbolic
    obtain ⟨L, hL, hM⟩ := nielsenBoundaryHyperbolic_axis_mem_family Pdisc
      (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) f hf M
    have hKL : K.val = (nielsenBoundaryLineMaximalCyclic Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
        (generalCoreTargetCayley_fg g orders s t ho hdef d hd hb) L hL).val := by
      rw [nielsenBoundaryLineMaximalCyclic_val, ← hM]
      exact nielsen_maximalBoundaryCyclic_eq_axisStabilizer Pdisc
        (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) K.val K.property.1 f hfK hf M
    have hclass : Quotient.mk (fuchsianBoundaryHyperbolicCyclicConjugacySetoid (Pdisc).asFuchsianDisc) K =
        nielsenBoundaryLineCyclicClass Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
          (generalCoreTargetCayley_fg g orders s t ho hdef d hd hb) L hL :=
      congrArg (Quotient.mk _) (Subtype.ext hKL)
    obtain ⟨z, _w, hz, _hw, _hne⟩ := L.toHalfPlane.exists_two_points
    have hzL : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z ∈ L.carrier := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
      exact hz
    obtain ⟨v, hvF, hev⟩ := nielsenBoundaryDiscLineFamily_subset_frontier Pdisc
      (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) L hL hzL
    obtain ⟨x, rfl⟩ := (Edisc).surjective v
    have heFront := (Edisc).image_frontier Ucore
    rw [generalCoreTargetCayley_chamber_image g orders s t ho hdef d hd hb hNE] at heFront
    obtain ⟨y, hy, hey⟩ := heFront.symm ▸ hvF
    have hxU : x ∈ frontier Ucore := (Edisc).injective hey ▸ hy
    rw [generalCoreCutChamber_frontier_eq_axes] at hxU
    obtain ⟨a, ha, y, hy, hay⟩ := mem_iUnion₂.mp hxU
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    have hpL : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain (Edisc x) ∈
        _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain '' ((Pdisc).finiteCoordinate.symm '' L.carrier) := by
      refine ⟨Edisc x, ?_, rfl⟩
      exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z, hzL, (congrArg (Pdisc).finiteCoordinate.symm hev).symm.trans
        ((Pdisc).finiteCoordinate.symm_apply_apply (Edisc x))⟩
    let aH : Htarget := ⟨a, ha⟩
    have hact : generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb aH • Edisc y = Edisc x :=
      (generalCoreBoundaryCayleyEquiv_action g orders s t ho hdef d hd hb aH y).trans
        (congrArg Edisc hay)
    have hproj : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain (Edisc x) =
        _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain (Edisc y) := by
      apply Quotient.sound
      change Edisc x ∈ MulAction.orbit Kdisc (Edisc y)
      exact MulAction.mem_orbit_iff.mpr ⟨generalCoreBoundaryCayleyEquiv g orders s t ho hdef d hd hb aH, hact⟩
    have hpJ : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain (Edisc x) ∈
        _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain '' ((Pdisc).finiteCoordinate.symm ''
          (generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j).carrier) :=
      ⟨Edisc y, (generalCoreBoundaryDiscLine_original_mem g orders s t ho hdef d hd hb j y).mpr hyj,
        hproj.symm⟩
    have hsame := nielsenBoundaryLineCyclicClass_eq_of_projection_inter Pdisc (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
      (generalCoreTargetCayley_fg g orders s t ho hdef d hd hb) L
      (generalCoreBoundaryDiscLine g orders s t ho hdef d hd hb j) hL
      (generalCoreBoundaryDiscLine_mem_family g orders s t ho hdef d hd hb hNE j)
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection (Pdisc).domain (Edisc x)) hpL hpJ
    exact ⟨j, hsame.symm.trans hclass.symm⟩

/-- The actual source boundary-hyperbolic cyclic class type is in genuine
bijection with the original t prescribed boundary labels. -/
def generalCoreBoundaryClassesEquiv
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    Fin t ≃ FuchsianBoundaryHyperbolicCyclicConjugacyClasses (Pdisc).asFuchsianDisc :=
  Equiv.ofBijective (generalCoreBoundaryCyclicClass g orders s t ho hdef d hd hb hNE)
    ⟨generalCoreBoundaryCyclicClass_injective g orders s t ho hdef d hd hb hNE,
      generalCoreBoundaryCyclicClass_surjective g orders s t ho hdef d hd hb hNE⟩

/-- The entire actual target group has exactly the prescribed t boundary
classes, with no boundary census, signature or area premise. -/
theorem generalCoreTarget_boundary_class_card
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Ktarget) :
    Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses (Pdisc).asFuchsianDisc) = t := by
  rw [← Nat.card_congr (generalCoreBoundaryClassesEquiv g orders s t ho hdef d hd hb hNE), Nat.card_fin]

end LowDimensionalTopology.Geometry.Fuchsian
