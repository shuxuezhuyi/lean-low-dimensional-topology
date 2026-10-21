/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureConeOccurrences
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCoreEquality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise OnePoint
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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "G₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "P₀" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb
local notation "K₀" => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius G₀
local notation "f₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc P₀

/-- The faithful actual target in its physical original Cayley coordinate. -/
def generalCoreTargetCayleyEquiv : H₀ ≃* K₀ :=
  (generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius G₀)

theorem generalCoreTargetCayleyEquiv_action (a : H₀) (x : ℍ) :
    f₀ (a.val x) = generalCoreTargetCayleyEquiv g orders s t ho hdef d hd hb a • f₀ x := by
  have h := (P₀).cayleyCoordinate_equivariant
    (generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb a) x
  rw [generalCoreTargetMobiusEquiv_action] at h
  exact h

/-- Whole native stabilizers and whole original-disc target stabilizers,
with no selected cyclic subgroup or order supplied. -/
def generalCoreTargetCayley_stabilizerEquiv (x : ℍ) :
    MulAction.stabilizer H₀ x ≃* MulAction.stabilizer K₀ (f₀ x) := by
  let E := generalCoreTargetCayleyEquiv g orders s t ho hdef d hd hb
  have hAct := generalCoreTargetCayleyEquiv_action g orders s t ho hdef d hd hb
  refine {
    toFun := fun a => ⟨E a.val, (hAct a.val x).symm.trans (congrArg f₀ a.property)⟩
    invFun := fun a => ⟨E.symm a.val, ?_⟩
    left_inv := fun a => Subtype.ext (E.symm_apply_apply a.val)
    right_inv := fun a => Subtype.ext (E.apply_symm_apply a.val)
    map_mul' := fun a b => Subtype.ext (E.map_mul a.val b.val)
  }
  apply (f₀).injective
  change f₀ ((E.symm a.val).val x) = f₀ x
  rw [hAct, E.apply_symm_apply]
  exact a.property

/-- Each original occurrence is a genuine elliptic point of the entire
actual target group in its physical disc coordinate. -/
theorem generalCoreConePoint_elliptic (j : Fin orders.length) :
    (f₀ (generalCoreConePoint g orders s t ho hdef d hd hb j)).val ∈
      fuchsianCyclicFixedPoints (P₀).cayleyData.asFuchsianDisc .elliptic := by
  let x := generalCoreConePoint g orders s t ho hdef d hd hb j
  let E := generalCoreTargetCayleyEquiv g orders s t ho hdef d hd hb
  have hc : 2 ≤ Nat.card (MulAction.stabilizer H₀ x) := by
    rw [generalCoreConePoint_stabilizer_card]
    exact ho _ (List.getElem_mem j.isLt)
  let actualStabilizerFinite : Finite (MulAction.stabilizer H₀ x) := Nat.finite_of_card_ne_zero (by omega)
  let actualStabilizerNontrivial : Nontrivial (MulAction.stabilizer H₀ x) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : MulAction.stabilizer H₀ x)
  have han : a.val ≠ 1 := fun he => ha (Subtype.ext he)
  have hn : (E a.val).val ≠ 1 := by
    intro he
    exact han (E.injective ((Subtype.ext he).trans E.map_one.symm))
  have hfix : (E a.val).val.val (f₀ x).val = (f₀ x).val := by
    have h := generalCoreTargetCayleyEquiv_action g orders s t ho hdef d hd hb a.val x
    rw [show a.val.val x = x from a.property] at h
    exact (congrArg Subtype.val h).symm
  have hp : (f₀ x).val ∈ (P₀).cayleyData.asFuchsianDisc.carrier := (f₀ x).property
  exact ⟨fun _ => hp, (E a.val).val, (E a.val).property,
    fuchsianDisc_nonidentity_fixed_elliptic (P₀).cayleyData.asFuchsianDisc _
      (E a.val).property hn _ hp hfix, hfix⟩

/-- A nontrivial actual native stabilizer center belongs to the actual
original half-plane Nielsen region, transported through the genuine Cayley map. -/
theorem generalCoreTarget_fixed_mem_nielsen
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary G₀)
    (x : ℍ) (a : H₀) (ha : a ≠ 1) (hfix : a.val x = x) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x ∈ (D₀).nielsenRegion hNE := by
  let E := generalCoreTargetCayleyEquiv g orders s t ho hdef d hd hb
  have han : E a ≠ 1 := fun he => ha (E.injective (he.trans E.map_one.symm))
  have hxf : E a • f₀ x = f₀ x := by
    rw [← generalCoreTargetCayleyEquiv_action, hfix]
  have hn := nielsen_nontrivial_stabilizer_mem_core (P₀).cayleyData
    (hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) (f₀ x) (E a) han hxf
  have heq (A B : FuchsianDisc K₀) (he : A.carrier = B.carrier) : A = B := by
    cases A
    cases B
    cases he
    rfl
  have hD : (P₀).cayleyData.asFuchsianDisc = (D₀).nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius := by
    apply heq
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier]
    exact cayleyMobius_image_openHalfPlane.symm
  change (f₀ x).val ∈ (P₀).cayleyData.asFuchsianDisc.nielsenRegion _ at hn
  rw [hD,
    ← nielsenRegion_conjugation_image (D₀) hNE _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius] at hn
  obtain ⟨y, hy, he⟩ := hn
  have hc : (f₀ x).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x) := by
    have h := _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)
    change _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (((x : ℂ) : Mobius.ExtendedComplex))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane]
    exact h
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.injective (he.trans hc) ▸ hy

/-- Every actual target elliptic center is moved by an actual target element
to an original closed tile point away from the complete cut-wall set. -/
theorem generalCoreTarget_fixed_original_representative
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary G₀)
    (x : ℍ) (a : H₀) (ha : a ≠ 1) (hfix : a.val x = x) :
    ∃ (b : H₀) (y : ℍ),
      y ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
        (generalCoreTheta_mem g orders s t ho hdef) hd hb)).carrier ∧
      y ∉ generalCoreCutWallUnion g orders s t ho hdef d hd hb ∧ b.val y = x := by
  have hxN := generalCoreTarget_fixed_mem_nielsen g orders s t ho hdef d hd hb hNE x a ha hfix
  have hxU : x ∈ generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I := by
    rw [generalCoreTarget_chamber_eq_nielsen g orders s t ho hdef d hd hb hNE]
    exact hxN
  have hxS := generalCoreTargetTileSaturation_base_chamber_cover g orders s t ho hdef d hd hb hxU
  obtain ⟨b, hbmem, y, hy, he⟩ := mem_iUnion₂.mp hxS
  have hxW : x ∉ generalCoreCutWallUnion g orders s t ho hdef d hd hb :=
    connectedComponentIn_subset _ _ hxU
  have hyW : y ∉ generalCoreCutWallUnion g orders s t ho hdef d hd hb := by
    intro hyW
    apply hxW
    rw [← he, ← generalCoreCutWallUnion_image g orders s t ho hdef d hd hb b
      (generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb hbmem)]
    exact mem_image_of_mem b hyW
  exact ⟨⟨b, hbmem⟩, y, hy, hyW, he⟩

end LowDimensionalTopology.Geometry.Fuchsian
