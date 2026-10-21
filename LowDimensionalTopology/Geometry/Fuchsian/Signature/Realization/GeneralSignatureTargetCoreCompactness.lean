/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetMobius
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryLabels
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane OnePoint
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

local notation "θ₀" => generalCoreTheta g orders s t
local notation "hθ₀" => generalCoreTheta_mem g orders s t ho hdef
local notation "ρ₀" => generalCoreAuxPairing g orders s t
local notation "hρ₀" => generalCoreAuxPairing_angle_profile g orders s t
local notation "τ₀" => Equiv.trans (generalCoreAuxPairing g orders s t) (finRotate _)
local notation "F₀" => cofiniteTangentialIdealFrame θ₀ d hθ₀ hd hb ρ₀ hρ₀
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "P₀" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "K₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "D₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc
  (generalCoreTargetMobiusData g orders s t ho hdef d hd hb)

/-- A genuine zero corner never lies on one of the deleted right-angle cuts. -/
theorem generalCore_zero_angle_not_cut
    (i : Fin (generalCoreAngles g orders s t).length) (hi : θ₀ i = 0) :
    ¬ generalCoreIsCutSide g orders s t i := by
  intro hcut
  obtain ⟨j, rfl⟩ := (generalCoreIsCutSide_iff g orders s t i).mp hcut
  rw [generalCoreBoundarySideIndex_angle] at hi
  norm_num at hi

/-- Every actual nonnegative cusp word uses only original retained generators.
Membership in the target is derived from the literal original word recursion. -/
theorem generalCoreTargetIdealWord_mem
    (i : Fin (generalCoreAngles g orders s t).length) (hi : θ₀ i = 0) (k : ℕ) :
    cofiniteTangentialIdealWord θ₀ d hθ₀ hd hb ρ₀ hρ₀ i (k : ℤ) ∈ H₀ := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, cofiniteTangentialIdealWord_zero]
    exact (H₀).one_mem
  | succ k ih =>
    rw [Nat.cast_succ, cofiniteTangentialIdealWord_step θ₀ d hθ₀ hd hb ρ₀ hρ₀ i hi]
    apply (H₀).mul_mem ih
    apply (H₀).inv_mem
    have hj : θ₀ ((τ₀ ^ (k : ℤ)) i) = 0 :=
      (cofiniteTangential_zpow_corner_angle θ₀ ρ₀ hρ₀ i (k : ℤ)).trans hi
    exact generalCoreTargetGenerator_mem g orders s t ho hdef d hd hb _
      (generalCore_zero_angle_not_cut g orders s t _ hj)

/-- The same actual positive label period gives a uniform height for every
original cusp. The translated peripheral elements belong to the true target,
and the source-defined Nielsen region contains their genuine high tails. -/
theorem generalCoreTarget_nielsen_uniform_cusp_tail
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    ∃ Y : ℝ, ∀ i : Fin (generalCoreAngles g orders s t).length, θ₀ i = 0 →
      ∀ z : ℍ, Y < (F₀ i • z).im → _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z ∈ (D₀).nielsenRegion hNE := by
  let N : ℕ := orderOf τ₀
  let a : ℝ := -(N : ℝ) * (2 * Real.sinh d)
  have hN : 0 < N := orderOf_pos τ₀
  have ha : a ≠ 0 := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    exact (mul_neg_of_neg_of_pos (neg_neg_of_pos hNp)
      (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr hd))).ne
  refine ⟨|a| / 2, ?_⟩
  intro i hi z hz
  let A := (F₀ i)⁻¹ * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL a * F₀ i
  have hreturn : (τ₀ ^ N) i = i := by rw [pow_orderOf_eq_one]; rfl
  have hword : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = cofiniteTangentialIdealWord θ₀ d hθ₀ hd hb ρ₀ hρ₀ i (N : ℤ) := by
    change fordSLNativeHom A = (fordSLNativeHom (F₀ i))⁻¹ *
      fordSLNativeHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL a) * fordSLNativeHom (F₀ ((τ₀ ^ (N : ℤ)) i))
    rw [zpow_natCast, hreturn]
    dsimp only [A]
    rw [map_mul, map_mul, map_inv]
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ H₀ := by
    rw [hword]
    exact generalCoreTargetIdealWord_mem g orders s t ho hdef d hd hb i hi N
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ K₀ := by
    refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩, ?_⟩
    exact nativeConformalSubgroupMobiusHom_matrix H₀
      (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb) A hA
  let q := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F₀ i)
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (a : ℂ) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K₀ := by
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q K₀ _).mpr
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, hproj, ?_⟩
    have hrepr : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q⁻¹ * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (a : ℂ) * q := by
      dsimp only [A, q]
      rw [map_mul, map_mul, map_inv, parabolicSL_translation_projection]
    rw [hrepr]
    group
  have hq : q.val '' (D₀).carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := realSLMobius_image_openHalfPlane (F₀ i)
  apply nielsenRegion_contains_normalized_translation_tail D₀ hNE q hq a ha hT
  refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (F₀ i • z), ⟨F₀ i • z, hz, rfl⟩, ?_⟩
  change q.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (F₀ i • z)) = _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z
  have hact : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (F₀ i • z) = q.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action (F₀ i) z).symm
  rw [hact]
  exact q.val.symm_apply_apply _

/-- Outside the actual target Nielsen region, the original closed polygon is
compact. All actual cusp tails were proved to lie in that same Nielsen region;
no truncation, desired parabolic, or core containment is supplied as a premise. -/
theorem generalCoreTarget_carrier_sdiff_nielsen_isCompact
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    IsCompact ((P₀).carrier \ (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE)) := by
  obtain ⟨Y, hY⟩ := generalCoreTarget_nielsen_uniform_cusp_tail g orders s t ho hdef d hd hb hNE
  have hcompact := cofiniteTangential_truncated_core_isCompact θ₀ d hθ₀ hd hb F₀
    (cofiniteTangentialIdealFrame_center θ₀ d hθ₀ hd hb ρ₀ hρ₀)
    (cofiniteTangentialIdealFrame_vertex θ₀ d hθ₀ hd hb ρ₀ hρ₀) Y
  have hclosedCarrier : IsClosed (P₀).carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
    exact isClosed_closure
  have hNopen : IsOpen (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) :=
    ((D₀).nielsenRegion_properties hNE).2.2.1.preimage _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous
  apply hcompact.of_isClosed_subset (hclosedCarrier.inter hNopen.isClosed_compl)
  intro z hz
  exact ⟨hz.1, fun i hi => le_of_not_gt (fun hhigh => hz.2 (hY i hi z hhigh))⟩

end LowDimensionalTopology.Geometry.Fuchsian
