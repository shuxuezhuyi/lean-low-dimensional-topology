module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier

public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ParabolicFundamentalBoundary
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Transversals
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonBoundarySides
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

@[expose] public section

open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Raising a genuine upper-half-plane point to a prescribed positive height. -/
def stripVerticalLift (z : ℍ) (Y : ℝ) (hY : 0 < Y) : ℍ :=
  ⟨⟨z.re, Y⟩, hY⟩

/-- An upward-closed preconnected set disjoint from its unit translate has horizontal width
strictly less than one between any two of its points. -/
theorem upward_preconnected_re_lt_add_one
    {S : Set ℍ} (hS : IsPreconnected S)
    (hup : ∀ z ∈ S, ∀ Y : ℝ, z.im ≤ Y → ∀ hY : 0 < Y,
      stripVerticalLift z Y hY ∈ S)
    (hdisj : Disjoint S ((fun z : ℍ => (1 : ℝ) +ᵥ z) '' S))
    {z w : ℍ} (hz : z ∈ S) (hw : w ∈ S) : w.re < z.re + 1 := by
  by_contra hlt
  have hzw : z.re + 1 ≤ w.re := le_of_not_gt hlt
  obtain ⟨u, hu, hure⟩ := hS.intermediate_value hz hw
    UpperHalfPlane.continuous_re.continuousOn
    (show z.re + 1 ∈ Icc z.re w.re from ⟨by linarith, hzw⟩)
  let Y := max z.im u.im
  have hY : 0 < Y := lt_of_lt_of_le z.im_pos (le_max_left _ _)
  have hzY : stripVerticalLift z Y hY ∈ S := hup z hz Y (le_max_left _ _) hY
  have huY : stripVerticalLift u Y hY ∈ S := hup u hu Y (le_max_right _ _) hY
  have heq : (1 : ℝ) +ᵥ stripVerticalLift z Y hY = stripVerticalLift u Y hY := by
    apply UpperHalfPlane.ext_re_im
    · simpa only [UpperHalfPlane.vadd_re, stripVerticalLift, UpperHalfPlane.mk_re] using
        (by linarith [hure] : 1 + z.re = u.re)
    · simp only [UpperHalfPlane.vadd_im, stripVerticalLift, UpperHalfPlane.mk_im]
  exact Set.disjoint_left.mp hdisj huY ⟨stripVerticalLift z Y hY, hzY, heq⟩

end LowDimensionalTopology.Geometry.Fuchsian

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped OnePoint Topology Complex.UnitDisc Pointwise
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
local instance parStripMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance parStripBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- Every actual normalized polygon point contains its complete upward vertical half-ray. -/
theorem IsConvexFuchsianPolygon.normalized_upward_closed
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (η : ℂ) (hη : η ∈ fuchsianPolygonIdealBoundary P D)
    (q : Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) (hqη : q.val (η : OnePoint ℂ) = ∞)
    (z : ℍ) (hz : z ∈ fordSLNativeHom A '' (P.halfPlaneCoordinate '' D))
    (Y : ℝ) (hzY : z.im ≤ Y) (hY : 0 < Y) :
    stripVerticalLift z Y hY ∈ fordSLNativeHom A '' (P.halfPlaneCoordinate '' D) := by
  obtain ⟨w,⟨x,hx,rfl⟩,rfl⟩ := hz
  have hηB : (η : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary η).mpr ((mem_fuchsianPolygonIdealBoundary P D η).mp hη).2
  have hηH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (η : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealBoundary_cayley_iff _).mpr (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply] using hηB)
  have hRay := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHLineRay_discHRay (P.finiteCoordinate x) η hηB).toHalfPlane
  let R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (P.halfPlaneCoordinate x) :=
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay (P.finiteCoordinate x) η,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm η,hηH,hRay⟩
  let R' := R.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ A)
  have hRend : R'.idealEndpoint = ∞ := by
    rw [hRay_realSLMap_idealEndpoint R A,R.idealEndpoint_unique hRay,hA]
    change q.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (η : OnePoint ℂ))) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply,hqη]
  have hsub : R'.val ⊆ fordSLNativeHom A '' (P.halfPlaneCoordinate '' D) := by
    rw [←R.realGLMap_carrier]
    exact image_mono (hD.ideal_halfPlane_ray_subset x hx η hη)
  apply hsub
  apply (R'.mem_iff_upward_of_endpoint_infty hRend _).mpr
  exact ⟨rfl,hzY⟩

/-- Actual normalized fundamental polygons are disjoint from their actual unit translations. -/
theorem IsFuchsianFundamentalDomain.normalized_disjoint_unitTranslation
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D)
    (q : Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) :
    Disjoint (fordSLNativeHom A '' (P.halfPlaneCoordinate '' D))
      ((fun z : ℍ => (1 : ℝ)+ᵥz) '' (fordSLNativeHom A '' (P.halfPlaneCoordinate '' D))) := by
  obtain ⟨g,hg,hgT⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mp hT
  let G : H := ⟨g,hg⟩
  have hGn : G ≠ 1 := by
    intro he
    have hg1 : g = 1 := congrArg Subtype.val he
    rw [hg1] at hgT
    simp only [mul_one,mul_inv_cancel] at hgT
    have hh := congrArg (fun f : Mobius.complexMobiusGroup => f.val (0 : ℂ)) hgT
    change ((0 : ℂ) : OnePoint ℂ) = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1).val (0 : ℂ) at hh
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe] at hh
    have hh' := OnePoint.coe_injective hh
    norm_num at hh'
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) = q*G.val*q⁻¹ :=
    realSLMobius_unitTranslation.trans hgT.symm
  have hact (x : P.domain.carrier) :
      (1 : ℝ)+ᵥfordSLNativeHom A (P.halfPlaneCoordinate x) =
        fordSLNativeHom A (P.halfPlaneCoordinate (G • x)) := by
    have he := congrArg (fun e : ℍ ≃ᵢ ℍ => e (P.halfPlaneCoordinate x))
      (halfPlane_chart_action_intertwine P q A hA G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) hB)
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 • (A • P.halfPlaneCoordinate x) =
      A • P.halfPlaneAction G (P.halfPlaneCoordinate x) at he
    rw [P.halfPlaneAction_coordinate] at he
    have ht (w : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 • w = (1 : ℝ)+ᵥw := by
      apply UpperHalfPlane.ext
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
      simp only [UpperHalfPlane.coe_vadd,Complex.ofReal_one,add_comm]
    rw [ht] at he
    exact he
  apply Set.disjoint_left.mpr
  rintro z ⟨v,⟨x,hx,rfl⟩,hxz⟩ ⟨w,⟨u,⟨y,hy,rfl⟩,rfl⟩,hwz⟩
  have he : G • y = x := by
    apply P.halfPlaneCoordinate.injective
    apply (fordSLNativeHom A).injective
    exact ((hact y).symm.trans hwz).trans hxz.symm
  exact Set.disjoint_left.mp (hD.disjoint_image hGn) ⟨y,hy,he⟩ hx

/-- Every genuine normalized polygon at a parabolic ideal point has actual horizontal width at most one. -/
theorem IsConvexFuchsianPolygon.normalized_horizontal_width
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (η : ℂ) (hη : η ∈ fuchsianPolygonIdealBoundary P D)
    (q : Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) (hqη : q.val (η : OnePoint ℂ) = ∞)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
    {z w : ℍ} (hz : z ∈ fordSLNativeHom A '' (P.halfPlaneCoordinate '' D))
    (hw : w ∈ fordSLNativeHom A '' (P.halfPlaneCoordinate '' D)) : w.re < z.re+1 := by
  have hc := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1
  have hs := hc.isPreconnected.image P.halfPlaneCoordinate P.halfPlaneCoordinate.continuous.continuousOn
  have hs' := hs.image (fordSLNativeHom A) (fordSLNativeHom A).continuous.continuousOn
  exact upward_preconnected_re_lt_add_one hs'
    (hD.normalized_upward_closed η hη q A hA hqη)
    (hD.locallyFinite.fundamental.normalized_disjoint_unitTranslation q A hA hT) hz hw


/-- Failure of genuine accumulation at infinity bounds all actual heights. -/
theorem halfPlane_height_bounded_of_not_infty_closure (S : Set ℍ)
    (hno : (∞ : OnePoint ℂ) ∉ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S)) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ S, z.im ≤ M := by
  have hc : IsCompact (((↑) : ℂ → OnePoint ℂ) ⁻¹' closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S)) :=
    ((OnePoint.isClosed_iff_of_notMem hno).mp isClosed_closure).2
  obtain ⟨M,hM,hm⟩ := hc.isBounded.exists_pos_norm_le
  refine ⟨M,hM,?_⟩
  intro z hz
  exact (Complex.im_le_norm (z : ℂ)).trans (hm (z : ℂ) (subset_closure ⟨z,hz,rfl⟩))

/-- A missing genuine ideal endpoint permits shrinking the actual horocyclic region away from the closed polygon. -/
theorem realSL_horocyclic_shrink_disjoint_of_endpoint_not_closure
    (S : Set ℍ) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hno : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ ∉ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S)) :
    ∃ M : ℝ, 0 < M ∧ Disjoint (closure S)
      ((fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion M) := by
  let U := (fun z : ℍ => B⁻¹ • z) '' closure S
  have hnot : (∞ : OnePoint ℂ) ∉ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' U) := by
    intro hmem
    have he := mem_closure_image (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)).continuous.continuousAt hmem
    apply hno
    apply closure_minimal (s := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' U))
      ?_ isClosed_closure he
    rintro _ ⟨_,⟨u,⟨v,hv,rfl⟩,rfl⟩,rfl⟩
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val (((B⁻¹ • v : ℍ) : ℂ) : OnePoint ℂ) ∈ _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,smul_inv_smul]
    exact image_closure_subset_closure_image
      (OnePoint.continuous_coe.comp UpperHalfPlane.continuous_coe) ⟨v,hv,rfl⟩
  obtain ⟨M,hM,hm⟩ := halfPlane_height_bounded_of_not_infty_closure U hnot
  refine ⟨M,hM,Set.disjoint_left.mpr ?_⟩
  rintro x hx ⟨u,hu,hux⟩
  have huU : u ∈ U := ⟨x,hx,by change B⁻¹ • x = u; rw [←hux]; exact inv_smul_smul B u⟩
  exact not_lt_of_ge (hm u huU) hu

/-- A genuine height-preserving real action preserves every literal horizontal horocyclic region. -/
theorem realSL_height_preserving_horocyclic_image
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : ∀ z : ℍ, (B • z : ℍ).im = z.im)
    (k : ℝ) : (fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k = _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k := by
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    change k < (B • u : ℍ).im
    rwa [hB]
  · intro hz
    refine ⟨B⁻¹ • z,?_,smul_inv_smul B z⟩
    have he := hB (B⁻¹ • z)
    rw [smul_inv_smul] at he
    change k < (B⁻¹ • z : ℍ).im
    rwa [←he]

/-- In the original discrete group with a unit translation, genuine horocyclic images
with a common ideal endpoint agree at every prescribed height. -/
theorem discrete_unitTranslation_horocyclic_image_eq_of_endpoint
    (N : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ N)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ N)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N)
    (hend : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞) (k : ℝ) :
    (fun z : ℍ => A • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k =
      (fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k := by
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B⁻¹*A) ∈ N := by
    rw [map_mul,map_inv]
    exact N.mul_mem (N.inv_mem hB) hA
  have hfix : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B⁻¹*A)).val ∞ = ∞ := by
    rw [map_mul,map_inv]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val.symm ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞) = ∞
    rw [hend,Equiv.symm_apply_apply]
  have hh := realSL_height_preserving_horocyclic_image (B⁻¹*A)
    (discrete_unitTranslation_fix_infty_preserves_height N hd hT (B⁻¹*A) hc hfix) k
  have he := congrArg (Set.image (fun z : ℍ => B • z)) hh
  rw [image_image] at he
  convert he using 1
  congr 1
  funext z
  rw [mul_smul,smul_inv_smul]


/-- Finitely many genuine horocyclic images can be shrunk simultaneously so that every
remaining incidence has its actual ideal basepoint in the genuine polygon closure. -/
theorem finite_horocyclic_images_shrink_to_actual_endpoints
    (N : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ N) (S : Set ℍ)
    (hF : {L : Set ℍ | ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ L = (fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 ∧
      (closure S ∩ L).Nonempty}.Finite) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N →
      (closure S ∩ ((fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)).Nonempty →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) := by
  classical
  let F : Set (Set ℍ) := {L | ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ L = (fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 ∧
    (closure S ∩ L).Nonempty}
  let : Fintype F := hF.fintype
  have hrep (L : F) : ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ L.val = (fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 := by
    obtain ⟨B,hB,he,_hhit⟩ := L.property
    exact ⟨B,hB,he⟩
  choose B hBN hBe using hrep
  have hbound (L : F) : ∃ M : ℝ, 0 < M ∧
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B L)).val ∞ ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) ∨
      Disjoint (closure S) ((fun z : ℍ => B L • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion M)) := by
    by_cases hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B L)).val ∞ ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S)
    · exact ⟨1,zero_lt_one,Or.inl hp⟩
    · obtain ⟨M,hM,hm⟩ := realSL_horocyclic_shrink_disjoint_of_endpoint_not_closure S (B L) hp
      exact ⟨M,hM,Or.inr hm⟩
  choose M _hM hML using hbound
  obtain ⟨K,hK⟩ := (Set.finite_range M).bddAbove
  let k := max 1 K
  refine ⟨k,le_max_left _ _,?_⟩
  intro A hAN hhit
  have hk1 : 1 ≤ k := le_max_left _ _
  have hsub : _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 :=
    fun _ hz => lt_of_le_of_lt hk1 hz
  let L : F := ⟨(fun z : ℍ => A • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1,
    A,hAN,rfl,hhit.mono (inter_subset_inter_right _ (image_mono hsub))⟩
  have hend : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B L)).val ∞ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ :=
    realSL_horocyclic_image_eq_endpoint (B L) A 1 zero_lt_one (hBe L).symm
  rcases hML L with hp | hdisj
  · exact hend ▸ hp
  · have hkM : M L ≤ k := (hK (mem_range_self L)).trans (le_max_right _ _)
    have hsM : _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion (M L) :=
      fun _ hz => lt_of_le_of_lt hkM hz
    have he := discrete_unitTranslation_horocyclic_image_eq_of_endpoint N hd hT
      (B L) A (hBN L) hAN hend k
    obtain ⟨z,hzS,hzA⟩ := hhit
    rw [←he] at hzA
    exact False.elim (Set.disjoint_left.mp hdisj hzS (image_mono hsM hzA))

/-- The preceding simultaneous shrinking is available for every original locally finite
polygon and its genuine whole-group cusp chart, with no incidence conclusion assumed. -/
theorem IsLocallyFiniteFuchsianDomain.normalized_horocyclic_shrink_to_actual_endpoints
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (q : Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H →
      (closure (fordSLNativeHom A '' (P.halfPlaneCoordinate '' D)) ∩
        ((fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)).Nonempty →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ ∈
        closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (fordSLNativeHom A '' (P.halfPlaneCoordinate '' D))) := by
  let N := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N := by
    let : DiscreteTopology H := P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  apply finite_horocyclic_images_shrink_to_actual_endpoints N hd hT
  have hf := hD.normalized_horocyclic_images_finite q hq A hA hT 1 zero_lt_one
  apply hf.subset
  rintro L ⟨B,hB,rfl,hhit⟩
  exact ⟨⟨fordSLNativeHom B,(mem_fordNativeGroup N _).mpr ⟨B,hB,rfl⟩⟩,rfl,hhit⟩


/-- The actual sphere closure commutes with a genuine real determinant-one action. -/
theorem realSL_extended_closure_image (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℍ) :
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' ((fun z : ℍ => B • z) '' S)) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val '' closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' ((fun z : ℍ => B • z) '' S) =
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) := by
    rw [image_image,image_image]
    congr 1
    funext z
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action B z).symm
  rw [he,←(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)).image_closure]
  rfl

/-- Every genuine ray to infinity from an open hyperbolically convex set accumulating
at infinity remains in the original set. -/
theorem open_hConvex_ray_to_infty_subset
    {S : Set ℍ}
    (ho : IsOpen S)
    (hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S)
    (hInf : (∞ : OnePoint ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S))
    {z : ℍ}
    (hz : z ∈ S)
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (hEnd : R.idealEndpoint = ∞) : R.val ⊆ S := by
  have hInfI : (∞ : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints S := ⟨hInf,by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary]⟩
  have ht : ((1 : ℂ) : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discTraceIdealEndpoints (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discTraceIdealEndpoints_cayley_image]
    exact ⟨∞,hInfI,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty⟩
  have hcl : (1 : ℂ) ∈ closure ((fun w : 𝔻 => (w : ℂ)) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S)) := by
    have hh := ht.1
    change (1 : ℂ) ∈ ((↑) : ℂ → OnePoint ℂ) ⁻¹'
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S)) at hh
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) =
        ((↑) : ℂ → OnePoint ℂ) '' ((fun w : 𝔻 => (w : ℂ)) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S)) := by
      simp only [image_image]
      rfl
    rw [he] at hh
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.onePoint_coe_preimage_closure_image] at hh
  have hRD := R.isRay.toDisc
  rw [hEnd,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty] at hRD
  let T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) :=
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' R.val,(1 : ℂ),by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary],hRD⟩
  have hTend : T.idealEndpoint = ((1 : ℂ) : OnePoint ℂ) := by
    obtain ⟨_,_,_,_,_,ht1⟩ := T.isRay
    obtain ⟨_,_,_,_,_,ht2⟩ := hRD
    exact singleton_injective (ht1.symm.trans ht2)
  have hs := open_discHConvex_ideal_ray_subset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap S ho)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hc) (mem_image_of_mem _ hz) T 1
    (by simp) hTend hcl
  intro w hw
  obtain ⟨u,hu,he⟩ := hs ⟨w,hw,rfl⟩
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective he ▸ hu

/-- The full genuine upward-closure conclusion follows from actual convexity and actual ideal accumulation. -/
theorem open_hConvex_upward_closed
    {S : Set ℍ}
    (ho : IsOpen S)
    (hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S)
    (hInf : (∞ : OnePoint ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S)) :
    ∀ z ∈ S, ∀ Y : ℝ, z.im ≤ Y → ∀ hY : 0 < Y, stripVerticalLift z Y hY ∈ S := by
  intro z hz Y hzY hY
  have hi : (∞ : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary := by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary]
  have hR := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isHLineRay_hRay z ∞ hi
  let R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRay z ∞,∞,hi,hR⟩
  have hEnd : R.idealEndpoint = ∞ := R.idealEndpoint_unique hR
  exact open_hConvex_ray_to_infty_subset ho hc hInf hz R hEnd
    ((R.mem_iff_upward_of_endpoint_infty hEnd _).mpr ⟨rfl,hzY⟩)

/-- Genuine upward closure passes to the actual topological closure. -/
theorem upward_closed_closure {S : Set ℍ}
    (hup : ∀ z ∈ S, ∀ Y : ℝ, z.im ≤ Y → ∀ hY : 0 < Y, stripVerticalLift z Y hY ∈ S) :
    ∀ z ∈ closure S, ∀ Y : ℝ, z.im ≤ Y → ∀ hY : 0 < Y,
      stripVerticalLift z Y hY ∈ closure S := by
  intro z hz Y hzY hY
  let t := Y-z.im
  have ht : 0 ≤ t := sub_nonneg.mpr hzY
  let F : ℍ → ℍ := fun w => stripVerticalLift w (w.im+t) (by linarith [w.im_pos])
  have hF : Continuous F := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun w : ℍ => ((F w : ℍ) : ℂ))
    have he (w : ℍ) : ((F w : ℍ) : ℂ) = (w : ℂ)+(t : ℂ)*Complex.I := by
      change (⟨w.re,w.im+t⟩ : ℂ) = (w : ℂ)+(t : ℂ)*Complex.I
      apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,mul_one,sub_zero,add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    simp_rw [he]
    fun_prop
  have hs : F '' S ⊆ S := by
    rintro _ ⟨w,hw,rfl⟩
    exact hup w hw _ (by linarith) _
  have hh := image_closure_subset_closure_image hF ⟨z,hz,rfl⟩
  have hmem : F z ∈ closure S := closure_mono hs hh
  have he : F z = stripVerticalLift z Y hY := by
    apply UpperHalfPlane.ext_re_im
    · rfl
    · change z.im+(Y-z.im) = Y
      ring
  exact he ▸ hmem


/-- Every nonempty horizontal section of an actual open strip of width at most one
has two distinct genuine frontier points on opposite sides of its interior point. -/
theorem open_strip_two_horizontal_frontier {S : Set ℍ} (ho : IsOpen S)
    (hwidth : ∀ z ∈ S, ∀ w ∈ S, w.re < z.re+1) {z : ℍ} (hz : z ∈ S) :
    ∃ u v : ℍ, u ∈ frontier S ∧ v ∈ frontier S ∧
      u.im = z.im ∧ v.im = z.im ∧ u.re < z.re ∧ z.re < v.re := by
  let φ : ℝ → ℍ := fun t => _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe t z.im z.im_pos
  have hφ : Continuous φ := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun t : ℝ => (⟨t,z.im⟩ : ℂ))
    have he (t : ℝ) : (⟨t,z.im⟩ : ℂ) = (t : ℂ)+(z.im : ℂ)*Complex.I := by
      apply Complex.ext <;> simp
    simp_rw [he]
    fun_prop
  let V : Set ℝ := φ ⁻¹' S
  have hV : IsOpen V := ho.preimage hφ
  have hzφ : φ z.re = z := by apply UpperHalfPlane.ext_re_im <;> rfl
  have hzV : z.re ∈ V := hzφ ▸ hz
  have hVn : V.Nonempty := ⟨z.re,hzV⟩
  have hbelow : BddBelow V := by
    refine ⟨z.re-1,?_⟩
    intro x hx
    have hh := hwidth (φ x) hx z hz
    change z.re < x+1 at hh
    linarith
  have habove : BddAbove V := by
    refine ⟨z.re+1,?_⟩
    intro x hx
    exact (hwidth z hz (φ x) hx).le
  have ha : sInf V ∉ V := by
    intro ha
    obtain ⟨l,r,hlr,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds ha)
    have hm : (l+sInf V)/2 ∈ V := hsub ⟨by linarith [hlr.1,hlr.2],by linarith [hlr.1,hlr.2]⟩
    have hh := csInf_le hbelow hm
    linarith [hlr.1]
  have hb : sSup V ∉ V := by
    intro hb
    obtain ⟨l,r,hlr,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds hb)
    have hm : (sSup V+r)/2 ∈ V := hsub ⟨by linarith [hlr.1,hlr.2],by linarith [hlr.1,hlr.2]⟩
    have hh := le_csSup habove hm
    linarith [hlr.2]
  have haS : φ (sInf V) ∈ closure S := by
    have hh := mem_closure_image hφ.continuousAt (csInf_mem_closure hVn hbelow)
    exact closure_mono (image_preimage_subset φ S) hh
  have hbS : φ (sSup V) ∈ closure S := by
    have hh := mem_closure_image hφ.continuousAt (csSup_mem_closure hVn habove)
    exact closure_mono (image_preimage_subset φ S) hh
  have haFront : φ (sInf V) ∈ frontier S := by
    rw [frontier,ho.interior_eq]
    exact ⟨haS,ha⟩
  have hbFront : φ (sSup V) ∈ frontier S := by
    rw [frontier,ho.interior_eq]
    exact ⟨hbS,hb⟩
  refine ⟨φ (sInf V),φ (sSup V),haFront,hbFront,rfl,rfl,?_,?_⟩
  · change sInf V < z.re
    exact lt_of_le_of_ne (csInf_le hbelow hzV) (fun he => ha (he.symm ▸ hzV))
  · change z.re < sSup V
    exact lt_of_le_of_ne (le_csSup habove hzV) (fun he => hb (he ▸ hzV))

/-- Actual normalized polygon interiors retain genuine hyperbolic convexity. -/
theorem IsConvexFuchsianPolygon.normalized_hConvex
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (fordSLNativeHom A '' (P.halfPlaneCoordinate '' D)) := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' (P.halfPlaneCoordinate '' D) = P.finiteCoordinate '' D := by
    simp only [image_image]
    congr 1
    funext x
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane (P.finiteCoordinate x)
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (P.halfPlaneCoordinate '' D) := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mpr
    rw [he]
    exact hD.convex
  exact hc.isometry_image (fordSLNativeHom A).isometry


/-- Two genuine closed tiles meeting sufficiently deep in a cusp retain every upward
vertical point in their actual intersection. -/
theorem cusp_closed_intersection_upward
    (N : Subgroup Mobius.complexMobiusGroup)
    {S : Set ℍ}
    (ho : IsOpen S)
    (hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S)
    (hInf : (∞ : OnePoint ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S))
    (k : ℝ) (hgood : ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N →
      (closure S ∩ ((fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)).Nonempty →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ N)
    {z : ℍ} (hz : z ∈ closure S ∩ ((fun w : ℍ => A • w) '' closure S)) (hzk : k < z.im)
    (Y : ℝ) (hzY : z.im ≤ Y) (hY : 0 < Y) :
    stripVerticalLift z Y hY ∈ closure S ∩ ((fun w : ℍ => A • w) '' closure S) := by
  obtain ⟨u,hu,huz⟩ := hz.2
  have hAi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹ ∈ N := by rw [map_inv]; exact N.inv_mem hA
  have hhit : (closure S ∩ ((fun w : ℍ => A⁻¹ • w) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)).Nonempty := by
    refine ⟨u,hu,z,hzk,?_⟩
    change A⁻¹ • z = u
    rw [←huz]
    exact inv_smul_smul A u
  have hAiEnd := hgood A⁻¹ hAi hhit
  have hTInf : (∞ : OnePoint ℂ) ∈
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' ((fun w : ℍ => A • w) '' S)) := by
    rw [realSL_extended_closure_image]
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹).val ∞,hAiEnd,?_⟩
    rw [map_inv]
    exact Equiv.apply_symm_apply _ _
  have htO : IsOpen ((fun w : ℍ => A • w) '' S) := (fordSLNativeHom A).toHomeomorph.isOpenMap S ho
  have htC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex ((fun w : ℍ => A • w) '' S) := hc.isometry_image (fordSLNativeHom A).isometry
  refine ⟨upward_closed_closure (open_hConvex_upward_closed ho hc hInf) z hz.1 Y hzY hY,?_⟩
  have he : closure ((fun w : ℍ => A • w) '' S) = (fun w : ℍ => A • w) '' closure S :=
    ((fordSLNativeHom A).toHomeomorph.image_closure S).symm
  have hzt : z ∈ closure ((fun w : ℍ => A • w) '' S) := by rw [he]; exact hz.2
  rw [←he]
  exact upward_closed_closure (open_hConvex_upward_closed htO htC hTInf) z hzt Y hzY hY

/-- A genuine native geodesic containing a full upward vertical half-ray is that vertical line. -/
theorem halfPlaneLine_eq_vertical_of_upward
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (z : ℍ)
    (hup : ∀ Y : ℝ, z.im ≤ Y → ∀ hY : 0 < Y, stripVerticalLift z Y hY ∈ L.carrier) :
    L = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical z.re := by
  cases L with
  | vertical c =>
    have hz := hup z.im le_rfl z.im_pos
    change z.re = c at hz
    rw [hz]
  | circle c r hr =>
    let Y := z.im+r+1
    have hY : 0 < Y := by dsimp [Y]; linarith [z.im_pos]
    have hz := hup Y (by dsimp [Y]; linarith) hY
    change ‖((stripVerticalLift z Y hY : ℍ) : ℂ)-(c : ℂ)‖ = r at hz
    have hi := Complex.im_le_norm (((stripVerticalLift z Y hY : ℍ) : ℂ)-(c : ℂ))
    rw [hz] at hi
    change Y-0 ≤ r at hi
    dsimp [Y] at hi
    linarith [z.im_pos]


/-- The genuine original polygon chart followed by its specified real determinant-one normalization. -/
def normalizedPolygonHalfPlaneChart {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    P.domain.carrier ≃ₜ ℍ := P.halfPlaneCoordinate.trans (fordSLNativeHom A).toHomeomorph

theorem normalizedPolygonHalfPlaneChart_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (S : Set P.domain.carrier) :
    normalizedPolygonHalfPlaneChart P A '' S = fordSLNativeHom A '' (P.halfPlaneCoordinate '' S) := by
  rw [image_image]
  rfl

/-- The original actual action intertwines with every actual normalized group element. -/
theorem normalizedPolygonHalfPlaneChart_smul
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (g : H) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B = q*g.val*q⁻¹) (x : P.domain.carrier) :
    B • normalizedPolygonHalfPlaneChart P A x = normalizedPolygonHalfPlaneChart P A (g • x) := by
  have he := congrArg (fun e : ℍ ≃ᵢ ℍ => e (P.halfPlaneCoordinate x))
    (halfPlane_chart_action_intertwine P q A hA g B hB)
  change B • (A • P.halfPlaneCoordinate x) = A • P.halfPlaneAction g (P.halfPlaneCoordinate x) at he
  rwa [P.halfPlaneAction_coordinate] at he

/-- The native chart preserves the literal intersection of the original two closed tiles. -/
theorem normalizedPolygonHalfPlaneChart_closed_tile_inter
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier)
    (q : Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) (g : H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B = q*g.val*q⁻¹) :
    normalizedPolygonHalfPlaneChart P A '' (closure D ∩ fuchsianDomainTile P D g) =
      closure (normalizedPolygonHalfPlaneChart P A '' D) ∩
      ((fun z : ℍ => B • z) '' closure (normalizedPolygonHalfPlaneChart P A '' D)) := by
  let ψ := normalizedPolygonHalfPlaneChart P A
  change ψ '' (closure D ∩ ((fun x : P.domain.carrier => g • x) '' closure D)) = _
  rw [image_inter ψ.injective,←ψ.image_closure D]
  congr 1
  rw [image_image,image_image]
  congr 1
  funext x
  exact (normalizedPolygonHalfPlaneChart_smul P q A hA g B hB x).symm

/-- The normalized image of each true original side still lies on a genuine native geodesic. -/
theorem normalizedPolygonHalfPlaneChart_side_line
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine, normalizedPolygonHalfPlaneChart P A '' S ⊆ L.carrier := by
  obtain ⟨L,hL⟩ := hS.2.1.2
  let M := L.toHalfPlane.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ A)
  refine ⟨M,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  exact ⟨P.halfPlaneCoordinate x,(L.mem_carrier _).mp (hL ⟨x,hx,rfl⟩),rfl⟩

/-- The actual extended closure of a normalized original set is transported by the same genuine Mobius map. -/
theorem normalizedPolygonHalfPlaneChart_extended_closure
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier)
    (q : Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) :
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (normalizedPolygonHalfPlaneChart P A '' D)) =
      q.val '' closure ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D) := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (normalizedPolygonHalfPlaneChart P A '' D) =
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D) := by
    simp only [image_image]
    congr 1
    funext x
    exact (halfPlane_chart_coordinate_extended P q A hA x).symm
  rw [he,←(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_closure]
  rfl

/-- A full actual upward ray in the normalized original side yields its genuine original ideal endpoint. -/
theorem normalizedPolygonHalfPlaneChart_side_idealEndpoint
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (S : Set P.domain.carrier)
    (q : Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) (η : Circle) (hqη : q.val ((η : ℂ) : OnePoint ℂ) = ∞)
    (z : ℍ) (hup : ∀ Y : ℝ, z.im ≤ Y → ∀ hY : 0 < Y,
      stripVerticalLift z Y hY ∈ normalizedPolygonHalfPlaneChart P A '' S) :
    IsFuchsianSideIdealEndpoint P S η := by
  let w (n : ℕ) := stripVerticalLift z (z.im+(n : ℝ)) (by positivity)
  have hw (n : ℕ) : w n ∈ normalizedPolygonHalfPlaneChart P A '' S :=
    hup _ (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) _
  have hlim : Filter.Tendsto (fun n => _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (w n)) Filter.atTop (𝓝 (∞ : OnePoint ℂ)) := by
    apply halfPlane_coe_tendsto_infty_of_height
    change Filter.Tendsto (fun n : ℕ => z.im+(n : ℝ)) Filter.atTop Filter.atTop
    exact Filter.tendsto_atTop_mono (fun n => by linarith [z.im_pos]) tendsto_natCast_atTop_atTop
  have hcl : (∞ : OnePoint ℂ) ∈
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (normalizedPolygonHalfPlaneChart P A '' S)) :=
    mem_closure_of_tendsto hlim (Filter.Eventually.of_forall (fun n => ⟨w n,hw n,rfl⟩))
  rw [normalizedPolygonHalfPlaneChart_extended_closure P S q A hA] at hcl
  obtain ⟨p,hp,hpInf⟩ := hcl
  have hpη : p = ((η : ℂ) : OnePoint ℂ) := q.val.injective (hpInf.trans hqη.symm)
  have hmem := (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P S (η : ℂ)).mpr
    ⟨Circle.norm_coe η,hpη ▸ hp⟩
  exact ((mem_fuchsianPolygonIdealBoundary P S (η : ℂ)).mp hmem).1


/-- Every actual parabolic fixed point on the genuine ideal boundary is the common
actual endpoint of two distinct genuine polygon sides. -/
theorem IsConvexFuchsianPolygon.parabolic_ideal_isProper
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (f : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (η : Circle) (hη : (η : ℂ) ∈ fuchsianPolygonIdealBoundary P D)
    (hfix : f.val.val ((η : ℂ) : OnePoint ℂ) = ((η : ℂ) : OnePoint ℂ)) :
    IsProperFuchsianInfiniteVertex P D η := by
  obtain ⟨q,hq,hT,hqη⟩ := parabolic_unit_halfPlane_normalizer P f hf (η : ℂ) hfix
  obtain ⟨A,hA⟩ := halfPlane_chart_real_lift q hq
  let ψ := normalizedPolygonHalfPlaneChart P A
  let S := ψ '' D
  let N := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hSimage : S = fordSLNativeHom A '' (P.halfPlaneCoordinate '' D) :=
    normalizedPolygonHalfPlaneChart_image P A D
  have hSo : IsOpen S := ψ.isOpenMap D hD.locallyFinite.fundamental.isOpen
  have hSc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S := hSimage.symm ▸ hD.normalized_hConvex A
  have hInf : (∞ : OnePoint ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) := by
    rw [normalizedPolygonHalfPlaneChart_extended_closure P D q A hA]
    exact ⟨(η : ℂ),((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D _).mp hη).2,hqη⟩
  obtain ⟨k,hk,hgood₀⟩ := hD.locallyFinite.normalized_horocyclic_shrink_to_actual_endpoints q hq A hA hT
  have hgood : ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N →
      (closure S ∩ ((fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)).Nonempty →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) := by
    simpa only [←hSimage] using hgood₀
  have hwidth : ∀ z ∈ S, ∀ w ∈ S, w.re < z.re+1 := by
    intro z hz w hw
    exact hD.normalized_horizontal_width (η : ℂ) hη q A hA hqη hT
      (hSimage ▸ hz) (hSimage ▸ hw)
  obtain ⟨x,hx⟩ := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let Y := max (ψ x).im (k+1)
  have hY : 0 < Y := lt_of_lt_of_le (ψ x).im_pos (le_max_left _ _)
  let z := stripVerticalLift (ψ x) Y hY
  have hz : z ∈ S := open_hConvex_upward_closed hSo hSc hInf (ψ x) ⟨x,hx,rfl⟩ Y (le_max_left _ _) hY
  have hzk : k < z.im := lt_of_lt_of_le (by linarith : k < k+1) (le_max_right _ _)
  obtain ⟨u,v,huf,hvf,huim,hvim,hure,hvre⟩ := open_strip_two_horizontal_frontier hSo hwidth hz
  have hside (w : ℍ) (hw : w ∈ frontier S) (hwk : k < w.im) :
      ∃ T : Set P.domain.carrier, IsFuchsianPolygonSide P D T ∧ w ∈ ψ '' T ∧
        ∀ Z : ℝ, w.im ≤ Z → ∀ hZ : 0 < Z, stripVerticalLift w Z hZ ∈ ψ '' T := by
    have hxf : ψ.symm w ∈ frontier D := by
      have he := ψ.image_frontier D
      rw [←he] at hw
      obtain ⟨y,hy,hey⟩ := hw
      rw [←hey,ψ.symm_apply_apply]
      exact hy
    obtain ⟨T,hT,hwT⟩ := hD.boundary_mem_side hxf
    obtain ⟨g,hgn,heT⟩ := hT.1
    have hpres : (q*g.val*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
      rw [←hq,_root_.LowDimensionalTopology.Geometry.Surfaces.cusp_conjugate_image,P.image_eq g]
    obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
    have hBN : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr
      ⟨g.val,g.property,hB.symm⟩
    have htile : ψ '' T = closure S ∩ ((fun z : ℍ => B • z) '' closure S) := by
      rw [heT]
      exact normalizedPolygonHalfPlaneChart_closed_tile_inter P D q A hA g B hB
    have hwψ : w ∈ ψ '' T := ⟨ψ.symm w,hwT,ψ.apply_symm_apply w⟩
    refine ⟨T,hT,hwψ,?_⟩
    intro Z hwZ hZ
    rw [htile]
    exact cusp_closed_intersection_upward N hSo hSc hInf k hgood B hBN (htile ▸ hwψ) hwk Z hwZ hZ
  obtain ⟨U,hU,huU,hupU⟩ := hside u huf (huim ▸ hzk)
  obtain ⟨V,hV,hvV,hupV⟩ := hside v hvf (hvim ▸ hzk)
  have hUV : U ≠ V := by
    intro heUV
    obtain ⟨L,hL⟩ := normalizedPolygonHalfPlaneChart_side_line hU A
    have hvert : L = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical u.re :=
      halfPlaneLine_eq_vertical_of_upward L u (fun Z huZ hZ => hL (hupU Z huZ hZ))
    have hvL := hL (heUV.symm ▸ hvV)
    rw [hvert] at hvL
    change v.re = u.re at hvL
    linarith
  exact ⟨hη,U,V,hU,hV,hUV,
    normalizedPolygonHalfPlaneChart_side_idealEndpoint P U q A hA η hqη u hupU,
    normalizedPolygonHalfPlaneChart_side_idealEndpoint P V q A hA η hqη v hupV⟩


/-- Every point in the literal original parabolic ideal-boundary cycle is a true proper infinite vertex. -/
theorem IsConvexFuchsianPolygon.parabolic_idealCycle_proper
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (f : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (ξ : OnePoint ℂ) (hfix : f.val.val ξ = ξ) (η : Circle)
    (hη : ((η : ℂ) : OnePoint ℂ) ∈ fuchsianPolygonIdealCycle P D ξ) :
    IsProperFuchsianInfiniteVertex P D η := by
  have hηE : (η : ℂ) ∈ fuchsianPolygonIdealBoundary P D := by
    obtain ⟨u,hu,huη⟩ := hη.1
    exact OnePoint.coe_injective huη ▸ hu
  obtain ⟨g,hgη⟩ := MulAction.mem_orbit_iff.mp hη.2
  let F := g*f*g⁻¹
  have hFE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic F.val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨g.val,rfl⟩)).mp hf
  have hFfix : F.val.val ((η : ℂ) : OnePoint ℂ) = ((η : ℂ) : OnePoint ℂ) := by
    rw [←hgη]
    change g.val.val (f.val.val (g.val.val.symm (g.val.val ξ))) = _
    rw [Equiv.symm_apply_apply,hfix]
    rfl
  exact hD.parabolic_ideal_isProper F hFE η hηE hFfix

/--
In full: every nonidentity ideal fixer is parabolic, no
hyperbolic member fixes that point, and its finite actual cycle consists of proper
infinite vertices of the original genuine convex locally finite polygon.
-/
theorem IsConvexFuchsianPolygon.ideal_fixer_parabolic_no_hyperbolic_fixer_and_finite_proper_cycle
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (f : H) (hfn : f ≠ 1) (η : Circle)
    (hη : (η : ℂ) ∈ fuchsianPolygonIdealBoundary P D)
    (hfix : f.val.val ((η : ℂ) : OnePoint ℂ) = ((η : ℂ) : OnePoint ℂ)) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧
    (∀ g : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val → g.val.val ((η : ℂ) : OnePoint ℂ) ≠ ((η : ℂ) : OnePoint ℂ)) ∧
    (fuchsianPolygonIdealCycle P D (η : ℂ)).Finite ∧
    ∀ p ∈ fuchsianPolygonIdealCycle P D (η : ℂ),
      ∃ u : Circle, ((u : ℂ) : OnePoint ℂ) = p ∧ IsProperFuchsianInfiniteVertex P D u := by
  have hf := hD.nonidentity_ideal_fixer_parabolic f hfn (η : ℂ) hη hfix
  refine ⟨hf,?_,hD.parabolic_idealCycle_finite f hf (η : ℂ) hfix,?_⟩
  · intro g hg hgf
    exact hD.hyperbolic_fixed_not_idealBoundary g hg (η : ℂ) hgf hη
  · intro p hp
    obtain ⟨v,hv,hvp⟩ := hp.1
    have hnorm := ((mem_fuchsianPolygonIdealBoundary P D v).mp hv).2
    let u : Circle := ⟨v,mem_sphere_zero_iff_norm.mpr hnorm⟩
    refine ⟨u,hvp,?_⟩
    apply hD.parabolic_idealCycle_proper f hf (η : ℂ) hfix u
    exact hvp.symm ▸ hp

end LowDimensionalTopology.Geometry.Fuchsian
