/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSidePairing
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual unit translation sends each high left boundary point to the right boundary. -/
theorem HalfPlaneFuchsianGroup.unitTranslation_probe {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ H)
    (t : ℝ) (ht : 0 < t) :
    letI := P.nativeAction
    (⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1,hT⟩ : H) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht = _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 1 t ht := by
  let parabolicSideHalfPlaneAction := P.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←P.nativeAction_boundary]
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
    1).val (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht : ℍ) : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
  congr 1
  apply Complex.ext <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]

/-- Every high right boundary point lies in both genuine closed Ford-strip tiles. -/
theorem parabolicFord_right_ray_mem_intersection {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ H)
    (t : ℝ) (ht : 1 ≤ t) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 1 t (by linarith) ∈ closure (parabolicFordDomain H) ∩
      ((⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1,hT⟩ : H) • closure (parabolicFordDomain H)) := by
  let parabolicSideHalfPlaneAction := P.nativeAction
  have hc := parabolicFord_high_closed_strip_subset H P.discrete hT
  refine ⟨hc (by change 0 ≤ (1:ℝ) ∧ (1:ℝ) ≤ 1 ∧ 1 ≤ t;exact ⟨by norm_num,le_rfl,ht⟩),?_⟩
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t (by linarith),hc ?_,P.unitTranslation_probe hT t (by linarith)⟩
  change 0 ≤ (0:ℝ) ∧ (0:ℝ) ≤ 1 ∧ 1 ≤ t
  exact ⟨le_rfl,by norm_num,ht⟩

/-- Two distinct points on the actual common ray witness positive side length. -/
theorem parabolicFord_closed_intersection_nontrivial {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈
      H) :
    letI := P.nativeAction
    (closure (parabolicFordDomain H) ∩
      ((⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1,hT⟩ : H) • closure (parabolicFordDomain H))).Nontrivial := by
  let parabolicSideHalfPlaneAction := P.nativeAction
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 1 1
    zero_lt_one,parabolicFord_right_ray_mem_intersection P hT 1 le_rfl,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 1 2 (by norm_num),parabolicFord_right_ray_mem_intersection P hT 2 (by norm_num),?_⟩
  intro he
  have hh := congrArg UpperHalfPlane.im he
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hh

/-- A native positive-length tile intersection is the same actual disc tile intersection. -/
theorem HalfPlaneFuchsianGroup.cayley_intersection_nontrivial {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (S : Set ℍ) (g : H) :
    letI := P.nativeAction
    (closure S ∩ (g • closure S)).Nontrivial →
      (closure (P.cayleyCoordinate '' S) ∩
        fuchsianDomainTile P.cayleyData (P.cayleyCoordinate '' S)
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H g)).Nontrivial := by
  let parabolicSideHalfPlaneAction := P.nativeAction
  rintro ⟨x,hx,y,hy,hxy⟩
  have hm {z : ℍ} (hz : z ∈ closure S ∩ (g • closure S)) :
      P.cayleyCoordinate z ∈ closure (P.cayleyCoordinate '' S) ∩
        fuchsianDomainTile P.cayleyData (P.cayleyCoordinate '' S)
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H g) := by
    refine ⟨?_,?_⟩
    · rw [←P.cayleyCoordinate.image_closure]
      exact mem_image_of_mem _ hz.1
    · obtain ⟨w,hw,hgw⟩ := hz.2
      refine ⟨P.cayleyCoordinate w,?_,?_⟩
      · rw [←P.cayleyCoordinate.image_closure]
        exact mem_image_of_mem _ hw
      · exact (P.cayleyCoordinate_equivariant g w).symm.trans (congrArg P.cayleyCoordinate hgw)
  exact ⟨P.cayleyCoordinate x,hm hx,P.cayleyCoordinate y,hm hy,P.cayleyCoordinate.injective.ne hxy⟩

/-- A primitive parabolic pairs two sides of a genuine original-group convex fundamental polygon. -/
theorem primitive_unitTranslation_side_pairing {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    ∃ s : FuchsianPolygonSides P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H),
      fuchsianSideElement (primitive_unitTranslation_Ford_polygon P hprim) s =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1,hprim.mem⟩ := by
  let hPoly := primitive_unitTranslation_Ford_polygon P hprim
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1,hprim.mem⟩
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  have hg : g ≠ 1 := by
    intro he
    have hh := congrArg Subtype.val he
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr
      one_ne_zero).1 hh
  have heg : e g ≠ 1 := by
    intro he
    exact hg (e.injective (he.trans (map_one e).symm))
  have hn := P.cayley_intersection_nontrivial (parabolicFordDomain H) g
    (parabolicFord_closed_intersection_nontrivial P hprim.mem)
  let s : FuchsianPolygonSides P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H) :=
    ⟨_,hPoly.side_of_nontrivial_intersection heg hn⟩
  refine ⟨s,?_⟩
  exact (hPoly.existsUnique_side_element s.property).choose_spec.2 (e g) ⟨heg,rfl⟩ |>.symm

end LowDimensionalTopology.Geometry.Fuchsian
