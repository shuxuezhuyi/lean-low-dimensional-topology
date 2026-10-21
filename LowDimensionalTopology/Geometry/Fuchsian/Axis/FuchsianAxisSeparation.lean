/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleHyperbolicAxisSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.FuchsianCrossingHalfTurns
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

-- BEGIN ORIGINAL DISC WRAPPERS
/-- Genuine hyperbolic separation is the infimum of actual pair distances on the
entire original disc; the two subsets are not replaced by chosen representative points. -/
def FuchsianDisc.setSeparation {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (S T : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : ℝ :=
  sInf {r : ℝ | ∃ x : (fuchsianGeometricDomain D).carrier, x.val ∈ S ∧
    ∃ y : (fuchsianGeometricDomain
      D).carrier, y.val ∈ T ∧ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x y = r}

/-- The actual original pair-distance infimum equals the genuine native line distance
when the whole-domain coordinate identifies the two complete sets. -/
theorem FuchsianDisc.setSeparation_eq_native_lines
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (S T : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hS : ∀ x : (fuchsianGeometricDomain D).carrier,
      x.val ∈ S ↔ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x ∈ L.carrier)
    (hT : ∀ x : (fuchsianGeometricDomain D).carrier,
      x.val ∈ T ↔ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x ∈ M.carrier) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.setSeparation D S T = L.lineDist M := by
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hr⟩
    exact ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x, (hS x).mp hx,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D y, (hT y).mp hy, hr.symm⟩
  · rintro ⟨x, hx, y, hy, hr⟩
    let p := (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).symm x
    let q := (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).symm y
    have hp : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D p = x :=
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).apply_symm_apply x
    have hq : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D q = y :=
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).apply_symm_apply y
    refine ⟨p, (hS p).mpr (hp.symm ▸ hx), q, (hT q).mpr (hq.symm ▸ hy), ?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist, hp, hq]
    exact hr.symm

/-- Complete membership in an actual original axis is equivalent to membership
in its constructed native axis, in both directions. -/
theorem FuchsianAxisModel.hyperbolicCoordinate_mem_iff
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : FuchsianDisc H} {f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f) (x : (fuchsianGeometricDomain D).carrier) :
    x.val ∈ M.carrier ↔ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x ∈ M.line.carrier := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem M x, ?_⟩
  intro hx
  change x.val ∈ D.halfPlaneNormalizer⁻¹.val '' M.nativeCarrier
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x), ⟨_, hx, rfl⟩, ?_⟩
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x) =
      D.halfPlaneNormalizer.val x.val := geometricHalfPlaneChart_extended D _ _ x
  rw [he]
  exact D.halfPlaneNormalizer.val.symm_apply_apply x.val

/-- The entire original translated axis has exactly the whole native translated carrier. -/
theorem FuchsianAxisModel.translated_hyperbolicCoordinate_mem_iff
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : FuchsianDisc H} {f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f) (g : H) (x : (fuchsianGeometricDomain D).carrier) :
    x.val ∈ g.val.val '' M.carrier ↔ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x ∈
      (M.line.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ (D.normalizedLift g))).carrier := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  change x.val ∈ g.val.val '' M.carrier ↔ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x ∈
    (fun y : ℍ => D.normalizedLift g • y) '' M.line.carrier
  constructor
  · rintro ⟨y, hy, he⟩
    let p : (fuchsianGeometricDomain D).carrier := ⟨y, M.carrier_subset_domain hy⟩
    have hx : g • p = x := Subtype.ext he
    refine ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D p,
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem_iff M p).mp hy, ?_⟩
    change D.normalizedLift g • _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D p = _
    rw [← _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate_action, hx]
  · rintro ⟨y, hy, he⟩
    let p := (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).symm y
    have hp : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D p = y :=
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).apply_symm_apply y
    have hpx : g • p = x := (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).injective (by
      rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate_action, hp]
      exact he)
    refine ⟨p.val, (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem_iff M
      p).mpr (hp.symm ▸ hy), ?_⟩
    exact congrArg Subtype.val hpx

/-- The actual one-half collar estimate on the original geometric invariant disc,
using genuine whole-axis pair distances and the genuine whole-disc translation infimum. -/
theorem fuchsian_simple_axis_collar
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (f g : H)
    (M : FuchsianAxisModel D f.val) (hs : IsSimple H f.val)
    (hne : M.carrier ≠ g.val.val '' M.carrier) :
    (1 : ℝ) / 2 ≤ Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f / 2) *
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.setSeparation D M.carrier (g.val.val '' M.carrier) / 2) := by
  let P : HalfPlaneFuchsianGroup D.normalizedGroup :=
    ⟨fun u => D.normalizedGroup_preserves_halfPlane u.val u.property, D.normalizedGroup_discrete⟩
  let F := D.normalizedLift g
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F ∈ D.normalizedGroup := by
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F =
      D.halfPlaneNormalizer*g.val*D.halfPlaneNormalizer⁻¹ from
      D.normalizedLift_spec g]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨g.val, g.property, rfl⟩
  have hsN : IsSimple D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix) := by
    rw [M.projection]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation H f.val D.halfPlaneNormalizer).mpr hs
  have hImage : D.halfPlaneNormalizer.val '' (g.val.val '' M.carrier) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (M.line.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)).carrier := by
    rw [← _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image, ← D.normalizedLift_spec g,
      M.carrier_image]
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.nativeCarrier,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_image_realSL,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hneN : M.line ≠ M.line.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F) := by
    intro he
    apply hne
    apply D.halfPlaneNormalizer.val.injective.image_injective
    rw [M.carrier_image, hImage, ← he]
    rfl
  have hdist := _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.setSeparation_eq_native_lines D M.carrier (g.val.val '' M.carrier)
    M.line (M.line.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F))
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem_iff M)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translated_hyperbolicCoordinate_mem_iff M g)
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f M, hdist]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_hyperbolic_axis_collar P M.matrix M.nontrivial
    M.trace_gt hsN F hF hneN

/-- The original-disc simple-axis collar alternative, with the actual axis model
constructed from the given original simple hyperbolic element. -/
theorem simple_hyperbolic_axis_image_eq_or_half_le_sinh_length_gap_product
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (f g : H)
    (hs : IsSimple H f.val) :
    let M := _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hs.2.1
    M.carrier = g.val.val '' M.carrier ∨
      (1 : ℝ) / 2 ≤ Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f / 2) *
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.setSeparation D M.carrier (g.val.val '' M.carrier) / 2) := by
  classical
  let M := _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hs.2.1
  by_cases he : M.carrier = g.val.val '' M.carrier
  · exact Or.inl he
  · exact Or.inr (fuchsian_simple_axis_collar D f g M hs he)

-- END ORIGINAL DISC WRAPPERS

end LowDimensionalTopology.Geometry.Fuchsian
