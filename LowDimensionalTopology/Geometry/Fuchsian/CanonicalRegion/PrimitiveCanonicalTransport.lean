/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Generation of every genuine fixed-point stabilizer is independent of the geometric chart. -/
theorem generatesFixedStabilizers_conjugation_iff
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    GeneratesFixedStabilizers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      H) (q*f*q⁻¹) ↔
      GeneratesFixedStabilizers H f := by
  have hpow : Subgroup.zpowers (q*f*q⁻¹)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.zpowers f) := by
    exact (MonoidHom.map_zpowers (MulAut.conj q).toMonoidHom f).symm
  constructor
  · intro h p hp
    have hgen := h (q.val p) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint f q p
      hp)
    rw [hpow,primitive_boundaryStabilizer_conjugation] at hgen
    exact Subgroup.map_injective (MulAut.conj q).injective hgen
  · intro h p hp
    obtain ⟨p,rfl⟩ := q.val.surjective p
    have hp' : f.val p=p := by
      apply q.val.injective
      change q•(f•p)=q•p
      change (q*f*q⁻¹)•(q•p)=q•p at hp
      simpa only [mul_smul,inv_smul_smul] using hp
    rw [hpow,primitive_boundaryStabilizer_conjugation]
    exact congrArg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q) (h p hp')

/-- The least positive elliptic angle condition is invariant under genuine conjugacy. -/
theorem hasLeastEllipticRotation_isConj {f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (hc :
  IsConj f g) :
    HasLeastEllipticRotation f ↔ HasLeastEllipticRotation g := by
  constructor
  · rintro ⟨n,hn,k,hk,he⟩
    exact ⟨n,hn,k,hc.symm.trans hk,he⟩
  · rintro ⟨n,hn,k,hk,he⟩
    exact ⟨n,hn,k,hc.trans hk,he⟩

/-- Primitivity is unchanged by simultaneous actual group and domain conjugation. -/
theorem isPrimitive_conjugation_iff (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (f q
  : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    IsPrimitive (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q*f*q⁻¹) ↔ IsPrimitive H f := by
  have hc : IsConj f (q*f*q⁻¹) := isConj_iff.mpr ⟨q,rfl⟩
  have hmem : q*f*q⁻¹∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ↔ f∈H := by
    constructor
    · intro h
      obtain ⟨g,hg,he⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mp h
      have hgf : g=f := (MulAut.conj q).injective he
      rwa [hgf] at hg
    · intro h
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
        _).mpr ⟨f,h,rfl⟩
  simp only [IsPrimitive,hmem,generatesFixedStabilizers_conjugation_iff,
    ←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj hc,←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_isConj hc,←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj hc,
    ←hasLeastEllipticRotation_isConj hc]

/-- The chosen actual lift of an original group element after the proved whole-disc normalization. -/
def FuchsianDisc.normalizedLift {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) (f : H) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  Classical.choose (D.normalizedGroup_exists_realSL
    (D.halfPlaneNormalizer*f.val*D.halfPlaneNormalizer⁻¹)
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _ _).mpr
      ⟨f.val,f.property,rfl⟩))

theorem FuchsianDisc.normalizedLift_spec {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift
      f)=D.halfPlaneNormalizer*f.val*D.halfPlaneNormalizer⁻¹ :=
  Classical.choose_spec (D.normalizedGroup_exists_realSL
    (D.halfPlaneNormalizer*f.val*D.halfPlaneNormalizer⁻¹)
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _ _).mpr
      ⟨f.val,f.property,rfl⟩))

/-- The parabolic maximality criterion holds for an original element of every actual Fuchsian disc. -/
theorem FuchsianDisc.primitive_parabolic_iff_normalized_maximal
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (f : H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) :
    IsPrimitive H f.val ↔ HasMaximalCanonicalRegion D.normalizedGroup (D.normalizedLift f) := by
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨D.halfPlaneNormalizer,rfl⟩)).mp hf
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)∈D.normalizedGroup := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨f.val,f.property,rfl⟩
  rw [←D.primitive_parabolic_iff_maximalCanonicalRegion _ hp hm,D.normalizedLift_spec]
  exact (isPrimitive_conjugation_iff H f.val D.halfPlaneNormalizer).symm

/-- The hyperbolic maximality criterion likewise holds for the whole original physical disc group. -/
theorem FuchsianDisc.primitive_hyperbolic_iff_normalized_maximal
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (f : H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) :
    IsPrimitive H f.val ↔ HasMaximalCanonicalRegion D.normalizedGroup (D.normalizedLift f) := by
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_isConj (isConj_iff.mpr
      ⟨D.halfPlaneNormalizer,rfl⟩)).mp hf
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)∈D.normalizedGroup := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨f.val,f.property,rfl⟩
  rw [←D.primitive_hyperbolic_iff_maximalCanonicalRegion _ hp hm,D.normalizedLift_spec]
  exact (isPrimitive_conjugation_iff H f.val D.halfPlaneNormalizer).symm

end LowDimensionalTopology.Geometry.Fuchsian
