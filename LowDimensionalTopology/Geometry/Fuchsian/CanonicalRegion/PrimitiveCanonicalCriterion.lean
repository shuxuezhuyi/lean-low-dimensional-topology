/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
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

/-- The exhaustive actual three-type maximal-canonical-region criterion. -/
theorem FuchsianDisc.primitive_iff_maximalCanonicalRegion
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup) :
    IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ↔ HasMaximalCanonicalRegion D.normalizedGroup A := by
  rcases lt_trichotomy ((Matrix.trace A.val)^2) 4 with he | hp | hh
  · exact D.primitive_elliptic_iff_maximalCanonicalRegion A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA).mpr he) hAH
  · exact D.primitive_parabolic_iff_maximalCanonicalRegion A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff A hA).mpr hp) hAH
  · exact D.primitive_hyperbolic_iff_maximalCanonicalRegion A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr hh) hAH

/-- The actual canonical subset of the original geometric disc, transported by the proved full-domain chart. -/
def FuchsianDisc.canonicalRegion {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) (f : H) :
    Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  (fun z : ℍ=>D.halfPlaneNormalizer⁻¹.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ''
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (D.normalizedLift f)

/-- Actual physical inclusion is exactly inclusion of the genuine normalized canonical regions. -/
theorem FuchsianDisc.canonicalRegion_subset_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f g : H) :
    D.canonicalRegion f⊆D.canonicalRegion g ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (D.normalizedLift f)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (D.normalizedLift g) := by
  apply Set.image_subset_image_iff
  intro z w he
  apply UpperHalfPlane.ext
  exact OnePoint.coe_eq_coe.mp (D.halfPlaneNormalizer⁻¹.val.injective he)

/-- The transported canonical region consists entirely of actual points of the original invariant disc. -/
theorem FuchsianDisc.canonicalRegion_subset_carrier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) : D.canonicalRegion f⊆D.carrier := by
  rintro _ ⟨z,_hz,rfl⟩
  have hm : ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈D.halfPlaneNormalizer.val '' D.carrier := by
    rw [D.halfPlaneNormalizer_image]
    exact ⟨(z:ℂ),z.im_pos,rfl⟩
  obtain ⟨w,hw,he⟩:=hm
  have heq : w=D.halfPlaneNormalizer⁻¹.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    apply D.halfPlaneNormalizer.val.injective
    change D.halfPlaneNormalizer.val w=D.halfPlaneNormalizer•(D.halfPlaneNormalizer⁻¹•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    rw [smul_inv_smul]
    exact he
  change D.halfPlaneNormalizer⁻¹.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈D.carrier
  rw [←heq]
  exact hw

/-- Any actual whole-disc normalizer and either real lift give the same physical canonical subset. -/
theorem FuchsianDisc.canonicalRegion_eq_image_of_normalizer
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (f : H)
    (Q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hQ : Q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=Q*f.val*Q⁻¹) :
    D.canonicalRegion f=(fun z : ℍ=>Q⁻¹.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B := by
  let q:=D.halfPlaneNormalizer
  have hpres : (Q*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    conv_lhs => rw [←D.halfPlaneNormalizer_image,image_image]
    calc
      (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>(Q*q⁻¹).val (q.val z)) '' D.carrier=Q.val '' D.carrier := by
        congr 1
        funext z
        change (Q*q⁻¹)•(q•z)=Q•z
        simp only [mul_smul,inv_smul_smul]
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=hQ
  obtain ⟨R,hR⟩:=mobius_preserves_halfPlane_exists_SL (Q*q⁻¹) hpres
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (R*D.normalizedLift f*R⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B := by
    rw [map_mul,map_mul,map_inv,D.normalizedLift_spec,hR,hB]
    change (Q*q⁻¹)*(q*f.val*q⁻¹)*(Q*q⁻¹)⁻¹=Q*f.val*Q⁻¹
    group
  have hcan:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr (R*D.normalizedLift f*R⁻¹) B hproj
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion,←hcan,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation,image_image]
  congr 1
  funext z
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
  change q⁻¹•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=Q⁻¹•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
  rw [hR,mul_smul,inv_smul_smul]

/-- Maximality is stated in the original group, for every genuine fixed point and every nonidentity stabilizer element. -/
def FuchsianDisc.CanonicalRegionMaximal {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) : Prop :=
  ∀p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,f.val.val p=p →
    ∀g : H,g.val.val p=p → g.val≠1 → D.canonicalRegion g⊆D.canonicalRegion f

/-- The original all-stabilizer comparison and the full normalized SL comparison are equivalent. -/
theorem FuchsianDisc.canonicalRegionMaximal_iff_normalized {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) :
    D.CanonicalRegionMaximal f ↔ HasMaximalCanonicalRegion D.normalizedGroup (D.normalizedLift f) := by
  let Q:=D.halfPlaneNormalizer
  constructor
  · intro h p hp B hBH hBp hB0
    obtain ⟨g,hg,hQg⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
      Q H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)).mp hBH
    let gH : H:=⟨g,hg⟩
    have hfp : f.val.val (Q⁻¹.val p)=Q⁻¹.val p := by
      rw [D.normalizedLift_spec] at hp
      exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff f.val Q p).mp hp
    have hgp : g.val (Q⁻¹.val p)=Q⁻¹.val p := by
      rw [←hQg] at hBp
      exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff g Q p).mp hBp
    have hg0 : g≠1 := by
      intro he
      apply hB0
      rw [he] at hQg
      simpa only [mul_one,mul_inv_cancel] using hQg.symm
    have hs := (D.canonicalRegion_subset_iff gH f).mp (h (Q⁻¹.val p) hfp gH hgp hg0)
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (D.normalizedLift gH) := by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr
      exact hQg.symm.trans (D.normalizedLift_spec gH).symm
    rwa [he]
  · intro h p hp g hgp hg0
    apply (D.canonicalRegion_subset_iff g f).mpr
    have hAf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)).val (Q.val p)=Q.val p := by
      rw [D.normalizedLift_spec]
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint f.val Q p hp
    have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)∈D.normalizedGroup := by
      rw [D.normalizedLift_spec]
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
        _).mpr ⟨g.val,g.property,rfl⟩
    have hBg : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)).val (Q.val p)=Q.val p := by
      rw [D.normalizedLift_spec]
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint g.val Q p hgp
    have hB0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)≠1 := by
      intro he
      rw [D.normalizedLift_spec] at he
      apply hg0
      have hh:=congrArg (fun k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>Q⁻¹*k*Q) he
      simpa only [Q,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh
    exact h (Q.val p) hAf (D.normalizedLift g) hBH hBg hB0

/-- For the entire original Fuchsian group and actual canonical subsets of its physical disc. -/
theorem FuchsianDisc.primitive_iff_canonicalRegionMaximal {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : f.val≠1) :
    IsPrimitive H f.val ↔ D.CanonicalRegionMaximal f := by
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)∈D.normalizedGroup := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨f.val,f.property,rfl⟩
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)≠1 := by
    intro he
    rw [D.normalizedLift_spec] at he
    apply hf
    have hh:=congrArg (fun k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>D.halfPlaneNormalizer⁻¹*k*D.halfPlaneNormalizer) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh
  rw [D.canonicalRegionMaximal_iff_normalized,←D.primitive_iff_maximalCanonicalRegion _ hn hmem,
    D.normalizedLift_spec]
  exact (isPrimitive_conjugation_iff H f.val D.halfPlaneNormalizer).symm

end LowDimensionalTopology.Geometry.Fuchsian
