/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalCylinderCoordinates
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalCriterion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSideNormalizers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Full original set stabilizers transform under actual simultaneous
conjugation of the original group and the original geometric region. -/
theorem canonical_setStabilizer_conjugation (H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (S:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H S)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val '' S) := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩
    refine ⟨⟨f,hf.1,rfl⟩,?_⟩
    change (q*f*q⁻¹).val '' (q.val '' S)=q.val '' S
    have hfS:f.val '' S=S:=hf.2
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,hfS]
  · rintro ⟨hg,hgS⟩
    obtain ⟨f,hf,rfl⟩:=hg
    refine ⟨f,⟨hf,?_⟩,rfl⟩
    apply q.val.injective.image_injective
    change q.val '' (f.val '' S)=q.val '' S
    change (q*f*q⁻¹).val '' (q.val '' S)=q.val '' S at hgS
    rwa [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image] at hgS

/-- The original-disc canonical region has exactly its genuine native
canonical image under the already constructed whole-disc normalizer. -/
theorem FuchsianDisc.canonicalRegion_normalized_image {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) :
    D.halfPlaneNormalizer.val '' D.canonicalRegion f=nativeCanonicalSphere (D.normalizedLift f) := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion,image_image]
  change (fun z:ℍ=>D.halfPlaneNormalizer•(D.halfPlaneNormalizer⁻¹•_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)) ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (D.normalizedLift
        f)=nativeCanonicalSphere (D.normalizedLift f)
  simp only [smul_inv_smul]
  rfl

/-- Original simplicity survives the constructed whole-disc normalization. -/
theorem FuchsianDisc.canonical_normalized_simple {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hs:IsSimple H f.val) :
    IsSimple D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)) := by
  rw [D.normalizedLift_spec]
  exact hs.conjugate D.halfPlaneNormalizer

/-- Genuine canonical collar stability in every original geometric
invariant disc, proved via its actual constructed full-domain chart. -/
theorem FuchsianDisc.canonicalRegion_simple_stable {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H) (hs:IsSimple H
      f.val) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H (D.canonicalRegion f) := by
  have hEn:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree D.normalizedGroup:=hE.conjugation D.halfPlaneNormalizer
  have hn:=nativeCanonicalSphere_simple_stable (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.normalizedHalfPlaneData D) hEn
    (D.normalizedLift f) (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f
      hs)
  rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D] at hn
  exact (mobiusStableSet_conjugation H (D.canonicalRegion f) D.halfPlaneNormalizer).mp hn

/-- The original actual canonical collar is open in the original sphere. -/
theorem FuchsianDisc.canonicalRegion_simple_isOpen {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hs:IsSimple H f.val) : IsOpen (D.canonicalRegion f) := by
  have hsN:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hs
  have ht:Matrix.trace (D.normalizedLift f).val≠0:=by
    intro he
    have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hsN.2.1.1.1).mp hsN.2.1
    rw [he] at hh
    norm_num at hh
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion]
  have ho:IsOpen (D.halfPlaneNormalizer⁻¹.val ''
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ''
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (D.normalizedLift f))):=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph D.halfPlaneNormalizer⁻¹).isOpenMap _
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.isOpenMap _
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_isOpen _ ht))
  simpa only [Set.image_image,_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint] using ho

/-- The actual canonical collar stable subset in the original arbitrary
geometric invariant disc and its original quotient surface. -/
def FuchsianDisc.canonicalCollar {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H) (hs:IsSimple H
      f.val) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain where
  carrier:=D.canonicalRegion f
  subset_domain:=D.canonicalRegion_subset_carrier f
  stable:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_simple_stable D hE f hs


/-- The genuine canonical collar in every original geometric invariant
disc is actually a circle times an open interval in the same original
whole-group quotient surface. -/
theorem FuchsianDisc.canonicalCollar_image_circle_product {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H) (hs:IsSimple H
      f.val) :
    ∃b:ℝ,0<b ∧ Nonempty ((_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCollar D hE f hs).quotientImage ≃ₜ Circle×Ioo (-b) b) := by
  let q:=D.halfPlaneNormalizer
  let S:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCollar D hE f hs
  let P:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.normalizedHalfPlaneData D
  have hEn:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree D.normalizedGroup:=hE.conjugation q
  have hsN:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hs
  let T:=canonicalCollarSubset P hEn (D.normalizedLift f) hsN
  have hS:q.val '' S.carrier=T.carrier:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D f
  have hK:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer=T.stabilizer:=by
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H (D.canonicalRegion f))=
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer D.normalizedGroup (nativeCanonicalSphere
        (D.normalizedLift f))
    dsimp only [q]
    rw [canonical_setStabilizer_conjugation,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D f]
    rfl
  have E:S.Quotient ≃ₜ T.Quotient:=by
    have E:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisConjugateQuotientHomeomorph S.stabilizer S.carrier q
    rw [hK,hS] at E
    exact E
  have ho:IsOpen (Subtype.val ⁻¹' S.carrier:Set D.domain.carrier):=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_simple_isOpen D f
      hs).preimage continuous_subtype_val
  have hT:IsOpen (Subtype.val ⁻¹' T.carrier:Set P.asFuchsianDisc.domain.carrier):=
    (canonicalCollarSubset_isOpen P hEn (D.normalizedLift f) hsN).preimage continuous_subtype_val
  obtain ⟨b,hb,⟨F⟩⟩:=canonicalCollarSubset_image_circle_product P hEn (D.normalizedLift f) hsN
  exact ⟨b,hb,⟨((S.openQuotientHomeomorph ho).symm.trans E).trans
    ((T.openQuotientHomeomorph hT).trans F)⟩⟩

/-- Every actual whole-disc normalizer transports the original
canonical region to the canonical region of its genuine real lift. -/
theorem FuchsianDisc.canonicalRegion_image_of_normalizer {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq:q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=q*f.val*q⁻¹) :
    q.val '' D.canonicalRegion f=nativeCanonicalSphere B := by
  rw [D.canonicalRegion_eq_image_of_normalizer f q hq B hB,image_image]
  change (fun z:ℍ=>q•(q⁻¹•_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
    z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B=nativeCanonicalSphere B
  simp only [smul_inv_smul]
  rfl

/-- A genuine original primitive parabolic cusp has a simultaneous
actual whole-disc normalization to the unit-period canonical horodisc.
The original group, generator, region and complete period are retained. -/
theorem FuchsianDisc.canonical_primitive_cusp_normalizer {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (hp:IsPrimitive H
      f.val) :
    ∃q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃_P:HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H),
      IsPrimitive (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
        H) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) ∧
      q.val '' D.canonicalRegion f=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2) := by
  let A:=D.normalizedLift f
  have hAf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨D.halfPlaneNormalizer,rfl⟩)).mp hf
  obtain ⟨s,hsH,hsA⟩:=realSL_parabolic_unit_normalizer A hAf
  let q:=s*D.halfPlaneNormalizer
  have hqD:q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change (fun z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>s.val (D.halfPlaneNormalizer.val
      z)) '' D.carrier=_
    rw [←image_image,D.halfPlaneNormalizer_image,hsH]
  have hDq:(D.nielsenConjugate q).carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier]
    exact hqD
  let P:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc (D.nielsenConjugate
    q) hDq
  have hproj:q*f.val*q⁻¹=s*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*s⁻¹:=by
    rw [D.normalizedLift_spec]
    dsimp only [q]
    group
  have hpn:IsPrimitive (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
    H) (q*f.val*q⁻¹):=
    (isPrimitive_conjugation_iff H f.val q).mpr hp
  have hTpar:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1):=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero
  have hex:∃hpT:IsPrimitive (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
    H) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1),
      ∃B:Matrix.SpecialLinearGroup (Fin
        2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=q*f.val*q⁻¹ ∧
        nativeCanonicalSphere B=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2):=by
    rcases hsA with he|he
    · have heq:q*f.val*q⁻¹=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1:=hproj.trans he
      refine ⟨heq ▸ hpn,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
        1,?_,canonical_unit_cusp_sphere⟩
      rw [heq,realSLMobius_unitTranslation]
    · have heq:q*f.val*q⁻¹=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹:=hproj.trans he
      have hpInv:IsPrimitive (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
        H) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹:=heq ▸ hpn
      have hpT:IsPrimitive (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1):=by
        have hh:=sidePairing_primitive_parabolic_inverse (sidePairing_parabolic_inverse hTpar) hpInv
        simpa only [inv_inv] using hh
      refine ⟨hpT,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)⁻¹,?_,?_⟩
      · rw [heq,map_inv,realSLMobius_unitTranslation]
      · rw [nativeCanonicalSphere,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_inverse]
        exact canonical_unit_cusp_sphere
  obtain ⟨hpT,B,hB,hC⟩:=hex
  refine ⟨q,P,hpT,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_image_of_normalizer D f q hqD B hB]
  exact hC

/-- Every original primitive parabolic canonical region is a stable
set for the original whole group, with stability derived from the
actual normalized cusp separation. -/
theorem FuchsianDisc.canonicalRegion_primitive_parabolic_stable {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (hp:IsPrimitive H f.val) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H (D.canonicalRegion f) := by
  obtain ⟨q,P,hpT,hS⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_primitive_cusp_normalizer D f hf hp
  have hn:=canonical_unit_cusp_stable P (hE.conjugation q) hpT
  rw [←hS] at hn
  exact (mobiusStableSet_conjugation H (D.canonicalRegion f) q).mp hn

/-- The genuine original primitive parabolic canonical region is open. -/
theorem FuchsianDisc.canonicalRegion_primitive_parabolic_isOpen {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (hp:IsPrimitive H
      f.val) :
    IsOpen (D.canonicalRegion f) := by
  obtain ⟨q,_P,_hpT,hS⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_primitive_cusp_normalizer D f hf hp
  have he:q.val ⁻¹' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)=D.canonicalRegion f:=by
    rw [←hS,Set.preimage_image_eq _ q.val.injective]
  rw [←he]
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isOpen
    (1/2)).preimage (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).continuous

/-- The actual primitive cusp in the original arbitrary geometric
invariant disc and its original whole-group quotient surface. -/
def FuchsianDisc.canonicalCusp {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (hp:IsPrimitive H
      f.val) : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain where
  carrier:=D.canonicalRegion f
  subset_domain:=D.canonicalRegion_subset_carrier f
  stable:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_primitive_parabolic_stable D hE f hf hp

/-- The actual primitive cusp in every original geometric invariant
disc has the genuine punctured-disc topology in the same original
whole-group quotient; its full actual set stabilizer is cyclic. -/
theorem FuchsianDisc.canonicalCusp_image_puncturedDisc {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (hp:IsPrimitive H f.val) :
    IsOpen ((_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp D hE f hf hp).quotientImage :Set
      (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain)) ∧
      IsCyclic (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp D hE f hf hp).stabilizer ∧
      Nonempty ((_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp D hE f hf hp).quotientImage ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspPuncturedDisc (1/2)) := by
  obtain ⟨q,P,hpT,hS⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_primitive_cusp_normalizer D f hf hp
  let S:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp D hE f hf hp
  let T:=canonicalCuspSubset P (hE.conjugation q) hpT
  have hST:q.val '' S.carrier=T.carrier:=hS
  have hK:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer=T.stabilizer:=by
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H (D.canonicalRegion f))=
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2))
    rw [canonical_setStabilizer_conjugation,hS]
  have hSo:IsOpen S.carrier:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_primitive_parabolic_isOpen D f hf hp
  have hSpre:IsOpen (Subtype.val ⁻¹' S.carrier:Set D.domain.carrier):=
    hSo.preimage continuous_subtype_val
  have hTpre:IsOpen (Subtype.val ⁻¹' T.carrier:Set P.asFuchsianDisc.domain.carrier):=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isOpen (1/2)).preimage continuous_subtype_val
  have E:S.Quotient ≃ₜ T.Quotient:=by
    have E:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisConjugateQuotientHomeomorph S.stabilizer S.carrier q
    rw [hK,hST] at E
    exact E
  have hcT:IsCyclic T.stabilizer:=by
    rw [canonicalCuspSubset_stabilizer]
    change IsCyclic (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1))
    infer_instance
  have hcS:IsCyclic S.stabilizer:=by
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      S.stabilizer).isCyclic.mpr
    rwa [hK]
  refine ⟨S.quotientImage_isOpen hSo,hcS,⟨?_⟩⟩
  exact (((S.openQuotientHomeomorph hSpre).symm.trans E).trans
    (T.openQuotientHomeomorph hTpre)).trans (canonicalCuspImageHomeomorph P (hE.conjugation q) hpT)

end LowDimensionalTopology.Geometry.Fuchsian
