/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSurfaceRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicHyperbolicSeparation
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

/-- Actual full-group quotient images are disjoint exactly when all
original group translates of the actual subsets are disjoint. -/
theorem canonical_quotient_images_disjoint_iff {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H) (S T:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hS:S⊆D.carrier) (hT:T⊆D.carrier) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D S
      hS) (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D T hT) ↔
      ∀g∈H,Disjoint (g.val '' S) T := by
  constructor
  · intro hd g hg
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    let X:S:=⟨x,hx⟩
    let Y:T:=⟨g.val x,hz⟩
    have he:_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D T hT Y=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D S hS X:=by
      apply _root_.Quotient.sound
      exact ⟨⟨g,hg⟩,rfl⟩
    exact Set.disjoint_left.mp hd ⟨X,he.symm⟩ ⟨Y,rfl⟩
  · intro hd
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx⟩ ⟨y,hy⟩
    obtain ⟨g,hg⟩:=_root_.Quotient.exact (hy.trans hx.symm)
    have hxy:g.val.val x.val=y.val:=congrArg Subtype.val hg
    exact Set.disjoint_left.mp (hd g.val g.property) ⟨x.val,x.property,hxy⟩ y.property

/-- Every genuine native canonical region lies in the original native half-plane. -/
theorem nativeCanonicalSphere_subset_domain {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    nativeCanonicalSphere A⊆P.asFuchsianDisc.domain.carrier := by
  rintro _ ⟨z,_hz,rfl⟩
  exact ⟨(z:ℂ),z.im_pos,rfl⟩

/-- The genuine image of any native canonical region in the original
entire-group quotient surface. -/
def nativeCanonicalQuotientImage {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Set (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage P.asFuchsianDisc.domain (nativeCanonicalSphere
    A)
    (nativeCanonicalSphere_subset_domain P A)

/-- The actual canonical regions of two original parabolic end-orbits
have disjoint images in the original whole-group surface. The premise
is precisely distinctness of those end-orbits, not region separation. -/
theorem native_parabolic_canonical_quotient_disjoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (p q:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p) (hq:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val q=q)
    (horbit:∀g∈H,g.val p≠q) :
    Disjoint (nativeCanonicalQuotientImage P A) (nativeCanonicalQuotientImage P B) := by
  apply (canonical_quotient_images_disjoint_iff _ _ _ _ _).mpr
  intro g hg
  obtain ⟨C,hC⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
  rw [←hC,←nativeCanonicalSphere_conjugation]
  have hPar:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C*A*C⁻¹)):=by
    simp only [map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C,rfl⟩)).mp hA
  have hmem:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C*A*C⁻¹)∈H:=by
    simp only [map_mul,map_inv]
    rw [hC]
    exact H.mul_mem (H.mul_mem hg hAm) (H.inv_mem hg)
  have hfix:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C*A*C⁻¹)).val (g.val p)=g.val p:=by
    simp only [map_mul,map_inv]
    rw [hC]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) g p hp
  have hd:=canonical_parabolic_regions_disjoint_fixed_points H
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet,_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc,P.preserves⟩ hE
    (C*A*C⁻¹) B hmem hBm hPar hB (g.val p) q hfix hq (horbit g hg)
  exact (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective).mpr hd

/-- Every original simple-hyperbolic canonical collar is disjoint from
all original parabolic cusp images in the actual entire-group surface. -/
theorem native_cusp_collar_quotient_disjoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hsB:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Disjoint (nativeCanonicalQuotientImage P A) (nativeCanonicalQuotientImage P B) := by
  apply (canonical_quotient_images_disjoint_iff _ _ _ _ _).mpr
  intro g hg
  obtain ⟨C,hC⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
  rw [←hC,←nativeCanonicalSphere_conjugation]
  have hPar:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C*A*C⁻¹)):=by
    simp only [map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C,rfl⟩)).mp hA
  have hmem:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C*A*C⁻¹)∈H:=by
    simp only [map_mul,map_inv]
    rw [hC]
    exact H.mul_mem (H.mul_mem hg hAm) (H.inv_mem hg)
  have hd:=canonical_parabolic_simple_hyperbolic_disjoint H P.discrete
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet,_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc,P.preserves⟩ hE (C*A*C⁻¹) B hmem hPar hsB
  exact (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective).mpr hd

/-- Two actual simple closed geodesic images that are disjoint in the
original whole-group surface have disjoint actual canonical collar
images in that same surface. No translate separation is assumed. -/
theorem native_disjoint_loops_collar_quotient_disjoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hsA:IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hsB:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hloops:Disjoint (canonicalAxisSubset P hE A hsA).quotientImage
      (canonicalAxisSubset P hE B hsB).quotientImage) :
    Disjoint (nativeCanonicalQuotientImage P A) (nativeCanonicalQuotientImage P B) := by
  have htrans:∀g∈H,Disjoint (g.val '' nativeHyperbolicAxisSphere A hsA.2.1)
      (nativeHyperbolicAxisSphere B hsB.2.1):=
    (canonical_quotient_images_disjoint_iff _ _ _ _ _).mp hloops
  apply (canonical_quotient_images_disjoint_iff _ _ _ _ _).mpr
  intro g hg
  obtain ⟨C,hC⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
  have hsC:IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C*A*C⁻¹)):=by
    simp only [map_mul,map_inv]
    rw [hC]
    have hh:=hsA.conjugate g
    have hK:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g H=H:=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (H.le_normalizer hg)
    rwa [hK] at hh
  have haxis:Disjoint (nativeHyperbolicAxisSphere (C*A*C⁻¹) hsC.2.1)
      (nativeHyperbolicAxisSphere B hsB.2.1):=by
    rw [nativeHyperbolicAxisSphere_conjugation A C hsA.2.1,hC]
    exact htrans g hg
  have hno:Disjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (C*A*C⁻¹) hsC.2.1.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hsC.2.1.1.1).mp
        hsC.2.1)).carrier
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hsB.2.1.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hsB.2.1.1.1).mp
        hsB.2.1)).carrier:=
    (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective).mp haxis
  have hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (C*A*C⁻¹) hsC.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hsC.2.1.1.1).mp hsC.2.1)≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hsB.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hsB.2.1.1.1).mp hsB.2.1):=by
    intro he
    rw [he] at hno
    obtain ⟨z,_w,hz,_hw,_hne⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hsB.2.1.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hsB.2.1.1.1).mp
        hsB.2.1)).exists_two_points
    exact Set.disjoint_left.mp hno hz hz
  rw [←hC,←nativeCanonicalSphere_conjugation]
  exact (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective).mpr
    (canonical_simple_hyperbolic_regions_disjoint_of_noncrossing H P.discrete hE
      (C*A*C⁻¹) B hsC hsB hne hno)

/-- Simultaneous actual conjugation preserves separation of all original
whole-group translates, without any surface-model assumptions. -/
theorem canonical_translate_disjoint_conjugation (H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (S T:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    (∀g∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,Disjoint (g.val ''
      (q.val '' S)) (q.val '' T)) ↔
      ∀g∈H,Disjoint (g.val '' S) T := by
  constructor
  · intro h g hg
    have hh:=h (q*g*q⁻¹) ⟨g,hg,rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image] at hh
    exact (Set.disjoint_image_iff q.val.injective).mp hh
  · intro h g hg
    obtain ⟨f,hf,rfl⟩:=hg
    change Disjoint ((q*f*q⁻¹).val '' (q.val '' S)) (q.val '' T)
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image]
    exact (Set.disjoint_image_iff q.val.injective).mpr (h f hf)

/-- Disjointness of actual full-group quotient images is independent
of an actual simultaneous group/domain coordinate change. -/
theorem canonical_quotient_disjoint_conjugation {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain
      H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (E:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (S T:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hS:S⊆D.carrier) (hT:T⊆D.carrier)
    (hqS:q.val '' S⊆E.carrier) (hqT:q.val '' T⊆E.carrier) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage E (q.val '' S) hqS)
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage E (q.val '' T) hqT) ↔
      Disjoint (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D S hS) (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D T hT) := by
  rw [canonical_quotient_images_disjoint_iff,canonical_quotient_images_disjoint_iff]
  exact canonical_translate_disjoint_conjugation H S T q

/-- In every original geometric invariant disc, distinct parabolic
end-orbits have disjoint genuine canonical images in the same original
whole-group surface. No normalized end or region is supplied. -/
theorem FuchsianDisc.canonical_cusp_images_disjoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val)
    (p r:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp:f.val.val p=p) (hr:g.val.val r=r)
    (horbit:∀k∈H,k.val p≠r) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D.domain (D.canonicalRegion f)
      (D.canonicalRegion_subset_carrier f))
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D.domain (D.canonicalRegion g) (D.canonicalRegion_subset_carrier g)) := by
  let q:=D.halfPlaneNormalizer
  let P:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.normalizedHalfPlaneData D
  let A:=D.normalizedLift f
  let B:=D.normalizedLift g
  have hfN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hgN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hg
  have hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact ⟨f.val,f.property,rfl⟩
  have hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact ⟨g.val,g.property,rfl⟩
  have hpN:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (q.val p)=q.val p:=by
    rw [D.normalizedLift_spec]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint f.val q p hp
  have hrN:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val (q.val r)=q.val r:=by
    rw [D.normalizedLift_spec]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint g.val q r hr
  have horbitN:∀k∈D.normalizedGroup,k.val (q.val p)≠q.val r:=by
    intro k hk he
    obtain ⟨u,hu,rfl⟩:=hk
    apply horbit u hu
    apply q.val.injective
    change q•(u•p)=q•r
    change (q*u*q⁻¹)•(q•p)=q•r at he
    simpa only [mul_smul,inv_smul_smul] using he
  have hd:=native_parabolic_canonical_quotient_disjoint P (hE.conjugation q)
    A B hAm hBm hfN hgN (q.val p) (q.val r) hpN hrN horbitN
  have hSF:q.val '' D.canonicalRegion f=nativeCanonicalSphere A:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D f
  have hSG:q.val '' D.canonicalRegion g=nativeCanonicalSphere B:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D g
  apply (canonical_quotient_images_disjoint_iff _ _ _ _ _).mpr
  apply (canonical_translate_disjoint_conjugation H _ _ q).mp
  change ∀k∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,Disjoint (k.val
    '' (q.val '' D.canonicalRegion f)) (q.val '' D.canonicalRegion g)
  rw [hSF,hSG]
  exact (canonical_quotient_images_disjoint_iff _ _ _ _ _).mp hd

/-- The genuine canonical image of any parabolic element is disjoint
from every simple closed-geodesic collar in the original arbitrary
geometric-disc whole-group surface. -/
theorem FuchsianDisc.canonical_cusp_collar_images_disjoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (hs:IsSimple H g.val) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscQuotientImage D.domain (D.canonicalRegion f)
      (D.canonicalRegion_subset_carrier f))
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCollar D hE g hs).quotientImage := by
  let q:=D.halfPlaneNormalizer
  let P:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.normalizedHalfPlaneData D
  let A:=D.normalizedLift f
  let B:=D.normalizedLift g
  have hfN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact ⟨f.val,f.property,rfl⟩
  have hsN:IsSimple D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D g hs
  have hd:=native_cusp_collar_quotient_disjoint P (hE.conjugation q) A B hAm hfN hsN
  have hSF:q.val '' D.canonicalRegion f=nativeCanonicalSphere A:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D f
  have hSG:q.val '' D.canonicalRegion g=nativeCanonicalSphere B:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D g
  apply (canonical_quotient_images_disjoint_iff _ _ _ _ _).mpr
  apply (canonical_translate_disjoint_conjugation H _ _ q).mp
  change ∀k∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,Disjoint (k.val
    '' (q.val '' D.canonicalRegion f)) (q.val '' D.canonicalRegion g)
  rw [hSF,hSG]
  exact (canonical_quotient_images_disjoint_iff _ _ _ _ _).mp hd

/-- Construct the original actual axis model from the original simple
hyperbolic generator, rather than assume a coordinate axis. -/
def FuchsianDisc.canonicalAxisModel {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hs:IsSimple H f.val) : FuchsianAxisModel D f.val where
  matrix:=D.normalizedLift f
  nontrivial:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hs).2.1.1.1
  trace_gt:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hs).2.1.1.1).mp
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hs).2.1
  projection:=D.normalizedLift_spec f

/-- The entire actual simple geodesic in the original geometric disc,
with its original whole-group surface projection. -/
def FuchsianDisc.canonicalAxis {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hs:IsSimple H
      f.val) : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain :=
  (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxisModel D f hs).stableSubset hs

/-- The constructed actual original axis has precisely its genuine
native hyperbolic-axis image under the constructed whole-disc chart. -/
theorem FuchsianDisc.canonicalAxis_normalized_image {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hs:IsSimple H f.val) :
    D.halfPlaneNormalizer.val '' (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f
      hs).carrier=
      nativeHyperbolicAxisSphere (D.normalizedLift f)
        (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hs).2.1 := by
  exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxisModel D f hs).carrier_image

/-- Actual disjoint simple closed geodesic images in any original
geometric-disc surface have disjoint actual canonical collar images
in that same original whole-group quotient surface. -/
theorem FuchsianDisc.canonical_disjoint_loops_collar_images_disjoint {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g:H)
    (hsF:IsSimple H f.val) (hsG:IsSimple H g.val)
    (hloops:Disjoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f hsF).quotientImage
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D g hsG).quotientImage) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCollar D hE f hsF).quotientImage
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCollar D hE g hsG).quotientImage := by
  let q:=D.halfPlaneNormalizer
  let P:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.normalizedHalfPlaneData D
  let A:=D.normalizedLift f
  let B:=D.normalizedLift g
  have hsA:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hsF
  have hsB:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D g hsG
  have hloopsN:Disjoint (canonicalAxisSubset P (hE.conjugation q) A hsA).quotientImage
      (canonicalAxisSubset P (hE.conjugation q) B hsB).quotientImage:=by
    apply (canonical_quotient_images_disjoint_iff _ _ _ _ _).mpr
    have horig:∀k∈H,Disjoint (k.val '' (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f
      hsF).carrier)
        (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D g hsG).carrier:=
      (canonical_quotient_images_disjoint_iff _ _ _ _ _).mp hloops
    have hn:∀k∈D.normalizedGroup,Disjoint
        (k.val '' (q.val '' (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f
          hsF).carrier))
        (q.val '' (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D g hsG).carrier):=
      (canonical_translate_disjoint_conjugation H _ _ q).mpr horig
    dsimp only [q] at hn
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis_normalized_image D f hsF,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis_normalized_image D g hsG] at hn
    exact hn
  have hd:=native_disjoint_loops_collar_quotient_disjoint P (hE.conjugation q) A B hsA hsB hloopsN
  apply (canonical_quotient_images_disjoint_iff _ _ _ _ _).mpr
  apply (canonical_translate_disjoint_conjugation H _ _ q).mp
  change ∀k∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,Disjoint
    (k.val '' (q.val '' D.canonicalRegion f)) (q.val '' D.canonicalRegion g)
  have hSF:q.val '' D.canonicalRegion f=nativeCanonicalSphere A:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D f
  have hSG:q.val '' D.canonicalRegion g=nativeCanonicalSphere B:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D g
  rw [hSF,hSG]
  exact (canonical_quotient_images_disjoint_iff _ _ _ _ _).mp hd

/-- The actual original simple axis has its true cyclic stabilizer,
circle quotient and embedded simple closed geodesic in the original
entire-group surface. -/
theorem FuchsianDisc.canonicalAxis_circle {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H) (hs:IsSimple H
      f.val) :
    (∃u:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic u ∧
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f
        hs).stabilizer=Subgroup.zpowers u) ∧
      Nonempty ((_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f hs).Quotient ≃ₜ
        Circle) ∧
      ∃e:Circle→_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain,Topology.IsEmbedding e ∧
        Set.range e=(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f hs).quotientImage :=
  (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxisModel D f hs).simple_closed_curve hs (fun u
    hu=>hE ⟨u,hu⟩)

/-- The actual original central geodesic is contained in its genuine
original canonical collar, not just in a separate normal-form model. -/
theorem FuchsianDisc.canonicalAxis_subset_collar {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hs:IsSimple H f.val) :
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f hs).carrier⊆D.canonicalRegion f := by
  apply (Set.image_subset_image_iff D.halfPlaneNormalizer.val.injective).mp
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis_normalized_image,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image]
  exact nativeHyperbolicAxisSphere_subset_canonical _
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonical_normalized_simple D f hs).2.1

/-- The actual embedded original simple closed geodesic lies in the
actual open canonical collar image in the same whole-group surface. -/
theorem FuchsianDisc.canonicalAxis_image_subset_collar {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f:H) (hs:IsSimple H
      f.val) :
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis D f hs).quotientImage⊆
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCollar D hE f hs).quotientImage := by
  rintro x ⟨z,rfl⟩
  exact ⟨⟨z.val,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalAxis_subset_collar D f hs
    z.property⟩,rfl⟩

/-- Every genuine parabolic end of an original Fuchsian group has an
actual primitive parabolic generator of its entire original point
stabilizer. The primitive-period assumption is derived at each end. -/
theorem FuchsianDisc.exists_primitive_cusp_generator {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp:f.val.val p=p) :
    ∃g:H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧ IsPrimitive H g.val ∧ g.val.val p=p := by
  obtain ⟨u,hu⟩:=(Subgroup.isCyclic_iff_exists_zpowers_eq_top
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p)).mp (D.stabilizer_isCyclic p)
  have hfm:f.val∈Subgroup.zpowers u:=by
    rw [hu]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨f.property,hp⟩
  obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hfm
  have huP:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic u:=mobius_parabolic_of_zpow n (hn.symm ▸ hf)
  have hum:u∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p:=by rw [←hu];exact Subgroup.mem_zpowers u
  obtain ⟨huH,hup⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p u).mp hum
  refine ⟨⟨u,huH⟩,huP,?_,hup⟩
  apply (primitive_iff_of_parabolic huP).mpr
  refine ⟨huH,?_⟩
  intro x hx
  obtain ⟨a,ha⟩:=huP.2
  have hxp:x=p:=((ha x).mp hx).trans ((ha p).mp hup).symm
  rwa [hxp]

/-- Every actual parabolic end, with no primitiveness or period
hypothesis, has a true open canonical cusp model in the original
surface, using its constructed full primitive stabilizer generator. -/
theorem FuchsianDisc.canonical_cusp_at_end {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree
      H) (f:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp:f.val.val p=p) :
    ∃g:H,∃hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val,∃hprim:IsPrimitive H g.val,
      g.val.val p=p ∧
      IsOpen ((_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp D hE g hg hprim).quotientImage
        :Set (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain)) ∧
      IsCyclic (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp D hE g hg hprim).stabilizer ∧
      Nonempty ((_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp D hE g hg hprim).quotientImage ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspPuncturedDisc (1/2)) := by
  obtain ⟨g,hg,hprim,hgp⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.exists_primitive_cusp_generator D f hf p hp
  exact ⟨g,hg,hprim,hgp,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalCusp_image_puncturedDisc D
    hE g hg hprim⟩

end LowDimensionalTopology.Geometry.Fuchsian
