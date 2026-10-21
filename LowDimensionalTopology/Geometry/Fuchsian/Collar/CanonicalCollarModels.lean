/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalQuotientRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.PrimitiveAxisIntersection
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

/-- The entire actual finite hyperbolic axis, with its original sphere coordinate. -/
def nativeHyperbolicAxisSphere (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)).carrier

/-- The actual axis sphere subset transforms under the same original real action. -/
theorem nativeHyperbolicAxisSphere_conjugation (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    nativeHyperbolicAxisSphere (B*A*B⁻¹) (by
      simpa only [map_mul,map_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ _ hA)=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val '' nativeHyperbolicAxisSphere A hA := by
  unfold nativeHyperbolicAxisSphere
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier,image_image,image_image]
  exact image_congr (fun z _=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action B z).symm)

/-- Preserving the full genuine canonical strip is equivalent to preserving
its actual axis; this uses reconstruction of the original map up to inversion. -/
theorem nativeCanonicalSphere_image_eq_iff_axis (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B).val '' nativeCanonicalSphere A=nativeCanonicalSphere A ↔
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val '' nativeHyperbolicAxisSphere A hA=nativeHyperbolicAxisSphere A hA := by
  let C:=B*A*B⁻¹
  have hC:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by
    dsimp only [C]
    simpa only [map_mul,map_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ _ hA
  rw [←nativeCanonicalSphere_conjugation,←nativeHyperbolicAxisSphere_conjugation A B hA]
  change nativeCanonicalSphere C=nativeCanonicalSphere A ↔
    nativeHyperbolicAxisSphere C hC=nativeHyperbolicAxisSphere A hA
  have hi:=Set.image_injective.mpr _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  constructor
  · intro he
    have hr:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion C:=(hi he).symm
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_hyperbolic_reconstruct A C hA.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA) hr
    have haxis:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hC.1.1).mp hC)=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA):=by
      rcases hh with heq|heq
      · exact hHyperbolicAxis_eq_of_realSLMobius_eq C A hC.1.1 hA.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hC.1.1).mp hC)
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA) heq
      · have hiA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹):=by
          have hn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹≠1:=by rw [map_inv];exact inv_ne_one.mpr hA.1.1
          apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A⁻¹ hn).mpr
          rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse]
          exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA
        have heq':_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹:=by rwa [map_inv]
        rw [hHyperbolicAxis_eq_of_realSLMobius_eq C A⁻¹ hC.1.1 hiA.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hC.1.1).mp hC)
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A⁻¹ hiA.1.1).mp hiA) heq',
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_inverse A hA.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)]
    exact congrArg (fun L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' L.carrier) haxis
  · intro he
    have hcarrier:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hC.1.1).mp hC)).carrier=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp
          hA)).carrier:=hi he
    have haxis:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective hcarrier
    have hr:=hCanonicalRegion_eq_of_axis_length C A hC hA haxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation A B)
    exact congrArg (fun S:Set ℍ=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) hr

/-- The original full set stabilizer of a genuine canonical strip is
exactly the original full stabilizer of its genuine geodesic axis. -/
theorem nativeCanonicalSphere_stabilizer_eq_axis {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H (nativeCanonicalSphere A)=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H (nativeHyperbolicAxisSphere A hA) := by
  ext g
  change (g∈H ∧ g.val '' nativeCanonicalSphere A=nativeCanonicalSphere A) ↔
    g∈H ∧ g.val '' nativeHyperbolicAxisSphere A hA=nativeHyperbolicAxisSphere A hA
  constructor
  · rintro ⟨hg,he⟩
    obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
    exact ⟨hg,by rw [←hB] at he ⊢;exact (nativeCanonicalSphere_image_eq_iff_axis A B hA).mp he⟩
  · rintro ⟨hg,he⟩
    obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
    exact ⟨hg,by rw [←hB] at he ⊢;exact (nativeCanonicalSphere_image_eq_iff_axis A B hA).mpr he⟩

/-- The entire actual axis is contained in the genuine open canonical strip. -/
theorem nativeHyperbolicAxisSphere_subset_canonical (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    nativeHyperbolicAxisSphere A hA⊆nativeCanonicalSphere A := by
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨z,?_,rfl⟩
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic A hA).1]
  change Real.sinh (Metric.infDist z _)*Real.sinh _<1
  rw [Metric.infDist_zero_of_mem hz,Real.sinh_zero,zero_mul]
  norm_num

/-- The actual simple-axis stability follows from the proved whole
canonical-strip stability and exact stabilizer-axis equivalence. -/
theorem nativeHyperbolicAxisSphere_simple_stable {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H (nativeHyperbolicAxisSphere A hs.2.1) := by
  intro g hg
  rcases nativeCanonicalSphere_simple_stable P hE A hs g hg with he|hd
  · left
    obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
    rw [←hB] at he ⊢
    exact (nativeCanonicalSphere_image_eq_iff_axis A B hs.2.1).mp he
  · right
    exact hd.mono (image_mono (nativeHyperbolicAxisSphere_subset_canonical A hs.2.1))
      (nativeHyperbolicAxisSphere_subset_canonical A hs.2.1)

/-- The actual whole simple geodesic is a stable subset in the same
original full invariant domain used by the canonical collar. -/
def canonicalAxisSubset {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset P.asFuchsianDisc.domain where
  carrier:=nativeHyperbolicAxisSphere A hs.2.1
  subset_domain:=by
    rintro _ ⟨z,_hz,rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    exact ⟨(z:ℂ),z.im_pos,rfl⟩
  stable:=nativeHyperbolicAxisSphere_simple_stable P hE A hs

/-- The actual hyperbolic generator preserves its entire native axis. -/
theorem nativeHyperbolicAxisSphere_self_image (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' nativeHyperbolicAxisSphere A hA=nativeHyperbolicAxisSphere A hA := by
  unfold nativeHyperbolicAxisSphere
  calc
    _=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((fun z:ℍ=>A•z) ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)).carrier):=by
      rw [image_image,image_image]
      exact image_congr (fun z _=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z)
    _=_:=by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_invariant]

/-- The embedded central geodesic is a genuine circle quotient of its
full actual cyclic stabilizer, including nonprimitive source generators. -/
theorem canonicalAxisSubset_circle {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    IsCyclic (canonicalAxisSubset P hE A hs).stabilizer ∧
      Nonempty ((canonicalAxisSubset P hE A hs).Quotient ≃ₜ Circle) ∧
      ∃e:Circle→_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain,
        Topology.IsEmbedding e ∧ Set.range e=(canonicalAxisSubset P hE A hs).quotientImage := by
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.axis_stabilizer_cyclic_quotient_circle_embeds (canonicalAxisSubset P hE A hs) P.discontinuous
    (fun g hg=>P.preserves ⟨g,hg⟩) (fun g hg hEll=>(hE ⟨g,hg⟩ hEll).elim)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hs.2.1.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hs.2.1.1.1).mp hs.2.1))
    rfl (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A) hs.1 hs.2.1.1.1 (nativeHyperbolicAxisSphere_self_image A hs.2.1)

/-- The full canonical-collar stabilizer itself is genuinely cyclic;
this follows from the actual central-axis quotient, with no primitive
or cyclic-stabilizer premise added to the source. -/
theorem canonicalCollarSubset_stabilizer_isCyclic {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    IsCyclic (canonicalCollarSubset P hE A hs).stabilizer := by
  have he:(canonicalCollarSubset P hE A hs).stabilizer=(canonicalAxisSubset P hE A hs).stabilizer:=
    nativeCanonicalSphere_stabilizer_eq_axis P A hs.2.1
  rw [he]
  exact (canonicalAxisSubset_circle P hE A hs).1

/-- The actual central geodesic circle lies in the actual canonical
collar image in the same original whole-group surface. -/
theorem canonicalAxisSubset_image_subset_collar {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    (canonicalAxisSubset P hE A hs).quotientImage⊆(canonicalCollarSubset P hE A hs).quotientImage := by
  rintro _ ⟨x,rfl⟩
  refine ⟨⟨x.val,nativeHyperbolicAxisSphere_subset_canonical A hs.2.1 x.property⟩,rfl⟩

/-- An actual simple closed geodesic and its original canonical strip
are constructed together in the same original full quotient. -/
theorem canonicalCollar_contains_circle {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    IsOpen ((canonicalCollarSubset P hE A hs).quotientImage:
      Set (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain)) ∧
      IsCyclic (canonicalCollarSubset P hE A hs).stabilizer ∧
      ∃e:Circle→_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain,
        Topology.IsEmbedding e ∧ Set.range e=(canonicalAxisSubset P hE A hs).quotientImage ∧
          Set.range e⊆(canonicalCollarSubset P hE A hs).quotientImage := by
  obtain ⟨e,he,hr⟩:=(canonicalAxisSubset_circle P hE A hs).2.2
  refine ⟨canonicalCollarSubset_image_isOpen P hE A hs,
    canonicalCollarSubset_stabilizer_isCyclic P hE A hs,e,he,hr,?_⟩
  rw [hr]
  exact canonicalAxisSubset_image_subset_collar P hE A hs

end LowDimensionalTopology.Geometry.Fuchsian
