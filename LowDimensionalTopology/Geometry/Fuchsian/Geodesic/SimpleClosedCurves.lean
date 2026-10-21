/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HalfPlaneH3
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.GeneralParabolicCusps
@[expose] public section
noncomputable section
open Set
open scoped OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The original genuine Fuchsian disc as the actual invariant surface domain. -/
def FuchsianDisc.domain
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H where
  carrier := D.carrier
  isOpen := D.isDisc.isOpen
  isConnected := D.isDisc.isConnected
  invariant := D.invariant

/-- Whole-subset stability transports under actual simultaneous group/domain conjugation. -/
theorem mobiusStableSet_conjugation (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex)
    (q : Mobius.complexMobiusGroup) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val '' S) ↔ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H S := by
  constructor
  · intro hs g hg
    have h := hs (q*g*q⁻¹) ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g,hg,rfl⟩)
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image] at h
    rcases h with he | hd
    · exact Or.inl (q.val.injective.image_injective he)
    · exact Or.inr ((Set.disjoint_image_iff q.val.injective).mp hd)
  · intro hs f hf
    obtain ⟨g,hg,rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f).mp hf
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image]
    rcases hs g hg with he | hd
    · exact Or.inl (congrArg (Set.image q.val) he)
    · exact Or.inr ((Set.disjoint_image_iff q.val.injective).mpr hd)

/-- A proved genuine native axis model for an actual original transformation and disc. -/
structure FuchsianAxisModel {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (f : Mobius.complexMobiusGroup) where
  matrix : Matrix.SpecialLinearGroup (Fin 2) ℝ
  nontrivial : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius matrix≠1
  trace_gt : 4<(Matrix.trace matrix.val)^2
  projection : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius matrix=D.halfPlaneNormalizer*f*D.halfPlaneNormalizer⁻¹

/-- Both the real matrix and its true hyperbolic type are constructed from the original data. -/
theorem FuchsianDisc.axisModel_exists
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (f : Mobius.complexMobiusGroup)
    (hfH : f ∈ H)
    (hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) :
    Nonempty (FuchsianAxisModel D f) := by
  let q := D.halfPlaneNormalizer
  have hmem : q*f*q⁻¹ ∈ D.normalizedGroup :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨f,hfH,rfl⟩
  obtain ⟨A,hA⟩ := D.normalizedGroup_exists_realSL _ hmem
  have hAh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [hA]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f q hh
  exact ⟨⟨A,hAh.1.1,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hAh.1.1).mp hAh,hA⟩⟩

/-- The entire actual native geodesic joining the genuine ideal fixed endpoints. -/
def FuchsianAxisModel.line
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis M.matrix M.nontrivial M.trace_gt

def FuchsianAxisModel.nativeCarrier
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f) : Set Mobius.ExtendedComplex :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' M.line.carrier

/-- The actual original-disc axis, using the inverse of the constructed geometric chart. -/
def FuchsianAxisModel.carrier
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f) : Set Mobius.ExtendedComplex :=
  D.halfPlaneNormalizer⁻¹.val '' M.nativeCarrier

theorem FuchsianAxisModel.carrier_image
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup} (M : FuchsianAxisModel D f) :
    D.halfPlaneNormalizer.val '' M.carrier=M.nativeCarrier := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.carrier,image_image]
  change (fun z : Mobius.ExtendedComplex => D.halfPlaneNormalizer•(D.halfPlaneNormalizer⁻¹•z)) '' M.nativeCarrier=_
  simp only [smul_inv_smul,image_id']

theorem FuchsianAxisModel.carrier_subset_domain
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f) :
    M.carrier ⊆ D.carrier := by
  rintro z ⟨u,⟨p,_hp,rfl⟩,rfl⟩
  have h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := ⟨(p:ℂ),p.im_pos,rfl⟩
  rw [←D.halfPlaneNormalizer_image] at h
  obtain ⟨a,ha,he⟩ := h
  change D.halfPlaneNormalizer⁻¹•_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint p ∈ D.carrier
  rw [←he]
  change D.halfPlaneNormalizer⁻¹•(D.halfPlaneNormalizer•a) ∈ D.carrier
  simpa only [inv_smul_smul] using ha

/-- The original actual axis is stable exactly when the original element is simple. -/
theorem FuchsianAxisModel.stable_iff_simple
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H M.carrier ↔ IsSimple H f := by
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix ∈ D.normalizedGroup := by
    rw [M.projection]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff D.halfPlaneNormalizer H _).mpr ⟨f,hfH,rfl⟩
  have hs := mobiusStableSet_conjugation H M.carrier D.halfPlaneNormalizer
  rw [M.carrier_image] at hs
  constructor
  · intro h
    have hst := hs.mpr h
    have hsimple := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_iff_native_axis_stable D.normalizedGroup M.matrix M.nontrivial
      M.trace_gt D.normalizedGroup_exists_realSL).mpr ⟨hmem,hst⟩
    rw [M.projection] at hsimple
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation H f D.halfPlaneNormalizer).mp hsimple
  · intro h
    have hsimple : IsSimple D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix) := by
      rw [M.projection]
      exact h.conjugate D.halfPlaneNormalizer
    exact hs.mp (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_iff_native_axis_stable D.normalizedGroup M.matrix M.nontrivial
      M.trace_gt D.normalizedGroup_exists_realSL).mp hsimple).2)


/-- A simple actual axis is an actual stable subset of the original invariant surface domain. -/
def FuchsianAxisModel.stableSubset
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hs : IsSimple H f) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain where
  carrier := M.carrier
  subset_domain := M.carrier_subset_domain
  stable := (M.stable_iff_simple hs.1).mpr hs

/-- The actual stabilizer-orbit quotient is unchanged by simultaneous geometric conjugation. -/
def stableSubsetConjugateQuotientHomeomorph
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H}
    (S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D)
    (q : Mobius.complexMobiusGroup) :
    S.Quotient ≃ₜ (S.conjugate q).Quotient := by
  change S.Quotient ≃ₜ _root_.Quotient
    ((MulAction.orbitRel (S.conjugate q).stabilizer Mobius.ExtendedComplex).comap
      (Subtype.val : (q.val '' S.carrier) → Mobius.ExtendedComplex))
  rw [S.conjugate_stabilizer]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisConjugateQuotientHomeomorph S.stabilizer S.carrier q

/-- Every actual simple hyperbolic axis in an arbitrary original invariant disc gives
its genuine cyclic stabilizer quotient and an embedded actual circle on the original surface. -/
theorem FuchsianAxisModel.simple_closed_curve
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hs : IsSimple H f) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    let S := M.stableSubset hs
    (∃ g : Mobius.complexMobiusGroup, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g ∧ S.stabilizer=Subgroup.zpowers g) ∧
      Nonempty (S.Quotient ≃ₜ Circle) ∧
      ∃ e : Circle → _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain,
        Topology.IsEmbedding e ∧ Set.range e=S.quotientImage := by
  let S := M.stableSubset hs
  let q := D.halfPlaneNormalizer
  let N := S.conjugate q
  have hprop := D.domain.conjugate_discontinuous q D.discontinuous
  have hH : ∀ g ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H, g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet :=
    D.normalizedGroup_preserves_halfPlane
  have hnoN : ∀ g ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g → g^2≠1 := by
    intro g hg hE
    obtain ⟨a,ha,he⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H g).mp hg
    exact False.elim (hno a ha ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation a q).mp (he.symm ▸ hE)))
  have hN : N.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' M.line.carrier := M.carrier_image
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H := by
    rw [M.projection]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨f,hs.1,rfl⟩
  have hhyper : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix) :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff M.matrix M.nontrivial).mpr M.trace_gt
  have hinv : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix).val '' N.carrier=N.carrier := by
    rw [hN,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_image_realSL]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' ((M.matrix•· : ℍ → ℍ) ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis M.matrix M.nontrivial M.trace_gt).carrier)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis M.matrix M.nontrivial M.trace_gt).carrier
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_invariant M.matrix M.nontrivial M.trace_gt]
  obtain ⟨⟨g,hg,hgen⟩,⟨C⟩,_⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.hyperbolic_axis_stabilizer_generated_quotient_circle_embeds N hprop hH hnoN M.line hN
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix) hmem hhyper hinv
  have hconj : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer=Subgroup.zpowers g := by
    rw [←S.conjugate_stabilizer]
    exact hgen
  have hgenOrig := _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_conjugate_generator S.stabilizer q g hconj
  have hhyperOrig : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (q⁻¹*g*q) := by
    simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward g q⁻¹ hg
  let Corig := (stableSubsetConjugateQuotientHomeomorph S q).trans C
  exact ⟨⟨q⁻¹*g*q,hhyperOrig,hgenOrig⟩,⟨Corig⟩,
    S.simpleClosedCurve_of_quotientCircle D.discontinuous Corig⟩

end LowDimensionalTopology.Geometry.Fuchsian
