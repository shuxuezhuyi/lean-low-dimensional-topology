/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.SimpleClosedCurves
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

/-- Without elliptics, every actual original-disc point has trivial actual stabilizer. -/
theorem FuchsianDisc.noElliptics_free
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (g : Mobius.complexMobiusGroup)
    (hg : g ∈ H)
    (p : Mobius.ExtendedComplex)
    (hp : p ∈ D.carrier)
    (hgp : g.val p=p) : g=1 := by
  by_contra hn
  have hnfront : p ∉ frontier D.carrier := by
    intro hb
    have hb' : p ∈ closure D.carrier ∧ p ∉ D.carrier := by
      simpa only [frontier,mem_sdiff,D.isDisc.isOpen.interior_eq] using hb
    exact hb'.2 hp
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy g hn with hpar | hlox | hell
  · exact hnfront (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier g hpar D.isDisc (D.image_eq ⟨g,hg⟩) hgp)
  · exact hnfront (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier g
      (D.loxodromic_hyperbolic ⟨g,hg⟩ hlox) D.isDisc (D.image_eq ⟨g,hg⟩) hgp)
  · exact hno g hg hell

/-- The genuine stabilizer-orbit quotient exists for every subset, without a stability hypothesis. -/
abbrev SphereSetOrbitQuotient
    (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) :=
  _root_.Quotient ((MulAction.orbitRel (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H S) Mobius.ExtendedComplex).comap
    (Subtype.val : S → Mobius.ExtendedComplex))

/-- The actual map from the subset-stabilizer quotient to the original whole surface quotient. -/
def sphereSetOrbitMap
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (S : Set Mobius.ExtendedComplex) (hSD : S ⊆ D.carrier) :
    SphereSetOrbitQuotient H S → _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D :=
  _root_.Quotient.lift (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D S hSD)
    (by
      intro x y h
      obtain ⟨g,hg⟩ := h
      apply _root_.Quotient.sound
      exact ⟨⟨g.val,g.property.1⟩,Subtype.ext hg⟩)

theorem sphereSetOrbitMap_continuous {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (S : Set Mobius.ExtendedComplex)
    (hSD : S ⊆ D.carrier) :
    Continuous (sphereSetOrbitMap D S hSD) :=
  continuous_quot_lift _ (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection_continuous D S hSD)

/-- Actual stability makes the canonical stabilizer-orbit map injective. -/
theorem sphereSetOrbitMap_injective_of_stable
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (S : Set Mobius.ExtendedComplex)
    (hSD : S ⊆ D.carrier)
    (hstable : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H S) : Function.Injective (sphereSetOrbitMap D S hSD) := by
  intro a b hab
  induction a using _root_.Quotient.inductionOn with
  | h x =>
    induction b using _root_.Quotient.inductionOn with
    | h y =>
      obtain ⟨g,hg⟩ := _root_.Quotient.exact hab
      have hgy : g.val.val y.val=x.val := congrArg Subtype.val hg
      have hgS : g.val ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H S :=
        _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusStableSet_mem_stabilizer_of_intersection hstable g.val g.property
          ⟨x.val,⟨y.val,y.property,hgy⟩,x.property⟩
      exact _root_.Quotient.sound ⟨⟨g.val,hgS⟩,hgy⟩

/-- For a genuinely free original action, injectivity forces whole-subset stability. -/
theorem stable_of_sphereSetOrbitMap_injective
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (S : Set Mobius.ExtendedComplex) (hSD : S ⊆ D.carrier)
    (hinj : Function.Injective (sphereSetOrbitMap D.domain S hSD)) : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H S := by
  intro g hg
  by_cases he : g.val '' S=S
  · exact Or.inl he
  · right
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hgx
    let a : S := ⟨g.val x,hgx⟩
    let b : S := ⟨x,hx⟩
    have hab : sphereSetOrbitMap D.domain S hSD (_root_.Quotient.mk _ a)=
        sphereSetOrbitMap D.domain S hSD (_root_.Quotient.mk _ b) :=
      _root_.Quotient.sound ⟨⟨g,hg⟩,Subtype.ext rfl⟩
    obtain ⟨k,hk⟩ := _root_.Quotient.exact (hinj hab)
    have hkx : k.val.val x=g.val x := hk
    have hfree : k.val⁻¹*g=1 := D.noElliptics_free hno (k.val⁻¹*g)
      (H.mul_mem (H.inv_mem k.property.1) hg) x (hSD hx) (by
        change (k.val⁻¹*g)•x=x
        change k.val•x=g•x at hkx
        rw [mul_smul,←hkx,inv_smul_smul])
    have hkg : g=k.val := by
      calc
        g=k.val*(k.val⁻¹*g) := by group
        _=k.val := by rw [hfree,mul_one]
    exact he (hkg.symm ▸ k.property.2)

/-- The actual full-group orbit map is injective exactly for the actual stable subsets. -/
theorem sphereSetOrbitMap_injective_iff_stable
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (S : Set Mobius.ExtendedComplex) (hSD : S ⊆ D.carrier) :
    Function.Injective (sphereSetOrbitMap D.domain S hSD) ↔ _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H S :=
  ⟨stable_of_sphereSetOrbitMap_injective D hno S hSD,
    sphereSetOrbitMap_injective_of_stable D.domain S hSD⟩

/-- Restrict the genuine action without changing the original geometric domain. -/
def restrictMobiusDomain {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain K where
  carrier := D.carrier
  isOpen := D.isOpen
  isConnected := D.isConnected
  invariant := fun g z hz => D.invariant ⟨g.val,hKH g.property⟩ z hz

/-- Proper discontinuity is inherited by an actual subgroup on the same domain. -/
theorem restrictMobiusDomain_discontinuous
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn K (restrictMobiusDomain D K hKH).carrier := by
  intro T hTc hTD
  let i : K → H := fun g => ⟨g.val,hKH g.property⟩
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (show a.val=b.val from congrArg (fun x : H => x.val) hab)
  change (i ⁻¹' {g : H | (g.val.val '' T ∩ T).Nonempty}).Finite
  exact Set.Finite.preimage hi.injOn (hD T hTc hTD)

/-- A subset is always stable under its own actual set stabilizer. -/
def stabilizerStableSubset
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (S : Set Mobius.ExtendedComplex) (hSD : S ⊆ D.carrier) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset (restrictMobiusDomain D (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H S)
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer_le H S)) where
  carrier := S
  subset_domain := hSD
  stable := fun _ hg => Or.inl hg.2

theorem stabilizerStableSubset_stabilizer
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (S : Set Mobius.ExtendedComplex)
    (hSD : S ⊆ D.carrier) :
    (stabilizerStableSubset D S hSD).stabilizer=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H S := by
  ext g
  exact ⟨fun hg => hg.1,fun hg => ⟨hg,hg.2⟩⟩

/-- The restricted stable-subset quotient is literally the original set-stabilizer quotient. -/
def stabilizerStableSubset_quotientHomeomorph
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (S : Set Mobius.ExtendedComplex)
    (hSD : S ⊆ D.carrier) :
    (stabilizerStableSubset D S hSD).Quotient ≃ₜ SphereSetOrbitQuotient H S := by
  change _root_.Quotient ((MulAction.orbitRel (stabilizerStableSubset D S hSD).stabilizer
    Mobius.ExtendedComplex).comap (Subtype.val : S → Mobius.ExtendedComplex)) ≃ₜ _
  rw [stabilizerStableSubset_stabilizer]
  exact Homeomorph.refl _

/-- Transport the actual native-axis theorem through any proved geometric normalization. -/
theorem stableSubset_axis_quotient_circle
    {G : Subgroup Mobius.complexMobiusGroup}
    {E : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain G}
    (S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset E)
    (hproper : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G E.carrier)
    (hno : ∀ g ∈ G, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (q : Mobius.complexMobiusGroup)
    (hH : ∀ g ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G,
      g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (ht : 4<(Matrix.trace A.val)^2)
    (hS : q.val '' S.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier)
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) :
    (∃ g : Mobius.complexMobiusGroup, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g ∧ S.stabilizer=Subgroup.zpowers g) ∧
      Nonempty (S.Quotient ≃ₜ Circle) := by
  let N := S.conjugate q
  have hnoN : ∀ g ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g → g^2≠1 := by
    intro g hg hE
    obtain ⟨a,ha,he⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q G g).mp hg
    exact False.elim (hno a ha ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation a q).mp (he.symm ▸ hE)))
  have hN : N.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier := hS
  have hinv : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' N.carrier=N.carrier := by
    rw [hN,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_image_realSL]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_invariant A hf ht]
  obtain ⟨⟨g,hg,hgen⟩,⟨C⟩,_⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.hyperbolic_axis_stabilizer_generated_quotient_circle_embeds N
    (E.conjugate_discontinuous q hproper) hH hnoN (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht) hN
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hmem ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hf).mpr ht) hinv
  have hconj : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer=Subgroup.zpowers g := by
    rw [←S.conjugate_stabilizer]
    exact hgen
  have hhyperOrig : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (q⁻¹*g*q) := by
    simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward g q⁻¹ hg
  exact ⟨⟨q⁻¹*g*q,hhyperOrig,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_conjugate_generator S.stabilizer q g hconj⟩,
    ⟨(stableSubsetConjugateQuotientHomeomorph S q).trans C⟩⟩

/-- The original hyperbolic transformation preserves its constructed genuine axis. -/
theorem FuchsianAxisModel.carrier_invariant
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f) :
    f.val '' M.carrier=M.carrier := by
  have hc := _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image D.halfPlaneNormalizer f M.carrier
  rw [M.carrier_image,←M.projection] at hc
  have hn : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix).val '' M.nativeCarrier=M.nativeCarrier := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix).val ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis M.matrix M.nontrivial M.trace_gt).carrier)=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_image_realSL,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_invariant M.matrix M.nontrivial M.trace_gt]
    rfl
  exact D.halfPlaneNormalizer.val.injective.image_injective
    (hc.symm.trans (hn.trans M.carrier_image.symm))

/-- Every hyperbolic axis has a genuine cyclic stabilizer and genuine circle quotient,
including axes whose full-group translates cross them. -/
theorem FuchsianAxisModel.axis_quotient_circle
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    (∃ g : Mobius.complexMobiusGroup, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H M.carrier=Subgroup.zpowers g) ∧
      Nonempty (SphereSetOrbitQuotient H M.carrier ≃ₜ Circle) := by
  let K := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H M.carrier
  let S := stabilizerStableSubset D.domain M.carrier M.carrier_subset_domain
  have hK : K ≤ H := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer_le H M.carrier
  have hfK : f ∈ K := ⟨hfH,M.carrier_invariant⟩
  have hH : ∀ g ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer K,
      g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff D.halfPlaneNormalizer K g).mp hg
    exact D.normalizedGroup_preserves_halfPlane _
      ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff D.halfPlaneNormalizer H _).mpr ⟨a,hK ha,rfl⟩)
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer K := by
    rw [M.projection]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff D.halfPlaneNormalizer K _).mpr ⟨f,hfK,rfl⟩
  obtain ⟨⟨g,hg,hgen⟩,⟨C⟩⟩ := stableSubset_axis_quotient_circle S
    (restrictMobiusDomain_discontinuous D.domain K hK D.discontinuous)
    (fun g hg => hno g (hK hg)) D.halfPlaneNormalizer hH M.matrix M.nontrivial M.trace_gt
    M.carrier_image hmem
  have hSK : S.stabilizer=K := stabilizerStableSubset_stabilizer D.domain M.carrier _
  exact ⟨⟨g,hg,hSK.symm.trans hgen⟩,
    ⟨(stabilizerStableSubset_quotientHomeomorph D.domain M.carrier _).symm.trans C⟩⟩

/-- Its image consists exactly of the original whole-group orbits met by the subset. -/
theorem sphereSetOrbitMap_range
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (S : Set Mobius.ExtendedComplex) (hSD : S ⊆ D.carrier) :
    Set.range (sphereSetOrbitMap D S hSD)=Set.range (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D S hSD) := by
  ext y
  constructor
  · rintro ⟨a,rfl⟩
    induction a using _root_.Quotient.inductionOn with
    | h x => exact ⟨x,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨_root_.Quotient.mk _ x,rfl⟩

/-- A circle coordinate chosen from the proved actual axis-stabilizer quotient theorem. -/
def FuchsianAxisModel.circleHomeomorph {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    SphereSetOrbitQuotient H M.carrier ≃ₜ Circle :=
  (M.axis_quotient_circle hfH hno).2.some

/-- The actual closed curve on the original quotient, for every actual hyperbolic element. -/
def FuchsianAxisModel.closedCurve {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    Circle → _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain :=
  sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain ∘
    (M.circleHomeomorph hfH hno).symm

theorem FuchsianAxisModel.closedCurve_continuous
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    Continuous (M.closedCurve hfH hno) :=
  (sphereSetOrbitMap_continuous D.domain M.carrier M.carrier_subset_domain).comp
    (M.circleHomeomorph hfH hno).symm.continuous

theorem FuchsianAxisModel.closedCurve_range
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    Set.range (M.closedCurve hfH hno)=
      Set.range (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D.domain M.carrier M.carrier_subset_domain) := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.closedCurve,Set.range_comp,
    (M.circleHomeomorph hfH hno).symm.surjective.range_eq,Set.image_univ]
  exact sphereSetOrbitMap_range D.domain M.carrier M.carrier_subset_domain

/-- Injectivity of the genuine circle parametrization is equivalent to original simplicity. -/
theorem FuchsianAxisModel.closedCurve_injective_iff_simple
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    Function.Injective (M.closedCurve hfH hno) ↔ IsSimple H f := by
  let C := M.circleHomeomorph hfH hno
  constructor
  · intro hi
    apply (M.stable_iff_simple hfH).mp
    apply (sphereSetOrbitMap_injective_iff_stable D hno M.carrier M.carrier_subset_domain).mp
    intro a b hab
    apply C.injective
    apply hi
    change sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain (C.symm (C a))=
      sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain (C.symm (C b))
    simpa only [C.symm_apply_apply] using hab
  · intro hs
    exact (sphereSetOrbitMap_injective_of_stable D.domain M.carrier M.carrier_subset_domain
      ((M.stable_iff_simple hfH).mpr hs)).comp C.symm.injective

/-- The actual hyperbolic closed curve is embedded exactly for simple elements. -/
theorem FuchsianAxisModel.closedCurve_embedding_iff_simple
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    Topology.IsEmbedding (M.closedCurve hfH hno) ↔ IsSimple H f := by
  constructor
  · intro he
    exact (M.closedCurve_injective_iff_simple hfH hno).mp he.injective
  · intro hs
    let : T2Space (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain) := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainQuotient_t2 D.domain D.discontinuous
    have hc := M.closedCurve_continuous hfH hno
    exact (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hc
      ((M.closedCurve_injective_iff_simple hfH hno).mpr hs) hc.isClosedMap).isEmbedding

/-- A nonsimple original element gives distinct genuine circle parameters at one surface point. -/
theorem FuchsianAxisModel.closedCurve_self_intersection
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup}
    (M : FuchsianAxisModel D f)
    (hfH : f ∈ H)
    (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hns : ¬IsSimple H f) :
    ∃ u v : Circle, u≠v ∧ M.closedCurve hfH hno u=M.closedCurve hfH hno v := by
  by_contra hex
  apply hns
  apply (M.closedCurve_injective_iff_simple hfH hno).mp
  intro a b he
  by_contra hne
  exact hex ⟨a,b,hne,he⟩

/-- The full original-disc closed-curve interpretation, without an assumed axis chart,
matrix model, cyclic stabilizer or circle parametrization. -/
theorem FuchsianDisc.hyperbolic_closed_curve
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hno : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (f : Mobius.complexMobiusGroup)
    (hfH : f ∈ H)
    (hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) :
    ∃ M : FuchsianAxisModel D f, ∃ c : Circle → _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain,
      Continuous c ∧
      Set.range c=Set.range (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDiscDomainProjection D.domain M.carrier M.carrier_subset_domain) ∧
      (Topology.IsEmbedding c ↔ IsSimple H f) ∧
      (¬IsSimple H f → ∃ u v : Circle, u≠v ∧ c u=c v) := by
  obtain ⟨M⟩ := D.axisModel_exists f hfH hh
  exact ⟨M,M.closedCurve hfH hno,M.closedCurve_continuous hfH hno,
    M.closedCurve_range hfH hno,M.closedCurve_embedding_iff_simple hfH hno,
    M.closedCurve_self_intersection hfH hno⟩

end LowDimensionalTopology.Geometry.Fuchsian
