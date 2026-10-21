module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Conjugacy.ConjugacyClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianLimitSets
public import Mathlib.Geometry.Manifold.Instances.Sphere
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Ordinary points on the actual invariant circle. -/
def fuchsianBoundaryOrdinarySet {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) :
    Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := frontier D.carrier \ fuchsianLimitSet H

/-- An interval of discontinuity is a nonempty connected component of the actual ordinary circle. -/
def IsFuchsianIntervalOfDiscontinuity {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : Prop :=
  (∃ p ∈ fuchsianBoundaryOrdinarySet D,
    I = connectedComponentIn (fuchsianBoundaryOrdinarySet D) p) ∧ I ≠ frontier D.carrier

theorem IsFuchsianIntervalOfDiscontinuity.nonempty {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    I.Nonempty := by
  obtain ⟨p, hp, rfl⟩ := hI.1
  exact ⟨p, mem_connectedComponentIn hp⟩

theorem IsFuchsianIntervalOfDiscontinuity.isConnected {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    IsConnected I := by
  obtain ⟨p, hp, rfl⟩ := hI.1
  exact ⟨⟨p, mem_connectedComponentIn hp⟩, isPreconnected_connectedComponentIn⟩

theorem IsFuchsianIntervalOfDiscontinuity.subset_boundaryOrdinary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    I ⊆ fuchsianBoundaryOrdinarySet D := by
  obtain ⟨p, _hp, rfl⟩ := hI.1
  exact connectedComponentIn_subset _ _

theorem IsFuchsianIntervalOfDiscontinuity.subset_frontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    I ⊆ frontier D.carrier := fun _ hz => (hI.subset_boundaryOrdinary hz).1

theorem IsFuchsianIntervalOfDiscontinuity.disjoint_limitSet {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    Disjoint I (fuchsianLimitSet H) :=
  disjoint_left.mpr fun _ hi hl => (hI.subset_boundaryOrdinary hi).2 hl

/-- The unnumbered boundary-hyperbolic definition, for actual group elements. -/
def IsBoundaryHyperbolic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) (f : H) : Prop :=
  _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val ∧ ∃ I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,
    IsFuchsianIntervalOfDiscontinuity D I ∧ f.val.val '' I = I

theorem IsBoundaryHyperbolic.hyperbolic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {f : H} (hf : IsBoundaryHyperbolic D
      f) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val := hf.1

/-- A genuine ordinary circle interval forces the original group to be of the second kind. -/
theorem IsFuchsianIntervalOfDiscontinuity.isSecondKind {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    D.IsSecondKind := by
  obtain ⟨p, hp, _hIp⟩ := hI.1
  change fuchsianLimitSet H ⊂ frontier D.carrier
  exact ⟨D.limitSet_subset_frontier, fun h => hp.2 (h hp.1)⟩

/-- The final clause of the boundary-hyperbolic definition paragraph. -/
theorem IsBoundaryHyperbolic.isSecondKind {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {f : H} (hf : IsBoundaryHyperbolic D f) : D.IsSecondKind := by
  obtain ⟨I, hI, _hpres⟩ := hf.2
  exact hI.isSecondKind

theorem IsBoundaryHyperbolic.ne_one {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {f : H} (hf : IsBoundaryHyperbolic D f) : f ≠ 1 :=
  fun he => hf.1.1.1 (congrArg Subtype.val he)

/-- On a non-elementary group this is exactly the ordinary set on the original circle. -/
theorem fuchsianBoundaryOrdinarySet_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) :
    fuchsianBoundaryOrdinarySet D = frontier D.carrier ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H := by
  rw [fuchsianBoundaryOrdinarySet, fuchsianLimitSet_eq_nonElementary H hH]
  rfl

/-- The actual finite circle in the compactified plane retains its standard circle topology. -/
def unitCircleExtendedHomeomorph : Circle ≃ₜ _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1 := by
  let f : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := fun z => ((z : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  have hf : Topology.IsEmbedding f :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hr : range f = _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1 := by
    ext p
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mem_complexUnitCircle_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.norm_coe, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, rfl⟩
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hr)

/-- Every actual invariant-disc boundary is homeomorphic to the native unit circle. -/
theorem complexDisc_frontier_homeomorphic_circle {D : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D) :
    Nonempty (frontier D ≃ₜ Circle) := by
  obtain ⟨q, _hq, hqf⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.complexDisc_frontier_normalize hD
  let e := ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).isEmbedding.homeomorphImage
    (frontier D)).trans
    (Homeomorph.setCongr hqf)
  exact ⟨e.trans unitCircleExtendedHomeomorph.symm⟩

/-- The actual geometric circle is locally path connected in its original subspace topology. -/
theorem complexDisc_frontier_locallyPathConnected {D : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D) :
    LocallyPathConnectedSpace (frontier D) := by
  have : LocallyPathConnectedSpace Circle :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
  obtain ⟨e⟩ := complexDisc_frontier_homeomorphic_circle hD
  exact e.symm.locallyPathConnectedSpace

/-- The ordinary part of the circle is relatively open. -/
theorem fuchsianBoundaryOrdinarySet_isOpen {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    IsOpen (((↑) : frontier D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' fuchsianBoundaryOrdinarySet D) := by
  have he : (((↑) : frontier D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹'
    fuchsianBoundaryOrdinarySet D) =
      {p : frontier D.carrier | p.val ∉ fuchsianLimitSet H} := by ext p; simp [fuchsianBoundaryOrdinarySet]
  rw [he]
  exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val

/-- An embedding preserves relative connected components exactly on its image. -/
theorem embedding_image_connectedComponentIn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f)
    (S : Set X) (p : X) (hp : p ∈ S) :
    f '' connectedComponentIn S p = connectedComponentIn (f '' S) (f p) := by
  apply le_antisymm (hf.continuous.continuousOn.image_connectedComponentIn_subset hp)
  let C := connectedComponentIn (f '' S) (f p)
  have hCr : C ⊆ range f := (connectedComponentIn_subset _ _).trans (image_subset_range _ _)
  have himg : f '' (f ⁻¹' C) = C := image_preimage_eq_of_subset hCr
  have hpre : IsPreconnected (f ⁻¹' C) := hf.isInducing.isPreconnected_image.mp
    (himg.symm ▸ isPreconnected_connectedComponentIn)
  have hpreS : f ⁻¹' C ⊆ S := by
    intro x hx
    obtain ⟨z, hz, he⟩ := connectedComponentIn_subset (f '' S) (f p) hx
    exact hf.injective he ▸ hz
  have hpreSub : f ⁻¹' C ⊆ connectedComponentIn S p :=
    hpre.subset_connectedComponentIn (mem_connectedComponentIn (mem_image_of_mem f hp)) hpreS
  intro y hy
  obtain ⟨x, _hxS, hxy⟩ := connectedComponentIn_subset (f '' S) (f p) hy
  refine ⟨x, hpreSub ?_, hxy⟩
  change f x ∈ C
  exact hxy.symm ▸ hy

/-- A genuine discontinuity interval is relatively open in the actual geometric circle. -/
theorem IsFuchsianIntervalOfDiscontinuity.isOpen {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    IsOpen (((↑) : frontier D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' I) := by
  have : LocallyPathConnectedSpace (frontier D.carrier) :=
    complexDisc_frontier_locallyPathConnected D.isDisc
  obtain ⟨p, hp, hIp⟩ := hI.1
  let U := (((↑) : frontier D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹'
    fuchsianBoundaryOrdinarySet D)
  let x : frontier D.carrier := ⟨p, hp.1⟩
  have hx : x ∈ U := hp
  have himg : ((↑) : frontier D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' U =
      fuchsianBoundaryOrdinarySet D := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hz
      exact ⟨⟨z, hz.1⟩, hz, rfl⟩
  have hc := embedding_image_connectedComponentIn
    (Topology.IsEmbedding.subtypeVal (p := (· ∈ frontier D.carrier))) U x hx
  rw [himg] at hc
  have he : (((↑) : frontier D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' I) = connectedComponentIn U x := by
    rw [hIp, ← hc, preimage_image_eq _ Subtype.val_injective]
  rw [he]
  exact (fuchsianBoundaryOrdinarySet_isOpen D).connectedComponentIn

theorem IsFuchsianIntervalOfDiscontinuity.ne_frontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I) :
    I ≠ frontier D.carrier := hI.2

/-- Relative connected-component maximality is literal maximality among connected ordinary subsets. -/
theorem IsFuchsianIntervalOfDiscontinuity.maximal {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I J : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I)
    (hJ : IsPreconnected J) (hJO : J ⊆ fuchsianBoundaryOrdinarySet D) (hIJ : I ⊆ J) : J ⊆ I := by
  obtain ⟨p, hp, hIp⟩ := hI.1
  rw [hIp] at hIJ ⊢
  exact hJ.subset_connectedComponentIn (hIJ (mem_connectedComponentIn hp)) hJO

theorem fuchsianLimitEndpoints_invariant (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g : H)
    {p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hp : p ∈ fuchsianLimitEndpoints H) :
    g • p ∈ fuchsianLimitEndpoints H := by
  obtain ⟨f, hft, hfp⟩ := hp
  refine ⟨g * f * g⁻¹, ?_, ?_⟩
  · rcases hft with hP | hL
    · exact Or.inl ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨g.val,
      rfl⟩)).mp hP)
    · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusLoxodromic_conjugation_forward f.val g.val hL)
  · change (g * f * g⁻¹) • (g • p) = g • p
    rw [mul_smul, mul_smul, inv_smul_smul]
    change g • (f.val.val p) = g • p
    rw [hfp]

theorem fuchsianLimitEndpoints_image (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g
  : H) :
    g.val.val '' fuchsianLimitEndpoints H = fuchsianLimitEndpoints H := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact fuchsianLimitEndpoints_invariant H g hp
  · intro p hp
    exact ⟨g⁻¹ • p, fuchsianLimitEndpoints_invariant H g⁻¹ hp, smul_inv_smul g p⟩

theorem fuchsianLimitSet_image (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g : H) :
    g.val.val '' fuchsianLimitSet H = fuchsianLimitSet H := by
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    g.val) '' closure (fuchsianLimitEndpoints H) = _
  rw [Homeomorph.image_closure]
  exact congrArg closure (fuchsianLimitEndpoints_image H g)

theorem fuchsianBoundaryOrdinarySet_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (g : H) :
    g.val.val '' fuchsianBoundaryOrdinarySet D = fuchsianBoundaryOrdinarySet D := by
  unfold fuchsianBoundaryOrdinarySet
  rw [image_sdiff g.val.val.injective, fuchsianLimitSet_image]
  have hfront : g.val.val '' frontier D.carrier = frontier D.carrier := by
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph g.val) '' frontier D.carrier = _
    rw [Homeomorph.image_frontier]
    exact congrArg frontier (D.image_eq g)
  rw [hfront]

/-- The original group permutes its actual open discontinuity intervals. -/
theorem IsFuchsianIntervalOfDiscontinuity.image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {I : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hI :
      IsFuchsianIntervalOfDiscontinuity D I)
    (g : H) : IsFuchsianIntervalOfDiscontinuity D (g.val.val '' I) := by
  obtain ⟨p, hp, hIp⟩ := hI.1
  refine ⟨⟨g • p, ?_, ?_⟩, ?_⟩
  · rw [← fuchsianBoundaryOrdinarySet_image D g]
    exact mem_image_of_mem g.val.val hp
  · rw [hIp]
    have hc := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
      g.val).image_connectedComponentIn hp
    change g.val.val '' connectedComponentIn (fuchsianBoundaryOrdinarySet D) p =
      connectedComponentIn (g.val.val '' fuchsianBoundaryOrdinarySet D) (g • p) at hc
    rwa [fuchsianBoundaryOrdinarySet_image D g] at hc
  · intro he
    have hfront : g.val.val '' frontier D.carrier = frontier D.carrier := by
      change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph g.val) '' frontier D.carrier = _
      rw [Homeomorph.image_frontier]
      exact congrArg frontier (D.image_eq g)
    exact hI.2 (g.val.val.injective.image_injective (he.trans hfront.symm))

/-- Boundary hyperbolicity is invariant under conjugacy inside the original group. -/
theorem IsBoundaryHyperbolic.conjugate {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {f : H} (hf : IsBoundaryHyperbolic D f) (g : H) :
    IsBoundaryHyperbolic D (g * f * g⁻¹) := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f.val g.val hf.1, ?_⟩
  obtain ⟨I, hI, hp⟩ := hf.2
  refine ⟨g.val.val '' I, hI.image g, ?_⟩
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image g.val f.val I).trans (congrArg
    (g.val.val '' ·) hp)

end LowDimensionalTopology.Geometry.Fuchsian
