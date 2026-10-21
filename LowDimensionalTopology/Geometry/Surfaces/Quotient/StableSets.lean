module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.Mobius
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.EuclideanQuotientSurfaces
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenAxes
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Analysis.Convex.Contractible
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicBoundary
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
@[expose] public section
noncomputable section
open Set Filter Topology
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/--
Every translate of an actual subset of the sphere either
coincides with it or is disjoint from it.
-/
def MobiusStableSet (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (S : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : Prop :=
  ∀ g ∈ G, g.val '' S = S ∨ Disjoint (g.val '' S) S

/-- The set stabilizer inside the specified actual Mobius subgroup. -/
def mobiusSetStabilizer (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (S : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := G ⊓ MulAction.stabilizer _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup S

theorem mem_mobiusSetStabilizer (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (S : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : g ∈ mobiusSetStabilizer G S ↔ g ∈ G ∧ g.val '' S = S := Iff.rfl

theorem mobiusSetStabilizer_le (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (S : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    mobiusSetStabilizer G S ≤ G := fun _ hg => hg.1

theorem mobiusStableSet_iff_separated (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (S
  : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    MobiusStableSet G S ↔ ∀ g ∈ G, g ∉ mobiusSetStabilizer G S → Disjoint (g.val '' S) S := by
  constructor
  · intro h g hg hn
    rcases h g hg with he | hd
    · exact False.elim (hn ⟨hg, he⟩)
    · exact hd
  · intro h g hg
    by_cases he : g ∈ mobiusSetStabilizer G S
    · exact Or.inl he.2
    · exact Or.inr (h g hg he)

theorem mobiusStableSet_mem_stabilizer_of_intersection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {S : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hS : MobiusStableSet G S) (g :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g ∈ G)
    (hne : (g.val '' S ∩ S).Nonempty) : g ∈ mobiusSetStabilizer G S := by
  rcases hS g hg with he | hd
  · exact ⟨hg, he⟩
  · rcases hne with ⟨z, hz₁, hz₂⟩
    exact False.elim (Set.disjoint_left.mp hd hz₁ hz₂)

/--
An arbitrary stable subset of the geometric actual invariant domain. It need not be open,
connected, or nonempty.
-/
structure MobiusStableSubset {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  MobiusInvariantDomain G) where
  carrier : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
  subset_domain : carrier ⊆ D.carrier
  stable : MobiusStableSet G carrier

def MobiusStableSubset.stabilizer {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset
      D) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := mobiusSetStabilizer G S.carrier

theorem MobiusStableSubset.stabilizer_le {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) : S.stabilizer ≤ G := mobiusSetStabilizer_le G S.carrier

theorem MobiusStableSubset.stabilizer_preserves {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (g : S.stabilizer) : g.val.val '' S.carrier = S.carrier := g.property.2

theorem MobiusStableSubset.separated {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D
  : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g ∈ G) (hn :
      g ∉ S.stabilizer) :
    Disjoint (g.val '' S.carrier) S.carrier := (mobiusStableSet_iff_separated G S.carrier).mp S.stable g hg hn

/-- The actual stabilizer-orbit quotient with its quotient topology. The relation is the
restriction of the genuine Mobius orbit relation to the actual subset. -/
abbrev MobiusStableSubset.Quotient {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) :=
  _root_.Quotient ((MulAction.orbitRel S.stabilizer _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
    (Subtype.val : S.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))

/-- Its genuine image, with the subspace topology of the full-group quotient. -/
abbrev MobiusStableSubset.quotientImage {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) := mobiusDiscQuotientImage D S.carrier S.subset_domain

/-- Equality in the full orbit quotient is exactly equality in the stabilizer quotient
when both representatives lie in the stable subset. -/
theorem MobiusStableSubset.orbitRel_iff_projection_eq {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (z w : S.carrier) :
    (MulAction.orbitRel S.stabilizer _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap (Subtype.val :
      S.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z w ↔
      mobiusDiscRangeProjection D S.carrier S.subset_domain z =
        mobiusDiscRangeProjection D S.carrier S.subset_domain w := by
  constructor
  · rintro ⟨g, hg⟩
    apply Subtype.ext
    apply _root_.Quotient.sound
    exact ⟨⟨g.val, S.stabilizer_le g.property⟩, Subtype.ext hg⟩
  · intro hzw
    have he : mobiusDiscDomainProjection D S.carrier S.subset_domain z =
        mobiusDiscDomainProjection D S.carrier S.subset_domain w := congrArg Subtype.val hzw
    obtain ⟨g, hg⟩ := _root_.Quotient.exact he
    have hgw : g.val.val w.val = z.val := congrArg Subtype.val hg
    have hgS : g.val ∈ S.stabilizer := mobiusStableSet_mem_stabilizer_of_intersection S.stable
      g.val g.property ⟨z.val, ⟨w.val, w.property, hgw⟩, z.property⟩
    exact ⟨⟨g.val, hgS⟩, hgw⟩

/-- The canonical map sends a stabilizer orbit to the same full-group orbit. -/
def MobiusStableSubset.quotientMap {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) : S.Quotient → S.quotientImage :=
  _root_.Quotient.lift (mobiusDiscRangeProjection D S.carrier S.subset_domain)
    (fun z w hzw => (S.orbitRel_iff_projection_eq z w).mp hzw)

theorem MobiusStableSubset.quotientMap_apply_mk {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (z : S.carrier) :
    S.quotientMap (_root_.Quotient.mk _ z) = mobiusDiscRangeProjection D S.carrier S.subset_domain z := rfl

theorem MobiusStableSubset.quotientMap_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) : Continuous S.quotientMap :=
  continuous_quot_lift _ ((mobiusDiscDomainProjection_continuous D S.carrier S.subset_domain).subtype_mk _)

theorem MobiusStableSubset.quotientMap_bijective {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) : Function.Bijective S.quotientMap := by
  constructor
  · intro u v
    refine _root_.Quotient.inductionOn₂ u v ?_
    intro z w hzw
    exact _root_.Quotient.sound ((S.orbitRel_iff_projection_eq z w).mpr hzw)
  · rintro ⟨_x, z, rfl⟩
    exact ⟨_root_.Quotient.mk _ z, rfl⟩

/-- With openness in the actual ambient invariant domain. -/
def MobiusStableSubset.openQuotientHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hS : IsOpen (Subtype.val ⁻¹' S.carrier : Set D.carrier)) : S.Quotient ≃ₜ S.quotientImage := by
  have hSo : IsOpen S.carrier := by
    have ho := D.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hS
    have he : (Subtype.val : D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' (Subtype.val ⁻¹' S.carrier) = S.carrier := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, S.subset_domain hz⟩, hz, rfl⟩
    exact he ▸ ho
  exact mobiusDiscOrbitQuotientHomeomorph D S.stabilizer S.carrier S.subset_domain hSo
    S.stabilizer_le (fun g hg hn => S.separated g hg hn)

/--
compactness is imposed on the genuine stabilizer quotient,
not on the subset itself. Discontinuity supplies Hausdorffness of the full quotient.
-/
def MobiusStableSubset.compactQuotientHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) [CompactSpace S.Quotient] : S.Quotient ≃ₜ S.quotientImage := by
  let : T2Space (MobiusDomainQuotient D) := mobiusDomainQuotient_t2 D hD
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective S.quotientMap S.quotientMap_bijective)
    S.quotientMap_continuous

/-- Both source alternatives yield a homeomorphism for the actual canonical orbit map. -/
theorem stable_quotient_homeomorphic_image_of_open_or_compactQuotient {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier)
    (h : IsOpen (Subtype.val ⁻¹' S.carrier : Set D.carrier) ∨ CompactSpace S.Quotient) :
    Nonempty (S.Quotient ≃ₜ S.quotientImage) := by
  rcases h with ho | hc
  · exact ⟨S.openQuotientHomeomorph ho⟩
  · let : CompactSpace S.Quotient := hc
    exact ⟨S.compactQuotientHomeomorph hD⟩


/-- The open and compact-quotient homeomorphisms represent the canonical orbit map. -/
theorem MobiusStableSubset.openQuotientHomeomorph_apply_mk {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (ho : IsOpen (Subtype.val ⁻¹' S.carrier : Set D.carrier)) (z : S.carrier) :
    S.openQuotientHomeomorph ho (_root_.Quotient.mk _ z) =
      mobiusDiscRangeProjection D S.carrier S.subset_domain z := rfl

theorem MobiusStableSubset.compactQuotientHomeomorph_apply_mk {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) [CompactSpace
      S.Quotient] (z : S.carrier) :
    S.compactQuotientHomeomorph hD (_root_.Quotient.mk _ z) =
      mobiusDiscRangeProjection D S.carrier S.subset_domain z := rfl

theorem MobiusStableSubset.quotientMap_isEmbedding_of_open {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (ho : IsOpen (Subtype.val ⁻¹' S.carrier : Set D.carrier)) : Topology.IsEmbedding S.quotientMap := by
  have he : (S.openQuotientHomeomorph ho : S.Quotient → S.quotientImage) = S.quotientMap := by
    funext u
    exact _root_.Quotient.inductionOn u (fun _z => rfl)
  exact he ▸ (S.openQuotientHomeomorph ho).isEmbedding

theorem MobiusStableSubset.quotientMap_isEmbedding_of_compact {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) [CompactSpace
      S.Quotient] :
    Topology.IsEmbedding S.quotientMap :=
  (S.compactQuotientHomeomorph hD).isEmbedding

theorem MobiusStableSubset.quotientImage_compact {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) [CompactSpace S.Quotient] :
    IsCompact (S.quotientImage : Set (MobiusDomainQuotient D)) := by
  have hc := isCompact_range (continuous_subtype_val.comp S.quotientMap_continuous)
  have he : Set.range ((Subtype.val : S.quotientImage → MobiusDomainQuotient D) ∘ S.quotientMap) =
      S.quotientImage := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact (S.quotientMap u).property
    · intro hx
      obtain ⟨u, hu⟩ := S.quotientMap_bijective.2 ⟨x, hx⟩
      exact ⟨u, congrArg Subtype.val hu⟩
  exact he ▸ hc

/-- The actual half-open strip used. -/
def stableTranslationStrip : Set ℂ := {z | 0 ≤ z.re ∧ z.re < 1}

theorem stableTranslationStrip_convex : Convex ℝ stableTranslationStrip :=
  ((convex_Ici (0 : ℝ)).linear_preimage Complex.reLm).inter
    ((convex_Iio (1 : ℝ)).linear_preimage Complex.reLm)

theorem stableTranslationStrip_simplyConnected : SimplyConnectedSpace stableTranslationStrip := by
  let : ContractibleSpace stableTranslationStrip := stableTranslationStrip_convex.contractibleSpace
    ⟨0, by constructor <;> norm_num⟩
  infer_instance

/-- The punctured plane cannot be simply connected: a global lift of its identity through
exp would, by covering uniqueness, make the genuinely periodic exponential injective. -/
theorem complexPuncturedPlane_not_simplyConnected : ¬SimplyConnectedSpace {z : ℂ // z ≠ 0} := by
  intro hsc
  let : SimplyConnectedSpace {z : ℂ // z ≠ 0} := hsc
  let : LocallyPathConnectedSpace {z : ℂ // z ≠ 0} :=
    puncturedPlaneRiemannSurface.toRiemannAtlas.locallyPathConnectedSpace
  let p : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have hp : IsCoveringMap p := Complex.isCoveringMap_exp
  obtain ⟨F, ⟨hF, hpF⟩, _hFu⟩ := hp.existsUnique_continuousMap_lifts
    ⟨id, continuous_id⟩ (p 0) (0 : ℂ) rfl
  have hleft : Function.LeftInverse F p := by
    have he : (F ∘ p : ℂ → ℂ) = id := hp.eq_of_comp_eq (F.continuous.comp hp.continuous)
      continuous_id (by funext z; exact congrFun hpF (p z)) 0 hF
    exact fun z => congrFun he z
  have hperiod : p (2 * Real.pi * Complex.I) = p 0 := by
    apply Subtype.ext
    exact Complex.exp_two_pi_mul_I.trans Complex.exp_zero.symm
  have hn : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact hn (hleft.injective hperiod)

theorem stableTranslationStrip_not_homeomorphic_puncturedPlane :
    ¬Nonempty (stableTranslationStrip ≃ₜ {z : ℂ // z ≠ 0}) := by
  rintro ⟨E⟩
  let : SimplyConnectedSpace stableTranslationStrip := stableTranslationStrip_simplyConnected
  exact complexPuncturedPlane_not_simplyConnected
    (E.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance)


/-- The actual cyclic Mobius group generated by the unit translation. -/
def stableTranslationGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)

theorem stableTranslation_zpow (n : ℤ) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (1 : ℂ)) ^ n = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ) := by
  have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationMobiusHom.map_zpow (Multiplicative.ofAdd (1
    : ℂ)) n
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n • (1 :
    ℂ)) = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) ^ n at h
  simpa only [zsmul_eq_mul, mul_one] using h.symm

theorem stableTranslationGroup_mem (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    g ∈ stableTranslationGroup ↔ ∃ n : ℤ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ) := by
  rw [stableTranslationGroup, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm.trans (stableTranslation_zpow n)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, stableTranslation_zpow n⟩

theorem stableTranslationGroup_translations (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg :
  g ∈ stableTranslationGroup) :
    ∃ b : ℂ, g = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b := by
  obtain ⟨n, hn⟩ := (stableTranslationGroup_mem g).mp hg
  exact ⟨n, hn⟩

def stableTranslationDomain : MobiusInvariantDomain stableTranslationGroup :=
  translationPlaneDomain stableTranslationGroup stableTranslationGroup_translations

/-- The same half-open strip as an actual subset of the sphere's finite plane. -/
def stableTranslationStripSphere : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ((↑) : ℂ →
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' stableTranslationStrip

theorem stableTranslationStripSphere_subset : stableTranslationStripSphere ⊆ stableTranslationDomain.carrier := by
  rintro _ ⟨z, _hz, rfl⟩
  exact ⟨z, rfl⟩

theorem stableTranslationStripSphere_stable : MobiusStableSet stableTranslationGroup stableTranslationStripSphere := by
  intro g hg
  obtain ⟨n, rfl⟩ := (stableTranslationGroup_mem g).mp hg
  by_cases hn : n = 0
  · subst n
    left
    simp only [Int.cast_zero]
    rw [(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_eq_one_iff 0).mpr rfl]
    exact Set.image_id _
  · right
    apply Set.disjoint_left.mpr
    rintro x ⟨_y, ⟨z, hz, rfl⟩, rfl⟩ ⟨w, hw, he⟩
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe] at he
    have heq : w = z + (n : ℂ) := OnePoint.coe_injective he
    have hre : w.re = z.re + (n : ℝ) := by simpa using congrArg Complex.re heq
    have hlo : (-1 : ℝ) < n := by linarith [hz.2, hw.1]
    have hhi : (n : ℝ) < 1 := by linarith [hz.1, hw.2]
    have hl : (-1 : ℤ) < n := by exact_mod_cast hlo
    have hh : n < (1 : ℤ) := by exact_mod_cast hhi
    exact hn (by omega)

def stableTranslationSubset : MobiusStableSubset stableTranslationDomain where
  carrier := stableTranslationStripSphere
  subset_domain := stableTranslationStripSphere_subset
  stable := stableTranslationStripSphere_stable

theorem stableTranslationSubset_stabilizer : stableTranslationSubset.stabilizer = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  change g = 1
  obtain ⟨n, hn⟩ := (stableTranslationGroup_mem g).mp hg.1
  have hzero : ((0 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ stableTranslationSubset.carrier :=
    ⟨0, by constructor <;> norm_num, rfl⟩
  have hgz : g.val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ stableTranslationSubset.carrier := by
    have him : g.val ((0 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ g.val '' stableTranslationSubset.carrier := ⟨_,
      hzero, rfl⟩
    exact hg.2 ▸ him
  rw [hn, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe, zero_add] at hgz
  obtain ⟨z, hz, he⟩ := hgz
  have heq : z = (n : ℂ) := OnePoint.coe_injective he
  have hnr : 0 ≤ (n : ℝ) ∧ (n : ℝ) < 1 := by
    change 0 ≤ z.re ∧ z.re < 1 at hz
    rw [heq] at hz
    simpa using hz
  have hni : 0 ≤ n ∧ n < 1 := by exact_mod_cast hnr
  have hn0 : n = 0 := by omega
  rw [hn, hn0]
  simpa only [Int.cast_zero] using (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_eq_one_iff
    0).mpr rfl

def stableTranslationStripHomeomorph : stableTranslationStrip ≃ₜ stableTranslationStripSphere :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage stableTranslationStrip

/-- The stabilizer quotient in the original counterexample really is the simply connected strip. -/
def stableTranslationSubsetQuotientHomeomorph : stableTranslationSubset.Quotient ≃ₜ stableTranslationStrip := by
  refine (Homeomorph.Quotient.congrRight (r' := (⊥ : Setoid stableTranslationSubset.carrier)) ?_).trans
    (Homeomorph.quotientBot.trans stableTranslationStripHomeomorph.symm)
  intro z w
  change (MulAction.orbitRel stableTranslationSubset.stabilizer
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z.val w.val ↔ z = w
  constructor
  · rintro ⟨g, hg⟩
    have hg1 : g.val = 1 := by simpa only [stableTranslationSubset_stabilizer, Subgroup.mem_bot] using g.property
    apply Subtype.ext
    change g.val.val w.val = z.val at hg
    rw [hg1] at hg
    exact hg.symm
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

/-- The actual translation coefficients are exactly the integer periods. -/
theorem stableTranslationGroup_displacements :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.translationDisplacements stableTranslationGroup = AddSubgroup.zmultiples (1 : ℂ) := by
  ext b
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_translationDisplacements, stableTranslationGroup_mem,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_injective hn).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, congrArg _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (by simpa only [zsmul_eq_mul, mul_one] using hn.symm)⟩

/-- The full quotient in the original example is the genuine punctured plane. -/
def stableTranslationDomainQuotientHomeomorph : MobiusDomainQuotient stableTranslationDomain ≃ₜ {z : ℂ // z ≠ 0} :=
  (translationPlaneQuotientHomeomorph stableTranslationGroup stableTranslationGroup_translations).trans
    ((complexAddQuotientCongr _ _ stableTranslationGroup_displacements).trans
      (complexCyclicQuotientHomeomorph 1 one_ne_zero))


/-- Every actual full-group orbit meets the half-open strip, via the real-part floor. -/
theorem stableTranslationSubset_quotientImage : stableTranslationSubset.quotientImage = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine _root_.Quotient.inductionOn x ?_
  intro z
  let E := translationPlaneHomeomorph stableTranslationGroup stableTranslationGroup_translations
  let w : ℂ := E.symm z
  let n : ℤ := ⌊w.re⌋
  let u : ℂ := w - (n : ℂ)
  have hu : u ∈ stableTranslationStrip := by
    change 0 ≤ u.re ∧ u.re < 1
    dsimp only [u]
    simp only [Complex.sub_re, Complex.intCast_re]
    exact ⟨sub_nonneg.mpr (Int.floor_le w.re), by linarith [Int.lt_floor_add_one w.re]⟩
  have hzd : z.val = (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := (congrArg Subtype.val
    (E.apply_symm_apply z)).symm
  let g : stableTranslationGroup :=
    ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((-n : ℤ) : ℂ), (stableTranslationGroup_mem
      _).mpr ⟨-n, rfl⟩⟩
  refine ⟨⟨(u : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨u, hu, rfl⟩⟩, ?_⟩
  apply _root_.Quotient.sound
  refine ⟨g, Subtype.ext ?_⟩
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((-n : ℤ) : ℂ)).val z.val = (u :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [hzd, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
  congr 1
  simp only [u, Int.cast_neg, sub_eq_add_neg]

def stableTranslationImageHomeomorph : stableTranslationSubset.quotientImage ≃ₜ {z : ℂ // z ≠ 0} :=
  (Homeomorph.setCongr stableTranslationSubset_quotientImage).trans
    ((Homeomorph.Set.univ _).trans stableTranslationDomainQuotientHomeomorph)

/--
The two actual orbit spaces are not even homeomorphic, despite
their canonical continuous bijection.
-/
theorem stable_translation_quotient_not_homeomorphic_image :
    ¬Nonempty (stableTranslationSubset.Quotient ≃ₜ stableTranslationSubset.quotientImage) := by
  rintro ⟨E⟩
  exact stableTranslationStrip_not_homeomorphic_puncturedPlane
    ⟨stableTranslationSubsetQuotientHomeomorph.symm.trans (E.trans stableTranslationImageHomeomorph)⟩


/-- The unit-translation group satisfies the original compact-set discontinuity condition
on the whole actual finite plane, not merely on an auxiliary fundamental strip. -/
theorem stableTranslationDomain_discontinuous :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn stableTranslationGroup stableTranslationDomain.carrier := by
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype
    stableTranslationGroup stableTranslationDomain.carrier
    stableTranslationDomain.invariant).mpr
  intro K hK
  let E := translationPlaneHomeomorph stableTranslationGroup stableTranslationGroup_translations
  obtain ⟨R, _hRpos, hR⟩ := (hK.image E.symm.continuous).isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R)
  let φ : ℤ → stableTranslationGroup := fun n =>
    ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ), (stableTranslationGroup_mem _).mpr
      ⟨n, rfl⟩⟩
  apply ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).image φ).subset
  rintro g ⟨v, ⟨u, hu, hguv⟩, hv⟩
  obtain ⟨n, hn⟩ := (stableTranslationGroup_mem g.val).mp g.property
  have huv (q : stableTranslationDomain.carrier) : q.val = (E.symm q : ℂ) :=
    (congrArg Subtype.val (E.apply_symm_apply q)).symm
  have he : E.symm v = E.symm u + (n : ℂ) := by
    have he' := congrArg Subtype.val hguv
    change g.val.val u.val = v.val at he'
    rw [hn, huv u, huv v, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe] at he'
    exact (OnePoint.coe_injective he').symm
  have hnN : ‖(n : ℂ)‖ ≤ 2 * R := by
    have hsub : (n : ℂ) = E.symm v - E.symm u := by rw [he]; ring
    rw [hsub]
    exact (norm_sub_le _ _).trans (by
      have hvR := hR _ ⟨v, hv, rfl⟩
      have huR := hR _ ⟨u, hu, rfl⟩
      linarith)
  have habs : |(n : ℝ)| ≤ 2 * R := by
    have hre : |(n : ℝ)| ≤ ‖(n : ℂ)‖ := by simpa only [Complex.intCast_re] using Complex.abs_re_le_norm (n : ℂ)
    exact hre.trans hnN
  have hnl : -(N : ℝ) ≤ (n : ℝ) := by linarith [(abs_le.mp habs).1]
  have hnu : (n : ℝ) ≤ N := (abs_le.mp habs).2.trans hN.le
  have hni : -(N : ℤ) ≤ n ∧ n ≤ N := by
    constructor
    · exact_mod_cast hnl
    · exact_mod_cast hnu
  exact ⟨n, hni, Subtype.ext hn.symm⟩

theorem stableTranslationSubsetQuotient_simplyConnected : SimplyConnectedSpace stableTranslationSubset.Quotient :=
  stableTranslationSubsetQuotientHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr
    stableTranslationStrip_simplyConnected

theorem stableTranslationImage_not_simplyConnected : ¬SimplyConnectedSpace stableTranslationSubset.quotientImage := by
  intro hsc
  exact complexPuncturedPlane_not_simplyConnected
    (stableTranslationImageHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mp hsc)

/-- All parts of the original counterexample use the actual specified translation action. -/
theorem stableTranslation_discontinuous_simplyConnected_quotient_nonsimplyConnected_image_not_homeomorphic :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn stableTranslationGroup stableTranslationDomain.carrier ∧
      SimplyConnectedSpace stableTranslationSubset.Quotient ∧
      ¬SimplyConnectedSpace stableTranslationSubset.quotientImage ∧
      ¬Nonempty (stableTranslationSubset.Quotient ≃ₜ stableTranslationSubset.quotientImage) :=
  ⟨stableTranslationDomain_discontinuous, stableTranslationSubsetQuotient_simplyConnected,
    stableTranslationImage_not_simplyConnected, stable_translation_quotient_not_homeomorphic_image⟩


open scoped UpperHalfPlane
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace



/-- Preservation of the real half-plane and the actual imaginary axis preserves its two
actual ideal endpoints. -/
theorem stableAxis_mobius_endpoints_preserved (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hL : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) : f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer := by
  change f.val '' {((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ∞} = {((0 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ∞}
  let F := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph f
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxis_idealEndpoints]
  change F '' (closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis ∩
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) = _
  rw [image_inter F.injective, F.image_closure,
    show F '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis from hL,
    show F '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary from _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_mobius_boundary_preserved f hH]

/-- The only obstruction to fixing both ends is a genuine order-two elliptic swapping them. -/
theorem stableAxis_mobius_endpoints_fixed (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hL : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hno : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f ^ 2 ≠ 1) : f.val (0 : ℂ) = (0 : ℂ) ∧ f.val ∞ = ∞ := by
  rcases _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_zeroInftyPair_cases ⟨f,
    stableAxis_mobius_endpoints_preserved f hH hL⟩ with hfix | hswap
  · exact hfix
  · change f.val (0 : ℂ) = ∞ ∧ f.val ∞ = (0 : ℂ) at hswap
    have hn : f ≠ 1 := by
      intro hf
      have he := hswap.1
      rw [hf] at he
      exact OnePoint.coe_ne_infty (0 : ℂ) he
    have hs : f ^ 2 = 1 := by
      simpa only [pow_two] using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square f hswap.1 hswap.2
    exact False.elim (hno (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic f hn
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hs⟩)) hs)

/-- The entire actual axis stabilizer is positive real scaling once endpoint exchanges
of order two are excluded. -/
theorem stableAxis_mobius_positive_scaling (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hL : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hno : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f ^ 2 ≠ 1) :
    ∃ r : ℝ, ∃ hr : 0 < r, f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')) := by
  obtain ⟨hzero, hinfty⟩ := stableAxis_mobius_endpoints_fixed f hH hL hno
  obtain ⟨a, ha⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_fix_zero_infty_eq_scaling f hzero hinfty
  have hI : ((Complex.I : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
    refine ⟨0, ?_⟩
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_coe]
  have hFI : f.val ((Complex.I : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis :=
    hL ▸ ⟨_, hI, rfl⟩
  obtain ⟨t, ht⟩ := hFI
  rw [ha, _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe] at ht
  have he : (Real.exp t : ℂ) * Complex.I = (a : ℂ) * Complex.I := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_coe] using OnePoint.coe_injective ht
  have har : (a : ℂ) = (Real.exp t : ℂ) := mul_right_cancel₀ Complex.I_ne_zero he.symm
  refine ⟨Real.exp t, Real.exp_pos t, ?_⟩
  rw [ha]
  exact congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.ext har)

/-- Evaluating the genuine scaling at one recovers its complex multiplier. -/
theorem stableAxis_scaling_injective : Function.Injective _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling := by
  intro a b hab
  apply Units.ext
  have he := congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f.val ((1 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hab
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe, mul_one, mul_one] at he
  exact OnePoint.coe_injective he

/-- The multiplier of a positive actual dilation is the given positive real number. -/
theorem stableAxis_positive_multiplier (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 :
      ℂ))
    (f : H) (r : ℝ) (hr : 0 < r)
    (hf : f.val = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (r : ℂ)
      (Complex.ofReal_ne_zero.mpr hr.ne'))) :
    ((_root_.LowDimensionalTopology.Geometry.Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ) = (r : ℂ) := by
  exact congrArg (fun a : ℂˣ => (a : ℂ)) (stableAxis_scaling_injective
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_multiplier_representation H hi hz f).symm.trans
      hf))

/-- A group of genuine positive dilations has no nontrivial logarithmic kernel. -/
theorem stableAxis_positive_log_kernel (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 :
      ℂ))
    (hp : ∀ f ∈ H, ∃ r : ℝ, ∃ hr : 0 < r,
      f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr
        hr.ne'))) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilationRotationKernel H hi = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨r, hr, hfr⟩ := hp f.val f.property
  have hnorm := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilationRotationKernel_mem_iff H hi f).mp hf
  rw [stableAxis_positive_multiplier H hi hz f r hr hfr, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr] at hnorm
  change f = 1
  apply Subtype.ext
  rw [hfr]
  have he : Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne') = 1 :=
    Units.ext (by simpa using congrArg (fun t : ℝ => (t : ℂ)) hnorm)
  rw [he, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_one]
  rfl

/-- A discrete subgroup consisting of actual positive real dilations is cyclic. -/
theorem stableAxis_positive_discrete_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hp : ∀ f ∈ H, ∃ r : ℝ, ∃ hr : 0 < r,
      f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne'))) : IsCyclic H := by
  have hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := hp f hf
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty _
  have hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ) := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := hp f hf
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _
  let φ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilationLogModulusHom H hi
  have hφ : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    exact stableAxis_positive_log_kernel H hi hz hp
  let : IsAddCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilationLogModulusRange H
    hi) := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilationLogModulusRange_isAddCyclic H hd hi hz
  let F : Additive H →+ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilationLogModulusRange H hi := φ.toAdditiveLeft.rangeRestrict
  have hFi : Function.Injective F := by
    intro a b hab
    exact hφ (congrArg (fun z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilationLogModulusRange H hi =>
      z.val) hab)
  let : IsAddCyclic (Additive H) := isAddCyclic_of_injective F hFi
  exact isAddCyclic_additive_iff.mp inferInstance

/--
The full actual stabilizer of the imaginary axis is cyclic under precisely the
order-two exclusion.
-/
theorem stableAxis_stabilizer_isCyclic (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G)
    (hH : ∀ f ∈ G, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hno : ∀ f ∈ G, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f ^ 2 ≠ 1) :
    IsCyclic (mobiusSetStabilizer G _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) := by
  let : DiscreteTopology G := hd
  apply stableAxis_positive_discrete_isCyclic _
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.subgroup_discrete (mobiusSetStabilizer_le G
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis))
  intro f hf
  exact stableAxis_mobius_positive_scaling f (hH f hf.1) hf.2 (hno f hf.1)

/-- The actual imaginary geodesic is a topological real line via its hyperbolic parameter. -/
def stableAxisParamHomeomorph : ℝ ≃ₜ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
  have h : Topology.IsEmbedding (fun t : ℝ => _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam t)) := by
    have he := OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryEuclideanAxis_isometry.isEmbedding.comp
        Real.isOpenEmbedding_exp.isEmbedding)
    simpa only [Function.comp_def, _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_coe] using he
  exact h.toHomeomorph

@[simp] theorem stableAxisParamHomeomorph_coe (t : ℝ) :
    (stableAxisParamHomeomorph t : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam t) := rfl

/-- The genuine positive dilation with logarithmic displacement `l`. -/
def stableAxisDilation (l : ℝ) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 ((Real.exp l : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l)))

/-- Powers of the actual dilation translate the real geodesic parameter. -/
theorem stableAxisDilation_zpow_param (l t : ℝ) (n : ℤ) :
    (stableAxisDilation l ^ n).val (stableAxisParamHomeomorph t :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      (stableAxisParamHomeomorph (t + n * l) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom _ ^ n).val _ = _
  rw [← map_zpow, stableAxisParamHomeomorph_coe, stableAxisParamHomeomorph_coe]
  simp only [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_coe]
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling ((Units.mk0 ((Real.exp l : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l))) ^ n)).val
      ((((Real.exp t : ℝ) : ℂ) * Complex.I : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      ((((Real.exp (t + n * l) : ℝ) : ℂ) * Complex.I : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  apply OnePoint.coe_injective
  have he : ((Real.exp l : ℝ) : ℂ) ^ n = (Real.exp (n * l) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.exp_int_mul]
  rw [he, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [add_comm (n * l) t]

/-- The restricted genuine Mobius orbit relation is the ordinary real period relation. -/
theorem stableAxisDilation_orbitRel_iff (l s t : ℝ) :
    (MulAction.orbitRel (Subgroup.zpowers (stableAxisDilation l))
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (stableAxisParamHomeomorph s :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (stableAxisParamHomeomorph t :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ↔
      -s + t ∈ AddSubgroup.zmultiples l := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨n, hn⟩ := f.property
    change f.val.val (stableAxisParamHomeomorph t :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _ at hf
    rw [← hn, stableAxisDilation_zpow_param] at hf
    have he : t + n * l = s := stableAxisParamHomeomorph.injective (Subtype.ext hf)
    refine ⟨-n, ?_⟩
    change (-n) • l = -s + t
    rw [zsmul_eq_mul, Int.cast_neg]
    linarith
  · rintro ⟨n, hn⟩
    change n • l = -s + t at hn
    rw [zsmul_eq_mul] at hn
    refine ⟨⟨stableAxisDilation l ^ (-n), ⟨-n, rfl⟩⟩, ?_⟩
    change (stableAxisDilation l ^ (-n)).val (stableAxisParamHomeomorph t :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    rw [stableAxisDilation_zpow_param]
    have he : t + (-n : ℤ) * l = s := by
      rw [Int.cast_neg]
      linarith
    rw [he]

/-- The actual stabilizer-orbit quotient of the imaginary axis is the native additive circle. -/
def stableAxisDilationQuotientHomeomorph (l : ℝ) :
    _root_.Quotient ((MulAction.orbitRel (Subgroup.zpowers (stableAxisDilation l))
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (Subtype.val : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ≃ₜ AddCircle l := by
  exact (Homeomorph.Quotient.congr stableAxisParamHomeomorph.symm (fun z w => by
    change (MulAction.orbitRel _ _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z.val w.val ↔
      (QuotientAddGroup.leftRel (AddSubgroup.zmultiples l)) _ _
    rw [QuotientAddGroup.leftRel_apply]
    have he := stableAxisDilation_orbitRel_iff l
      (stableAxisParamHomeomorph.symm z) (stableAxisParamHomeomorph.symm w)
    simpa only [Homeomorph.apply_symm_apply] using he))

/-- For a nonzero displacement the actual geodesic quotient is homeomorphic to the
ordinary unit circle. -/
def stableAxisDilationQuotientCircle (l : ℝ) (hl : l ≠ 0) :
    _root_.Quotient ((MulAction.orbitRel (Subgroup.zpowers (stableAxisDilation l))
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (Subtype.val : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis →
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ≃ₜ Circle :=
  (stableAxisDilationQuotientHomeomorph l).trans (AddCircle.homeomorphCircle hl)

/-- Reversing the logarithmic parameter inverts the genuine dilation. -/
theorem stableAxisDilation_neg (l : ℝ) : stableAxisDilation (-l) = (stableAxisDilation l)⁻¹ := by
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom _ = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom _)⁻¹
  rw [← map_inv]
  congr 1
  apply Units.ext
  simp [Real.exp_neg]

/-- Every nontrivial discrete positive dilation group has a generator translating the
actual geodesic parameter by a strictly positive real number. -/
theorem stableAxis_positive_generator (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hn : H ≠ ⊥)
    (hp : ∀ f ∈ H, ∃ r : ℝ, ∃ hr : 0 < r,
      f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr
        hr.ne'))) :
    ∃ l : ℝ, 0 < l ∧ H = Subgroup.zpowers (stableAxisDilation l) := by
  have hc := stableAxis_positive_discrete_isCyclic H hd hp
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hc
  obtain ⟨r, hr, hgr⟩ := hp g (hg ▸ Subgroup.mem_zpowers g)
  have hge : g = stableAxisDilation (Real.log r) := by
    rw [hgr]
    change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _ = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _
    apply congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    apply Units.ext
    simp only [Units.val_mk0, Real.exp_log hr]
  have hl : Real.log r ≠ 0 := by
    intro he
    apply hn
    rw [← hg, hge, he]
    have hz : stableAxisDilation 0 = 1 := by simp [stableAxisDilation, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_one]
    rw [hz, Subgroup.zpowers_one_eq_bot]
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · refine ⟨-Real.log r, neg_pos.mpr hneg, ?_⟩
    rw [stableAxisDilation_neg, Subgroup.zpowers_inv, ← hge, hg]
  · exact ⟨Real.log r, hpos, by rw [← hge, hg]⟩

/-- The original quotient of any stable actual imaginary axis is the ordinary circle
when its full stabilizer is this nontrivial dilation group. -/
def MobiusStableSubset.axisQuotientCircle {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hS : S.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) (l : ℝ) (hl : l ≠ 0)
    (hK : S.stabilizer = Subgroup.zpowers (stableAxisDilation l)) : S.Quotient ≃ₜ Circle := by
  refine (Homeomorph.Quotient.congr (Homeomorph.setCongr hS) ?_).trans
    (stableAxisDilationQuotientCircle l hl)
  intro z w
  change (MulAction.orbitRel S.stabilizer _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z.val w.val ↔
    (MulAction.orbitRel (Subgroup.zpowers (stableAxisDilation l))
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z.val w.val
  rw [hK]

/-- A stable actual hyperbolic axis gives an embedded genuine circle in the full-group
quotient, using compactness of the axis quotient rather than compactness of the axis. -/
theorem MobiusStableSubset.axis_simpleClosedCurve {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hS : S.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) (l : ℝ) (hl : l ≠ 0)
    (hK : S.stabilizer = Subgroup.zpowers (stableAxisDilation l)) :
    ∃ e : Circle → MobiusDomainQuotient D, Topology.IsEmbedding e ∧ Set.range e = S.quotientImage := by
  let C := S.axisQuotientCircle hS l hl hK
  let : CompactSpace S.Quotient := C.symm.compactSpace
  let F := S.compactQuotientHomeomorph hD
  refine ⟨fun x => (F (C.symm x)).val,
    Topology.IsEmbedding.subtypeVal.comp (F.isEmbedding.comp C.symm.isEmbedding), ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (F (C.symm x)).property
  · intro hy
    refine ⟨C (F.symm ⟨y, hy⟩), ?_⟩
    simp only [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]

/--
In its genuine normalized upper-half-plane coordinates. Any nontrivial
axis-preserving element suffices to make the full stable-axis image a simple closed curve.
-/
theorem normalized_axis_stabilizer_cyclic_quotient_circle_embeds {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hH : ∀ f ∈ G, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hno : ∀ f ∈ G, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f ^ 2 ≠ 1)
    (hS : S.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g ∈ G) (hgn : g ≠ 1)
    (hgL : g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) :
    ∃ l : ℝ, 0 < l ∧ S.stabilizer = Subgroup.zpowers (stableAxisDilation l) ∧
      Nonempty (S.Quotient ≃ₜ Circle) ∧
      ∃ e : Circle → MobiusDomainQuotient D,
        Topology.IsEmbedding e ∧ Set.range e = S.quotientImage := by
  have hdG : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete G D.carrier D.invariant D.isConnected.nonempty hD
  let : DiscreteTopology G := hdG
  have hdK : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup S.stabilizer := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.subgroup_discrete S.stabilizer_le
  have hnK : S.stabilizer ≠ ⊥ := by
    intro he
    have hgK : g ∈ S.stabilizer := by
      change g ∈ mobiusSetStabilizer G S.carrier
      apply (mem_mobiusSetStabilizer G S.carrier g).mpr
      exact ⟨hg, by simpa only [hS] using hgL⟩
    rw [he] at hgK
    exact hgn hgK
  have hp : ∀ f ∈ S.stabilizer, ∃ r : ℝ, ∃ hr : 0 < r,
      f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')) := by
    intro f hf
    change f ∈ mobiusSetStabilizer G S.carrier at hf
    have hf' := (mem_mobiusSetStabilizer G S.carrier f).mp hf
    exact stableAxis_mobius_positive_scaling f (hH f hf'.1)
      (by simpa only [hS] using hf'.2) (hno f hf'.1)
  obtain ⟨l, hl, hK⟩ := stableAxis_positive_generator S.stabilizer hdK hnK hp
  exact ⟨l, hl, hK, ⟨S.axisQuotientCircle hS l hl.ne' hK⟩,
    S.axis_simpleClosedCurve hD hS l hl.ne' hK⟩


/-- Conjugation transports the original restricted orbit quotient with its original topology. -/
def stableAxisConjugateQuotientHomeomorph (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (S : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    _root_.Quotient ((MulAction.orbitRel H _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (Subtype.val : S → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ≃ₜ
    _root_.Quotient ((MulAction.orbitRel
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (Subtype.val : (q.val '' S) → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) := by
  let E := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).isEmbedding.homeomorphImage S
  refine Homeomorph.Quotient.congr E ?_
  intro z w
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨⟨q * f.val * q⁻¹, ⟨f.val, f.property, rfl⟩⟩, ?_⟩
    change q.val (f.val.val (q.val.symm (q.val w.val))) = q.val z.val
    rw [Equiv.symm_apply_apply]
    exact congrArg q.val hf
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg, hgf⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f.val).mp f.property
    refine ⟨⟨g, hg⟩, ?_⟩
    change f.val.val (q.val w.val) = q.val z.val at hf
    rw [← hgf] at hf
    change q.val (g.val (q.val.symm (q.val w.val))) = q.val z.val at hf
    rw [Equiv.symm_apply_apply] at hf
    exact q.val.injective hf

/-- Positive-determinant real matrices act on the genuine open half-plane bijectively. -/
theorem stableAxis_real_normalizer_halfPlane (a : GL (Fin 2) ℝ) (ha : 0 < a.val.det) :
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix a)).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have hmem (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp : p ∈
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
      ∃ z : ℍ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint z = p := by
    induction p using OnePoint.rec with
    | infty => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet] at hp
    | coe z => exact ⟨⟨z, (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet z).mp hp⟩, rfl⟩
  apply Set.Subset.antisymm
  · rintro p ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := hmem z hz
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection_apply]
    change _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix a) (((w : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realMobiusMatrix_coe a ha]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet _).mpr (a • w).im_pos
  · intro p hp
    obtain ⟨w, rfl⟩ := hmem p hp
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (a⁻¹ • w),
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet _).mpr (a⁻¹ • w).im_pos, ?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection_apply]
    change _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix a) (((a⁻¹ • w : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realMobiusMatrix_coe a ha]
    simp only [smul_inv_smul]
    rfl

/-- Every native half-plane line has an actual Mobius normalizer to the full imaginary axis. -/
theorem stableAxis_nativeLine_normalizer (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      q.val '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' L.carrier) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
  obtain ⟨a, ha, hL⟩ := L.exists_normalizer
  let q := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix a)
  refine ⟨q, stableAxis_real_normalizer_halfPlane a ha, ?_⟩
  ext p
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [hL] at hz
    have hz0 : (a • z).re = 0 := hz
    have ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (Real.log (a • z).im) = a • z := by
      apply UpperHalfPlane.ext_re_im
      · exact hz0.symm
      · exact Real.exp_log (a • z).im_pos
    refine ⟨Real.log (a • z).im, ?_⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (Real.log (a • z).im)) = q.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint z)
    rw [ht]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realMobiusMatrix_coe a ha z).symm
  · rintro ⟨t, rfl⟩
    let z := a⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam t
    have hz : z ∈ L.carrier := by
      rw [hL]
      change (a • (a⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam t)).re = 0
      simp only [smul_inv_smul]
      rfl
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint z, ⟨z, hz, rfl⟩, ?_⟩
    change _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix a) (((z : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realMobiusMatrix_coe a ha]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (a • (a⁻¹ •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam t)) = _
    rw [smul_inv_smul]

/-- A true normalizer identifies the original axis quotient with a circle; the
restricted group remains the actual conjugate Mobius subgroup. -/
theorem MobiusStableSubset.normalizedAxis_quotient_circle {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G)
    (hH : ∀ f ∈ G, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hno : ∀ f ∈ G, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f ^ 2 ≠ 1)
    (hn : S.stabilizer ≠ ⊥) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hqH : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hqS : q.val '' S.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) :
    ∃ l : ℝ, 0 < l ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer =
      Subgroup.zpowers (stableAxisDilation l) ∧ Nonempty (S.Quotient ≃ₜ Circle) := by
  let : DiscreteTopology G := hd
  let : DiscreteTopology S.stabilizer := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.subgroup_discrete S.stabilizer_le
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer
  have hdK : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q S.stabilizer
  have hnK : K ≠ ⊥ := by
    intro he
    apply hn
    apply le_antisymm _ bot_le
    intro f hf
    have hc : q * f * q⁻¹ ∈ K := ⟨f, hf, rfl⟩
    rw [he] at hc
    change q * f * q⁻¹ = 1 at hc
    apply (MulAut.conj q).injective
    simpa only [map_one, MulAut.conj_apply] using hc
  have hpK : ∀ f ∈ K, ∃ r : ℝ, ∃ hr : 0 < r,
      f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q S.stabilizer f).mp hf
    have hgf := (mem_mobiusSetStabilizer G S.carrier g).mp hg
    apply stableAxis_mobius_positive_scaling
    · simpa only [hqH, hH g hgf.1] using _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image q g _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    · simpa only [hqS,
      hgf.2] using _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image q g S.carrier
    · intro he hs
      apply hno g hgf.1 ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g q).mp he)
      apply (MulAut.conj q).injective
      rw [map_pow, map_one]
      exact hs
  obtain ⟨l, hl, hK⟩ := stableAxis_positive_generator K hdK hnK hpK
  refine ⟨l, hl, hK, ⟨?_⟩⟩
  let E := stableAxisConjugateQuotientHomeomorph S.stabilizer S.carrier q
  refine (E.trans (Homeomorph.Quotient.congr (Homeomorph.setCongr hqS) ?_)).trans
    (stableAxisDilationQuotientCircle l hl.ne')
  intro z w
  change (MulAction.orbitRel K _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z.val w.val ↔
    (MulAction.orbitRel (Subgroup.zpowers (stableAxisDilation l))
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z.val w.val
  rw [hK]

/-- A genuine circle quotient makes the canonical image an embedded circle. -/
theorem MobiusStableSubset.simpleClosedCurve_of_quotientCircle {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (C : S.Quotient ≃ₜ
      Circle) :
    ∃ e : Circle → MobiusDomainQuotient D, Topology.IsEmbedding e ∧ Set.range e = S.quotientImage := by
  let : CompactSpace S.Quotient := C.symm.compactSpace
  let F := S.compactQuotientHomeomorph hD
  refine ⟨fun x => (F (C.symm x)).val,
    Topology.IsEmbedding.subtypeVal.comp (F.isEmbedding.comp C.symm.isEmbedding), ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (F (C.symm x)).property
  · intro hy
    refine ⟨C (F.symm ⟨y, hy⟩), ?_⟩
    simp only [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]

/--
For an arbitrary genuine native upper-half-plane geodesic.
The order-two elliptic exclusion is exactly the source exclusion, and compactness is
proved for the true stabilizer quotient.
-/
theorem axis_stabilizer_cyclic_quotient_circle_embeds {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hH : ∀ f ∈ G, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hno : ∀ f ∈ G, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f ^ 2 ≠ 1)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (hS : S.carrier =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' L.carrier)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g ∈ G) (hgn : g ≠ 1)
    (hgL : g.val '' S.carrier = S.carrier) :
    IsCyclic S.stabilizer ∧ Nonempty (S.Quotient ≃ₜ Circle) ∧
      ∃ e : Circle → MobiusDomainQuotient D,
        Topology.IsEmbedding e ∧ Set.range e = S.quotientImage := by
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete G D.carrier D.invariant D.isConnected.nonempty hD
  have hn : S.stabilizer ≠ ⊥ := by
    intro he
    have hgK : g ∈ S.stabilizer := (mem_mobiusSetStabilizer G S.carrier g).mpr ⟨hg, hgL⟩
    rw [he] at hgK
    exact hgn hgK
  obtain ⟨q, hqH, hqL⟩ := stableAxis_nativeLine_normalizer L
  have hqS : q.val '' S.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by rw [hS, hqL]
  obtain ⟨l, _hl, hK, ⟨C⟩⟩ := S.normalizedAxis_quotient_circle hd hH hno hn q hqH hqS
  have hcK : IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer) := by
    rw [hK]
    infer_instance
  have hc : IsCyclic S.stabilizer := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q S.stabilizer).isCyclic.mpr hcK
  exact ⟨hc, ⟨C⟩, S.simpleClosedCurve_of_quotientCircle hD C⟩

/-- A nonunit actual scaling agrees with the corresponding standard geometric form. -/
theorem stableAxis_scaling_eq_standard (a : ℂˣ) (ha : (a : ℂ) ≠ 1) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement a := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty,
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_infty]
  | coe z => rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_coe, ite_eq_right ha]

/-- The positive generator is a genuine hyperbolic Mobius map. -/
theorem stableAxisDilation_hyperbolic (l : ℝ) (hl : 0 < l) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (stableAxisDilation l) := by
  let a : ℂˣ := Units.mk0 ((Real.exp l : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l))
  have hr : 1 < Real.exp l := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hl
  have ha : (a : ℂ) ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    change Real.exp l = 1 at hre
    exact hr.ne' hre
  change _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a)
  rw [stableAxis_scaling_eq_standard a ha]
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_positive_isHyperbolic a
  · exact Complex.ofReal_im _
  · exact Real.exp_pos l
  · simpa only [a, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos l)] using hr.ne'

/-- Actual subgroup conjugation recovers an actual generator in the original group. -/
theorem stableAxis_conjugate_generator (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q a : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hK :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H = Subgroup.zpowers a) :
    H = Subgroup.zpowers (q⁻¹ * a * q) := by
  apply Subgroup.map_injective (f := (MulAut.conj q).toMonoidHom) (MulAut.conj q).injective
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H = _
  rw [hK, MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/--
includes a genuine hyperbolic generator of the full original axis
stabilizer, as well as the canonical simple closed curve in the full quotient.
-/
theorem hyperbolic_axis_stabilizer_generated_quotient_circle_embeds {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hH : ∀ f ∈ G, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hno : ∀ f ∈ G, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f ^ 2 ≠ 1)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (hS : S.carrier =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' L.carrier)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g ∈ G) (hgh :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g)
    (hgL : g.val '' S.carrier = S.carrier) :
    (∃ h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic h ∧ S.stabilizer = Subgroup.zpowers h) ∧
      Nonempty (S.Quotient ≃ₜ Circle) ∧
      ∃ e : Circle → MobiusDomainQuotient D,
        Topology.IsEmbedding e ∧ Set.range e = S.quotientImage := by
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete G D.carrier D.invariant D.isConnected.nonempty hD
  have hn : S.stabilizer ≠ ⊥ := by
    intro he
    have hgK : g ∈ S.stabilizer := (mem_mobiusSetStabilizer G S.carrier g).mpr ⟨hg, hgL⟩
    rw [he] at hgK
    exact hgh.1.1 hgK
  obtain ⟨q, hqH, hqL⟩ := stableAxis_nativeLine_normalizer L
  have hqS : q.val '' S.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by rw [hS, hqL]
  obtain ⟨l, hl, hK, ⟨C⟩⟩ := S.normalizedAxis_quotient_circle hd hH hno hn q hqH hqS
  have hgen := stableAxis_conjugate_generator S.stabilizer q (stableAxisDilation l) hK
  have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (q⁻¹ * stableAxisDilation l * q) := by
    simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward
      (stableAxisDilation l) q⁻¹ (stableAxisDilation_hyperbolic l hl)
  exact ⟨⟨_, hh, hgen⟩, ⟨C⟩, S.simpleClosedCurve_of_quotientCircle hD C⟩



open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The surface interpretation of the analytic remark uses a genuine open connected
stable subdomain, with the original actual set-stabilizer action. -/
def MobiusStableSubset.openDomain {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) : MobiusInvariantDomain S.stabilizer where
  carrier := S.carrier
  isOpen := hSo
  isConnected := hSc
  invariant := by
    intro g z hz
    exact S.stabilizer_preserves g ▸ ⟨z, hz, rfl⟩

/-- The actual original compact-hit condition restricts to the actual stable subdomain. -/
theorem MobiusStableSubset.openDomain_discontinuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn S.stabilizer (S.openDomain hSo hSc).carrier := by
  intro K hK hKS
  let i : S.stabilizer → G := fun g => ⟨g.val, S.stabilizer_le g.property⟩
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (congrArg (fun g : G => g.val) hab)
  have hf := hD K hK (hKS.trans S.subset_domain)
  exact Set.Finite.preimage (f := i) hi.injOn hf

/-- The surface-domain quotient and the already-defined restricted orbit quotient have
exactly the same original quotient topology. -/
def MobiusStableSubset.openDomainQuotientHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    MobiusDomainQuotient (S.openDomain hSo hSc) ≃ₜ S.Quotient := by
  refine Homeomorph.Quotient.congrRight ?_
  intro z w
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

/-- The actual inclusion-induced map on the original surface quotients. -/
def MobiusStableSubset.openDomainQuotientMap {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    MobiusDomainQuotient (S.openDomain hSo hSc) → MobiusDomainQuotient D :=
  fun x => (S.quotientMap (S.openDomainQuotientHomeomorph hSo hSc x)).val

theorem MobiusStableSubset.openDomainQuotientMap_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    Continuous (S.openDomainQuotientMap hSo hSc) :=
  continuous_subtype_val.comp (S.quotientMap_continuous.comp
    (S.openDomainQuotientHomeomorph hSo hSc).continuous)

@[simp] theorem MobiusStableSubset.openDomainQuotientMap_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) (z : S.carrier) :
    S.openDomainQuotientMap hSo hSc (mobiusDomainProjection (S.openDomain hSo hSc) z) =
      mobiusDomainProjection D ⟨z.val, S.subset_domain z.property⟩ := rfl

/-- A genuine stabilizer-quotient power chart extends unchanged to the whole group:
stability separates the translates belonging to other cosets. -/
def MobiusQuotientChartData.extendStable {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (C : MobiusQuotientChartData (S.openDomain hSo hSc)) : MobiusQuotientChartData D where
  stabilizer := C.stabilizer
  finiteStabilizer := C.finiteStabilizer
  normalizer := C.normalizer
  fixInfty := C.fixInfty
  fixZero := C.fixZero
  radius := C.radius
  radius_pos := C.radius_pos
  disc_subset := C.disc_subset.trans S.subset_domain
  stabilizer_le := C.stabilizer_le.trans S.stabilizer_le
  separated := by
    intro g hg hn
    by_cases hgs : g ∈ S.stabilizer
    · exact C.separated g hgs hn
    · exact (S.separated g hg hgs).mono (image_mono C.disc_subset) C.disc_subset

/-- The canonical stable-subdomain quotient map is genuinely analytic for the original
branched atlases, including at elliptic branch values. -/
theorem MobiusStableSubset.openDomainQuotientMap_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    RiemannAnalyticMap
      (mobiusQuotientRiemannSurface (S.openDomain hSo hSc) (S.openDomain_discontinuous hD hSo hSc)).toRiemannAtlas
      (mobiusQuotientRiemannSurface D hD).toRiemannAtlas (S.openDomainQuotientMap hSo hSc) := by
  rw [riemannAnalyticMap_iff_locally]
  refine ⟨S.openDomainQuotientMap_continuous hSo hSc, ?_⟩
  intro x
  obtain ⟨z, rfl⟩ := mobiusDomainProjection_surjective (S.openDomain hSo hSc) x
  obtain ⟨C, hzC⟩ := mobiusQuotientChartData_containing (S.openDomain hSo hSc)
    (S.openDomain_discontinuous hD hSo hSc) z
  let E := C.extendStable S hSo hSc
  have hx : mobiusDomainProjection (S.openDomain hSo hSc) z ∈ C.chart.source :=
    C.projection_mem_source ⟨z.val, hzC⟩
  have hy : S.openDomainQuotientMap hSo hSc
      (mobiusDomainProjection (S.openDomain hSo hSc) z) ∈ E.chart.source := by
    have hp := S.openDomainQuotientMap_projection hSo hSc z
    exact hp.symm ▸ E.projection_mem_source ⟨z.val, hzC⟩
  refine ⟨C.chart, ⟨C, rfl⟩, hx, E.chart, ⟨E, rfl⟩, hy, ?_⟩
  apply analyticAt_id.congr
  filter_upwards [C.chart.open_target.mem_nhds (C.chart.map_source hx)] with w hw
  obtain ⟨a, ha⟩ := C.chart_source ▸ C.chart.map_target hw
  change mobiusDomainProjection (S.openDomain hSo hSc)
    ⟨a.val, C.disc_subset a.property⟩ = C.chart.symm w at ha
  have hC : C.chart (mobiusDomainProjection (S.openDomain hSo hSc)
      ⟨a.val, C.disc_subset a.property⟩) = w := by rw [ha, C.chart.right_inv hw]
  have hE : E.chart (mobiusDomainProjection D ⟨a.val, S.subset_domain (C.disc_subset a.property)⟩) =
      C.chart (mobiusDomainProjection (S.openDomain hSo hSc) ⟨a.val, C.disc_subset a.property⟩) := by
    exact (E.chart_apply_projection a).trans (C.chart_apply_projection a).symm
  change w = E.chart (S.openDomainQuotientMap hSo hSc (C.chart.symm w))
  rw [← ha]
  have hp := S.openDomainQuotientMap_projection hSo hSc
    (⟨a.val, C.disc_subset a.property⟩ : S.carrier)
  exact hC.symm.trans (hE.symm.trans (congrArg E.chart hp.symm))

/-- The actual stable open-subdomain image is open in the original full quotient. -/
theorem MobiusStableSubset.quotientImage_isOpen {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (hSo : IsOpen S.carrier) :
    IsOpen (S.quotientImage : Set (MobiusDomainQuotient D)) :=
  mobiusDiscQuotientImage_isOpen D S.carrier S.subset_domain hSo

/-- The actual image retains connectedness of the stable subdomain. -/
theorem MobiusStableSubset.quotientImage_isConnected {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (hSc : IsConnected S.carrier) :
    IsConnected (S.quotientImage : Set (MobiusDomainQuotient D)) := by
  let : ConnectedSpace S.carrier := Subtype.connectedSpace hSc
  exact isConnected_range (mobiusDiscDomainProjection_continuous D S.carrier S.subset_domain)

/-- The genuine inherited Riemann surface on the actual open quotient image. -/
def MobiusStableSubset.openImageRiemannSurface {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) : RiemannSurface S.quotientImage where
  toRiemannAtlas := (mobiusQuotientRiemannSurface D hD).toRiemannAtlas.liftLocalHomeomorph
    (Subtype.val : S.quotientImage → MobiusDomainQuotient D)
    (S.quotientImage_isOpen hSo).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  t2Space := by
    let : T2Space (MobiusDomainQuotient D) := mobiusDomainQuotient_t2 D hD
    infer_instance
  connectedSpace := Subtype.connectedSpace (S.quotientImage_isConnected hSc)

/-- The canonical topological identification between the genuine subdomain quotient
and its actual image in the whole quotient. -/
def MobiusStableSubset.openDomainImageHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    MobiusDomainQuotient (S.openDomain hSo hSc) ≃ₜ S.quotientImage :=
  (S.openDomainQuotientHomeomorph hSo hSc).trans
    (S.openQuotientHomeomorph (hSo.preimage continuous_subtype_val))

/-- The canonical topological homeomorphism is exactly the original orbit map. -/
theorem MobiusStableSubset.openDomainImageHomeomorph_coe {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (x : MobiusDomainQuotient (S.openDomain hSo hSc)) :
    (S.openDomainImageHomeomorph hSo hSc x).val = S.openDomainQuotientMap hSo hSc x := by
  induction x using _root_.Quotient.inductionOn with
  | h z =>
    change (S.openQuotientHomeomorph (hSo.preimage continuous_subtype_val)
      (_root_.Quotient.mk _ z)).val = (S.quotientMap (_root_.Quotient.mk _ z)).val
    let w : S.carrier := ⟨z.val, z.property⟩
    have h₁ := S.openQuotientHomeomorph_apply_mk (hSo.preimage continuous_subtype_val) w
    have h₂ := S.quotientMap_apply_mk w
    exact congrArg (fun y : S.quotientImage => y.val) (h₁.trans h₂.symm)

/-- The topological identification is analytic in the genuine inherited image atlas. -/
theorem MobiusStableSubset.openDomainImageHomeomorph_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    RiemannAnalyticMap
      (mobiusQuotientRiemannSurface (S.openDomain hSo hSc) (S.openDomain_discontinuous hD hSo hSc)).toRiemannAtlas
      (S.openImageRiemannSurface hD hSo hSc).toRiemannAtlas (S.openDomainImageHomeomorph hSo hSc) := by
  have hinc := (mobiusQuotientRiemannSurface D hD).toRiemannAtlas.liftLocalHomeomorph_projection_analytic
    (Subtype.val : S.quotientImage → MobiusDomainQuotient D)
    (S.quotientImage_isOpen hSo).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph hinc
    (S.quotientImage_isOpen hSo).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (S.openDomainImageHomeomorph hSo hSc).continuous
  have he : (Subtype.val : S.quotientImage → MobiusDomainQuotient D) ∘
      (S.openDomainImageHomeomorph hSo hSc) = S.openDomainQuotientMap hSo hSc := by
    funext x
    exact S.openDomainImageHomeomorph_coe hSo hSc x
  rw [he]
  exact S.openDomainQuotientMap_analytic hD hSo hSc

/-- The analytic stable-quotient remark, under its necessary surface-domain reading.
The complex structures are the original branched quotient and the genuine inherited
open-image structure, without excluding elliptic elements. -/
theorem mobius_stable_quotient_conformallyEquivalent {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    RiemannConformallyEquivalent
      (mobiusQuotientRiemannSurface (S.openDomain hSo hSc) (S.openDomain_discontinuous hD hSo hSc))
      (S.openImageRiemannSurface hD hSo hSc) :=
  ⟨S.openDomainImageHomeomorph hSo hSc, S.openDomainImageHomeomorph_analytic hD hSo hSc,
    (S.openDomainImageHomeomorph hSo hSc).bijective⟩


end LowDimensionalTopology.Geometry.Surfaces
