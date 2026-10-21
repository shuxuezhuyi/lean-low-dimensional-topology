module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FundamentalDomain
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianStabilizers
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Perfect
public import Mathlib.Tactic.Ext
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

local instance fuchsianSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance fuchsianSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The original actual Fuchsian action in the standard disc; elliptic stabilizers are allowed. -/
structure UnitDiscFuchsianGroup (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) where
  invariant : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  discontinuous : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc

/-- The same invariant disc points, with the actual Mobius group action. -/
def UnitDiscFuchsianGroup.domain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H := _root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H P.invariant

/-- The same genuine finite coordinate, explicitly typed with its standard disc measurable structure. -/
def UnitDiscFuchsianGroup.finiteCoordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    P.domain.carrier ≃ₜ Complex.UnitDisc := _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph

/-- The actual density area transported from the finite unit-disc coordinate. -/
def UnitDiscFuchsianGroup.area {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H) :
    Measure P.domain.carrier := Measure.map P.finiteCoordinate.symm _root_.LowDimensionalTopology.Geometry.Surfaces.discNativeAreaMeasure

/-- This is the usual density-weighted area on the actual corresponding finite disc set. -/
theorem UnitDiscFuchsianGroup.area_apply {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (s : Set P.domain.carrier) (hs : MeasurableSet s) :
    P.area s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.finiteCoordinate '' s) := by
  have he : P.finiteCoordinate.symm ⁻¹' s = P.finiteCoordinate '' s :=
    (P.finiteCoordinate.toEquiv.image_eq_preimage_symm s).symm
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.area, Measure.map_apply
    P.finiteCoordinate.symm.continuous.measurable hs,
    he, _root_.LowDimensionalTopology.Geometry.Surfaces.discNativeAreaMeasure_apply _ (P.finiteCoordinate.measurableEmbedding.measurableSet_image.mpr hs)]

theorem UnitDiscFuchsianGroup.image_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (g : H) : g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact P.invariant g z hz
  · intro z hz
    exact ⟨g⁻¹ • z, P.invariant g⁻¹ z hz, smul_inv_smul g z⟩

/-- The native finite-disc coordinate intertwines the original Mobius action exactly. -/
theorem UnitDiscFuchsianGroup.finite_smul {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (g : H) (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (hform : g.val.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation a c hdet) (x :
      P.domain.carrier) :
    P.finiteCoordinate (g • x) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet (P.finiteCoordinate x) := by
  change _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph (g • x) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph x)
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm.injective
  apply Subtype.val_injective
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm_apply_apply,
    _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe,
    ← _root_.LowDimensionalTopology.Geometry.Surfaces.discFractionalHomeomorph_actual g.val a c hdet hform]
  change g.val.val x.val = g.val.val (((P.finiteCoordinate x : Complex.UnitDisc) : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  apply congrArg g.val.val
  exact (congrArg Subtype.val (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm_apply_apply
    x)).symm.trans
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (P.finiteCoordinate x))

/-- Every actual Fuchsian map preserves the genuine hyperbolic area. -/
theorem UnitDiscFuchsianGroup.area_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (g : H) (s : Set P.domain.carrier) (hs : MeasurableSet s) :
    P.area ((fun x : P.domain.carrier => g • x) '' s) = P.area s := by
  obtain ⟨a, c, hdet,
    hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form g.val (P.image_eq g)
  have hsm : MeasurableSet ((fun x : P.domain.carrier => g • x) '' s) :=
    (Homeomorph.smul g).measurableEmbedding.measurableSet_image.mpr hs
  rw [P.area_apply _ hsm, P.area_apply _ hs]
  have him : P.finiteCoordinate '' ((fun x : P.domain.carrier => g • x) '' s) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet '' (P.finiteCoordinate '' s) := by
    rw [image_image, image_image]
    exact Set.image_congr (fun x _ => P.finite_smul g a c hdet hform x)
  rw [him]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.normalizedDisc_hyperbolicArea a c hdet _
    (P.finiteCoordinate.measurableEmbedding.measurableSet_image.mpr hs)

/-- Fundamental sets for the actual disc action and its genuine area. -/
def IsFuchsianFundamentalDomain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) : Prop :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H P.domain.carrier P.area D

/-- The geometric exact point selector for the original Fuchsian orbits, including elliptic points. -/
def IsFuchsianFundamentalSet {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (F : Set P.domain.carrier) : Prop :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet H P.domain.carrier F

/-- Every orbit of the disc action admits a chosen representative, including elliptic orbits. -/
theorem exists_fuchsianFundamentalSet {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P
  : UnitDiscFuchsianGroup H) :
    ∃ F : Set P.domain.carrier, IsFuchsianFundamentalSet P F :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.exists_isFundamentalSet H P.domain.carrier

/-- Nonidentity actual Mobius maps have only finitely many boundary fixed points. -/
theorem mobius_boundary_fixed_finite (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ≠
  1) :
    {z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex | f.val z = z}.Finite := by
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_fixedPoint_dichotomy f hf with ⟨a, ha⟩ | ⟨a,
    b, _hab, hab⟩
  · have he : {z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex | f.val z = z} = {a} := by ext z; exact ha z
    rw [he]
    exact Set.finite_singleton a
  · have he : {z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex | f.val z = z} = {a,b} := by ext z; exact hab z
    rw [he]
    exact Set.toFinite _

/-- The actual action is locally effective, including Fuchsian groups with elliptics. -/
theorem UnitDiscFuchsianGroup.local_effective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H)
    (hfix : ∃ U : Set P.domain.carrier, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, g • x = x) : g = 1 := by
  by_contra hg
  have hgn : g.val ≠ 1 := fun he => hg (Subtype.ext he)
  obtain ⟨U, hU, ⟨x, hx⟩, hfix⟩ := hfix
  have hfin := mobius_boundary_fixed_finite g.val hgn
  have hUi : ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
    U).Finite :=
    hfin.subset (by rintro _ ⟨z, hz, rfl⟩; exact congrArg Subtype.val (hfix z hz))
  have hUo : IsOpen ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
    U) :=
    P.domain.isOpen.isOpenEmbedding_subtypeVal.isOpenMap U hU
  exact (infinite_of_mem_nhds x.val (hUo.mem_nhds ⟨x, hx, rfl⟩)) hUi

/-- The exact disjoint-tile assertion, with no local-effectivity premise. -/
theorem IsFuchsianFundamentalDomain.disjoint_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {g : H} (hg : g ≠ 1) :
    Disjoint ((fun x : P.domain.carrier => g • x) '' D) D :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.disjoint_image H P.domain.carrier hD (P.local_effective) hg

/-- The genuine closed disc tiles cover the original Fuchsian plane. -/
theorem IsFuchsianFundamentalDomain.closure_cover {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) :
    (⋃ g : H, (fun x : P.domain.carrier => g • x) '' closure D) = univ :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.iUnion_image_closure_eq_univ H P.domain.carrier hD

/-- The actual hyperbolic area is unchanged by choosing boundary representatives. -/
theorem IsFuchsianFundamentalDomain.area_between {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D F : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (hDF : D ⊆ F) (hFC : F ⊆ closure D) :
    P.area D = P.area F :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.measure_eq_of_between H P.domain.carrier hD hDF hFC

/-- Lebesgue measurability in the completed genuine area measure, not merely Borel measurability. -/
theorem IsFuchsianFundamentalDomain.nullMeasurableSet_between {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D F : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (hDF : D ⊆ F) (hFC : F ⊆ closure D) :
    NullMeasurableSet F P.area :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.nullMeasurableSet_of_between H P.domain.carrier hD hDF hFC

/-- For the genuine Fuchsian orbit quotients and actual closed domain. -/
theorem IsFuchsianFundamentalDomain.comparisonData {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.FundamentalDomainComparisonData H P.domain.carrier D :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.comparisonData H P.domain.carrier hD

/-- All three fundamental-domain conditions, using the genuine hyperbolic area. -/
theorem isFuchsianFundamentalDomain_iff {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    IsFuchsianFundamentalDomain P D ↔ IsOpen D ∧ IsConnected D ∧
      (∃ F : Set P.domain.carrier, IsFuchsianFundamentalSet P F ∧ D ⊆ F ∧ F ⊆ closure D) ∧
      P.area (frontier D) = 0 := by
  constructor
  · intro h
    exact ⟨h.isOpen, h.isConnected, h.exists_fundamentalSet, h.null_frontier⟩
  · rintro ⟨ho, hc, hf, hn⟩
    exact ⟨ho, hc, hf, hn⟩

/-- The actual closure identification quotient appearing. -/
abbrev FuchsianClosedDomainQuotient {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedOrbitQuotient H P.domain.carrier (closure D)

/-- The source's natural comparison map takes an actual closed-domain orbit intersection
into the original full Fuchsian orbit space. -/
def fuchsianDomainComparisonMap {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    FuchsianClosedDomainQuotient P D → _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.domain :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.comparisonMap H P.domain.carrier (closure D)

/-- The genuine projection square is the identity stated. -/
theorem fuchsianDomainComparisonMap_projection {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (z : closure D) :
    fuchsianDomainComparisonMap P D (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection H
      P.domain.carrier (closure D) z) =
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.domain z.val := rfl

theorem UnitDiscFuchsianGroup.isFuchsian {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup H :=
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc, P.invariant,
    P.discontinuous⟩

theorem UnitDiscFuchsianGroup.discrete {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc P.invariant
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc.isConnected.nonempty P.discontinuous

theorem UnitDiscFuchsianGroup.countable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup
      H) : Countable H := _root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable H P.discrete

/-- The true density area has no point masses. -/
instance UnitDiscFuchsianGroup.area_noAtoms {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : NullSingletonClass P.area where
  measure_singleton x := by
    rw [P.area_apply _ (measurableSet_singleton x)]
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaMeasure]

/-- The original actual group action preserves the genuine area measure. -/
instance UnitDiscFuchsianGroup.area_smulInvariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : SMulInvariantMeasure H P.domain.carrier P.area where
  measure_preimage_smul g s hs := by
    have he : (fun x : P.domain.carrier => g • x) ⁻¹' s =
        (fun x : P.domain.carrier => g⁻¹ • x) '' s := by
      ext x
      exact ⟨fun hx => ⟨g • x, hx, inv_smul_smul g x⟩,
        fun ⟨y, hy, he⟩ => by
          rw [← he]
          change g • (g⁻¹ • y) ∈ s
          simpa only [smul_inv_smul] using hy⟩
    rw [he]
    exact P.area_image g⁻¹ s hs

/-- The elliptic fixed points cause no artificial free-action hypothesis in area arguments. -/
theorem UnitDiscFuchsianGroup.fixed_null {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (hg : g ≠ 1) :
    P.area {x : P.domain.carrier | g • x = x} = 0 := by
  have hgn : g.val ≠ 1 := fun he => hg (Subtype.ext he)
  have hf := (mobius_boundary_fixed_finite g.val hgn).preimage
    (Subtype.val_injective.injOn : Set.InjOn (Subtype.val : P.domain.carrier →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) _)
  have hsub : {x : P.domain.carrier | g • x = x} ⊆
      Subtype.val ⁻¹' {z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex | g.val.val z = z} := by
    intro x hx
    exact congrArg (Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hx
  exact (hf.subset hsub).countable.measure_zero P.area

/--
The pointwise selector in this formulation is a Mathlib a.e. fundamental domain because all
nonidentity fixed sets have genuine area zero; no freeness assumption is imposed.
-/
theorem IsFuchsianFundamentalSet.measureFundamentalDomain {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {F : Set P.domain.carrier}
    (hF : IsFuchsianFundamentalSet P F) (hm : NullMeasurableSet F P.area) :
    MeasureTheory.IsFundamentalDomain H F P.area where
  nullMeasurableSet := hm
  ae_covers := Filter.Eventually.of_forall (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet.meetsEveryOrbit H P.domain.carrier hF)
  aedisjoint := by
    intro g k hne
    change P.area ((g • F) ∩ (k • F)) = 0
    apply measure_mono_null _ (P.fixed_null (k * g⁻¹) (by
      intro he
      exact hne (mul_inv_eq_one.mp he).symm))
    intro x hx
    obtain ⟨a, ha, hga⟩ := hx.1
    obtain ⟨b, hb, hkb⟩ := hx.2
    have hab : a = b := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet.eq_of_mem H P.domain.carrier hF ha hb
      ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul H P.domain.carrier g
        a).symm.trans
        ((congrArg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier)
          (hga.trans hkb.symm)).trans
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul H P.domain.carrier k b)))
    subst b
    change (k * g⁻¹) • x = x
    rw [mul_smul, ← hga, inv_smul_smul]
    exact hkb.trans hga.symm

/--
first assertion: every measurable exact fundamental set has the same
actual hyperbolic area, including actions with finite elliptic stabilizers.
-/
theorem fuchsianFundamentalSet_area_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {F₁ F₂ : Set P.domain.carrier}
    (h₁ : IsFuchsianFundamentalSet P F₁) (hm₁ : NullMeasurableSet F₁ P.area)
    (h₂ : IsFuchsianFundamentalSet P F₂) (hm₂ : NullMeasurableSet F₂ P.area) :
    P.area F₁ = P.area F₂ := by
  let : Countable H := P.countable
  exact (h₁.measureFundamentalDomain hm₁).measure_eq (h₂.measureFundamentalDomain hm₂)

end LowDimensionalTopology.Geometry.Fuchsian
