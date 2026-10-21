module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Area
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonCycles
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenOriginalRegion
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance coreSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance coreSphereBorelSpace : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- The actual Nielsen region, as a subset of the original invariant disc points. -/
def fuchsianNielsenCore
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hH : DiscreteGroups.IsNonElementary H) : Set P.domain.carrier :=
  Subtype.val ⁻¹' P.asFuchsianDisc.nielsenRegion hH

theorem fuchsianNielsenCore_isOpen {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hH : DiscreteGroups.IsNonElementary H) : IsOpen (fuchsianNielsenCore P hH) :=
  (P.asFuchsianDisc.nielsenRegion_properties hH).2.2.1.preimage continuous_subtype_val

theorem fuchsianNielsenCore_invariant {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hH : DiscreteGroups.IsNonElementary H) :
    ∀ g : H, ∀ x ∈ fuchsianNielsenCore P hH, g • x ∈ fuchsianNielsenCore P hH := by
  intro g x hx
  exact (P.asFuchsianDisc.nielsenRegion_properties hH).2.2.2.2 g x.val hx

/-- Restriction to a genuine invariant measurable set preserves actual hyperbolic-area invariance. -/
theorem fuchsian_area_restrict_invariant {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) (hS : MeasurableSet S)
    (hInv : ∀ g : H, ∀ x ∈ S, g • x ∈ S) :
    SMulInvariantMeasure H P.domain.carrier (P.area.restrict S) := by
  have hiff (g : H) (x : P.domain.carrier) : g • x ∈ S ↔ x ∈ S :=
    ⟨fun hx => by simpa only [inv_smul_smul] using hInv g⁻¹ (g • x) hx, hInv g x⟩
  constructor
  intro g t ht
  rw [Measure.restrict_apply (ht.preimage (measurable_const_smul g)), Measure.restrict_apply ht]
  have he : ((fun x : P.domain.carrier => g • x) ⁻¹' t) ∩ S =
      (fun x : P.domain.carrier => g • x) ⁻¹' (t ∩ S) := by
    ext x
    change (g • x ∈ t ∧ x ∈ S) ↔ (g • x ∈ t ∧ g • x ∈ S)
    rw [hiff]
  rw [he]
  exact SMulInvariantMeasure.measure_preimage_smul g (ht.inter hS)

/-- Every original fundamental domain has the same genuine area inside an invariant measurable set. -/
theorem fuchsianFundamentalDomain_invariant_inter_area_eq
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) (hS : MeasurableSet S)
    (hInv : ∀ g : H, ∀ x ∈ S, g • x ∈ S) {D₁ D₂ : Set P.domain.carrier}
    (h₁ : IsFuchsianFundamentalDomain P D₁) (h₂ : IsFuchsianFundamentalDomain P D₂) :
    P.area (D₁ ∩ S) = P.area (D₂ ∩ S) := by
  let : Countable H := P.countable
  let ν := P.area.restrict S
  have hν : ν ≪ P.area := Measure.restrict_le_self.absolutelyContinuous
  have : SMulInvariantMeasure H P.domain.carrier ν := fuchsian_area_restrict_invariant P S hS hInv
  obtain ⟨F₁, hF₁, hDF₁, hFC₁⟩ := h₁.exists_fundamentalSet
  obtain ⟨F₂, hF₂, hDF₂, hFC₂⟩ := h₂.exists_fundamentalSet
  have hfd₁ : MeasureTheory.IsFundamentalDomain H F₁ ν :=
    (Fuchsian.IsFuchsianFundamentalSet.measureFundamentalDomain (P := P) hF₁
      (h₁.nullMeasurableSet_between hDF₁ hFC₁)).mono hν
  have hfd₂ : MeasureTheory.IsFundamentalDomain H F₂ ν :=
    (Fuchsian.IsFuchsianFundamentalSet.measureFundamentalDomain (P := P) hF₂
      (h₂.nullMeasurableSet_between hDF₂ hFC₂)).mono hν
  have hAE₁ : F₁ =ᵐ[ν] D₁ := hν (DiscreteGroups.Action.IsFundamentalDomain.ae_eq_of_between H P.domain.carrier h₁ hDF₁
    hFC₁)
  have hAE₂ : F₂ =ᵐ[ν] D₂ := hν (DiscreteGroups.Action.IsFundamentalDomain.ae_eq_of_between H P.domain.carrier h₂ hDF₂
    hFC₂)
  have he : ν D₁ = ν D₂ := (measure_congr hAE₁.symm).trans
    (hfd₁.measure_eq hfd₂ |>.trans (measure_congr hAE₂))
  change P.area.restrict S D₁ = P.area.restrict S D₂ at he
  rwa [Measure.restrict_apply h₁.isOpen.measurableSet, Measure.restrict_apply h₂.isOpen.measurableSet] at he

/-- The original Nielsen-core area, with no finite-generation or finite-side assumption. -/
def fuchsianNielsenCoreArea {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hH : DiscreteGroups.IsNonElementary H)
    (D : Set P.domain.carrier) : ℝ≥0∞ :=
  P.area (D ∩ fuchsianNielsenCore P hH)

/--
The actual area of the polygon inside the actual Nielsen region is independent
of the original chosen fundamental polygon. The stronger result holds for every fundamental domain.
-/
theorem fuchsianNielsenCoreArea_independent
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hH : DiscreteGroups.IsNonElementary H)
    {D₁ D₂ : Set P.domain.carrier}
    (h₁ : IsFuchsianFundamentalDomain P D₁) (h₂ : IsFuchsianFundamentalDomain P D₂) :
    fuchsianNielsenCoreArea P hH D₁ = fuchsianNielsenCoreArea P hH D₂ :=
  fuchsianFundamentalDomain_invariant_inter_area_eq P _ (fuchsianNielsenCore_isOpen P hH).measurableSet
    (fuchsianNielsenCore_invariant P hH) h₁ h₂

end LowDimensionalTopology.Geometry.Fuchsian
