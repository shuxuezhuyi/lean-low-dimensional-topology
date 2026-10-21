module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FundamentalDomainMeasure
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Hyperbolic areas of Fuchsian fundamental sets

Measurable fundamental sets for the same unit-disc Fuchsian group have equal hyperbolic area.
For a subgroup, the area is multiplied by the extended coset cardinal; in finite index this is
the usual subgroup index. The final result transports area equality to fundamental domains by
choosing exact orbit representatives between each domain and its closure.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry.DiscreteGroups.Action
  (IsFundamentalSet fundamentalSet_subgroup_index_area)
open LowDimensionalTopology.Geometry.Mobius (ExtendedComplex complexMobiusGroup)

local instance indexSphereMeasurableSpace : MeasurableSpace ExtendedComplex := borel ExtendedComplex
local instance indexSphereBorelSpace : BorelSpace ExtendedComplex := ⟨rfl⟩

/--
The area of a subgroup fundamental set equals the area of a fundamental set for the original
group times the extended coset cardinal. Infinite index is included through `ENat.card`.
-/
theorem fuchsianFundamentalSet_subgroup_index_area {H : Subgroup complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (K : Subgroup H) {F₀ F₁ : Set P.domain.carrier}
    (h₀ : IsFundamentalSet K P.domain.carrier F₀) (hm₀ : NullMeasurableSet F₀ P.area)
    (h₁ : IsFuchsianFundamentalSet P F₁) (hm₁ : NullMeasurableSet F₁ P.area) :
    P.area F₀ = (ENat.card (H ⧸ K) : ℝ≥0∞) * P.area F₁ := by
  let : Countable H := P.countable
  exact fundamentalSet_subgroup_index_area K h₀ hm₀ h₁ hm₁ P.fixed_null

/-- In finite index the coefficient is the familiar natural-number subgroup index. -/
theorem fuchsianFundamentalSet_finite_index_area {H : Subgroup complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (K : Subgroup H) [Finite (H ⧸ K)]
    {F₀ F₁ : Set P.domain.carrier}
    (h₀ : IsFundamentalSet K P.domain.carrier F₀) (hm₀ : NullMeasurableSet F₀ P.area)
    (h₁ : IsFuchsianFundamentalSet P F₁) (hm₁ : NullMeasurableSet F₁ P.area) :
    P.area F₀ = (K.index : ℝ≥0∞) * P.area F₁ := by
  simpa only [ENat.card_eq_coe_natCard, ENat.toENNReal_coe, ← Subgroup.index_eq_card]
    using fuchsianFundamentalSet_subgroup_index_area P K h₀ hm₀ h₁ hm₁

/-- Fundamental sets for the same Fuchsian group have equal hyperbolic area, and a subgroup
fundamental set has area multiplied by the extended coset cardinal. -/
theorem fundamentalSet_area_eq_and_subgroup_area_eq_extendedIndex_mul
    {H : Subgroup complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {F₁ F₂ : Set P.domain.carrier}
    (h₁ : IsFuchsianFundamentalSet P F₁) (hm₁ : NullMeasurableSet F₁ P.area)
    (h₂ : IsFuchsianFundamentalSet P F₂) (hm₂ : NullMeasurableSet F₂ P.area)
    (K : Subgroup H) {F₀ : Set P.domain.carrier}
    (h₀ : IsFundamentalSet K P.domain.carrier F₀) (hm₀ : NullMeasurableSet F₀ P.area) :
    P.area F₁ = P.area F₂ ∧
      P.area F₀ = (ENat.card (H ⧸ K) : ℝ≥0∞) * P.area F₁ :=
  ⟨fuchsianFundamentalSet_area_eq h₁ hm₁ h₂ hm₂,
    fuchsianFundamentalSet_subgroup_index_area P K h₀ hm₀ h₁ hm₁⟩

/-- Fundamental domains for the same unit-disc Fuchsian group have equal hyperbolic area. -/
theorem fuchsianFundamentalDomain_area_eq {H : Subgroup complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D₁ D₂ : Set P.domain.carrier}
    (h₁ : IsFuchsianFundamentalDomain P D₁) (h₂ : IsFuchsianFundamentalDomain P D₂) :
    P.area D₁ = P.area D₂ := by
  obtain ⟨F₁, hF₁, hDF₁, hFC₁⟩ := h₁.exists_fundamentalSet
  obtain ⟨F₂, hF₂, hDF₂, hFC₂⟩ := h₂.exists_fundamentalSet
  exact (h₁.area_between hDF₁ hFC₁).trans
    ((fuchsianFundamentalSet_area_eq (P := P) hF₁ (h₁.nullMeasurableSet_between hDF₁ hFC₁)
      hF₂ (h₂.nullMeasurableSet_between hDF₂ hFC₂)).trans (h₂.area_between hDF₂ hFC₂).symm)

end LowDimensionalTopology.Geometry.Fuchsian
