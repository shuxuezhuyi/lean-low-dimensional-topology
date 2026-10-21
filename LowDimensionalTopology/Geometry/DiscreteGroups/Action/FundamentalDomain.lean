/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.OrbitQuotient
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Fundamental sets and fundamental domains

The definitions below retain the pointwise orbit-selector condition in the
formulation. They do not require a unique group element taking a point into the set:
that condition would incorrectly exclude actions with elliptic stabilizers.

The measure parameter is explicit. To obtain the geometric hyperbolic instance,
one must still supply the Fuchsian action and its hyperbolic area measure.
-/

public section

open MeasureTheory Set Topology

universe u v

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

variable (G : Type u) [Group G] (X : Type v) [MulAction G X]

/-- A fundamental set contains one point from each orbit. -/
@[expose] def IsFundamentalSet (F : Set X) : Prop :=
  ∀ x : X, ∃! y : X, y ∈ F ∧ orbitProjection G X y = orbitProjection G X x

/-- The choice-based existence assertion for fundamental sets. -/
theorem exists_isFundamentalSet : ∃ F : Set X, IsFundamentalSet G X F := by
  classical
  refine ⟨Set.range (Quotient.out : orbitQuotient G X → X), ?_⟩
  intro x
  refine ⟨(orbitProjection G X x).out, ⟨⟨orbitProjection G X x, rfl⟩, ?_⟩, ?_⟩
  · exact Quotient.out_eq _
  · intro y hy
    obtain ⟨q, rfl⟩ := hy.1
    have hq : q = orbitProjection G X x := (Quotient.out_eq q).symm.trans hy.2
    exact congrArg Quotient.out hq

/-- Distinct points in a fundamental set cannot be in the same orbit. -/
theorem IsFundamentalSet.eq_of_mem {F : Set X} (hF : IsFundamentalSet G X F)
    {x y : X} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : orbitProjection G X x = orbitProjection G X y) : x = y :=
  (hF y).unique ⟨hx, hxy⟩ ⟨hy, rfl⟩

/-- The point-selector definition implies the orbit-covering condition. -/
theorem IsFundamentalSet.meetsEveryOrbit {F : Set X} (hF : IsFundamentalSet G X F) :
    MeetsEveryOrbit G X F := by
  intro x
  obtain ⟨y, ⟨hy, hrel⟩, _⟩ := hF x
  obtain ⟨g, hgy⟩ := (Quotient.exact hrel : MulAction.orbitRel G X y x)
  change g • x = y at hgy
  refine ⟨g, ?_⟩
  rw [hgy]
  exact hy

/-- translates of a fundamental set cover the ambient space. -/
theorem IsFundamentalSet.iUnion_image_eq_univ {F : Set X} (hF : IsFundamentalSet G X F) :
    (⋃ g : G, (fun x : X => g • x) '' F) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨g, hg⟩ := IsFundamentalSet.meetsEveryOrbit G X hF x
  exact Set.mem_iUnion.mpr ⟨g⁻¹, g • x, hg, by simp⟩

section TopologicalMeasureSpace

variable [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X)

/-- Fundamental domains with the acting space and area measure as parameters. -/
structure IsFundamentalDomain (D : Set X) : Prop where
  isOpen : IsOpen D
  isConnected : IsConnected D
  exists_fundamentalSet : ∃ F : Set X, IsFundamentalSet G X F ∧ D ⊆ F ∧ F ⊆ closure D
  null_frontier : μ (frontier D) = 0

variable {μ} {D : Set X}

/-- The domain condition includes nonemptiness. -/
theorem IsFundamentalDomain.nonempty (hD : IsFundamentalDomain G X μ D) : D.Nonempty :=
  hD.isConnected.nonempty

/-- Interior points of a fundamental domain are unique representatives of their orbit. -/
theorem IsFundamentalDomain.eq_of_mem (hD : IsFundamentalDomain G X μ D)
    {x y : X} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : orbitProjection G X x = orbitProjection G X y) : x = y := by
  obtain ⟨F, hF, hDF, _⟩ := hD.exists_fundamentalSet
  exact IsFundamentalSet.eq_of_mem G X hF (hDF hx) (hDF hy) hxy

/--
The disjoint-interior assertion uses local effectivity.
For Möbius transformations, agreement with the identity on an open set forces equality.
-/
theorem IsFundamentalDomain.disjoint_image [ContinuousConstSMul G X]
    (hD : IsFundamentalDomain G X μ D)
    (hfixed : ∀ g : G, (∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, g • x = x) → g = 1)
    {g : G} (hg : g ≠ 1) : Disjoint ((fun x : X => g • x) '' D) D := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, hgy⟩ hx
  apply hg
  apply hfixed g
  refine ⟨D ∩ (fun z : X => g • z) ⁻¹' D,
    hD.isOpen.inter (hD.isOpen.preimage (continuous_const_smul g)),
    ⟨y, hy, ?_⟩, ?_⟩
  · change g • y = x at hgy
    change g • y ∈ D
    rw [hgy]
    exact hx
  · intro z hz
    exact IsFundamentalDomain.eq_of_mem G X hD hz.2 hz.1 (orbitProjection_smul G X g z)

/-- The fundamental-set sandwich implies that the closed domain meets every orbit. -/
theorem IsFundamentalDomain.closure_meetsEveryOrbit (hD : IsFundamentalDomain G X μ D) :
    MeetsEveryOrbit G X (closure D) := by
  obtain ⟨F, hF, _, hFC⟩ := hD.exists_fundamentalSet
  intro x
  obtain ⟨g, hg⟩ := IsFundamentalSet.meetsEveryOrbit G X hF x
  exact ⟨g, hFC hg⟩

/-- Pointwise covering by translates of the closed domain. -/
theorem IsFundamentalDomain.closure_covering (hD : IsFundamentalDomain G X μ D) :
    ∀ x : X, ∃ g : G, ∃ y ∈ closure D, g • y = x := by
  intro x
  obtain ⟨g, hg⟩ := IsFundamentalDomain.closure_meetsEveryOrbit G X hD x
  exact ⟨g⁻¹, g • x, hg, by simp⟩

/-- The closure-covering equality for a fundamental domain. -/
theorem IsFundamentalDomain.iUnion_image_closure_eq_univ
    (hD : IsFundamentalDomain G X μ D) :
    (⋃ g : G, (fun x : X => g • x) '' closure D) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨g, y, hy, hgy⟩ := IsFundamentalDomain.closure_covering G X hD x
  exact Set.mem_iUnion.mpr ⟨g, y, hy, hgy⟩

/-- The fundamental-domain definition supplies the missing hypothesis for the comparison map. -/
theorem IsFundamentalDomain.closure_comparisonMap_bijective
    (hD : IsFundamentalDomain G X μ D) :
    Function.Bijective (comparisonMap G X (closure D)) :=
  comparisonMap_bijective G X (closure D)
    (IsFundamentalDomain.closure_meetsEveryOrbit G X hD)

/-- The null-boundary axiom controls the gap between the open domain and its closure. -/
theorem IsFundamentalDomain.measure_closure_sdiff (hD : IsFundamentalDomain G X μ D) :
    μ (closure D \ D) = 0 := by
  rw [← hD.isOpen.frontier_eq]
  exact hD.null_frontier

/-- Every set between the domain and its closure has the same area. -/
theorem IsFundamentalDomain.measure_eq_of_between (hD : IsFundamentalDomain G X μ D)
    {F : Set X} (hDF : D ⊆ F) (hFC : F ⊆ closure D) : μ D = μ F :=
  (measure_eq_measure_of_between_null_sdiff hDF hFC
    (IsFundamentalDomain.measure_closure_sdiff G X hD)).1

/-- A set in the fundamental-domain sandwich differs from the domain only on a null set. -/
theorem IsFundamentalDomain.ae_eq_of_between (hD : IsFundamentalDomain G X μ D)
    {F : Set X} (hDF : D ⊆ F) (hFC : F ⊆ closure D) : F =ᵐ[μ] D := by
  have hnull : μ (F \ D) = 0 := measure_mono_null
    (by intro x hx; exact ⟨hFC hx.1, hx.2⟩)
    (IsFundamentalDomain.measure_closure_sdiff G X hD)
  exact (ae_le_set.mpr hnull).antisymm hDF.eventuallySubset

/-- Measurability modulo null sets suffices without assuming a complete measure. -/
theorem IsFundamentalDomain.nullMeasurableSet_of_between [OpensMeasurableSpace X]
    (hD : IsFundamentalDomain G X μ D) {F : Set X} (hDF : D ⊆ F) (hFC : F ⊆ closure D) :
    NullMeasurableSet F μ :=
  hD.isOpen.measurableSet.nullMeasurableSet.congr
    (IsFundamentalDomain.ae_eq_of_between G X hD hDF hFC).symm

/-- The ordinary measurability assertion holds for complete area measures. -/
theorem IsFundamentalDomain.measurableSet_of_between [OpensMeasurableSpace X] [μ.IsComplete]
    (hD : IsFundamentalDomain G X μ D) {F : Set X} (hDF : D ⊆ F) (hFC : F ⊆ closure D) :
    MeasurableSet F :=
  (IsFundamentalDomain.nullMeasurableSet_of_between G X hD hDF hFC).measurable_of_complete

/-- The comparison-map data, at the closed domain. -/
structure FundamentalDomainComparisonData (D : Set X) : Prop where
  inclusion_injective : Function.Injective (Subtype.val : closure D → X)
  comparison_injective : Function.Injective (comparisonMap G X (closure D))
  ambient_surjective : Function.Surjective (orbitProjection G X)
  restricted_surjective : Function.Surjective (restrictedProjection G X (closure D))
  comparison_surjective : Function.Surjective (comparisonMap G X (closure D))
  ambient_continuous : Continuous (orbitProjection G X)
  restricted_continuous : Continuous (restrictedProjection G X (closure D))
  inclusion_continuous : Continuous (Subtype.val : closure D → X)
  comparison_continuous : Continuous (comparisonMap G X (closure D))
  ambient_isOpenMap : IsOpenMap (orbitProjection G X)

/-- A fundamental domain supplies the comparison map's bijectivity and continuity data. -/
theorem IsFundamentalDomain.comparisonData [ContinuousConstSMul G X]
    (hD : IsFundamentalDomain G X μ D) : FundamentalDomainComparisonData G X D where
  inclusion_injective := subsetInclusion_injective X (closure D)
  comparison_injective := comparisonMap_injective G X (closure D)
  ambient_surjective := orbitProjection_surjective G X
  restricted_surjective := restrictedProjection_surjective G X (closure D)
  comparison_surjective := comparisonMap_surjective G X (closure D)
    (IsFundamentalDomain.closure_meetsEveryOrbit G X hD)
  ambient_continuous := orbitProjection_continuous G X
  restricted_continuous := restrictedProjection_continuous G X (closure D)
  inclusion_continuous := subsetInclusion_continuous X (closure D)
  comparison_continuous := comparisonMap_continuous G X (closure D)
  ambient_isOpenMap := orbitProjection_isOpenMap G X

end TopologicalMeasureSpace

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
