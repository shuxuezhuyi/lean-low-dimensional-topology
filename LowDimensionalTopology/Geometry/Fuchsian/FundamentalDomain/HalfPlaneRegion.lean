module

public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FunProp

/-!
# Open fundamental regions in the actual upper half-plane

The open-region definition requires disjoint nonidentity translates, coverage
by translates of its relative closure, and planar-Lebesgue-null relative
frontier. It imposes no connectedness condition. The existing connected
selector-based fundamental domains satisfy exactly these conditions together
with connectedness. Hyperbolic area and planar Lebesgue area have the same null
sets because the original reciprocal-height-squared density is positive.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Actual hyperbolic-area-null sets are precisely the planar-Lebesgue-null
images under the original upper-half-plane inclusion, for arbitrary sets. -/
theorem halfPlane_volume_eq_zero_iff_planar_volume_eq_zero (S : Set ℍ) :
    (volume : Measure ℍ) S = 0 ↔
      (volume : Measure ℂ) (UpperHalfPlane.coe '' S) = 0 := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let ρ : ℍ → ℝ≥0∞ := fun z => ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)
  have hρ : Measurable ρ := by
    dsimp only [ρ]
    fun_prop
  have hρ0 (z : ℍ) : ρ z ≠ 0 := by
    have hz : NNReal.mk z.im z.im_pos.le ≠ 0 := NNReal.ne_iff.mp z.im_ne_zero
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (one_div_ne_zero hz))
  have hflat : μ ≪ μ.withDensity ρ :=
    withDensity_absolutelyContinuous' hρ.aemeasurable (Eventually.of_forall hρ0)
  have hweighted : μ.withDensity ρ ≪ μ := withDensity_absolutelyContinuous μ ρ
  rw [← UpperHalfPlane.measurableEmbedding_coe.comap_apply (volume : Measure ℂ) S]
  change (μ.withDensity ρ) S = 0 ↔ μ S = 0
  exact ⟨fun h => hflat h, fun h => hweighted h⟩

end LowDimensionalTopology.Geometry.Hyperbolic

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry
open DiscreteGroups.Action

/-- The actual half-plane action is locally effective: a nonidentity Möbius
transformation cannot fix a nonempty open set pointwise. -/
theorem HalfPlaneFuchsianGroup.native_local_effective
    {H : Subgroup Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) (g : H) :
    letI := P.nativeAction
    (∃ U : Set ℍ, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, g • x = x) → g = 1 := by
  let := P.nativeAction
  rintro ⟨U, hU, ⟨x, hx⟩, hfix⟩
  by_contra hg
  have hgn : g.val ≠ 1 := fun he => hg (Subtype.ext he)
  have hfin := mobius_boundary_fixed_finite g.val hgn
  have him : (Mobius.halfPlaneBoundaryPoint '' U).Finite := hfin.subset (by
    rintro _ ⟨z, hz, rfl⟩
    change g.val.val (Mobius.halfPlaneBoundaryPoint z) = Mobius.halfPlaneBoundaryPoint z
    rw [P.nativeAction_boundary, hfix z hz])
  have ho : IsOpen (Mobius.halfPlaneBoundaryPoint '' U) :=
    Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.isOpenMap U hU
  exact (infinite_of_mem_nhds (Mobius.halfPlaneBoundaryPoint x)
    (ho.mem_nhds ⟨x, hx, rfl⟩)) him

/-- An open fundamental region with the actual planar boundary measure. The
three geometric conditions do not impose connectedness. -/
def IsHalfPlaneFundamentalRegion
    {H : Subgroup Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (F : Set ℍ) : Prop :=
  letI := P.nativeAction
  IsOpen F ∧
    (∀ g : H, g ≠ 1 → Disjoint ((fun x : ℍ => g • x) '' F) F) ∧
    (∀ x : ℍ, ∃ g : H, ∃ y ∈ closure F, g • y = x) ∧
    (volume : Measure ℂ) (UpperHalfPlane.coe '' frontier F) = 0

/-- The original connected selector-based definition agrees with the broader
open-region definition exactly after retaining its extra connectedness. -/
theorem HalfPlaneFuchsianGroup.nativeFundamentalDomain_iff_region_and_connected
    {H : Subgroup Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (F : Set ℍ) :
    letI := P.nativeAction
    IsFundamentalDomain H ℍ volume F ↔ IsHalfPlaneFundamentalRegion P F ∧ IsConnected F := by
  dsimp only [IsHalfPlaneFundamentalRegion]
  let := P.nativeAction
  let : ContinuousConstSMul H ℍ := ⟨fun g => (P.nativeHom g).continuous⟩
  constructor
  · intro hF
    refine ⟨⟨hF.isOpen, ?_, IsFundamentalDomain.closure_covering H ℍ hF,
      (Hyperbolic.halfPlane_volume_eq_zero_iff_planar_volume_eq_zero
        (frontier F)).mp hF.null_frontier⟩, hF.isConnected⟩
    intro g hg
    exact IsFundamentalDomain.disjoint_image H ℍ hF (P.native_local_effective) hg
  · rintro ⟨⟨ho, hd, hc, hn⟩, hconn⟩
    refine ⟨ho, hconn, ?_,
      (Hyperbolic.halfPlane_volume_eq_zero_iff_planar_volume_eq_zero
        (frontier F)).mpr hn⟩
    apply exists_fundamentalSet_between F (closure F) subset_closure
    · intro x
      obtain ⟨g, y, hy, hgy⟩ := hc x
      refine ⟨g⁻¹, ?_⟩
      rw [← hgy, inv_smul_smul]
      exact hy
    · intro x hx y hy hxy
      obtain ⟨g, hgy⟩ := (Quotient.exact hxy : MulAction.orbitRel H ℍ x y)
      change g • y = x at hgy
      by_cases hg : g = 1
      · simpa only [hg, one_smul] using hgy.symm
      · exact (Set.disjoint_left.mp (hd g hg) ⟨y, hy, hgy⟩ hx).elim

/-- Every existing actual connected fundamental domain satisfies the exact
open-region definition without adding a connectedness premise to that definition. -/
theorem HalfPlaneFuchsianGroup.isHalfPlaneFundamentalRegion_of_native
    {H : Subgroup Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (F : Set ℍ) :
    letI := P.nativeAction
    IsFundamentalDomain H ℍ volume F → IsHalfPlaneFundamentalRegion P F := by
  exact fun h => ((P.nativeFundamentalDomain_iff_region_and_connected F).mp h).1

end LowDimensionalTopology.Geometry.Fuchsian
