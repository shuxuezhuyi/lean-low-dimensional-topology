module

public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ConvexFundamentalPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FundamentalDomainAccessCriterion

/-!
# Boundary mates for actual convex fundamental domains

The boundary-mate criterion, including its converse without
assuming local finiteness. Actual Klein segments provide boundary access.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon

private theorem convex_open_embedding_boundary_access {X : Type*} [TopologicalSpace X]
    (f : X → ℂ) (hf : Topology.IsOpenEmbedding f) {D : Set X}
    (ho : IsOpen D) (hn : D.Nonempty) (hc : Convex ℝ (f '' D))
    {x : X} (hx : x ∈ frontier D) :
    ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧
      ∀ t ∈ Ioc 0 1, γ t ∈ D := by
  classical
  let : Nonempty X := ⟨x⟩
  obtain ⟨y, hy⟩ := hn
  let L : ℝ → ℂ := fun t => (1 - t) • f x + t • f y
  have hfo : IsOpen (f '' D) := hf.isOpenMap D ho
  have hxcl : f x ∈ closure (f '' D) := by
    have hxc : x ∈ closure D := frontier_subset_closure hx
    rw [hf.isEmbedding.closure_eq_preimage_closure_image D] at hxc
    exact hxc
  have hyint : f y ∈ interior (f '' D) := by
    rw [hfo.interior_eq]
    exact ⟨y, hy, rfl⟩
  have hLmem : ∀ t ∈ Ioc 0 1, L t ∈ f '' D := by
    intro t ht
    rw [← hfo.interior_eq]
    exact hc.combo_closure_interior_mem_interior hxcl hyint
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hLrange : ∀ t ∈ Icc 0 1, ∃ z, f z = L t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with heq | hpos
    · exact ⟨x, by simp only [← heq, L, sub_zero, one_smul, zero_smul, add_zero]⟩
    · obtain ⟨z, hz, heq⟩ := hLmem t ⟨hpos, ht.2⟩
      exact ⟨z, heq⟩
  let γ : ℝ → X := fun t => Function.invFun f (L t)
  have hγf : ∀ t ∈ Icc 0 1, f (γ t) = L t := fun t ht =>
    Function.invFun_eq (hLrange t ht)
  have hcont : ContinuousOn γ (Icc 0 1) := by
    apply hf.isEmbedding.continuousOn_iff.mpr
    apply (show Continuous L by fun_prop).continuousOn.congr
    intro t ht
    exact hγf t ht
  refine ⟨γ, hcont, ?_, ?_⟩
  · apply hf.injective
    simpa only [L, sub_zero, one_smul, zero_smul, add_zero] using
      hγf 0 ⟨le_rfl, zero_le_one⟩
  · intro t ht
    obtain ⟨z, hz, heq⟩ := hLmem t ht
    have hγz : γ t = z := hf.injective ((hγf t ⟨ht.1.le, ht.2⟩).trans heq.symm)
    exact hγz ▸ hz

/--
Actual hyperbolic convexity gives the continuous access needed,
without assuming local finiteness.
-/
theorem convex_fundamentalDomain_boundary_access {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D)
    (hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' D)) :
    ∀ x ∈ frontier D, ∃ γ : ℝ → P.domain.carrier,
      ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ ∀ t ∈ Ioc 0 1, γ t ∈ D := by
  have ho := ((isFuchsianFundamentalDomain_iff P D).mp hD).1
  have hn := ((isFuchsianFundamentalDomain_iff P D).mp hD).2.1.nonempty
  have hc : Convex ℝ (P.kleinCoordinate '' D) := by
    change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x))
      '' D)
    rw [← image_image]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp hconv
  exact fun x hx => convex_open_embedding_boundary_access P.kleinCoordinate
    P.kleinCoordinate_isOpenEmbedding ho hn hc hx

/--
The converse boundary-mate criterion for an original convex
fundamental domain, with local finiteness proved rather than assumed.
-/
theorem convex_fundamentalDomain_locallyFinite_iff_boundary_mates
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (hD : IsFuchsianFundamentalDomain P D)
    (hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' D)) :
    IsLocallyFiniteFuchsianDomain P D ↔
      ∀ x ∈ frontier D, ∃ g : H, g ≠ 1 ∧ g • x ∈ frontier D := by
  constructor
  · intro hlf x hx
    exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.boundary_mate ⟨hlf, hconv⟩ hx)
  · intro hmate
    exact locallyFinite_of_frontier_mates_and_positive_access_paths P D hD hmate
      (convex_fundamentalDomain_boundary_access P hD hconv)

end LowDimensionalTopology.Geometry.Fuchsian
