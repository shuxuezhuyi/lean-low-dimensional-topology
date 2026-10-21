module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.LocallyFiniteFundamentalDomains
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ModelCoordinates
public import Mathlib.Tactic
/-!
# Convex Fuchsian fundamental polygons

Klein coordinates express hyperbolic convexity as ordinary convexity. A locally
finite convex fundamental domain is regular open, has convex closure, and gives
every boundary point a nonidentity translate on the boundary.
-/

@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean

/-- The actual original disc point, expressed in the Klein model only as a coordinate. -/
def UnitDiscFuchsianGroup.kleinCoordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : ℂ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x)

theorem UnitDiscFuchsianGroup.kleinCoordinate_isOpenEmbedding {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : Topology.IsOpenEmbedding P.kleinCoordinate :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.comp P.finiteCoordinate.isOpenEmbedding

/-- uses geodesic convexity and actual local finiteness, without a finite-edge assumption. -/
structure IsConvexFuchsianPolygon {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) : Prop where
  locallyFinite : IsLocallyFiniteFuchsianDomain P D
  convex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' D)

/-- The source convexity is equivalent to ordinary convexity of the actual Klein image. -/
theorem IsConvexFuchsianPolygon.klein_convex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Convex ℝ (P.kleinCoordinate '' D) := by
  change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x))
    '' D)
  rw [← image_image]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp hD.convex

/-- An open convex set remains regular open under any genuine open coordinate embedding. -/
theorem interior_closure_eq_of_convex_open_embedding {X : Type*} [TopologicalSpace X]
    (f : X → ℂ) (hf : Topology.IsOpenEmbedding f) (D : Set X) (ho : IsOpen D)
    (hn : D.Nonempty) (hc : Convex ℝ (f '' D)) : interior (closure D) = D := by
  have hfo : IsOpen (f '' D) := hf.isOpenMap D ho
  have hfi : (interior (f '' D)).Nonempty := by rw [hfo.interior_eq]; exact hn.image f
  have he : interior (closure (f '' D)) = f '' D :=
    (hc.interior_closure_eq_interior_of_nonempty_interior hfi).trans hfo.interior_eq
  rw [hf.isEmbedding.closure_eq_preimage_closure_image D,
    ← hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous, he,
    preimage_image_eq _ hf.injective]

/-- The genuine hyperbolically convex fundamental polygon has no artificial interior slits. -/
theorem IsConvexFuchsianPolygon.interior_closure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    interior (closure D) = D :=
  interior_closure_eq_of_convex_open_embedding P.kleinCoordinate P.kleinCoordinate_isOpenEmbedding D
    ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
    ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty hD.klein_convex

/-- Hyperbolic convexity also holds for the actual closed polygon. -/
theorem IsConvexFuchsianPolygon.closure_convex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' closure D) := by
  rw [P.finiteCoordinate.image_closure]
  exact hD.convex.closure

/-- Every polygon boundary point has a nonidentity group image on the same genuine boundary. -/
theorem IsConvexFuchsianPolygon.boundary_mate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : x ∈ frontier D) :
    ∃ g : H, g ≠ 1 ∧ g • x ∈ frontier D := by
  classical
  have ho := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hnx : x ∉ D := by simpa only [frontier, ho.interior_eq, mem_sdiff] using hx |>.2
  have hex : ∃ g : H, g ≠ 1 ∧ x ∈ fuchsianDomainTile P D g := by
    by_contra hn
    push Not at hn
    obtain ⟨N, _hNc, hNx, _hf, hNcov, _hd⟩ := hD.locallyFinite.finite_neighborhood_star x
    have hNsub : N ⊆ closure D := by
      intro y hy
      obtain ⟨g, hxg, hyg⟩ := mem_iUnion₂.mp (hNcov hy)
      have hg : g = 1 := by by_contra hg; exact hn g hg hxg
      simpa only [hg, fuchsianDomainTile, one_smul] using hyg
    have hxint : x ∈ interior (closure D) := mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hNx hNsub)
    exact hnx (hD.interior_closure ▸ hxint)
  obtain ⟨g, hg, u, hu, hgu⟩ := hex
  change g • u = x at hgu
  refine ⟨g⁻¹, inv_ne_one.mpr hg, ?_⟩
  have he : g⁻¹ • x = u := by rw [← hgu, inv_smul_smul]
  rw [he]
  have hnu : u ∉ D := by
    intro huD
    exact Set.disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image_closure hg)
      ⟨u, huD, hgu⟩ (frontier_subset_closure hx)
  simpa only [frontier, ho.interior_eq, mem_sdiff] using And.intro hu hnu

end LowDimensionalTopology.Geometry.Fuchsian
