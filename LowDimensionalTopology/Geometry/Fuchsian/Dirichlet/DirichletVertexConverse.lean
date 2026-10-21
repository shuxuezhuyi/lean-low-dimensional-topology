/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSidePairing
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- A genuine weak Dirichlet minimizer tied with an orbit center belongs to
the actual neighboring closed tile. This derives the required tile membership
from the source metric hypotheses, including possible elliptic fixed points. -/
theorem dirichlet_mem_closedTile_of_bisector {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    {x : P.domain.carrier} (hx : x ∈ closure (dirichletDomain P w)) (g : H)
    (hbis : x ∈ dirichletBisector P w g) :
    x ∈ fuchsianDomainTile P (dirichletDomain P w) g := by
  have he : P.hyperbolicDist (g⁻¹ • x) w = P.hyperbolicDist x w := by
    rw [← P.hyperbolicDist_inverse_smul g]
    exact hbis.symm
  have hginv : g⁻¹ • x ∈ closure (dirichletDomain P w) := by
    rw [closure_dirichletDomain P w hw]
    intro k
    rw [he]
    have hk := closure_dirichletDomain_le P w hx (g * k)
    simpa only [mul_smul, P.hyperbolicDist_inverse_smul g] using hk
  exact ⟨g⁻¹ • x, hginv, smul_inv_smul g x⟩

/--
The missing reverse implication in 's boundary description:
two distinct nontrivial orbit bisectors meeting in the actual closed Dirichlet
polygon give a genuine singleton triple-tile vertex. Triple uniqueness is
derived from the already proved convex fundamental-polygon geometry.
-/
theorem dirichlet_vertex_of_two_bisectors {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    {x : P.domain.carrier} (hx : x ∈ closure (dirichletDomain P w))
    (g h : H) (hg : g ≠ 1) (hh : h ≠ 1) (hgh : g ≠ h)
    (hbis : x ∈ dirichletBisector P w g ∩ dirichletBisector P w h) :
    IsFuchsianPolygonVertex P (dirichletDomain P w) x := by
  have hxg := dirichlet_mem_closedTile_of_bisector P w hw hx g hbis.1
  have hxh := dirichlet_mem_closedTile_of_bisector P w hw hx h hbis.2
  have hs := (dirichletDomain_isConvexFuchsianPolygon P w hw).closed_tile_triple_subsingleton hg hh hgh
  exact ⟨g, h, hg, hh, hgh, hs.eq_singleton_of_mem ⟨⟨hx, hxg⟩, hxh⟩⟩

/-- The complete closed-domain criterion uses the original actual group
labels and imposes no extra neighboring-tile or uniqueness hypothesis. -/
theorem dirichlet_vertex_iff_two_bisectors {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) :
    IsFuchsianPolygonVertex P (dirichletDomain P w) x ↔
      x ∈ closure (dirichletDomain P w) ∧
        ∃ g h : H, g ≠ 1 ∧ h ≠ 1 ∧ g ≠ h ∧
          x ∈ dirichletBisector P w g ∩ dirichletBisector P w h := by
  constructor
  · intro hv
    obtain ⟨g, h, hg, hh, hgh, _, hbis⟩ := dirichlet_vertex_bisectors P w hw hv
    exact ⟨frontier_subset_closure (hv.mem_frontier (dirichletDomain_fundamental P w hw)),
      g, h, hg, hh, hgh, hbis⟩
  · rintro ⟨hx, g, h, hg, hh, hgh, hbis⟩
    exact dirichlet_vertex_of_two_bisectors P w hw hx g h hg hh hgh hbis

/-- The source's literal boundary formulation: a vertex is precisely an
actual boundary point where two distinct genuine nontrivial bisectors meet. -/
theorem dirichlet_vertex_iff_frontier_two_bisectors {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) :
    IsFuchsianPolygonVertex P (dirichletDomain P w) x ↔
      x ∈ frontier (dirichletDomain P w) ∧
        ∃ g h : H, g ≠ 1 ∧ h ≠ 1 ∧ dirichletBisector P w g ≠ dirichletBisector P w h ∧
          x ∈ dirichletBisector P w g ∩ dirichletBisector P w h := by
  constructor
  · intro hv
    exact ⟨hv.mem_frontier (dirichletDomain_fundamental P w hw),
      dirichlet_vertex_distinct_bisectors P w hw hv⟩
  · rintro ⟨hx, g, h, hg, hh, hne, hbis⟩
    apply dirichlet_vertex_of_two_bisectors P w hw (frontier_subset_closure hx) g h hg hh
      (fun he => hne (he ▸ rfl)) hbis

end LowDimensionalTopology.Geometry.Fuchsian
