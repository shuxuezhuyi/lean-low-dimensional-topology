/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.Discontinuity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Hyperbolic

/-- The original native closed Dirichlet set, allowing actual center stabilizers. -/
def nativeClosedDirichlet (H : Subgroup (ℍ≃ᵢℍ)) (w : ℍ) : Set ℍ:=
  {z | ∀g : H,dist z w≤dist z (g.val w)}

/-- Actual compact-orbit finiteness supplies a genuine closest original orbit representative. -/
theorem native_closest_orbit_representative (H : Subgroup (ℍ≃ᵢℍ))
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H ℍ) (x w : ℍ) :
    ∃g : H,∀h : H,dist (g.val x) w≤dist (h.val x) w := by
  let F:=Metric.closedBall w (dist x w)∩MulAction.orbit H x
  have hF : F.Finite:=hH.finite_inter_orbit x (isCompact_closedBall w (dist x w))
  have hx : x∈F:=⟨Metric.mem_closedBall.mpr le_rfl,MulAction.mem_orbit_self x⟩
  obtain ⟨y,hy,hmin⟩:=Set.exists_min_image F (fun z : ℍ=>dist z w) hF ⟨x,hx⟩
  obtain ⟨g,rfl⟩:=hy.2
  refine ⟨g,fun h=>?_⟩
  by_cases hh : h.val x∈F
  · exact hmin _ hh
  · have hnot : ¬dist (h.val x) w≤dist x w:=by
      intro he
      exact hh ⟨he,⟨h,rfl⟩⟩
    exact hy.1.trans (not_le.mp hnot).le

/-- Every genuine orbit meets the actual closed Dirichlet set, without a free-center assumption. -/
theorem nativeClosedDirichlet_meets_orbit (H : Subgroup (ℍ≃ᵢℍ))
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H ℍ) (w x : ℍ) :
    ∃g : H,g.val x∈nativeClosedDirichlet H w := by
  obtain ⟨g,hg⟩:=native_closest_orbit_representative H hH x w
  refine ⟨g,fun h=>?_⟩
  have hm:=hg (h⁻¹*g)
  change dist (g.val x) w≤dist (h.val⁻¹ (g.val x)) w at hm
  have he:=(h.val).dist_eq (h.val⁻¹ (g.val x)) w
  rw [IsometryEquiv.apply_inv_self] at he
  exact hm.trans_eq he.symm

/-- Any actual closed region containing the genuine closed Dirichlet set has a full original translate cover. -/
theorem native_closed_region_cover_of_dirichlet (H : Subgroup (ℍ≃ᵢℍ))
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H ℍ) (w : ℍ) (D : Set ℍ)
    (hD : nativeClosedDirichlet H w⊆D) :
    (⋃g : H,g.val '' D)=univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨g,hg⟩:=nativeClosedDirichlet_meets_orbit H hH w x
  refine mem_iUnion.mpr ⟨g⁻¹,g.val x,hD hg,?_⟩
  exact (g.val).inv_apply_self x

end LowDimensionalTopology.Geometry.Fuchsian
