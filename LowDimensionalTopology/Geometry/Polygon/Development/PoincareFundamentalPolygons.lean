/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCompactDevelopment
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.WanderingDomain
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincarePolygon
open MeasureTheory
variable {X : Type*} [TopologicalSpace X] (P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X)

/-- For a genuine closed polygon the literal given side union is exactly its topological frontier. -/
theorem frontier_eq_boundary (hP : IsOpen P.interior) (hc : P.carrier = closure P.interior) :
    frontier P.interior = P.boundary := by
  rw [frontier, hP.interior_eq,←hc]
  change (P.interior ∪ P.boundary) \ P.interior = P.boundary
  ext x
  constructor
  · rintro ⟨hx,hni⟩
    exact hx.resolve_left hni
  · intro hx
    exact ⟨Or.inr hx,fun hi => Set.disjoint_left.mp P.disjoint hi hx⟩

/-- Countably many genuine null sides make the original polygon frontier null. -/
theorem measure_frontier_zero [MeasurableSpace X] (μ : Measure X)
    (hP : IsOpen P.interior) (hc : P.carrier = closure P.interior)
    (hcount : P.sides.Countable) (hs : ∀ s ∈ P.sides,μ s = 0) : μ (frontier P.interior) = 0 := by
  rw [P.frontier_eq_boundary hP hc]
  exact (measure_sUnion_null_iff hcount).mpr hs

end LowDimensionalTopology.Geometry.Polygon.PoincarePolygon

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open MeasureTheory
open scoped UpperHalfPlane
variable {Γ : Type*} [Group Γ] [MulAction Γ ℍ]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- local tessellation and the actual uniform geometric cover yield the original closed-cover/interior-disjoint tessellation. -/
theorem FiniteFiberLocalTessellationCondition.uniform_polygon_tessellation
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier ⊆ closure P.interior) :
    (⋃ g : S.Generated,(fun x : ℍ => g • x) '' P.carrier) = univ ∧
      ∀ g k : S.Generated,g ≠ k →
        Disjoint ((fun x : ℍ => g • x) '' P.interior) ((fun x : ℍ => k • x) '' P.interior) := by
  have he := (h.covering_homeomorph_of_uniform_cover S hu hm hcl).2
  exact ⟨S.evaluation_surjective_iff_closed_cover.mp he.surjective,
    fun _ _ hne => S.original_interior_tiles_disjoint_of_evaluation_injective he.injective hne⟩

/-- The actual closed polygon meets every original generated orbit, as derived from global development. -/
theorem FiniteFiberLocalTessellationCondition.closure_meetsEveryOrbit
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier = closure P.interior) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit S.Generated ℍ (closure P.interior) := by
  have hcover := (h.uniform_polygon_tessellation S hu hm hcl.le).1
  intro x
  have hx : x ∈ ⋃ g : S.Generated,(fun x : ℍ => g • x) '' P.carrier := by rw [hcover];trivial
  obtain ⟨g,y,hy,hgy⟩ := mem_iUnion.mp hx
  refine ⟨g⁻¹,?_⟩
  rw [←hgy,inv_smul_smul,←hcl]
  exact hy

/-- True generated translates of the polygon interior give unique original interior orbit representatives. -/
theorem FiniteFiberLocalTessellationCondition.interior_orbit_unique
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier ⊆ closure P.interior)
    {x y : ℍ} (hx : x ∈ P.interior) (hy : y ∈ P.interior)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ x = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ y) : x = y := by
  obtain ⟨g,hgy⟩ := (Quotient.exact he : MulAction.orbitRel S.Generated ℍ x y)
  change g • y = x at hgy
  by_cases hg : g = 1
  · simpa only [hg,one_smul] using hgy.symm
  · have hd := (h.uniform_polygon_tessellation S hu hm hcl).2 g 1 hg
    exact False.elim (Set.disjoint_left.mp hd ⟨y,hy,hgy⟩ ⟨x,hx,one_smul _ _⟩)

/-- The actual global development yields a genuine fundamental polygon, including its original orbit-selector requirement. -/
theorem FiniteFiberLocalTessellationCondition.fundamentalDomain_of_uniform_cover
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier = closure P.interior)
    (hnull : volume (frontier P.interior) = 0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ volume P.interior := by
  refine ⟨hm.open_interior,hm.connected_interior,?_,hnull⟩
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.exists_fundamentalSet_between _ _ subset_closure
    (h.closure_meetsEveryOrbit S hu hm hcl)
    (fun _ hx _ hy he => h.interior_orbit_unique S hu hm hcl.le hx hy he)

/-- The standard topological action is discrete as a consequence of the genuine Poincare tessellation. -/
theorem FiniteFiberLocalTessellationCondition.discrete_of_uniform_cover
    [TopologicalSpace S.Generated] [IsTopologicalGroup S.Generated] [ContinuousSMul S.Generated ℍ]
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier ⊆ closure P.interior) :
    DiscreteTopology S.Generated := by
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_of_wandering_open P.interior hm.open_interior P.interior_nonempty
  intro g hg
  have hd := (h.uniform_polygon_tessellation S hu hm hcl).2 g 1 hg
  simpa only [one_smul,Set.image_id',Set.image_smul] using hd

/-- Countable genuine geodesic sides supply the area condition in the Poincare fundamental-polygon conclusion. -/
theorem FiniteFiberLocalTessellationCondition.fundamentalDomain_of_geodesic_sides
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier = closure P.interior)
    (hcount : P.sides.Countable) (hside : ∀ s ∈ P.sides,∃ L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s ⊆ L.carrier) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ volume P.interior := by
  apply h.fundamentalDomain_of_uniform_cover S hu hm hcl
  apply P.measure_frontier_zero volume hm.open_interior hcl hcount
  intro s hs
  obtain ⟨L,hL⟩ := hside s hs
  exact measure_mono_null hL L.volume_zero

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
