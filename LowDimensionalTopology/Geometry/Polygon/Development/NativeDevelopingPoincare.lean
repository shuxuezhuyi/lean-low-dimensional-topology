module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeGeodesicPolygonGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Covering.UniformCharts
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)

/-- Bijective actual global development gives the original native discreteness and literal
fundamental polygon; this is a consequence helper, not a replacement for proving development. -/
theorem native_poincare_of_evaluation_bijective (he : Function.Bijective S.evaluation)
    (ho : IsOpen P.interior) (hc : IsConnected P.interior)
    (hcl : P.carrier=closure P.interior) (hcount : P.sides.Countable)
    (hside : ∀s∈P.sides,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s⊆L.carrier) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ volume P.interior := by
  let : TopologicalSpace S.Generated:=inferInstanceAs
    (TopologicalSpace (↥(Subgroup.closure (range S.element))))
  let : IsTopologicalGroup S.Generated:=inferInstanceAs
    (IsTopologicalGroup (↥(Subgroup.closure (range S.element))))
  let : ContinuousSMul S.Generated ℍ:=inferInstanceAs
    (ContinuousSMul (↥(Subgroup.closure (range S.element))) ℍ)
  have hCover:=S.evaluation_surjective_iff_closed_cover.mp he.2
  have hDis : ∀g k : S.Generated,g≠k →Disjoint
      ((fun x : ℍ=>g•x) '' P.interior) ((fun x : ℍ=>k•x) '' P.interior):=
    fun _ _ hne=>S.original_interior_tiles_disjoint_of_evaluation_injective he.1 hne
  have hMeet : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit S.Generated ℍ (closure P.interior) := by
    intro x
    have hx : x∈⋃g : S.Generated,(fun x : ℍ=>g•x) '' P.carrier:=by rw [hCover];trivial
    obtain ⟨g,y,hy,hgy⟩:=mem_iUnion.mp hx
    refine ⟨g⁻¹,?_⟩
    rw [←hgy,inv_smul_smul,←hcl]
    exact hy
  have hUnique : ∀x∈P.interior,∀y∈P.interior,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ y →x=y := by
    intro x hx y hy hxy
    obtain ⟨g,hgy⟩:=(Quotient.exact hxy : MulAction.orbitRel S.Generated ℍ x y)
    change g•y=x at hgy
    by_cases hg : g=1
    · simpa only [hg,one_smul] using hgy.symm
    · exact (Set.disjoint_left.mp (hDis g 1 hg) ⟨y,hy,hgy⟩ ⟨x,hx,one_smul _ _⟩).elim
  constructor
  · apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_of_wandering_open P.interior ho P.interior_nonempty
    intro g hg
    simpa only [one_smul,Set.image_id',Set.image_smul] using hDis g 1 hg
  · refine ⟨ho,hc,_root_.LowDimensionalTopology.Geometry.Fuchsian.exists_fundamentalSet_between _ _ subset_closure hMeet
    hUnique,?_⟩
    apply P.measure_frontier_zero volume ho hcl hcount
    intro s hs
    obtain ⟨L,hL⟩:=hside s hs
    exact measure_mono_null hL L.volume_zero

/--
The original uniform full-ball developing-chart radius, together with actual local tessellation,
gives global evaluation without a uniform margin for the literal raw class stars.
-/
theorem FiniteFiberLocalTessellationCondition.evaluation_homeomorph_of_uniform_charts
    (h : S.FiniteFiberLocalTessellationCondition) (hc : IsConnected P.interior)
    (hcl : P.carrier⊆closure P.interior) {ε : ℝ} (hε : 0<ε)
    (hCharts : _root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts S.evaluation ε) : IsHomeomorph S.evaluation := by
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  let : T2Space S.Development:=h.t2Space S
  let : ConnectedSpace S.Development:=S.development_connectedSpace_of_interior hc hcl
  exact hCharts.isHomeomorph hε

/--
Actual local tessellation and the original uniform developing-ball chart radius give both native
Poincare conclusions for arbitrary noncompact or infinitely sided original polygons.
-/
theorem native_poincare_of_uniform_developing_charts
    (h : S.FiniteFiberLocalTessellationCondition) (ho : IsOpen P.interior) (hc : IsConnected P.interior)
    (hcl : P.carrier=closure P.interior) (hcount : P.sides.Countable)
    (hside : ∀s∈P.sides,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s⊆L.carrier)
    {ε : ℝ} (hε : 0<ε) (hCharts : _root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts
      S.evaluation ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ volume P.interior := by
  have he:=h.evaluation_homeomorph_of_uniform_charts S hc hcl.le hε hCharts
  exact S.native_poincare_of_evaluation_bijective he.bijective ho hc hcl hcount hside

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
open scoped UpperHalfPlane
/-- General original cycle data and an actual uniform developing-chart radius give the
native Poincare theorem, without requiring compactness or a uniform raw-star margin. -/
theorem NativeGeodesicPolygonGeometry.poincare_of_uniform_developing_charts
    {P : PoincarePolygon ℍ} {V : Set ℍ} (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (hCycles : S.CompleteVertexCycleCondition V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hε : 0<ε) (hCharts : _root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts
      S.evaluation ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior :=
  S.native_poincare_of_uniform_developing_charts (D.local_tessellation S hCycles hOpp)
    D.interior_open D.interior_connected D.carrier_closure D.countable_sides
    (fun s hs=>⟨D.line ⟨s,hs⟩,D.side_subset_line ⟨s,hs⟩⟩) hε hCharts
end LowDimensionalTopology.Geometry.Polygon
