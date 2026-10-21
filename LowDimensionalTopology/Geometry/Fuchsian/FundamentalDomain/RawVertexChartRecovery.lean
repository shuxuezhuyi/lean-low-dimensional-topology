/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.NaturalCyclePoincare
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCycleFolding
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare
public import Mathlib.Topology.SeparatedMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
variable {P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon
  ℍ} (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
local instance rawRecoveryIndexTopology : TopologicalSpace S.Generated:=⊥
local instance rawRecoveryIndexDiscrete : DiscreteTopology S.Generated:=⟨rfl⟩
local instance rawRecoveryActionIsometric : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩

/-- Quotient openness gives a genuine original-coordinate radius at any indexed copy.
The discrete topology here belongs only to the copy index, not to the native isometry group. -/
theorem original_copy_radius_in_open {U:Set S.Development} (hU:IsOpen U)
    (a:S.Copy) (ha:S.project a∈U) :
    ∃δ:ℝ,0<δ ∧∀p:P.Point,dist p.val a.2.val<δ→S.project (a.1,p)∈U := by
  have hc:Continuous (fun p:P.Point=>S.project (a.1,p)):=
    S.continuous_project.comp (continuous_const.prodMk continuous_id)
  obtain ⟨δ,hδ,hsub⟩:=Metric.isOpen_iff.mp (hU.preimage hc) a.2 ha
  exact ⟨δ,hδ,fun p hp=>hsub hp⟩

/-- A finite raw ball-covering cycle exhausts its entire original gluing class whenever
the actual developing map is locally injective. A common chart margin for the finitely
many selected copies makes every additional copy meet one selected open inside piece. -/
theorem VertexCycle.fiber_subset_of_local_injectivity
    {V:Set P.Point} {x:P.Point} {r:ℝ} (c:S.VertexCycle V x r)
    (ho:IsOpen P.interior) (hcl:P.carrier⊆closure P.interior)
    (hLI:IsLocallyInjective S.evaluation) :
    S.project⁻¹'{S.project (1,x)}⊆range c.copies := by
  classical
  obtain ⟨U,hU,hqU,hInj⟩:=hLI (S.project (1,x))
  have hRawU:∀i:Fin (c.lengthPred+1),S.project (c.copies i)∈U:=by
    intro i
    rw [c.project_eq S i]
    exact hqU
  choose δ hδ hMap using fun i=>S.original_copy_radius_in_open hU (c.copies i) (hRawU i)
  obtain ⟨imin,_himin,hMin⟩:=Set.exists_min_image (univ:Set (Fin (c.lengthPred+1))) δ
    (Set.toFinite _) ⟨0,mem_univ _⟩
  intro b hb
  have hbq:S.project b=S.project (1,x):=hb
  have hbx:S.copyEvaluation b=x.val:=by
    have h:=congrArg S.evaluation hbq
    simpa only [S.evaluation_project,_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.copyEvaluation,one_smul] using h
  obtain ⟨δb,hδb,hMapB⟩:=S.original_copy_radius_in_open hU b (hbq ▸hqU)
  let ρ:=min r (min (δ imin) δb)
  have hρ:0<ρ:=lt_min c.radius_pos (lt_min (hδ imin) hδb)
  have hρr:ρ≤r:=min_le_left _ _
  have hρb:ρ≤δb:=(min_le_right _ _).trans (min_le_right _ _)
  have hρi (i:Fin (c.lengthPred+1)):ρ≤δ i:=
    ((min_le_right _ _).trans (min_le_left _ _)).trans (hMin i (mem_univ _))
  let d:=c.mono S hρ hρr
  let A:Fin (c.lengthPred+1)→Set ℍ:=fun i=>S.vertexCycleInteriorPiece (c.copies i) ρ
  let B:Set ℍ:=S.vertexCycleInteriorPiece b ρ
  have hBopen:IsOpen B:=S.vertexCycleInteriorPiece_isOpen ho b ρ
  have hBcl:x.val∈closure B:=by
    rw [←hbx]
    exact S.vertexCyclePiece_subset_closure_interior hcl b ρ
      ⟨b.2.val,⟨b.2.property,Metric.mem_ball_self hρ⟩,rfl⟩
  have hBball:B⊆Metric.ball x.val ρ:=by
    rintro y ⟨p,hp,rfl⟩
    change dist (b.1•p) x.val<ρ
    rw [←hbx]
    exact ((isometry_smul ℍ b.1).dist_eq p b.2.val).trans_lt hp.2
  have hBallcl:Metric.ball x.val ρ⊆closure (⋃i,A i):=by
    intro z hz
    obtain ⟨i,hi⟩:=mem_iUnion.mp (d.covers.symm ▸hz)
    apply closure_mono (fun y hy=>mem_iUnion.mpr ⟨i,hy⟩)
    exact S.vertexCyclePiece_subset_closure_interior hcl (c.copies i) ρ hi
  obtain ⟨z,_hz,hzB⟩:=mem_closure_iff.mp hBcl univ isOpen_univ (mem_univ _)
  obtain ⟨y,hyB,hyA⟩:=mem_closure_iff.mp (hBallcl (hBball hzB)) B hBopen hzB
  obtain ⟨i,hi⟩:=mem_iUnion.mp hyA
  obtain ⟨p,hp,hpe⟩:=hyB
  obtain ⟨q,hq,hqe⟩:=hi
  let pP:P.Point:=⟨p,P.interior_subset_carrier hp.1⟩
  let qP:P.Point:=⟨q,P.interior_subset_carrier hq.1⟩
  have hpU:S.project (b.1,pP)∈U:=hMapB pP (lt_of_lt_of_le hp.2 hρb)
  have hqU:S.project ((c.copies i).1,qP)∈U:=hMap i qP (lt_of_lt_of_le hq.2 (hρi i))
  have he:S.project (b.1,pP)=S.project ((c.copies i).1,qP):=by
    apply hInj hpU hqU
    change b.1•p=(c.copies i).1•q
    exact hpe.trans hqe.symm
  have hCopies:=S.gluing_interior_rigid ((S.project_eq_iff _ _).mp he) (Or.inl hp.1)
  have hIndexRaw:=congrArg (fun a:S.Generated×P.Point=>a.1) hCopies
  have hIndex:b.1=(c.copies i).1:=hIndexRaw
  have hCenter:b=c.copies i:=S.copy_eq_of_evaluation_same_index hIndex
    (hbx.trans (c.evaluation_eq S i).symm)
  exact ⟨i,hCenter.symm⟩

/-- Whole-class equality follows from genuine local injectivity, with no natural-label
or nonbacktracking assumption on the original finite cycle. -/
theorem VertexCycle.fiber_eq_of_local_injectivity
    {V:Set P.Point} {x:P.Point} {r:ℝ} (c:S.VertexCycle V x r)
    (ho:IsOpen P.interior) (hcl:P.carrier⊆closure P.interior)
    (hLI:IsLocallyInjective S.evaluation) :
    S.project⁻¹'{S.project (1,x)}=range c.copies :=
  subset_antisymm (c.fiber_subset_of_local_injectivity S ho hcl hLI) (c.copies_subset_fiber S)

/-- Every original incident side mate lies in the chosen raw cycle once local injectivity
has established that the cycle exhausts the entire original equivalence class. -/
theorem VertexCycle.incidence_closed_of_local_injectivity
    {V:Set P.Point} {x:P.Point} {r:ℝ} (c:S.VertexCycle V x r)
    (ho:IsOpen P.interior) (hcl:P.carrier⊆closure P.interior)
    (hLI:IsLocallyInjective S.evaluation)
    (i:Fin (c.lengthPred+1)) (s:P.Side) (hx:(c.copies i).2.val∈s.val) :
    S.sideMateCopy (c.copies i) s hx∈range c.copies := by
  rw [←c.fiber_eq_of_local_injectivity S ho hcl hLI]
  change S.project (S.sideMateCopy (c.copies i) s hx)=S.project (1,x)
  exact ((S.project_eq_iff _ _).mpr
    (Relation.EqvGen.rel _ _ (S.step_symm (S.step_sideMateCopy (c.copies i) s hx)))).trans
    (c.project_eq S i)

/--
Actual native side geometry and local injectivity recover all of local tessellation from raw vertex-cycle.
No condition on the length, side-label turns or the whole fiber is an extra hypothesis.
-/
theorem FiniteVertexCycleCondition.finiteFiberLocalTessellationCondition_of_local_injectivity
    (V:Set ℍ) (h:S.FiniteVertexCycleCondition {p:P.Point|p.val∈V}) (hV:IsDiscrete V)
    (hLF:LocallyFinite (fun s:P.Side=>s.val)) (hClosed:∀s:P.Side,IsClosed s.val)
    (ho:IsOpen P.interior) (hcl:P.carrier⊆closure P.interior)
    (hReg:∀p:P.Point,p.val∉V→p.val∈P.interior∨∃s:P.Side,∃ρ:ℝ,S.PairedSideNeighborhood p s ρ)
    (hLI:IsLocallyInjective S.evaluation) : S.FiniteFiberLocalTessellationCondition := by
  have hx:∀x:P.Point,(S.project⁻¹'{S.project (1,x)}).Finite∧
      ∃r₀:ℝ,0<r₀∧∀t:ℝ,0<t→t≤r₀→S.LocalTessellation (1,x) t:=by
    intro x
    by_cases hxV:x.val∈V
    · obtain ⟨r,⟨c⟩⟩:=h x hxV
      exact c.local_radius_of_locally_finite_sides S V hV hLF hClosed ho hcl hReg
        (c.incidence_closed_of_local_injectivity S ho hcl hLI)
    · rcases hReg x hxV with hxInt|⟨s,ρ,hs⟩
      · constructor
        · rw [S.project_fiber_eq_singleton_of_interior (1,x) hxInt]
          exact Set.finite_singleton _
        · exact S.interior_local_radius ho x hxInt
      · exact ⟨hs.finite_class S,hs.local_radius S⟩
  exact ⟨fun x=>(hx x).1,fun x=>(hx x).2⟩

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/--
For the actual native Jordan polygon, the raw finite-cycle condition and genuine
local injectivity imply local tessellation. Nonvertex regularity is derived from actual opposite-side data.
-/
theorem nativeJordan_raw_cycles_local_tessellation_of_local_injectivity
    {P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (C:Set
      ℂ) (hC:_root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hbound:C⊆Metric.closedBall (0:ℂ)
      1) (hInside:P.interior=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordanInside C)
    (hBoundary:P.boundary=(fun z:ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ))⁻¹'C)
    (D:_root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicSideIntervals
      P) (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hRaw:S.FiniteVertexCycleCondition {p:P.Point|p.val∈D.vertices})
    (hOpp:∀s:P.Side,∀x∈s.val,x∉D.vertices→S.OppositeSideNeighborhoods s x)
    (hLI:IsLocallyInjective S.evaluation) : S.FiniteFiberLocalTessellationCondition := by
  let G:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  exact hRaw.finiteFiberLocalTessellationCondition_of_local_injectivity S D.vertices D.vertices_discrete
    D.locallyFinite D.side_geometry.side_closed G.interior_open G.carrier_closure.le
    (G.regularity_of_vertex_preservation S (D.pairing_preserves_vertices S) hOpp) hLI

/--
The corrected developing-chart version of the Poincare criterion needs only the
printed raw finite cycles. Actual uniform charts recover the missing whole-class local tessellation
condition before the native discreteness and literal fundamental-domain conclusions.
This theorem does not identify these charts with a literal uniform raw-star radius.
-/
theorem nativeJordan_raw_cycles_poincare_of_uniform_charts
    {P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (C:Set
      ℂ) (hC:_root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hbound:C⊆Metric.closedBall (0:ℂ)
      1) (hInside:P.interior=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordanInside C)
    (hBoundary:P.boundary=(fun z:ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ))⁻¹'C)
    (D:_root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicSideIntervals
      P) (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hRaw:S.FiniteVertexCycleCondition {p:P.Point|p.val∈D.vertices})
    (hOpp:∀s:P.Side,∀x∈s.val,x∉D.vertices→S.OppositeSideNeighborhoods s x)
    {ε:ℝ} (hε:0<ε) (hCharts:_root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts S.evaluation
      ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element)))∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior := by
  let G:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  exact S.native_poincare_of_uniform_developing_charts
    (nativeJordan_raw_cycles_local_tessellation_of_local_injectivity C hC hbound hInside
      hBoundary D S hRaw hOpp hCharts.isLocalHomeomorph.isLocallyInjective)
    G.interior_open G.interior_connected G.carrier_closure G.countable_sides
    (fun s hs=>⟨G.line ⟨s,hs⟩,G.side_subset_line ⟨s,hs⟩⟩) hε hCharts

/-- The same corrected criterion on the existing concrete geometric bundle. The native
polygon, all side intervals and genuine developing charts remain explicit inputs. -/
theorem _root_.LowDimensionalTopology.Geometry.Polygon.NativeJordanGeodesicPolygon.corrected_raw_cycle_poincare
    (J:_root_.LowDimensionalTopology.Geometry.Polygon.NativeJordanGeodesicPolygon) (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) J.polygon)
    (hRaw:S.FiniteVertexCycleCondition {p:J.polygon.Point|p.val∈J.sideIntervals.vertices})
    (hOpp:∀s:J.polygon.Side,∀x∈s.val,x∉J.sideIntervals.vertices→S.OppositeSideNeighborhoods s x)
    {ε:ℝ} (hε:0<ε) (hCharts:_root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts S.evaluation
      ε) :
    DiscreteTopology S.Generated∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume J.polygon.interior :=
  nativeJordan_raw_cycles_poincare_of_uniform_charts J.curve J.jordan J.contained
    J.interior_eq J.boundary_eq J.sideIntervals S hRaw hOpp hε hCharts

end LowDimensionalTopology.Geometry.Fuchsian
