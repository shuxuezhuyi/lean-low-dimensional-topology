module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.NativeRegularBoundaryGerms
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.FiniteSideCompatibility
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePolygonRegularity
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Geometric original polygon data: its actual regular-open inside, locally finite closed
geodesic sides, actual supporting lines and local open side intervals. No group, equivalence
class, local tessellation, developing chart or fundamental-domain property occurs here. -/
structure NativeGeodesicPolygonGeometry (P : PoincarePolygon ℍ) (V : Set ℍ) where
  interior_open : IsOpen P.interior
  interior_connected : IsConnected P.interior
  carrier_closure : P.carrier=closure P.interior
  regular_open : interior (closure P.interior)=P.interior
  frontier_boundary : frontier P.interior=P.boundary
  locallyFinite : LocallyFinite (fun s : P.Side=>s.val)
  side_closed : ∀s : P.Side,IsClosed s.val
  vertex_discrete : IsDiscrete V
  line : P.Side→_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine
  side_subset_line : ∀s : P.Side,s.val⊆(line s).carrier
  side_two_points : ∀s : P.Side,∃a∈s.val,∃b∈s.val,a≠b
  side_meet_vertex : ∀s t : P.Side,s≠t →∀x∈s.val,x∈t.val →x∈V
  side_interval : ∀s : P.Side,∀x∈s.val,x∉V →∀ᶠy in 𝓝 x,y∈s.val ↔y∈(line s).carrier

/-- Local finiteness and true original side incidence identify the actual boundary germ
with its single original supporting geodesic at a nonvertex side point. -/
theorem NativeGeodesicPolygonGeometry.boundary_line_germ {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hv : x.val∉V) :
    ∀ᶠy in 𝓝 x.val,y∈P.boundary ↔y∈(D.line s).carrier := by
  obtain ⟨r,hr,hNear⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.exists_ball_incident_sides D.locallyFinite D.side_closed x
  filter_upwards [Metric.ball_mem_nhds x.val hr,D.side_interval s x.val hx hv] with y hy hLine
  apply Iff.trans ?_ hLine
  constructor
  · intro hyB
    obtain ⟨t,ht,hyt⟩:=mem_sUnion.mp hyB
    let t' : P.Side:=⟨t,ht⟩
    have hxt:=hNear y hy t' hyt
    have hts : t'=s := by
      by_contra hne
      exact hv (D.side_meet_vertex t' s hne x.val hxt hx)
    exact hts ▸ hyt
  · intro hys
    exact mem_sUnion.mpr ⟨s.val,s.property,hys⟩

/-- Native side maps carry their entire actual supporting geodesic onto the actual
supporting geodesic of the original paired side. -/
theorem NativeGeodesicPolygonGeometry.pairing_line_image {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V) (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (s : P.Side) :
    S.element s '' (D.line s).carrier=(D.line (S.paired s)).carrier := by
  obtain ⟨a,ha,b,hb,hab⟩:=D.side_two_points s
  obtain ⟨M,hM⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine (S.element
    s).isometry (D.line s)
  have himg (z : ℍ) (hz : z∈s.val) : S.element s z∈(S.paired s).val := by
    rw [←S.side_image]
    exact mem_image_of_mem _ hz
  have hEq:=M.eq_of_two_points (D.line (S.paired s)) ((S.element s).injective.ne hab)
    (hM ▸ mem_image_of_mem (S.element s) (D.side_subset_line s ha))
    (hM ▸ mem_image_of_mem (S.element s) (D.side_subset_line s hb))
    (D.side_subset_line _ (himg a ha)) (D.side_subset_line _ (himg b hb))
  rwa [hEq] at hM


namespace PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X] [MetricSpace X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
/-- Complete original vertex cycles force every original side crossing out of a vertex
to land at an actual original vertex. No vertex-invariance assumption is added. -/
theorem CompleteVertexCycleCondition.side_vertex_mem (V : Set X)
    (h : S.CompleteVertexCycleCondition V) (x : P.Point) (hx : x.val∈V)
    (s : P.Side) (hs : x.val∈s.val) : S.generator s •x.val∈V := by
  obtain ⟨r,c,hc⟩:=h x hx
  have hbase : (c.copies 0).2.val∈s.val := by rw [c.base];exact hs
  obtain ⟨i,hi⟩:=c.incidence_complete_of_two_sides S hc 0 s hbase
  have hv:=c.vertices i
  have he : (c.copies i).2.val=S.generator s •x.val := by
    rw [hi]
    change S.generator s •(c.copies 0).2.val=S.generator s •x.val
    rw [c.base]
  change (c.copies i).2.val∈V at hv
  rwa [he] at hv

/-- An original side map cannot send a nonvertex side point to a vertex once the
original complete natural vertex cycles are given. -/
theorem CompleteVertexCycleCondition.side_nonvertex_mem (V : Set X)
    (h : S.CompleteVertexCycleCondition V) (x : P.Point) (hx : x.val∉V)
    (s : P.Side) (hs : x.val∈s.val) : S.generator s •x.val∉V := by
  intro hyV
  have hyS : S.generator s •x.val∈(S.paired s).val := by
    rw [←S.side_image]
    exact ⟨x.val,hs,rfl⟩
  let y : P.Point:=⟨S.generator s •x.val,P.side_subset_carrier (S.paired s) hyS⟩
  have he:=h.side_vertex_mem S V y hyV (S.paired s) hyS
  rw [S.generator_paired,inv_smul_smul] at he
  exact hx he

end PoincareSidePairing


/-- The actual original nonvertex side geometry gives a genuine closed-component germ
for a locally finite, possibly noncompact or infinitely sided original polygon. -/
theorem NativeGeodesicPolygonGeometry.component_germ {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hv : x.val∉V) :
    ∃u : ℍ,u∉(D.line s).carrier ∧∃r : ℝ,0<r ∧∀w : ℍ,dist w x.val<r →
      (w∈P.carrier ↔w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (D.line s) u) := by
  have hxB : x.val∈P.boundary:=mem_sUnion.mpr ⟨s.val,s.property,hx⟩
  have hxF : x.val∈frontier P.interior:=D.frontier_boundary.symm ▸ hxB
  obtain ⟨m,t,hm,hLine,hG⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_regular_closed_line_germ D.interior_open D.regular_open hxF
    (D.line s) (by simpa only [D.frontier_boundary] using D.boundary_line_germ x s hx hv)
  obtain ⟨u,hu,hCut⟩:=native_support_closed_cut_component (D.line s) m t hm hLine x.val
    (D.side_subset_line s hx)
  rw [←D.carrier_closure] at hG
  change ∀ᶠy in 𝓝 x.val,y∈P.carrier ↔y∈{z : ℍ|inner ℝ m
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤t} at hG
  rw [←hCut] at hG
  obtain ⟨r,hr,he⟩:=Metric.eventually_nhds_iff_ball.mp hG
  exact ⟨u,hu,r,hr,he⟩

/-- Nonvertex incidence and genuine local finiteness avoid every other original side. -/
theorem NativeGeodesicPolygonGeometry.unique_side_near {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hv : x.val∉V) :
    ∃r : ℝ,0<r ∧∀t : P.Side,∀p∈t.val,dist p x.val<r →t=s := by
  obtain ⟨r,hr,hNear⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.exists_ball_incident_sides D.locallyFinite D.side_closed x
  refine ⟨r,hr,?_⟩
  intro t p hp hpx
  by_contra hne
  exact hv (D.side_meet_vertex t s hne x.val (hNear p hpx t hp) hx)

/-- A true local closed-component germ identifies its line points with actual original
boundary points, even for arbitrary locally finite original polygons. -/
theorem NativeGeodesicPolygonGeometry.component_germ_boundary {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V) (x : ℍ) (N :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u : ℍ)
    (hu : u∉N.carrier) (r : ℝ)
    (hG : ∀w : ℍ,dist w x<r →(w∈P.carrier ↔w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u))
    {z : ℍ} (hz : dist z x<r) (hzP : z∈P.carrier) (hzL : z∈N.carrier) : z∈P.boundary := by
  apply hzP.resolve_left
  intro hzI
  apply native_closed_halfPlane_not_nhds N u z hu hzL
  filter_upwards [D.interior_open.mem_nhds hzI,Metric.isOpen_ball.mem_nhds hz] with w hwI hwBall
  exact (hG w hwBall).mp (P.interior_subset_carrier hwI)


/-- Actual endpoint preservation and the original opposite-side-neighborhood convention
imply genuine paired-side half-balls in the original locally finite native geometry. -/
theorem NativeGeodesicPolygonGeometry.oppositeSideNeighborhoods_paired_of_vertex_preservation {P : PoincarePolygon ℍ}
    {V : Set ℍ} (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hV : ∀z∈V,∀t : P.Side,z∈t.val →S.element t z∈V)
    (x : P.Point) (s : P.Side) (hx : x.val∈s.val) (hv : x.val∉V)
    (hOpp : S.OppositeSideNeighborhoods s x.val) : ∃r : ℝ,S.PairedSideNeighborhood x s r := by
  let f:=S.element s
  let N:=D.line s
  let M:=D.line (S.paired s)
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hySide : f x.val∈(S.paired s).val := by
    rw [←S.side_image]
    exact ⟨x.val,hx,rfl⟩
  let y : P.Point:=⟨f x.val,P.side_subset_carrier (S.paired s) hySide⟩
  have hyv : y.val∉V := by
    intro hyV
    have he:=hV y.val hyV (S.paired s) hySide
    change S.element (S.paired s) (f x.val)∈V at he
    rw [S.element_paired] at he
    change f.symm (f x.val)∈V at he
    rw [f.symm_apply_apply] at he
    exact hv he
  obtain ⟨u,hu,r₀,hr₀,h₀⟩:=D.component_germ x s hx hv
  obtain ⟨v,hvM,r₁,hr₁,h₁⟩:=D.component_germ y (S.paired s) hySide hyv
  have hLines : f '' N.carrier=M.carrier:=D.pairing_line_image S s
  let w:=f.symm v
  have hw : w∉N.carrier := by
    intro hw
    apply hvM
    rw [←hLines]
    exact ⟨w,hw,f.apply_symm_apply v⟩
  have hImage : f '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane M v := by
    simpa only [w,f.apply_symm_apply] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closed_halfPlane f N M hLines w hw
  have hPull (z : ℍ) : f z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane M v ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w := by
    rw [←hImage]
    exact f.injective.mem_set_image
  have hActual : P.carrier∪(fun z : ℍ=>f z) ⁻¹' P.carrier∈𝓝 x.val:=
    (S.oppositeSideNeighborhoods_iff s x.val).mp hOpp
  have hComponents : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w∈𝓝 x.val := by
    filter_upwards [hActual,Metric.ball_mem_nhds x.val (lt_min hr₀ hr₁)] with z hz hzBall
    have hd₀ : dist z x.val<r₀:=lt_of_lt_of_le hzBall (min_le_left _ _)
    have hd₁ : dist (f z) y.val<r₁ := by
      change dist (f z) (f x.val)<r₁
      rw [f.isometry.dist_eq]
      exact lt_of_lt_of_le hzBall (min_le_right _ _)
    rcases hz with hz | hz
    · exact Or.inl ((h₀ z hd₀).mp hz)
    · exact Or.inr ((hPull z).mp ((h₁ (f z) hd₁).mp hz))
  obtain ⟨a,t,ha,hLine⟩:=N.klein_affine_equation
  have hIntersect : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w=N.carrier:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlanes_opposite N a t ha hLine u w x.val hu hw
      (D.side_subset_line s hx) hComponents
  obtain ⟨r₂,hr₂,h₂⟩:=D.unique_side_near x s hx hv
  obtain ⟨r₃,hr₃,h₃⟩:=D.unique_side_near y (S.paired s) hySide hyv
  obtain ⟨r₄,hr₄,h₄⟩:=Metric.mem_nhds_iff.mp hActual
  let r:=min (min r₀ r₁) (min r₂ (min r₃ r₄))
  have hr : 0<r:=lt_min (lt_min hr₀ hr₁) (lt_min hr₂ (lt_min hr₃ hr₄))
  have hrr₀ : r≤r₀:=le_trans (min_le_left _ _) (min_le_left _ _)
  have hrr₁ : r≤r₁:=le_trans (min_le_left _ _) (min_le_right _ _)
  have hrr₂ : r≤r₂:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hrr₃ : r≤r₃:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrr₄ : r≤r₄:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨r,⟨hr,hx,?_,?_,?_,?_⟩⟩
  · intro a z hz hzx
    exact h₂ a z hz (lt_of_lt_of_le hzx hrr₂)
  · intro a z hz hzy
    exact h₃ a z hz (lt_of_lt_of_le hzy hrr₃)
  · intro z hz
    exact h₄ (lt_of_lt_of_le hz hrr₄)
  · intro z hz hzP hzfP
    have hd₀ : dist z x.val<r₀:=lt_of_lt_of_le hz hrr₀
    have hd₁ : dist (f z) y.val<r₁ := by
      change dist (f z) (f x.val)<r₁
      rw [f.isometry.dist_eq]
      exact lt_of_lt_of_le hz hrr₁
    have hzL : z∈N.carrier := by
      rw [←hIntersect]
      exact ⟨(h₀ z hd₀).mp hzP,(hPull z).mp ((h₁ (f z) hd₁).mp hzfP)⟩
    have hzBoundary:=D.component_germ_boundary x.val N u hu r₀ h₀ hd₀ hzP hzL
    obtain ⟨a,ha,hza⟩:=mem_sUnion.mp hzBoundary
    let a' : P.Side:=⟨a,ha⟩
    have he:=h₂ a' z hza (lt_of_lt_of_le hz hrr₂)
    exact he ▸ hza



/-- The original opposite-neighborhood convention and original complete vertex cycles
imply literal paired-side half-balls in the general actual locally finite native geometry. -/
theorem NativeGeodesicPolygonGeometry.oppositeSideNeighborhoods_paired {P : PoincarePolygon ℍ}
    {V : Set ℍ} (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (hCycles : S.CompleteVertexCycleCondition V)
    (x : P.Point) (s : P.Side) (hx : x.val∈s.val) (hv : x.val∉V)
    (hOpp : S.OppositeSideNeighborhoods s x.val) : ∃r : ℝ,S.PairedSideNeighborhood x s r := by
  apply D.oppositeSideNeighborhoods_paired_of_vertex_preservation S ?_ x s hx hv hOpp
  intro z hz t ht
  let p : P.Point:=⟨z,P.side_subset_carrier t ht⟩
  exact hCycles.side_vertex_mem S V p hz t ht

/-- A genuine locally finite side family in the actual hyperbolic plane is countable;
countability is a consequence of the original geometry, not an additional input. -/
theorem NativeGeodesicPolygonGeometry.countable_sides {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V) : P.sides.Countable := by
  have h:=(D.locallyFinite.countable_univ (fun s=>P.side_nonempty s.val s.property)).image
    (Subtype.val : P.Side→Set ℍ)
  have he : range (Subtype.val : P.Side→Set ℍ)=P.sides := by
    ext z
    constructor
    · rintro ⟨s,rfl⟩
      exact s.property
    · intro hz
      exact ⟨⟨z,hz⟩,rfl⟩
  simpa only [image_univ,he] using h

/-- Original side geometry and actual endpoint preservation derive regular nonvertex
half-neighborhoods from the original universal opposite-neighborhood assumption. -/
theorem NativeGeodesicPolygonGeometry.regularity_of_vertex_preservation {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hV : ∀z∈V,∀t : P.Side,z∈t.val →S.element t z∈V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x) :
    ∀x : P.Point,x.val∉V →x.val∈P.interior ∨∃s r,S.PairedSideNeighborhood x s r := by
  intro x hx
  rcases x.property with hxI | hxB
  · exact Or.inl hxI
  · obtain ⟨s,hs,hxs⟩:=mem_sUnion.mp hxB
    let s' : P.Side:=⟨s,hs⟩
    obtain ⟨r,hr⟩:=D.oppositeSideNeighborhoods_paired_of_vertex_preservation S hV x s' hxs hx (hOpp s' x.val hxs hx)
    exact Or.inr ⟨s',r,hr⟩

/-- The original geometric polygon and complete natural cycles derive regular nonvertex
half-neighborhoods from the original universal opposite-neighborhood assumption. -/
theorem NativeGeodesicPolygonGeometry.regularity {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (hCycles : S.CompleteVertexCycleCondition V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x) :
    ∀x : P.Point,x.val∉V →x.val∈P.interior ∨∃s r,S.PairedSideNeighborhood x s r := by
  intro x hx
  rcases x.property with hxI | hxB
  · exact Or.inl hxI
  · obtain ⟨s,hs,hxs⟩:=mem_sUnion.mp hxB
    let s' : P.Side:=⟨s,hs⟩
    obtain ⟨r,hr⟩:=D.oppositeSideNeighborhoods_paired S hCycles x s' hxs hx (hOpp s' x.val hxs hx)
    exact Or.inr ⟨s',r,hr⟩

/--
The original general geometric polygon, original complete natural cycles and original
side compatibility imply actual local tessellation, without class, chart, overlap or finite-sidedness hypotheses.
-/
theorem NativeGeodesicPolygonGeometry.local_tessellation {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (hCycles : S.CompleteVertexCycleCondition V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x) :
    S.FiniteFiberLocalTessellationCondition := by
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  exact hCycles.finiteFiberLocalTessellationCondition S V D.vertex_discrete D.locallyFinite D.side_closed
    D.interior_open D.carrier_closure.le (D.regularity S hCycles hOpp)

/-- In the general actual native geometric polygon, the original complete cycles, side
compatibility and uniform developing-ball chart radius imply discreteness and the literal
original fundamental polygon. Compactness and finite-sidedness are not assumed. -/
theorem NativeGeodesicPolygonGeometry.poincare {P : PoincarePolygon ℍ} {V : Set ℍ}
    (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) (hCycles : S.CompleteVertexCycleCondition V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x)
    {ε : ℝ} (hUniform : S.UniformLocalTessellationCover ε) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior := by
  exact S.native_poincare_of_uniform_cover (D.local_tessellation S hCycles hOpp) hUniform
    D.interior_open D.interior_connected D.carrier_closure D.countable_sides
    (fun s hs=>⟨D.line ⟨s,hs⟩,D.side_subset_line ⟨s,hs⟩⟩)


/-- The literal original finite Jordan polygon inside is genuinely regular open in the
actual native metric topology; this property is derived rather than imposed. -/
theorem finitePolygon_interior_regular_open {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    interior (closure (finiteDiscPoincarePolygon Q hf).interior)=(finiteDiscPoincarePolygon Q hf).interior := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hfc : Continuous f:=Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f:=hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  change interior (closure (f ⁻¹' Q.complexInterior))=f ⁻¹' Q.complexInterior
  rw [←hfo.preimage_closure_eq_closure_preimage hfc,
    ←hfo.preimage_interior_eq_interior_preimage hfc,Q.interior_closure_complexInterior]

/-- The literal original native Jordan boundary is the genuine frontier of its actual inside. -/
theorem finitePolygon_frontier_boundary {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    frontier (finiteDiscPoincarePolygon Q hf).interior=(finiteDiscPoincarePolygon Q hf).boundary := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hfc : Continuous f:=Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f:=hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  change frontier (f ⁻¹' Q.complexInterior)=_
  rw [←hfo.preimage_frontier_eq_frontier_preimage hfc,Q.frontier_complexInterior,
    finiteDiscPoincarePolygon_boundary]

/-- Every original finite nonvertex side point is in a genuine local open interval of
its supporting h-line, without global convexity of the original Jordan polygon. -/
theorem finitePolygon_nonvertex_side_interval {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m) (x : ℍ)
    (hx : x∈finitePolygonSide Q i) (hv : x∉range (finitePolygonVertex Q hf)) :
    ∀ᶠy in 𝓝 x,y∈finitePolygonSide Q i ↔y∈(finitePolygonLine Q i).carrier := by
  obtain ⟨m₀,t₀,hm,hLine,hleft,hright⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_native_side_equation Q hf i
  have hOpen:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_nonvertex_klein_openSegment Q hf hx hv
  have hB : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
      y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary ↔inner ℝ m₀ y=t₀ := by
    filter_upwards [Q.klein_boundary_line_germ_edge i hOpen] with y hy
    exact hy.trans (_root_.LowDimensionalTopology.Geometry.Fuchsian.polygonLineEquation_iff_support
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Q.vertices_injective.ne
        (Q.next_ne_self i).symm))
      hm hleft hright y)
  have hNative:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous.continuousAt.eventually hB
  have hb (z : ℍ) : z∈(finiteDiscPoincarePolygon Q hf).boundary ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image]
    constructor
    · rintro ⟨a,⟨j,rfl⟩,hza⟩
      exact mem_iUnion.mpr ⟨j,hza⟩
    · intro hz
      obtain ⟨j,hj⟩:=mem_iUnion.mp hz
      exact mem_sUnion.mpr ⟨finitePolygonSide Q j,mem_range_self j,hj⟩
  let x' : (finiteDiscPoincarePolygon Q hf).Point:=
    ⟨x,(finiteDiscPoincarePolygon Q hf).side_subset_carrier (finitePolygonSideEquiv Q hf i) hx⟩
  obtain ⟨r,hr,hNear⟩:=finitePolygon_nonvertex_unique_side_near Q hf x' i hx hv
  filter_upwards [hNative,Metric.ball_mem_nhds x hr] with y hy hd
  have hBoundary : y∈(finiteDiscPoincarePolygon Q hf).boundary ↔y∈(finitePolygonLine Q i).carrier:=
    (hb y).trans (hy.trans (hLine y).symm)
  apply Iff.trans ?_ hBoundary
  constructor
  · intro hys
    exact mem_sUnion.mpr ⟨finitePolygonSide Q i,mem_range_self i,hys⟩
  · intro hyB
    obtain ⟨a,ha,hya⟩:=mem_sUnion.mp hyB
    let a' : (finiteDiscPoincarePolygon Q hf).Side:=⟨a,ha⟩
    have he:=hNear a' y hya hd
    change y∈(finitePolygonSideEquiv Q hf i).val
    exact he ▸ hya

/-- Every original finite Jordan polygon supplies all of the general native geometric
polygon data from its actual original vertices and sides, without assuming any group property. -/
def finitePolygon_native_geometry {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    NativeGeodesicPolygonGeometry (finiteDiscPoincarePolygon Q hf) (range (finitePolygonVertex Q hf)) where
  interior_open:=finiteDiscPoincarePolygon_interior_isOpen Q hf
  interior_connected:=finiteDiscPoincarePolygon_interior_isConnected Q hf
  carrier_closure:=finiteDiscPoincarePolygon_carrier Q hf
  regular_open:=finitePolygon_interior_regular_open Q hf
  frontier_boundary:=finitePolygon_frontier_boundary Q hf
  locallyFinite:=finiteDiscPoincarePolygon_locallyFiniteSides Q hf
  side_closed:=finiteDiscPoincarePolygon_closedSides Q hf
  vertex_discrete:=finitePolygonVertices_isDiscrete Q hf
  line s:=finitePolygonLine Q ((finitePolygonSideEquiv Q hf).symm s)
  side_subset_line:=by
    intro s
    obtain ⟨i,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective s
    change finitePolygonSide Q i⊆(finitePolygonLine Q ((finitePolygonSideEquiv Q hf).symm
      (finitePolygonSideEquiv Q hf i))).carrier
    rw [(finitePolygonSideEquiv Q hf).symm_apply_apply]
    exact finitePolygonSide_subset_line Q i
  side_two_points:=by
    intro s
    obtain ⟨i,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective s
    exact ⟨finitePolygonVertex Q hf i,finitePolygonSide_left_mem Q hf i,
      finitePolygonVertex Q hf (finRotate m i),finitePolygonSide_right_mem Q hf i,
      (finitePolygonVertex_injective Q hf).ne (Q.next_ne_self i).symm⟩
  side_meet_vertex:=by
    intro s t hst x hx ht
    obtain ⟨i,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective s
    obtain ⟨j,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective t
    have hij : i≠j:=fun he=>hst (congrArg (finitePolygonSideEquiv Q hf) he)
    exact finitePolygon_common_sides_vertex Q hf hij hx ht
  side_interval:=by
    intro s x hx hv
    obtain ⟨i,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective s
    change ∀ᶠy in 𝓝 x,y∈finitePolygonSide Q i ↔y∈(finitePolygonLine Q
      ((finitePolygonSideEquiv Q hf).symm (finitePolygonSideEquiv Q hf i))).carrier
    rw [(finitePolygonSideEquiv Q hf).symm_apply_apply]
    exact finitePolygon_nonvertex_side_interval Q hf i x hx hv

end LowDimensionalTopology.Geometry.Polygon
