module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCycleFolding
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativePoincarePolygons
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X] [MetricSpace X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- A locally finite family of actual closed sides has no nonincident side in a sufficiently small ball. -/
theorem exists_ball_incident_sides (hLF : LocallyFinite (fun s : P.Side=>s.val))
    (hClosed : ∀s : P.Side,IsClosed s.val) (x : P.Point) :
    ∃r : ℝ,0<r ∧ ∀p : X,dist p x.val<r →∀s : P.Side,p∈s.val → x.val∈s.val := by
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hLF.iInter_compl_mem_nhds hClosed x.val)
  refine ⟨r,hr,?_⟩
  intro p hp s hs
  by_contra hxs
  have hn := mem_iInter₂.mp (hBall hp) s hxs
  exact hn hs

/-- A genuine discrete vertex set contains no other vertex in a sufficiently small ambient ball. -/
theorem exists_ball_single_vertex (V : Set X) (hV : IsDiscrete V) (x : P.Point) (hx : x.val∈V) :
    ∃r : ℝ,0<r ∧ ∀p∈V,dist p x.val<r →p=x.val := by
  obtain ⟨U,hU,hUV⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hV x.val hx
  have hxU : x.val∈U := by
    have hxUV : x.val∈U∩V := by rw [hUV];exact mem_singleton x.val
    exact hxUV.1
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  refine ⟨r,hr,?_⟩
  intro p hp hpr
  have hpUV : p∈U∩V := ⟨hBall hpr,hp⟩
  rwa [hUV,mem_singleton_iff] at hpUV

/-- Actual closed-side local finiteness and an isolated geometric vertex set provide one
common small radius for all representatives of a genuine finite vertex cycle. -/
theorem VertexCycle.exists_regular_radius [IsIsometricSMul S.Generated X]
    (V : Set X) (hV : IsDiscrete V)
    (hLF : LocallyFinite (fun s : P.Side=>s.val)) (hClosed : ∀s : P.Side,IsClosed s.val)
    (hReg : ∀p : P.Point,p.val∉V →
      p.val∈P.interior ∨ ∃s : P.Side,∃ρ : ℝ,S.PairedSideNeighborhood p s ρ)
    {x : P.Point} {r : ℝ} (h : S.VertexCycle {p : P.Point | p.val∈V} x r) :
    ∃t : ℝ,0<t ∧ t≤r ∧
      (∀i,∀p∈P.carrier,dist p (h.copies i).2.val<t →
        ∀s : P.Side,p∈s.val → (h.copies i).2.val∈s.val) ∧
      (∀i,∀p : P.Point,dist p.val (h.copies i).2.val<t →
        p.val≠(h.copies i).2.val →
        p.val∈P.interior ∨ ∃s : P.Side,∃ρ : ℝ,S.PairedSideNeighborhood p s ρ) := by
  have hi : ∀i : Fin (h.lengthPred+1),∃t : ℝ,0<t ∧
      (∀p : X,dist p (h.copies i).2.val<t →∀s : P.Side,p∈s.val → (h.copies i).2.val∈s.val) ∧
      ∀p∈V,dist p (h.copies i).2.val<t →p=(h.copies i).2.val := by
    intro i
    obtain ⟨a,ha,hA⟩ := exists_ball_incident_sides hLF hClosed (h.copies i).2
    obtain ⟨b,hb,hB⟩ := exists_ball_single_vertex V hV (h.copies i).2 (h.vertices i)
    refine ⟨min a b,lt_min ha hb,?_,?_⟩
    · intro p hp
      exact hA p (lt_of_lt_of_le hp (min_le_left _ _))
    · intro p hp hd
      exact hB p hp (lt_of_lt_of_le hd (min_le_right _ _))
  choose δ hδ hSides hVertices using hi
  obtain ⟨i,_hi,hmin⟩ := Set.exists_min_image (Set.univ : Set (Fin (h.lengthPred+1))) δ
    (Set.toFinite _) (by exact ⟨0,mem_univ _⟩)
  let t := min r (δ i)
  have ht : 0<t := lt_min h.radius_pos (hδ i)
  have htδ (j : Fin (h.lengthPred+1)) : t≤δ j := (min_le_right _ _).trans (hmin j (mem_univ _))
  refine ⟨t,ht,min_le_left _ _,?_,?_⟩
  · intro j p _hp hd
    exact hSides j p (lt_of_lt_of_le hd (htδ j))
  · intro j p hd hne
    apply hReg p
    intro hpV
    exact hne (hVertices j p.val hpV (lt_of_lt_of_le hd (htδ j)))

/--
The original geometric side and vertex conditions reduce local tessellation to complete natural vertex cycles;
the neighboring-point and nonincident-side obligations are derived rather than assumed.
-/
theorem VertexCycle.local_radius_of_locally_finite_sides [IsIsometricSMul S.Generated X]
    (V : Set X) (hV : IsDiscrete V)
    (hLF : LocallyFinite (fun s : P.Side=>s.val)) (hClosed : ∀s : P.Side,IsClosed s.val)
    (ho : IsOpen P.interior) (hcl : P.carrier ⊆ closure P.interior)
    (hReg : ∀p : P.Point,p.val∉V →
      p.val∈P.interior ∨ ∃s : P.Side,∃ρ : ℝ,S.PairedSideNeighborhood p s ρ)
    {x : P.Point} {r : ℝ} (h : S.VertexCycle {p : P.Point | p.val∈V} x r)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies) :
    (S.project ⁻¹' {S.project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀t : ℝ,0<t → t≤r₀ → S.LocalTessellation (1,x) t := by
  obtain ⟨t,ht,htr,hNear,hRegular⟩ := h.exists_regular_radius S V hV hLF hClosed hReg
  exact (h.mono S ht htr).local_radius_of_regular_sides S ho hcl hc hNear hRegular

/-- A complete natural original vertex cycle explicitly exhausts the incoming and outgoing
original sides at each of its representatives. No condition on a quotient fiber is part of this definition. -/
def CompleteVertexCycleCondition (V : Set X) : Prop :=
  ∀x : P.Point,x.val∈V →∃r : ℝ,∃h : S.VertexCycle {p : P.Point | p.val∈V} x r,
    ∀i : Fin (h.lengthPred+1),∀s : P.Side,(h.copies i).2.val∈s.val →
      s=h.nextSide S i ∨ s=S.paired (h.nextSide S ((finRotate (h.lengthPred+1)).symm i))

/-- A complete natural cycle in particular supplies the original finite cyclic ball-cover data. -/
theorem CompleteVertexCycleCondition.finiteVertexCycleCondition (V : Set X)
    (h : S.CompleteVertexCycleCondition V) : S.FiniteVertexCycleCondition {p : P.Point | p.val∈V} := by
  intro x hx
  obtain ⟨r,c,_hc⟩ := h x hx
  exact ⟨r,⟨c⟩⟩

/--
Complete natural vertex cycles and the original regular polygon geometry imply all of local tessellation.
Side-local finiteness and vertex isolation produce the needed small balls in the proof.
-/
theorem CompleteVertexCycleCondition.finiteFiberLocalTessellationCondition [IsIsometricSMul S.Generated X]
    (V : Set X) (h : S.CompleteVertexCycleCondition V) (hV : IsDiscrete V)
    (hLF : LocallyFinite (fun s : P.Side=>s.val)) (hClosed : ∀s : P.Side,IsClosed s.val)
    (ho : IsOpen P.interior) (hcl : P.carrier ⊆ closure P.interior)
    (hReg : ∀p : P.Point,p.val∉V →
      p.val∈P.interior ∨ ∃s : P.Side,∃ρ : ℝ,S.PairedSideNeighborhood p s ρ) :
    S.FiniteFiberLocalTessellationCondition := by
  have hx : ∀x : P.Point,(S.project ⁻¹' {S.project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀t : ℝ,0<t → t≤r₀ → S.LocalTessellation (1,x) t := by
    intro x
    by_cases hxV : x.val∈V
    · obtain ⟨r,c,hc⟩ := h x hxV
      exact c.local_radius_of_locally_finite_sides S V hV hLF hClosed ho hcl hReg
        (c.incidence_complete_of_two_sides S hc)
    · rcases hReg x hxV with hxInt | ⟨s,ρ,hs⟩
      · constructor
        · rw [S.project_fiber_eq_singleton_of_interior (1,x) hxInt]
          exact Set.finite_singleton _
        · exact S.interior_local_radius ho x hxInt
      · exact ⟨hs.finite_class S,hs.local_radius S⟩
  exact ⟨fun x=>(hx x).1,fun x=>(hx x).2⟩

open scoped UpperHalfPlane
open MeasureTheory LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Complete original vertex cycles give the actual native discrete group and the literal
original fundamental polygon once the original uniform recentered chart condition holds. -/
theorem CompleteVertexCycleCondition.native_poincare
    {Q : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (T :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ ≃ᵢ ℍ) Q)
    (V : Set ℍ) (h : T.CompleteVertexCycleCondition V) (hV : IsDiscrete V)
    (hLF : LocallyFinite (fun s : Q.Side=>s.val)) (hClosed : ∀s : Q.Side,IsClosed s.val)
    (ho : IsOpen Q.interior) (hconn : IsConnected Q.interior)
    (hcl : Q.carrier=closure Q.interior)
    (hReg : ∀p : Q.Point,p.val∉V →
      p.val∈Q.interior ∨ ∃s : Q.Side,∃ρ : ℝ,T.PairedSideNeighborhood p s ρ)
    {ε : ℝ} (hu : T.UniformLocalTessellationCover ε)
    (hcount : Q.sides.Countable) (hside : ∀s∈Q.sides,∃L :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s⊆L.carrier) :
    DiscreteTopology (↥(Subgroup.closure (range T.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain T.Generated ℍ volume Q.interior := by
  let : IsIsometricSMul T.Generated ℍ := (T.native_metric_assumptions ho hconn).generatedIsometricSMul T
  exact T.native_poincare_of_uniform_cover
    (h.finiteFiberLocalTessellationCondition T V hV hLF hClosed ho hcl.le hReg) hu ho hconn hcl hcount hside

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
