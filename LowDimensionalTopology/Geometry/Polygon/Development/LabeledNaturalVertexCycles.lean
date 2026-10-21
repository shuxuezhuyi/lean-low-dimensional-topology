module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareVertexCycles
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePairedSideStars
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanEndpointExclusion
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X] [MetricSpace X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- The original outgoing side labels of a natural closed vertex walk. Each literal
crossing advances to the next original copy, and the walk exits by the other original
incident side rather than immediately reversing its incoming label. This retains the
original labels even when two supports or two reflections coincide. -/
structure VertexCycle.NaturalLabels {V : Set P.Point} {x : P.Point} {r : ℝ}
    (c : S.VertexCycle V x r) where
  side : Fin (c.lengthPred+1) → P.Side
  crossing : ∀i,∃hi : (c.copies i).2.val∈(side i).val,
    S.sideMateCopy (c.copies i) (side i) hi=c.copies (finRotate (c.lengthPred+1) i)
  turns : ∀i,side i≠S.paired (side ((finRotate (c.lengthPred+1)).symm i))

theorem VertexCycle.NaturalLabels.previous_side_mem {V : Set P.Point} {x : P.Point} {r : ℝ}
    {c : S.VertexCycle V x r} (L : c.NaturalLabels S) (i : Fin (c.lengthPred+1)) :
    (c.copies i).2.val∈(S.paired (L.side ((finRotate (c.lengthPred+1)).symm i))).val := by
  let j:=(finRotate (c.lengthPred+1)).symm i
  obtain ⟨hj,he⟩:=L.crossing j
  have hi : finRotate (c.lengthPred+1) j=i:=(finRotate (c.lengthPred+1)).apply_symm_apply i
  rw [hi] at he
  have hm:=S.sideMateCopy_mem_paired (c.copies j) (L.side j) hj
  rw [he] at hm
  exact hm

theorem VertexCycle.NaturalLabels.previous_side_mate {V : Set P.Point} {x : P.Point} {r : ℝ}
    {c : S.VertexCycle V x r} (L : c.NaturalLabels S) (i : Fin (c.lengthPred+1))
    (hi : (c.copies i).2.val∈(S.paired (L.side ((finRotate (c.lengthPred+1)).symm i))).val) :
    S.sideMateCopy (c.copies i) (S.paired (L.side ((finRotate (c.lengthPred+1)).symm i))) hi=
      c.copies ((finRotate (c.lengthPred+1)).symm i) := by
  let j:=(finRotate (c.lengthPred+1)).symm i
  obtain ⟨hj,he⟩:=L.crossing j
  have hrot : finRotate (c.lengthPred+1) j=i:=(finRotate (c.lengthPred+1)).apply_symm_apply i
  rw [hrot] at he
  have undo {a b : S.Copy} {t : P.Side} (ha : a.2.val∈t.val)
      (heq : S.sideMateCopy a t ha=b) (hb : b.2.val∈(S.paired t).val) :
      S.sideMateCopy b (S.paired t) hb=a := by
    subst b
    exact S.sideMateCopy_paired a t ha
  exact undo hj he hi

/-- Actual valence two and the original other-side rule exhaust every literal original
side incidence. No quotient-fiber or local-chart condition is introduced. -/
theorem VertexCycle.NaturalLabels.incidence_complete {V : Set P.Point} {x : P.Point} {r : ℝ}
    {c : S.VertexCycle V x r} (L : c.NaturalLabels S)
    (hTwo : ∀i : Fin (c.lengthPred+1),∀s t : P.Side,s≠t  →
      (c.copies i).2.val∈s.val  → (c.copies i).2.val∈t.val  →
      ∀v : P.Side,(c.copies i).2.val∈v.val  → v=s ∨v=t) :
    ∀i : Fin (c.lengthPred+1),∀s : P.Side,∀hi : (c.copies i).2.val∈s.val,
      S.sideMateCopy (c.copies i) s hi∈range c.copies := by
  intro i s hi
  obtain ⟨hout,hStep⟩:=L.crossing i
  rcases hTwo i (L.side i) (S.paired (L.side ((finRotate (c.lengthPred+1)).symm i)))
      (L.turns i) hout (L.previous_side_mem S i) s hi with hs | hs
  · subst s
    exact ⟨finRotate (c.lengthPred+1) i,hStep.symm⟩
  · subst s
    exact ⟨(finRotate (c.lengthPred+1)).symm i,(L.previous_side_mate S i hi).symm⟩



/--
The original vertex-cycle condition, using complete natural labeled side walks rather
than arbitrary backtracking walks or a choice of a label among coincident reflections.
-/
def NaturalVertexCycleCondition (V : Set X) : Prop :=
  ∀x : P.Point,x.val∈V  → ∃r : ℝ,∃c : S.VertexCycle {p : P.Point|p.val∈V} x r,
    Nonempty (c.NaturalLabels S)

/--
Actual valence two and the original labeled natural cycles imply the whole original
local tessellation condition. All quotient fibers and neighboring-point identifications are conclusions.
-/
theorem NaturalVertexCycleCondition.finiteFiberLocalTessellationCondition [IsIsometricSMul S.Generated X]
    (V : Set X) (h : S.NaturalVertexCycleCondition V) (hV : IsDiscrete V)
    (hLF : LocallyFinite (fun s : P.Side=>s.val)) (hClosed : ∀s : P.Side,IsClosed s.val)
    (ho : IsOpen P.interior) (hcl : P.carrier⊆closure P.interior)
    (hTwo : ∀x∈V,∀s t : P.Side,s≠t  → x∈s.val  → x∈t.val  →
      ∀v : P.Side,x∈v.val  → v=s ∨v=t)
    (hReg : ∀p : P.Point,p.val∉V  → p.val∈P.interior ∨∃s r,S.PairedSideNeighborhood p s r) :
    S.FiniteFiberLocalTessellationCondition := by
  have hx : ∀x : P.Point,(S.project ⁻¹' {S.project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧∀r : ℝ,0<r  → r ≤ r₀  → S.LocalTessellation (1,x) r := by
    intro x
    by_cases hxV : x.val∈V
    · obtain ⟨r,c,⟨L⟩⟩:=h x hxV
      have hc := L.incidence_complete S (fun i=>hTwo (c.copies i).2.val (c.vertices i))
      exact c.local_radius_of_locally_finite_sides S V hV hLF hClosed ho hcl hReg hc
    · rcases hReg x hxV with hxInt | ⟨s,r,hs⟩
      · constructor
        · rw [S.project_fiber_eq_singleton_of_interior (1,x) hxInt]
          exact Set.finite_singleton _
        · exact S.interior_local_radius ho x hxInt
      · exact ⟨hs.finite_class S,hs.local_radius S⟩
  exact ⟨fun x=>(hx x).1,fun x=>(hx x).2⟩

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
