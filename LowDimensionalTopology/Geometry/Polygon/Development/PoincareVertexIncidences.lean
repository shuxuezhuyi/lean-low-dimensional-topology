module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareVertexCycles
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- The literal original side-crossing equations determine precisely the original neighboring copy. -/
theorem sideMateCopy_eq_of_side_step (a b : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val)
    (hy : b.2.val=S.generator s • a.2.val) (hg : a.1=b.1*S.generator s) :
    S.sideMateCopy a s hx=b := by
  apply Prod.ext
  · change a.1*(S.generator s)⁻¹=b.1
    rw [hg]
    group
  · exact Subtype.ext hy.symm

variable [MetricSpace X]

/-- The original finite side cycle has a genuine forward side at every position, including its closing step. -/
theorem VertexCycle.next_side_spec {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1)) :
    ∃ s : P.Side,∃ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx=h.copies (finRotate (h.lengthPred+1) i) := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · obtain ⟨s,hs,hy,hg⟩ := h.closing
    refine ⟨s,hs,?_⟩
    rw [finRotate_last]
    exact S.sideMateCopy_eq_of_side_step _ _ s hs hy hg
  · obtain ⟨s,hs,hy,hg⟩ := h.adjacent j
    refine ⟨s,hs,?_⟩
    have he : finRotate (h.lengthPred+1) j.castSucc=j.succ := finRotate_of_lt j.isLt
    rw [he]
    exact S.sideMateCopy_eq_of_side_step _ _ s hs hy hg

def VertexCycle.nextSide {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1)) : P.Side :=
  Classical.choose (h.next_side_spec S i)

theorem VertexCycle.nextSide_mem {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1)) :
    (h.copies i).2.val ∈ (h.nextSide S i).val :=
  Classical.choose (Classical.choose_spec (h.next_side_spec S i))

theorem VertexCycle.nextSide_mate {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1)) :
    S.sideMateCopy (h.copies i) (h.nextSide S i) (h.nextSide_mem S i)=
      h.copies (finRotate (h.lengthPred+1) i) :=
  Classical.choose_spec (Classical.choose_spec (h.next_side_spec S i))

/-- The inverse-pair rule identifies the preceding actual copy across the incoming side. -/
theorem VertexCycle.previousSide_mate {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1))
    (hx : (h.copies i).2.val ∈ (S.paired (h.nextSide S ((finRotate (h.lengthPred+1)).symm i))).val) :
    S.sideMateCopy (h.copies i) (S.paired (h.nextSide S ((finRotate (h.lengthPred+1)).symm i))) hx=
      h.copies ((finRotate (h.lengthPred+1)).symm i) := by
  let j := (finRotate (h.lengthPred+1)).symm i
  have he := h.nextSide_mate S j
  have hi : finRotate (h.lengthPred+1) j=i := (finRotate (h.lengthPred+1)).apply_symm_apply i
  rw [hi] at he
  have hindex : (h.copies j).1*(S.generator (h.nextSide S j))⁻¹=(h.copies i).1 :=
    congrArg Prod.fst he
  have hpoint : S.generator (h.nextSide S j) • (h.copies j).2.val=(h.copies i).2.val :=
    congrArg (fun a : S.Copy => a.2.val) he
  apply Prod.ext
  · change (h.copies i).1*(S.generator (S.paired (h.nextSide S j)))⁻¹=(h.copies j).1
    rw [S.generator_paired,inv_inv,←hindex]
    group
  · apply Subtype.ext
    change S.generator (S.paired (h.nextSide S j)) • (h.copies i).2.val=(h.copies j).2.val
    rw [S.generator_paired,←hpoint,inv_smul_smul]

/-- A natural two-sided vertex cycle exhausts every actual side incidence;
this is a local geometric side statement, not a condition on the quotient fiber. -/
theorem VertexCycle.incidence_complete_of_two_sides {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r)
    (hSides : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,(h.copies i).2.val ∈ s.val →
      s=h.nextSide S i ∨ s=S.paired (h.nextSide S ((finRotate (h.lengthPred+1)).symm i))) :
    ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies := by
  intro i s hx
  rcases hSides i s hx with hs | hs
  · subst s
    exact ⟨finRotate (h.lengthPred+1) i,(h.nextSide_mate S i).symm⟩
  · subst s
    exact ⟨(finRotate (h.lengthPred+1)).symm i,(h.previousSide_mate S i hx).symm⟩

/-- Genuine two-sided vertex-cycle incidence proves finiteness of the whole original gluing class. -/
theorem VertexCycle.finite_fiber_of_two_sides {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r)
    (hSides : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,(h.copies i).2.val ∈ s.val →
      s=h.nextSide S i ∨ s=S.paired (h.nextSide S ((finRotate (h.lengthPred+1)).symm i))) :
    (S.project ⁻¹' {S.project (1,x)}).Finite :=
  h.finite_fiber_of_incidence_complete S (h.incidence_complete_of_two_sides S hSides)

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
