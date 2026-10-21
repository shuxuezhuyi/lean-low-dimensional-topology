/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy

Strengthened exact-vertex refinement lemmas adapted for this project from the
same-pin PolygonalCrosscut refinement construction.
-/
module
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.Moise.PolygonalCrosscut
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
namespace LowDimensionalTopology.Geometry.Surfaces
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- Inserting an actual boundary point adds exactly that vertex, with no auxiliary vertices. -/
theorem polygonalCircle_insertZero_vertex_iff (J:PolygonalCircle) (p:Plane)
    (hp:p∈J.edgeSegment 0) (hp0:p≠J.vertex 0) (hp1:p≠J.vertex 1) (q:Plane) :
    (J.insertZero p hp hp0 hp1).IsVertexPoint q↔q=p∨J.IsVertexPoint q := by
  constructor
  · rintro ⟨i,hi⟩
    change (if i.val=0 then p else J.vertex (i.val:ZMod J.n))=q at hi
    by_cases hz:i.val=0
    · rw [ite_eq_left hz] at hi
      exact Or.inl hi.symm
    · rw [ite_eq_right hz] at hi
      exact Or.inr ⟨(i.val:ZMod J.n),hi⟩
  · rintro (he|hq)
    · exact he.symm ▸ ⟨0,J.insertZero_vertex_zero p hp hp0 hp1⟩
    · exact J.isVertexPoint_insertZero p hp hp0 hp1 hq

/-- Refine at one genuine boundary point, retaining precisely the original vertices and that point. -/
theorem polygonalCircle_exists_insert_vertex_exact (J:PolygonalCircle) (p:Plane)
    (hp:p∈J.carrier) : ∃K:PolygonalCircle,K.carrier=J.carrier ∧
      ∀q,K.IsVertexPoint q↔q=p∨J.IsVertexPoint q := by
  classical
  by_cases hold:J.IsVertexPoint p
  · exact ⟨J,rfl,fun q=>⟨fun h=>Or.inr h,fun h=>h.elim (fun he=>he.symm ▸ hold) id⟩⟩
  obtain ⟨i,hi⟩:=mem_iUnion.mp hp
  let R:=J.rotate i
  have hpR:p∈R.edgeSegment 0:=by
    change p∈(J.rotate i).edgeSegment (0:ZMod J.n)
    rw [J.rotate_edgeSegment]
    simpa only [zero_add] using hi
  have hp0:p≠R.vertex 0:=by
    intro he
    apply hold
    apply (J.isVertexPoint_rotate_iff i p).mp
    exact ⟨0,he.symm⟩
  have hp1:p≠R.vertex 1:=by
    intro he
    apply hold
    apply (J.isVertexPoint_rotate_iff i p).mp
    exact ⟨1,he.symm⟩
  refine ⟨R.insertZero p hpR hp0 hp1,
    (R.insertZero_carrier p hpR hp0 hp1).trans (J.rotate_carrier i),?_⟩
  intro q
  rw [polygonalCircle_insertZero_vertex_iff,J.isVertexPoint_rotate_iff]

/-- Insert an arbitrary finite set of actual boundary points into the cyclic polygon. Its trace is unchanged, and its vertex set is exactly the requested points together with the old vertices. -/
theorem polygonalCircle_exists_refinement_exact (J:PolygonalCircle) (F:Finset Plane)
    (hF:∀p∈F,p∈J.carrier) : ∃K:PolygonalCircle,K.carrier=J.carrier ∧
      ∀q,K.IsVertexPoint q↔q∈F∨J.IsVertexPoint q := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨J,rfl,fun q=>by simp only [Finset.notMem_empty,false_or]⟩
  | @insert p F hpF ih =>
    obtain ⟨K,hK,hvertices⟩:=ih (fun q hq=>hF q (Finset.mem_insert_of_mem hq))
    have hpK:p∈K.carrier:=hK.symm ▸ hF p (Finset.mem_insert_self p F)
    obtain ⟨L,hL,hnew⟩:=polygonalCircle_exists_insert_vertex_exact K p hpK
    refine ⟨L,hL.trans hK,fun q=>?_⟩
    rw [hnew,hvertices,Finset.mem_insert,or_assoc]

/-- When all original vertices are requested, the refined cyclic traversal has exactly the prescribed vertex set. In particular, no straight marked boundary vertex is discarded. -/
theorem polygonalCircle_exists_refinement_exact_of_vertex_cover (J:PolygonalCircle)
    (F:Finset Plane) (hF:∀p∈F,p∈J.carrier) (hold:∀p,J.IsVertexPoint p→p∈F) :
    ∃K:PolygonalCircle,K.carrier=J.carrier ∧∀q,K.IsVertexPoint q↔q∈F := by
  obtain ⟨K,hK,hvertices⟩:=polygonalCircle_exists_refinement_exact J F hF
  refine ⟨K,hK,fun q=>?_⟩
  rw [hvertices]
  exact ⟨fun h=>h.elim id (hold q),Or.inl⟩
end LowDimensionalTopology.Geometry.Surfaces
