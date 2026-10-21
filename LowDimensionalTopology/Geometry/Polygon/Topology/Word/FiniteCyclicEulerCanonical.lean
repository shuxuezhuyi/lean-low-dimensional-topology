/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicEuler
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex NormalForm
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

def oneFaceCorner {E:Type} [Fintype E] (w:List (SignedDart E)) (i:Fin w.length):
    (ofOneFaceWord w).BoundaryOccurrence:=
  ⟨0,⟨i.val,by simpa only [ofOneFaceWord_boundary_zero,List.length_map] using i.isLt⟩⟩

 theorem oneFaceCorner_dart {E:Type} [Fintype E] (w:List (SignedDart E)) (i:Fin w.length):
     (oneFaceCorner w i).dart=SignedDart.mapEquiv (Fintype.equivFin E) (w.get i):=by
  simp [oneFaceCorner,FiniteCyclicPresentation.BoundaryOccurrence.dart]

 theorem oneFaceCorner_surjective {E:Type} [Fintype E] (w:List (SignedDart E)):
     Function.Surjective (oneFaceCorner w):=by
  rintro ⟨f,i⟩
  have hf:=ofOneFaceWord_face_eq_zero w f
  subst f
  refine ⟨⟨i.val,by simpa only [ofOneFaceWord_boundary_zero,List.length_map] using i.isLt⟩,?_⟩
  rfl

 theorem oneFaceCorner_next {E:Type} [Fintype E] (w:List (SignedDart E)) (i:Fin w.length):
     cornerNext (ofOneFaceWord w) (oneFaceCorner w i)=oneFaceCorner w (finRotate _ i):=by
  unfold cornerNext oneFaceCorner
  apply congrArg (fun j=>(⟨0,j⟩:(ofOneFaceWord w).BoundaryOccurrence))
  apply Fin.ext
  by_cases h:i.val+1<w.length
  · rw [finRotate_val_of_succ_lt _ (by simpa only [ofOneFaceWord_boundary_zero,List.length_map] using h),
      finRotate_val_of_succ_lt i h]
  · have hi:i.val+1=w.length:=by omega
    rw [finRotate_val_of_last _ (by simpa only [ofOneFaceWord_boundary_zero,List.length_map] using hi),
      finRotate_val_of_last i hi]

 def handleCorner (g:ℕ) (i:Fin g) (k:Fin 4):
     (NormalForm.orientable g 0).canonicalPresentation.BoundaryOccurrence:=
  oneFaceCorner (orientableBoundaryWord g 0) (orientableHandlePosition g 0 i k)

 theorem handleCorner_dart (g:ℕ) (i:Fin g) (k:Fin 4):
     (handleCorner g i k).dart=SignedDart.mapEquiv (Fintype.equivFin (OrientableEdge g 0))
       ((orientableHandleBlock (n:=0) i).get k):=by
  rw [handleCorner,oneFaceCorner_dart,orientableBoundaryWord_get_handle_block]

 theorem handleCorner_next_inside (g:ℕ) (i:Fin g) (k:Fin 4) (h:k.val<3):
     cornerNext (NormalForm.orientable g 0).canonicalPresentation (handleCorner g i k)=
       handleCorner g i ⟨k.val+1,by omega⟩:=by
  change cornerNext (ofOneFaceWord (orientableBoundaryWord g 0))
    (oneFaceCorner (orientableBoundaryWord g 0) (orientableHandlePosition g 0 i k))=
      oneFaceCorner (orientableBoundaryWord g 0) (orientableHandlePosition g 0 i ⟨k.val+1,by omega⟩)
  rw [oneFaceCorner_next]
  apply congrArg (oneFaceCorner (orientableBoundaryWord g 0))
  apply Fin.ext
  have hb:(orientableHandlePosition g 0 i k).val+1<(orientableBoundaryWord g 0).length:=by
    simp only [orientableHandlePosition_val,orientableBoundaryWord_length,Nat.mul_zero,Nat.add_zero]
    omega
  rw [finRotate_val_of_succ_lt _ hb]
  simp only [orientableHandlePosition_val]
  omega

 theorem handleCorner_next_last (g:ℕ) (i:Fin g):
     cornerNext (NormalForm.orientable g 0).canonicalPresentation (handleCorner g i 3)=
       handleCorner g (finRotate _ i) 0:=by
  change cornerNext (ofOneFaceWord (orientableBoundaryWord g 0))
    (oneFaceCorner (orientableBoundaryWord g 0) (orientableHandlePosition g 0 i 3))=
      oneFaceCorner (orientableBoundaryWord g 0) (orientableHandlePosition g 0 (finRotate g i) 0)
  rw [oneFaceCorner_next]
  apply congrArg (oneFaceCorner (orientableBoundaryWord g 0))
  apply Fin.ext
  by_cases h:i.val+1<g
  · have hb:(orientableHandlePosition g 0 i 3).val+1<(orientableBoundaryWord g 0).length:=by
      simp only [orientableHandlePosition_val,orientableBoundaryWord_length,Nat.mul_zero,Nat.add_zero]
      change i.val*4+3+1<4*g
      omega
    rw [finRotate_val_of_succ_lt _ hb]
    simp only [orientableHandlePosition_val,finRotate_val_of_succ_lt i h]
    change i.val*4+3+1=(i.val+1)*4+0
    omega
  · have hi:i.val+1=g:=by omega
    have hb:(orientableHandlePosition g 0 i 3).val+1=(orientableBoundaryWord g 0).length:=by
      simp only [orientableHandlePosition_val,orientableBoundaryWord_length,Nat.mul_zero,Nat.add_zero]
      change i.val*4+3+1=4*g
      omega
    rw [finRotate_val_of_last _ hb]
    simp only [orientableHandlePosition_val,finRotate_val_of_last i hi]
    rfl


 theorem handleCorner_class_inside (g:ℕ) (i:Fin g) (k:Fin 4):
     vertexClass (NormalForm.orientable g 0).canonicalPresentation (handleCorner g i k)=
       vertexClass (NormalForm.orientable g 0).canonicalPresentation (handleCorner g i 0):=by
  let P:=(NormalForm.orientable g 0).canonicalPresentation
  have ha:(handleCorner g i 0).edge=(handleCorner g i 2).edge:=by
    simp [FiniteCyclicPresentation.BoundaryOccurrence.edge,handleCorner_dart,orientableHandleBlock,SignedDart.mapEquiv,edgeOfDart]
  have hb:(handleCorner g i 1).edge=(handleCorner g i 3).edge:=by
    simp [FiniteCyclicPresentation.BoundaryOccurrence.edge,handleCorner_dart,orientableHandleBlock,SignedDart.mapEquiv,edgeOfDart]
  have hai:=vertexClass_initial P _ _ ha
  have hat:=vertexClass_terminal P _ _ ha
  have hbt:=vertexClass_terminal P _ _ hb
  simp [-canonicalPresentation_orientable,P,occurrenceInitial,handleCorner_dart,orientableHandleBlock,SignedDart.mapEquiv,
    handleCorner_next_inside] at hai
  simp [-canonicalPresentation_orientable,P,occurrenceTerminal,handleCorner_dart,orientableHandleBlock,SignedDart.mapEquiv,
    handleCorner_next_inside] at hat hbt
  fin_cases k
  · rfl
  · exact hat.trans (hbt.trans hai.symm)
  · exact hbt.trans hai.symm
  · exact hai.symm

 theorem handleCorner_class_next (g:ℕ) (i:Fin g):
     vertexClass (NormalForm.orientable g 0).canonicalPresentation (handleCorner g i 0)=
       vertexClass (NormalForm.orientable g 0).canonicalPresentation (handleCorner g (finRotate _ i) 0):=by
  let P:=(NormalForm.orientable g 0).canonicalPresentation
  have hb:(handleCorner g i 1).edge=(handleCorner g i 3).edge:=by
    simp [FiniteCyclicPresentation.BoundaryOccurrence.edge,handleCorner_dart,orientableHandleBlock,SignedDart.mapEquiv,edgeOfDart]
  have hbi:=vertexClass_initial P _ _ hb
  simp [-canonicalPresentation_orientable,-finRotate_apply,P,occurrenceInitial,handleCorner_dart,orientableHandleBlock,SignedDart.mapEquiv,
    handleCorner_next_last] at hbi
  exact (handleCorner_class_inside g i 1).symm.trans hbi


 theorem handleCorner_class_base (g:ℕ) (hg:0<g) (i:Fin g):
     vertexClass (NormalForm.orientable g 0).canonicalPresentation (handleCorner g i 0)=
       vertexClass (NormalForm.orientable g 0).canonicalPresentation (handleCorner g ⟨0,hg⟩ 0):=by
  cases g with
  | zero=>omega
  | succ n=>
    induction i using Fin.induction with
    | zero=>rfl
    | succ j ih=>
      have hs:finRotate (n+1) j.castSucc=j.succ:=by
        apply Fin.ext
        rw [finRotate_val_of_succ_lt _ (by simp)]
        rfl
      have h:=handleCorner_class_next (n+1) j.castSucc
      rw [hs] at h
      exact h.symm.trans ih

 theorem orientableClosed_corner_class (g:ℕ) (hg:0<g)
     (o:(NormalForm.orientable g 0).canonicalPresentation.BoundaryOccurrence):
     vertexClass (NormalForm.orientable g 0).canonicalPresentation o=
       vertexClass (NormalForm.orientable g 0).canonicalPresentation (handleCorner g ⟨0,hg⟩ 0):=by
  obtain ⟨j,rfl⟩:=oneFaceCorner_surjective (orientableBoundaryWord g 0) o
  have hj:j.val<4*g:=by
    simpa only [orientableBoundaryWord_length,Nat.mul_zero,Nat.add_zero] using j.isLt
  let i:Fin g:=⟨j.val/4,by omega⟩
  let k:Fin 4:=⟨j.val%4,Nat.mod_lt _ (by decide)⟩
  have hp:orientableHandlePosition g 0 i k=j:=by
    apply Fin.ext
    change (j.val/4)*4+j.val%4=j.val
    omega
  rw [←hp]
  exact (handleCorner_class_inside g i k).trans (handleCorner_class_base g hg i)

 theorem orientableClosedVertex_subsingleton (g:ℕ) (hg:0<g):
     Subsingleton (Vertex (NormalForm.orientable g 0).canonicalPresentation):=by
  constructor
  intro v w
  refine Quotient.inductionOn₂ v w ?_
  intro o p
  change vertexClass _ o=vertexClass _ p
  exact (orientableClosed_corner_class g hg o).trans (orientableClosed_corner_class g hg p).symm

 theorem orientableClosed_vertexCount (g:ℕ) (hg:0<g):
     Nat.card (Vertex (NormalForm.orientable g 0).canonicalPresentation)=1:=by
  let orientableClosedVerticesSubsingleton :
      Subsingleton (Vertex (NormalForm.orientable g 0).canonicalPresentation):=
    orientableClosedVertex_subsingleton g hg
  let orientableClosedVerticesNonempty :
      Nonempty (Vertex (NormalForm.orientable g 0).canonicalPresentation):=
    ⟨vertexClass _ (handleCorner g ⟨0,hg⟩ 0)⟩
  exact Nat.card_unique

 def orientableClosedEdgeEquiv (g:ℕ):OrientableEdge g 0≃Fin g⊕Fin g where
  toFun
    | .a i=>.inl i
    | .b i=>.inr i
    | .c i=>i.elim0
    | .h i=>i.elim0
  invFun
    | .inl i=>.a i
    | .inr i=>.b i
  left_inv e:=by cases e with
    | a _=>rfl
    | b _=>rfl
    | c i=>exact i.elim0
    | h i=>exact i.elim0
  right_inv e:=by cases e <;> rfl

 theorem orientableClosed_edgeCount (g:ℕ):
     (NormalForm.orientable g 0).canonicalPresentation.edgeCount=2*g:=by
  change Fintype.card (OrientableEdge g 0)=2*g
  have h:=Fintype.card_congr (orientableClosedEdgeEquiv g)
  simpa [two_mul] using h

 theorem orientableClosed_eulerCharacteristic (g:ℕ) (hg:0<g):
     eulerCharacteristic (NormalForm.orientable g 0).canonicalPresentation=2-2*(g:ℤ):=by
  unfold eulerCharacteristic
  rw [orientableClosed_vertexCount g hg]
  have he:((NormalForm.orientable g 0).canonicalPresentation.edgeCount:ℤ)=2*(g:ℤ):=by
    exact_mod_cast orientableClosed_edgeCount g
  have hf:((NormalForm.orientable g 0).canonicalPresentation.faces.length:ℤ)=1:=by
    rfl
  omega

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
