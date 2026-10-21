/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicEulerIsomorphism
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

theorem uniform_unoriented_isSurfaceValid {P Q:FiniteCyclicPresentation}
    (e:UnorientedPresentationIso P Q) (b:Bool) (hb:∀f,e.reverseFace f=b) (hP:P.IsSurfaceValid):
    Q.IsSurfaceValid:=by
  refine ⟨e.faceEquiv.nonempty_congr.mp hP.1,?_,?_,?_⟩
  · intro q
    obtain ⟨f,rfl⟩:=e.faceEquiv.surjective q
    intro h
    have hz:(P.boundary f).length=0:=by
      rw [e.boundary_length_eq,h]
      rfl
    exact hP.2.1 f (List.length_eq_zero_iff.mp hz)
  · intro q r h
    obtain ⟨f,rfl⟩:=e.faceEquiv.surjective q
    obtain ⟨g,rfl⟩:=e.faceEquiv.surjective r
    apply congrArg e.faceEquiv
    apply hP.2.2.1
    have hf:=e.boundary_rotated f
    have hg:=e.boundary_rotated g
    have hm:(Q.orientedBoundary ⟨e.faceEquiv f,e.reverseFace f⟩).IsRotated
        (Q.orientedBoundary ⟨e.faceEquiv g,e.reverseFace g⟩):=by
      cases b
      · simpa [orientedBoundary,hb] using h
      · simpa [orientedBoundary,hb] using inverseWord_isRotated h
    have hh:=hf.trans (hm.trans hg.symm)
    simpa only [EdgeRelabeling.map_mapDart_symm] using hh.map e.edgeRelabeling.symm.mapDart
  · intro q
    obtain ⟨a,rfl⟩:=e.edgeEquiv.surjective q
    rw [←e.edgeMultiplicity_eq]
    exact hP.2.2.2 a

/-- Rewrite the selected cut literally, reversing every other face by the same
 global sign so ordinary distinct-face validity is preserved. -/
def cutSpellingWord (P:FiniteCyclicPresentation) (cut:P2Cut P) (f:P.Face):List P.Dart:=
  if f=cut.face.face then cut.left++cut.right else P2.storedWord cut.face.orientation (P.boundary f)

abbrev cutSpelling (P:FiniteCyclicPresentation) (cut:P2Cut P):FiniteCyclicPresentation where
  edgeCount:=P.edgeCount
  faces:=List.ofFn (cutSpellingWord P cut)

def cutSpellingFaceEquiv (P:FiniteCyclicPresentation) (cut:P2Cut P):P.Face≃(cutSpelling P cut).Face:=
  finCongr (by simp [cutSpelling])

 theorem cutSpelling_boundary (P:FiniteCyclicPresentation) (cut:P2Cut P) (f:P.Face):
     (cutSpelling P cut).boundary (cutSpellingFaceEquiv P cut f)=cutSpellingWord P cut f:=by
  unfold FiniteCyclicPresentation.boundary cutSpelling
  rw [List.get_ofFn]
  apply congrArg (cutSpellingWord P cut)
  apply Fin.ext
  rfl

 def cutSpellingIso (P:FiniteCyclicPresentation) (cut:P2Cut P):
     UnorientedPresentationIso P (cutSpelling P cut) where
  edgeRelabeling:=EdgeRelabeling.refl _
  faceEquiv:=cutSpellingFaceEquiv P cut
  reverseFace:=fun _=>cut.face.orientation
  boundary_rotated f:=by
    rw [EdgeRelabeling.map_mapDart_refl]
    unfold orientedBoundary
    rw [cutSpelling_boundary]
    unfold cutSpellingWord
    by_cases hf:f=cut.face.face
    · subst f
      rw [ite_eq_left rfl]
      cases hb:cut.face.orientation
      · simpa [hb,orientedBoundary] using cut.boundary_rotated
      · have h:=inverseWord_isRotated cut.boundary_rotated
        simpa [hb,orientedBoundary] using h
    · rw [ite_eq_right hf]
      cases cut.face.orientation <;> simpa [P2.storedWord] using List.IsRotated.refl (P.boundary f)

 theorem cutSpelling_isSurfaceValid (P:FiniteCyclicPresentation) (cut:P2Cut P) (hP:P.IsSurfaceValid):
     (cutSpelling P cut).IsSurfaceValid:=
  uniform_unoriented_isSurfaceValid (cutSpellingIso P cut) cut.face.orientation (fun _=>rfl) hP

 def literalCut (P:FiniteCyclicPresentation) (cut:P2Cut P):P2Cut (cutSpelling P cut) where
  face:=⟨cutSpellingFaceEquiv P cut cut.face.face,false⟩
  left:=cut.left
  right:=cut.right
  boundary_rotated:=by
    simp only [orientedBoundary,Bool.false_eq_true,ite_false,cutSpelling_boundary,cutSpellingWord]
    exact List.IsRotated.refl _

 theorem cutSpelling_eulerCharacteristic (P:FiniteCyclicPresentation) (cut:P2Cut P) (hP:P.IsSurfaceValid):
     eulerCharacteristic P=eulerCharacteristic (cutSpelling P cut):=
  unoriented_eulerCharacteristic (cutSpellingIso P cut) (cutSpelling_isSurfaceValid P cut hP)

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

/-- Internal literal spelling, obtained from an arbitrary valid cut by cutSpelling. -/
structure LiteralSplitData (P:FiniteCyclicPresentation) where
  cut:P2Cut P
  orientation:cut.face.orientation=false
  boundary:P.boundary cut.face.face=cut.left++cut.right
  nonempty:0<(P.boundary cut.face.face).length

namespace LiteralSplitData
variable {P:FiniteCyclicPresentation} (d:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.LiteralSplitData
  P)
abbrev Target:FiniteCyclicPresentation:=P2.split P d.cut

theorem selectedLength:(d.Target.boundary (P2.oldFace P d.cut d.cut.face.face)).length=d.cut.left.length+1:=by
  rw [P2.split_boundary_selected]
  simp [P2.selectedBoundary,P2.selectedOrientedBoundary,P2.storedWord,d.orientation,P2.retainWord]

theorem rightLength:(d.Target.boundary (P2.rightFace P d.cut)).length=d.cut.right.length+1:=by
  rw [P2.split_boundary_right]
  simp [P2.rightBoundary,P2.rightOrientedBoundary,P2.storedWord,d.orientation,P2.retainWord]

theorem retainedLength (f:P.Face) (h:f≠d.cut.face.face):
    (d.Target.boundary (P2.oldFace P d.cut f)).length=(P.boundary f).length:=by
  rw [P2.split_boundary_old_of_ne P d.cut h]
  simp [P2.retainWord]

theorem originalLength:(P.boundary d.cut.face.face).length=d.cut.left.length+d.cut.right.length:=by
  rw [d.boundary,List.length_append]

def collapseIndexed (f:Fin (P.faces.length+1)):
    Fin (d.Target.boundary (P2.faceEquiv P d.cut f)).length→P.BoundaryOccurrence:=
  Fin.lastCases (motive:=fun f=>Fin (d.Target.boundary (P2.faceEquiv P d.cut f)).length→P.BoundaryOccurrence)
    (fun i=>⟨d.cut.face.face,⟨(if i.val=0 then 0 else d.cut.left.length+i.val-1)%
      (P.boundary d.cut.face.face).length,Nat.mod_lt _ d.nonempty⟩⟩)
    (fun f i=>if h:f=d.cut.face.face then
      ⟨d.cut.face.face,⟨i.val%(P.boundary d.cut.face.face).length,Nat.mod_lt _ d.nonempty⟩⟩
    else ⟨f,⟨i.val,by
      have hi:=i.isLt
      change i.val<(d.Target.boundary (P2.oldFace P d.cut f)).length at hi
      rwa [d.retainedLength f h] at hi⟩⟩) f

def collapse (o:d.Target.BoundaryOccurrence):P.BoundaryOccurrence:=
  d.collapseIndexed ((P2.faceEquiv P d.cut).symm o.1)
    (o.2.cast (congrArg (fun f=>(d.Target.boundary f).length)
      ((P2.faceEquiv P d.cut).apply_symm_apply o.1).symm))

theorem collapse_at (f:Fin (P.faces.length+1)) (i:Fin (d.Target.boundary (P2.faceEquiv P d.cut f)).length):
    d.collapse ⟨P2.faceEquiv P d.cut f,i⟩=d.collapseIndexed f i:=by
  simp only [collapse]
  rfl

theorem collapse_selected (i:Fin (d.Target.boundary (P2.oldFace P d.cut d.cut.face.face)).length):
    d.collapse ⟨P2.oldFace P d.cut d.cut.face.face,i⟩=
      ⟨d.cut.face.face,⟨i.val%(P.boundary d.cut.face.face).length,Nat.mod_lt _ d.nonempty⟩⟩:=by
  change d.collapse ⟨P2.faceEquiv P d.cut d.cut.face.face.castSucc,i⟩=_
  rw [d.collapse_at]
  simp [collapseIndexed]

theorem collapse_right (i:Fin (d.Target.boundary (P2.rightFace P d.cut)).length):
    d.collapse ⟨P2.rightFace P d.cut,i⟩=
      ⟨d.cut.face.face,⟨(if i.val=0 then 0 else d.cut.left.length+i.val-1)%
        (P.boundary d.cut.face.face).length,Nat.mod_lt _ d.nonempty⟩⟩:=by
  change d.collapse ⟨P2.faceEquiv P d.cut (Fin.last P.faces.length),i⟩=_
  rw [d.collapse_at]
  simp [collapseIndexed]

theorem collapse_retained (f:P.Face) (h:f≠d.cut.face.face)
    (i:Fin (d.Target.boundary (P2.oldFace P d.cut f)).length):
    d.collapse ⟨P2.oldFace P d.cut f,i⟩=
      ⟨f,⟨i.val,by have hi:=i.isLt;simpa only [d.retainedLength f h] using hi⟩⟩:=by
  change d.collapse ⟨P2.faceEquiv P d.cut f.castSucc,i⟩=_
  rw [d.collapse_at]
  simp [collapseIndexed,h]

/-- Each old side remains a genuine occurrence in one child or retained face. -/
def embed (o:P.BoundaryOccurrence):d.Target.BoundaryOccurrence:=by
  rcases o with ⟨f,i⟩
  by_cases hf:f=d.cut.face.face
  · subst f
    by_cases hi:i.val<d.cut.left.length
    · exact ⟨P2.oldFace P d.cut d.cut.face.face,⟨i.val,by rw [d.selectedLength];omega⟩⟩
    · exact ⟨P2.rightFace P d.cut,⟨i.val-d.cut.left.length+1,by
        rw [d.rightLength]
        have hn:=d.originalLength
        have hb:=i.isLt
        omega⟩⟩
  · exact ⟨P2.oldFace P d.cut f,⟨i.val,by rw [d.retainedLength f hf];exact i.isLt⟩⟩

theorem collapse_embed (o:P.BoundaryOccurrence):d.collapse (d.embed o)=o:=by
  rcases o with ⟨f,i⟩
  by_cases hf:f=d.cut.face.face
  · subst f
    by_cases hi:i.val<d.cut.left.length
    · simp only [embed,hi,eq_self,dite_true]
      rw [d.collapse_selected]
      apply congrArg (fun j=>(⟨d.cut.face.face,j⟩:P.BoundaryOccurrence))
      exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
    · simp only [embed,hi,eq_self,dite_true,dite_false]
      rw [d.collapse_right]
      have hv:i.val-d.cut.left.length+1≠0:=by omega
      simp only [hv,ite_false]
      apply congrArg (fun j=>(⟨d.cut.face.face,j⟩:P.BoundaryOccurrence))
      apply Fin.ext
      change (d.cut.left.length+(i.val-d.cut.left.length+1)-1)%(P.boundary d.cut.face.face).length=i.val
      have he:d.cut.left.length+(i.val-d.cut.left.length+1)-1=i.val:=by omega
      rw [he,Nat.mod_eq_of_lt i.isLt]
  · simp only [embed,dite_eq_right hf]
    rw [d.collapse_retained f hf]


 theorem embed_selected_left (i:Fin (P.boundary d.cut.face.face).length) (h:i.val<d.cut.left.length):
     d.embed ⟨d.cut.face.face,i⟩=
       ⟨P2.oldFace P d.cut d.cut.face.face,⟨i.val,by rw [d.selectedLength];omega⟩⟩:=by
  simp [embed,h]

 theorem embed_selected_right (i:Fin (P.boundary d.cut.face.face).length) (h:¬i.val<d.cut.left.length):
     d.embed ⟨d.cut.face.face,i⟩=
       ⟨P2.rightFace P d.cut,⟨i.val-d.cut.left.length+1,by
         rw [d.rightLength]
         have hn:=d.originalLength
         have _hi:=i.isLt
         omega⟩⟩:=by
  simp [embed,h]

 theorem embed_retained (f:P.Face) (h:f≠d.cut.face.face) (i:Fin (P.boundary f).length):
     d.embed ⟨f,i⟩=⟨P2.oldFace P d.cut f,⟨i.val,by rw [d.retainedLength f h];exact i.isLt⟩⟩:=by
  simp [embed,h]

 theorem embed_dart (o:P.BoundaryOccurrence):
     (d.embed o).dart=P1.castSuccDart o.dart:=by
  rcases o with ⟨f,i⟩
  by_cases hf:f=d.cut.face.face
  · subst f
    by_cases hi:i.val<d.cut.left.length
    · rw [d.embed_selected_left i hi]
      simp [FiniteCyclicPresentation.BoundaryOccurrence.dart,
        P2.selectedBoundary,P2.selectedOrientedBoundary,P2.storedWord,d.orientation,P2.retainWord,
        d.boundary,hi]
    · rw [d.embed_selected_right i hi]
      simp [FiniteCyclicPresentation.BoundaryOccurrence.dart,P2.split_boundary_right,
        P2.rightBoundary,P2.rightOrientedBoundary,P2.storedWord,d.orientation,P2.retainWord,
        d.boundary,Nat.le_of_not_lt hi]
  · rw [d.embed_retained f hf]
    simp [FiniteCyclicPresentation.BoundaryOccurrence.dart,P2.split_boundary_old_of_ne P d.cut hf,P2.retainWord]

 theorem embed_edge (o:P.BoundaryOccurrence):(d.embed o).edge=o.edge.castSucc:=by
  rw [FiniteCyclicPresentation.BoundaryOccurrence.edge,d.embed_dart,P1.edgeOfDart_castSuccDart]
  rfl


abbrev freshLeft:d.Target.BoundaryOccurrence:=P2.positiveSelectedFreshOccurrence P d.cut d.orientation
abbrev freshRight:d.Target.BoundaryOccurrence:=P2.positiveRightFreshOccurrence P d.cut d.orientation

 theorem freshLeft_dart:d.freshLeft.dart=.pos (P2.freshEdge P):=
  P2.positiveSelectedFreshOccurrence_dart P d.cut d.orientation

 theorem freshRight_dart:d.freshRight.dart=.neg (P2.freshEdge P):=
  P2.positiveRightFreshOccurrence_dart P d.cut d.orientation

 theorem fresh_edge_eq:d.freshLeft.edge=d.freshRight.edge:=by
  rw [FiniteCyclicPresentation.BoundaryOccurrence.edge,d.freshLeft_dart,
    FiniteCyclicPresentation.BoundaryOccurrence.edge,d.freshRight_dart]
  rfl

/-- Every literal new boundary occurrence is an old occurrence or one of the two
 copies of the cutting edge, including either one-sided cut. -/
 theorem occurrence_cases (q:d.Target.BoundaryOccurrence):
     (∃o:P.BoundaryOccurrence,q=d.embed o)∨q=d.freshLeft∨q=d.freshRight:=by
  rcases q with ⟨q,j⟩
  rcases P2.face_cases P d.cut q with ⟨f,hf⟩|hf
  · subst q
    by_cases h:f=d.cut.face.face
    · subst f
      have hb:j.val<d.cut.left.length+1:=by simpa only [d.selectedLength] using j.isLt
      by_cases hl:j.val<d.cut.left.length
      · have hs:j.val<(P.boundary d.cut.face.face).length:=by rw [d.originalLength];omega
        refine Or.inl ⟨⟨d.cut.face.face,⟨j.val,hs⟩⟩,?_⟩
        rw [d.embed_selected_left _ hl]
      · refine Or.inr (Or.inl ?_)
        change (⟨P2.oldFace P d.cut d.cut.face.face,j⟩:d.Target.BoundaryOccurrence)=
          ⟨P2.oldFace P d.cut d.cut.face.face,P2.positiveSelectedFreshIndex P d.cut d.orientation⟩
        apply congrArg (fun i=>(⟨P2.oldFace P d.cut d.cut.face.face,i⟩:d.Target.BoundaryOccurrence))
        apply Fin.ext
        change j.val=d.cut.left.length
        omega
    · have hs:j.val<(P.boundary f).length:=by simpa only [d.retainedLength f h] using j.isLt
      refine Or.inl ⟨⟨f,⟨j.val,hs⟩⟩,?_⟩
      rw [d.embed_retained f h]
  · subst q
    by_cases hz:j.val=0
    · refine Or.inr (Or.inr ?_)
      change (⟨P2.rightFace P d.cut,j⟩:d.Target.BoundaryOccurrence)=
        ⟨P2.rightFace P d.cut,P2.positiveRightFreshIndex P d.cut d.orientation⟩
      apply congrArg (fun i=>(⟨P2.rightFace P d.cut,i⟩:d.Target.BoundaryOccurrence))
      exact Fin.ext hz
    · have hb:j.val<d.cut.right.length+1:=by simpa only [d.rightLength] using j.isLt
      have hs:d.cut.left.length+j.val-1<(P.boundary d.cut.face.face).length:=by
        rw [d.originalLength]
        omega
      have hn:¬d.cut.left.length+j.val-1<d.cut.left.length:=by omega
      refine Or.inl ⟨⟨d.cut.face.face,⟨d.cut.left.length+j.val-1,hs⟩⟩,?_⟩
      rw [d.embed_selected_right _ hn]
      apply congrArg (fun i=>(⟨P2.rightFace P d.cut,i⟩:d.Target.BoundaryOccurrence))
      apply Fin.ext
      change j.val=(d.cut.left.length+j.val-1)-d.cut.left.length+1
      omega


 theorem collapse_next_embed (o:P.BoundaryOccurrence):
     d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target (d.embed o))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext P o:=by
  rcases o with ⟨f,i⟩
  by_cases hf:f=d.cut.face.face
  · subst f
    by_cases hi:i.val<d.cut.left.length
    · rw [d.embed_selected_left i hi]
      unfold _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext
      rw [d.collapse_selected]
      apply congrArg (fun j=>(⟨d.cut.face.face,j⟩:P.BoundaryOccurrence))
      apply Fin.ext
      have hb:i.val+1<(d.Target.boundary (P2.oldFace P d.cut d.cut.face.face)).length:=by
        rw [d.selectedLength]
        omega
      change (finRotate _ ⟨i.val,_⟩).val%(P.boundary d.cut.face.face).length=(finRotate _ i).val
      rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_succ_lt _
        hb,_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_mod]
    · rw [d.embed_selected_right i hi]
      unfold _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext
      rw [d.collapse_right]
      apply congrArg (fun j=>(⟨d.cut.face.face,j⟩:P.BoundaryOccurrence))
      apply Fin.ext
      change (if (finRotate _ ⟨i.val-d.cut.left.length+1,_⟩).val=0 then 0
        else d.cut.left.length+(finRotate _ ⟨i.val-d.cut.left.length+1,_⟩).val-1)%
          (P.boundary d.cut.face.face).length=(finRotate _ i).val
      by_cases hn:i.val+1<(P.boundary d.cut.face.face).length
      · have hb:(i.val-d.cut.left.length+1)+1<(d.Target.boundary (P2.rightFace P d.cut)).length:=by
          rw [d.rightLength]
          have hh:=d.originalLength
          omega
        rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_succ_lt _
          hb,_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_mod]
        have hz:(i.val-d.cut.left.length+1)+1≠0:=by omega
        rw [ite_eq_right hz]
        change (d.cut.left.length+((i.val-d.cut.left.length+1)+1)-1)%
          (P.boundary d.cut.face.face).length=(i.val+1)%(P.boundary d.cut.face.face).length
        congr 1
        omega
      · have hn':i.val+1=(P.boundary d.cut.face.face).length:=by omega
        have hb:(i.val-d.cut.left.length+1)+1=(d.Target.boundary (P2.rightFace P d.cut)).length:=by
          rw [d.rightLength]
          have hh:=d.originalLength
          omega
        rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_last _
          hb,_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_last i hn']
        simp
  · rw [d.embed_retained f hf]
    unfold _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext
    rw [d.collapse_retained f hf]
    apply congrArg (fun j=>(⟨f,j⟩:P.BoundaryOccurrence))
    apply Fin.ext
    rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_mod,_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_mod]
    change (i.val+1)%(d.Target.boundary (P2.oldFace P d.cut f)).length=
      (i.val+1)%(P.boundary f).length
    rw [d.retainedLength f hf]

 theorem collapse_initial_embed (o:P.BoundaryOccurrence):
     d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial d.Target (d.embed o))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial P o:=by
  have hd:=d.embed_dart o
  cases ho:o.dart <;>
    simp [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial,hd,ho,P1.castSuccDart,d.collapse_embed,d.collapse_next_embed]

 theorem collapse_terminal_embed (o:P.BoundaryOccurrence):
     d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal d.Target (d.embed o))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal P o:=by
  have hd:=d.embed_dart o
  cases ho:o.dart <;>
    simp [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal,hd,ho,P1.castSuccDart,d.collapse_embed,d.collapse_next_embed]


 theorem freshLeft_next:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshLeft=
     ⟨P2.oldFace P d.cut d.cut.face.face,⟨0,by rw [d.selectedLength];omega⟩⟩:=by
  change (⟨P2.oldFace P d.cut d.cut.face.face,
    finRotate _ (P2.positiveSelectedFreshIndex P d.cut d.orientation)⟩:d.Target.BoundaryOccurrence)=_
  apply congrArg (fun i=>(⟨P2.oldFace P d.cut d.cut.face.face,i⟩:d.Target.BoundaryOccurrence))
  apply Fin.ext
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_last
  change d.cut.left.length+1=(d.Target.boundary (P2.oldFace P d.cut d.cut.face.face)).length
  exact d.selectedLength.symm

 theorem freshRight_next_of_pos (h:0<d.cut.right.length):_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshRight=
     ⟨P2.rightFace P d.cut,⟨1,by rw [d.rightLength];omega⟩⟩:=by
  change (⟨P2.rightFace P d.cut,
    finRotate _ (P2.positiveRightFreshIndex P d.cut d.orientation)⟩:d.Target.BoundaryOccurrence)=_
  apply congrArg (fun i=>(⟨P2.rightFace P d.cut,i⟩:d.Target.BoundaryOccurrence))
  apply Fin.ext
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_succ_lt _ (by change 0+1<(d.Target.boundary (P2.rightFace P d.cut)).length;rw [d.rightLength];omega)]
  rfl

 theorem freshRight_next_of_zero (h:d.cut.right.length=0):_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshRight=d.freshRight:=by
  change (⟨P2.rightFace P d.cut,
    finRotate _ (P2.positiveRightFreshIndex P d.cut d.orientation)⟩:d.Target.BoundaryOccurrence)=_
  apply congrArg (fun i=>(⟨P2.rightFace P d.cut,i⟩:d.Target.BoundaryOccurrence))
  apply Fin.ext
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_last _ (by change 0+1=(d.Target.boundary (P2.rightFace P d.cut)).length;rw [d.rightLength];omega)]
  rfl

 theorem collapse_freshLeft:d.collapse d.freshLeft=
     ⟨d.cut.face.face,⟨d.cut.left.length%(P.boundary d.cut.face.face).length,Nat.mod_lt _ d.nonempty⟩⟩:=by
  change d.collapse ⟨P2.oldFace P d.cut d.cut.face.face,P2.positiveSelectedFreshIndex P d.cut d.orientation⟩=_
  rw [d.collapse_selected]
  rfl

 theorem collapse_freshRight:d.collapse d.freshRight=
     ⟨d.cut.face.face,⟨0,d.nonempty⟩⟩:=by
  change d.collapse ⟨P2.rightFace P d.cut,P2.positiveRightFreshIndex P d.cut d.orientation⟩=_
  rw [d.collapse_right]
  rfl

 theorem collapse_initial_fresh:
     d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial d.Target d.freshLeft)=d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial d.Target d.freshRight):=by
  simp only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial,d.freshLeft_dart,d.freshRight_dart]
  by_cases h:d.cut.right.length=0
  · rw [d.freshRight_next_of_zero h,d.collapse_freshLeft,d.collapse_freshRight]
    apply congrArg (fun i=>(⟨d.cut.face.face,i⟩:P.BoundaryOccurrence))
    apply Fin.ext
    change d.cut.left.length%(P.boundary d.cut.face.face).length=0
    have he:d.cut.left.length=(P.boundary d.cut.face.face).length:=by
      have hh:=d.originalLength
      omega
    rw [he,Nat.mod_self]
  · rw [d.freshRight_next_of_pos (Nat.pos_of_ne_zero h),d.collapse_freshLeft,d.collapse_right]
    rfl

 theorem collapse_terminal_fresh:
     d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal d.Target d.freshLeft)=d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal d.Target d.freshRight):=by
  simp only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal,d.freshLeft_dart,d.freshRight_dart]
  rw [d.freshLeft_next,d.collapse_selected,d.collapse_freshRight]
  rfl


 theorem embed_edge_ne_freshLeft (o:P.BoundaryOccurrence):(d.embed o).edge≠d.freshLeft.edge:=by
  have he:d.freshLeft.edge=P2.freshEdge P:=P2.positiveSelectedFreshOccurrence_edge P d.cut d.orientation
  rw [d.embed_edge,he]
  change o.edge.castSucc≠Fin.last P.edgeCount
  exact Fin.castSucc_ne_last o.edge

 theorem embed_edge_ne_freshRight (o:P.BoundaryOccurrence):(d.embed o).edge≠d.freshRight.edge:=by
  rw [←d.fresh_edge_eq]
  exact d.embed_edge_ne_freshLeft o

 theorem collapse_initial_compatible (o p:d.Target.BoundaryOccurrence) (h:o.edge=p.edge):
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (d.collapse
       (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial d.Target o))=
       _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial d.Target p)):=by
  rcases d.occurrence_cases o with ⟨a,rfl⟩|rfl|rfl
  · rcases d.occurrence_cases p with ⟨b,rfl⟩|rfl|rfl
    · rw [d.collapse_initial_embed,d.collapse_initial_embed]
      apply _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial
      rw [d.embed_edge,d.embed_edge] at h
      exact Fin.castSucc_injective P.edgeCount h
    · exact False.elim (d.embed_edge_ne_freshLeft a h)
    · exact False.elim (d.embed_edge_ne_freshRight a h)
  · rcases d.occurrence_cases p with ⟨b,rfl⟩|rfl|rfl
    · exact False.elim (d.embed_edge_ne_freshLeft b h.symm)
    · rfl
    · rw [d.collapse_initial_fresh]
  · rcases d.occurrence_cases p with ⟨b,rfl⟩|rfl|rfl
    · exact False.elim (d.embed_edge_ne_freshRight b h.symm)
    · rw [d.collapse_initial_fresh]
    · rfl

 theorem collapse_terminal_compatible (o p:d.Target.BoundaryOccurrence) (h:o.edge=p.edge):
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (d.collapse
       (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal d.Target o))=
       _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (d.collapse (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal d.Target p)):=by
  rcases d.occurrence_cases o with ⟨a,rfl⟩|rfl|rfl
  · rcases d.occurrence_cases p with ⟨b,rfl⟩|rfl|rfl
    · rw [d.collapse_terminal_embed,d.collapse_terminal_embed]
      apply _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal
      rw [d.embed_edge,d.embed_edge] at h
      exact Fin.castSucc_injective P.edgeCount h
    · exact False.elim (d.embed_edge_ne_freshLeft a h)
    · exact False.elim (d.embed_edge_ne_freshRight a h)
  · rcases d.occurrence_cases p with ⟨b,rfl⟩|rfl|rfl
    · exact False.elim (d.embed_edge_ne_freshLeft b h.symm)
    · rfl
    · rw [d.collapse_terminal_fresh]
  · rcases d.occurrence_cases p with ⟨b,rfl⟩|rfl|rfl
    · exact False.elim (d.embed_edge_ne_freshRight b h.symm)
    · rw [d.collapse_terminal_fresh]
    · rfl

/-- Collapse the new cutting edge on the actual endpoint quotient. -/
def collapseVertex:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex d.Target→_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex P:=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexLift (fun
    q=>_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (d.collapse
    q)) d.collapse_initial_compatible d.collapse_terminal_compatible

 theorem collapseVertex_class (q:d.Target.BoundaryOccurrence):
     d.collapseVertex (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target
       q)=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (d.collapse q):=rfl


 theorem fresh_initial_vertex:
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target d.freshLeft=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshRight):=by
  have h:=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial d.Target d.freshLeft d.freshRight d.fresh_edge_eq
  simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial,d.freshLeft_dart,d.freshRight_dart] using h

 theorem fresh_terminal_vertex:
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshLeft)=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target d.freshRight:=by
  have h:=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal d.Target d.freshLeft d.freshRight d.fresh_edge_eq
  simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal,d.freshLeft_dart,d.freshRight_dart] using h

abbrev zeroCorner:P.BoundaryOccurrence:=⟨d.cut.face.face,⟨0,d.nonempty⟩⟩

 theorem embed_zero_of_left_pos (h:0<d.cut.left.length):
     d.embed d.zeroCorner=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshLeft:=by
  rw [zeroCorner,d.embed_selected_left _ h,d.freshLeft_next]

 theorem embed_zero_of_left_zero (h:d.cut.left.length=0):
     d.embed d.zeroCorner=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshRight:=by
  have hr:0<d.cut.right.length:=by have hn:=d.originalLength;have hp:=d.nonempty;omega
  rw [zeroCorner,d.embed_selected_right _ (by change ¬0<d.cut.left.length;omega),d.freshRight_next_of_pos hr]
  apply congrArg (fun i=>(⟨P2.rightFace P d.cut,i⟩:d.Target.BoundaryOccurrence))
  apply Fin.ext
  change 0-d.cut.left.length+1=1
  omega

 theorem freshLeft_next_of_zero (h:d.cut.left.length=0):_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshLeft=d.freshLeft:=by
  rw [d.freshLeft_next]
  change (⟨P2.oldFace P d.cut d.cut.face.face,⟨0,_⟩⟩:d.Target.BoundaryOccurrence)=
    ⟨P2.oldFace P d.cut d.cut.face.face,P2.positiveSelectedFreshIndex P d.cut d.orientation⟩
  apply congrArg (fun i=>(⟨P2.oldFace P d.cut d.cut.face.face,i⟩:d.Target.BoundaryOccurrence))
  apply Fin.ext
  exact h.symm

 theorem collapse_freshLeft_of_right_zero (h:d.cut.right.length=0):d.collapse d.freshLeft=d.zeroCorner:=by
  rw [d.collapse_freshLeft]
  apply congrArg (fun i=>(⟨d.cut.face.face,i⟩:P.BoundaryOccurrence))
  apply Fin.ext
  change d.cut.left.length%(P.boundary d.cut.face.face).length=0
  have hn:d.cut.left.length=(P.boundary d.cut.face.face).length:=by have he:=d.originalLength;omega
  rw [hn,Nat.mod_self]

 theorem embed_collapse_freshLeft_of_right_pos (h:0<d.cut.right.length):
     d.embed (d.collapse d.freshLeft)=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext d.Target d.freshRight:=by
  have hl:d.cut.left.length<(P.boundary d.cut.face.face).length:=by rw [d.originalLength];omega
  have hc:d.collapse d.freshLeft=⟨d.cut.face.face,⟨d.cut.left.length,hl⟩⟩:=by
    rw [d.collapse_freshLeft]
    apply congrArg (fun i=>(⟨d.cut.face.face,i⟩:P.BoundaryOccurrence))
    exact Fin.ext (Nat.mod_eq_of_lt hl)
  rw [hc,d.embed_selected_right _ (by change ¬d.cut.left.length<d.cut.left.length;omega),
    d.freshRight_next_of_pos h]
  apply congrArg (fun i=>(⟨P2.rightFace P d.cut,i⟩:d.Target.BoundaryOccurrence))
  apply Fin.ext
  change d.cut.left.length-d.cut.left.length+1=1
  omega

 theorem embed_collapse_freshLeft_class:
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed (d.collapse d.freshLeft))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target d.freshLeft:=by
  by_cases hr:d.cut.right.length=0
  · have hl:0<d.cut.left.length:=by have hn:=d.originalLength;have hp:=d.nonempty;omega
    rw [d.collapse_freshLeft_of_right_zero hr,d.embed_zero_of_left_pos hl]
    have hi:=d.fresh_initial_vertex
    rw [d.freshRight_next_of_zero hr] at hi
    exact d.fresh_terminal_vertex.trans hi.symm
  · rw [d.embed_collapse_freshLeft_of_right_pos (Nat.pos_of_ne_zero hr)]
    exact d.fresh_initial_vertex.symm

 theorem embed_collapse_freshRight_class:
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed (d.collapse d.freshRight))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target d.freshRight:=by
  rw [d.collapse_freshRight]
  by_cases hl:d.cut.left.length=0
  · rw [d.embed_zero_of_left_zero hl]
    have ht:=d.fresh_terminal_vertex
    rw [d.freshLeft_next_of_zero hl] at ht
    exact d.fresh_initial_vertex.symm.trans ht
  · rw [d.embed_zero_of_left_pos (Nat.pos_of_ne_zero hl)]
    exact d.fresh_terminal_vertex

 theorem embed_collapse_class (q:d.Target.BoundaryOccurrence):
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed (d.collapse q))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target q:=by
  rcases d.occurrence_cases q with ⟨o,rfl⟩|rfl|rfl
  · rw [d.collapse_embed]
  · exact d.embed_collapse_freshLeft_class
  · exact d.embed_collapse_freshRight_class


 theorem embed_initial_compatible (o p:P.BoundaryOccurrence) (h:o.edge=p.edge):
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed
       (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial P o))=
       _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial P p)):=by
  have ho:=d.embed_collapse_class (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial
    d.Target (d.embed o))
  have hp:=d.embed_collapse_class (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial
    d.Target (d.embed p))
  rw [d.collapse_initial_embed] at ho hp
  apply ho.trans
  apply Eq.trans _ hp.symm
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial
  rw [d.embed_edge,d.embed_edge,h]

 theorem embed_terminal_compatible (o p:P.BoundaryOccurrence) (h:o.edge=p.edge):
     _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed
       (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal P o))=
       _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal P p)):=by
  have ho:=d.embed_collapse_class (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal
    d.Target (d.embed o))
  have hp:=d.embed_collapse_class (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal
    d.Target (d.embed p))
  rw [d.collapse_terminal_embed] at ho hp
  apply ho.trans
  apply Eq.trans _ hp.symm
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal
  rw [d.embed_edge,d.embed_edge,h]

/-- Embed the actual old endpoint quotient into the split presentation. -/
def embedVertex:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex P→_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex d.Target:=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexLift (fun
    o=>_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed
    o)) d.embed_initial_compatible d.embed_terminal_compatible

 theorem embedVertex_class (o:P.BoundaryOccurrence):
     d.embedVertex (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P
       o)=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target (d.embed o):=rfl

/-- Adding the cutting edge and splitting a face preserves the genuine set of
 glued vertices, even when exactly one of the two cut words is empty. -/
def vertexEquiv:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex d.Target≃_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex P where
  toFun:=d.collapseVertex
  invFun:=d.embedVertex
  left_inv v:=by
    refine Quotient.inductionOn v ?_
    intro q
    change d.embedVertex (d.collapseVertex (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass
      d.Target q))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass d.Target q
    rw [d.collapseVertex_class,d.embedVertex_class,d.embed_collapse_class]
  right_inv v:=by
    refine Quotient.inductionOn v ?_
    intro o
    change d.collapseVertex (d.embedVertex (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P
      o))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P o
    rw [d.embedVertex_class,d.collapseVertex_class,d.collapse_embed]

 theorem vertexCount:Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex
   d.Target)=Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex
   P):=Nat.card_congr d.vertexEquiv

 theorem eulerCharacteristic_eq:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic d.Target=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic P:=by
  unfold _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic
  rw [d.vertexCount,P2.split_faces_length,P2.split_edgeCount]
  push_cast
  ring

end LiteralSplitData
end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

def cutSpellingLiteralData (P:FiniteCyclicPresentation) (cut:P2Cut P) (hP:P.IsSurfaceValid):
    LiteralSplitData (cutSpelling P cut) where
  cut:=literalCut P cut
  orientation:=rfl
  boundary:=by simp [literalCut,cutSpelling_boundary,cutSpellingWord]
  nonempty:=List.length_pos_of_ne_nil ((cutSpelling_isSurfaceValid P cut hP).2.1 _)

def cutSpellingSplitFaceEquiv (P:FiniteCyclicPresentation) (cut:P2Cut P):
    (P2.split P cut).Face≃(P2.split (cutSpelling P cut) (literalCut P cut)).Face:=
  (P2.faceEquiv P cut).symm.trans ((finCongr (by simp [cutSpelling])).trans
    (P2.faceEquiv (cutSpelling P cut) (literalCut P cut)))

 theorem cutSpellingSplitFaceEquiv_old (P:FiniteCyclicPresentation) (cut:P2Cut P) (f:P.Face):
     cutSpellingSplitFaceEquiv P cut (P2.oldFace P cut f)=
       P2.oldFace (cutSpelling P cut) (literalCut P cut) (cutSpellingFaceEquiv P cut f):=by
  apply Fin.ext
  rfl

 theorem cutSpellingSplitFaceEquiv_right (P:FiniteCyclicPresentation) (cut:P2Cut P):
     cutSpellingSplitFaceEquiv P cut (P2.rightFace P cut)=
       P2.rightFace (cutSpelling P cut) (literalCut P cut):=by
  apply Fin.ext
  change P.faces.length=(cutSpelling P cut).faces.length
  simp [cutSpelling]

 theorem cutSpellingSplit_boundary_old (P:FiniteCyclicPresentation) (cut:P2Cut P) (f:P.Face):
     (P2.split (cutSpelling P cut) (literalCut P cut)).boundary
       (cutSpellingSplitFaceEquiv P cut (P2.oldFace P cut f))=
       if f=cut.face.face then P2.retainWord cut.left++[.pos (P2.freshEdge P)]
       else P2.retainWord (P2.storedWord cut.face.orientation (P.boundary f)):=by
  rw [cutSpellingSplitFaceEquiv_old]
  by_cases hf:f=cut.face.face
  · subst f
    change (P2.split (cutSpelling P cut) (literalCut P cut)).boundary
      (P2.oldFace (cutSpelling P cut) (literalCut P cut) (literalCut P cut).face.face)=_
    rw [P2.split_boundary_selected]
    simp [P2.selectedBoundary,P2.selectedOrientedBoundary,P2.storedWord,literalCut,P2.freshEdge]
  · have hn:cutSpellingFaceEquiv P cut f≠(literalCut P cut).face.face:=
      (cutSpellingFaceEquiv P cut).injective.ne hf
    rw [P2.split_boundary_old_of_ne _ _ hn,cutSpelling_boundary]
    simp [cutSpellingWord,hf]

 theorem cutSpellingSplit_boundary_right (P:FiniteCyclicPresentation) (cut:P2Cut P):
     (P2.split (cutSpelling P cut) (literalCut P cut)).boundary
       (cutSpellingSplitFaceEquiv P cut (P2.rightFace P cut))=
       .neg (P2.freshEdge P)::P2.retainWord cut.right:=by
  rw [cutSpellingSplitFaceEquiv_right,P2.split_boundary_right]
  simp [P2.rightBoundary,P2.rightOrientedBoundary,P2.storedWord,literalCut,P2.freshEdge]

/-- The source cut and its literal global respelling induce genuinely isomorphic
 split presentations; the same global orientation is used on every face. -/
def cutSpellingSplitIso (P:FiniteCyclicPresentation) (cut:P2Cut P):
    UnorientedPresentationIso (P2.split P cut)
      (P2.split (cutSpelling P cut) (literalCut P cut)) where
  edgeRelabeling:=EdgeRelabeling.refl _
  faceEquiv:=cutSpellingSplitFaceEquiv P cut
  reverseFace:=fun _=>cut.face.orientation
  boundary_rotated q:=by
    rw [EdgeRelabeling.map_mapDart_refl]
    unfold orientedBoundary
    rcases P2.face_cases P cut q with ⟨f,rfl⟩|rfl
    · rw [P2.split_boundary_old,cutSpellingSplit_boundary_old]
      by_cases hf:f=cut.face.face
      · subst f
        cases hb:cut.face.orientation <;>
          simp only [P2.selectedBoundary,P2.selectedOrientedBoundary,P2.storedWord,hb,↓reduceIte] <;>
          exact List.IsRotated.refl _
      · rw [ite_eq_right hf,ite_eq_right hf]
        cases hb:cut.face.orientation <;>
          simpa [P2.storedWord,hb,P2.retainWord_inverseWord] using
            List.IsRotated.refl (P2.retainWord (P.boundary f))
    · rw [P2.split_boundary_right,cutSpellingSplit_boundary_right]
      cases hb:cut.face.orientation <;>
        simpa [P2.rightBoundary,P2.rightOrientedBoundary,P2.storedWord,hb] using
          List.IsRotated.refl (P2.storedWord cut.face.orientation
            (.neg (P2.freshEdge P)::P2.retainWord cut.right))

 theorem p2_eulerCharacteristic (P:FiniteCyclicPresentation) (cut:P2Cut P) (hP:P.IsSurfaceValid):
     eulerCharacteristic (P2.split P cut)=eulerCharacteristic P:=by
  have hQ:=cutSpelling_isSurfaceValid P cut hP
  calc
    eulerCharacteristic (P2.split P cut)=
        eulerCharacteristic (P2.split (cutSpelling P cut) (literalCut P cut)):=
      unoriented_eulerCharacteristic (cutSpellingSplitIso P cut) (P2.split_isSurfaceValid _ _ hQ)
    _=eulerCharacteristic (cutSpelling P cut):=(cutSpellingLiteralData P cut hP).eulerCharacteristic_eq
    _=eulerCharacteristic P:=(cutSpelling_eulerCharacteristic P cut hP).symm

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
