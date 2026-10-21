/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicEuler
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

/-- Literal endpoint transport, including reversal of an individual edge. -/
structure EndpointTransport (P Q:FiniteCyclicPresentation) where
  corners:P.BoundaryOccurrence≃Q.BoundaryOccurrence
  occurrences:P.BoundaryOccurrence≃Q.BoundaryOccurrence
  edges:P.Edge≃Q.Edge
  faces:P.Face≃Q.Face
  reverse:P.Edge→Bool
  edge:∀o,(occurrences o).edge=edges o.edge
  initial:∀o,corners (occurrenceInitial P o)=if reverse o.edge
    then occurrenceTerminal Q (occurrences o) else occurrenceInitial Q (occurrences o)
  terminal:∀o,corners (occurrenceTerminal P o)=if reverse o.edge
    then occurrenceInitial Q (occurrences o) else occurrenceTerminal Q (occurrences o)

namespace EndpointTransport
variable {P Q:FiniteCyclicPresentation} (e:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.EndpointTransport P Q)

theorem inverse_initial (o:P.BoundaryOccurrence):
    e.corners.symm (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial Q (e.occurrences
      o))=
      if e.reverse o.edge then _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal P o else _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial P o:=by
  cases h:e.reverse o.edge with
  | false=>simpa [h] using (congrArg e.corners.symm (e.initial o)).symm
  | true=>simpa [h] using (congrArg e.corners.symm (e.terminal o)).symm

theorem inverse_terminal (o:P.BoundaryOccurrence):
    e.corners.symm (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal Q (e.occurrences
      o))=
      if e.reverse o.edge then _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial P o else _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal P o:=by
  cases h:e.reverse o.edge with
  | false=>simpa [h] using (congrArg e.corners.symm (e.terminal o)).symm
  | true=>simpa [h] using (congrArg e.corners.symm (e.initial o)).symm

theorem forward_initial_compatible (o p:P.BoundaryOccurrence) (h:o.edge=p.edge):
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass Q (e.corners
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial P o))=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass Q (e.corners (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial P p)):=by
  rw [e.initial,e.initial,h]
  have he:(e.occurrences o).edge=(e.occurrences p).edge:=by rw [e.edge,e.edge,h]
  split
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal Q _ _ he
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial Q _ _ he

theorem forward_terminal_compatible (o p:P.BoundaryOccurrence) (h:o.edge=p.edge):
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass Q (e.corners
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal P o))=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass Q (e.corners (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal P p)):=by
  rw [e.terminal,e.terminal,h]
  have he:(e.occurrences o).edge=(e.occurrences p).edge:=by rw [e.edge,e.edge,h]
  split
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial Q _ _ he
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal Q _ _ he

theorem inverse_initial_compatible (o p:Q.BoundaryOccurrence) (h:o.edge=p.edge):
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (e.corners.symm
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial Q o))=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (e.corners.symm (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial Q p)):=by
  obtain ⟨r,rfl⟩:=e.occurrences.surjective o
  obtain ⟨s,rfl⟩:=e.occurrences.surjective p
  have hs:r.edge=s.edge:=e.edges.injective (by simpa only [e.edge] using h)
  rw [e.inverse_initial,e.inverse_initial,hs]
  split
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal P _ _ hs
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial P _ _ hs

theorem inverse_terminal_compatible (o p:Q.BoundaryOccurrence) (h:o.edge=p.edge):
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (e.corners.symm
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal Q o))=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (e.corners.symm (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal Q p)):=by
  obtain ⟨r,rfl⟩:=e.occurrences.surjective o
  obtain ⟨s,rfl⟩:=e.occurrences.surjective p
  have hs:r.edge=s.edge:=e.edges.injective (by simpa only [e.edge] using h)
  rw [e.inverse_terminal,e.inverse_terminal,hs]
  split
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial P _ _ hs
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal P _ _ hs

def mapVertex:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex P→_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex Q:=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexLift (fun
    o=>_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass Q (e.corners
    o)) e.forward_initial_compatible e.forward_terminal_compatible

def inverseVertex:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex Q→_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex P:=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexLift (fun
    o=>_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (e.corners.symm
    o)) e.inverse_initial_compatible e.inverse_terminal_compatible

def vertexEquiv:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex P≃_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex Q where
  toFun:=e.mapVertex
  invFun:=e.inverseVertex
  left_inv v:=by
    refine Quotient.inductionOn v ?_
    intro o
    change _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P (e.corners.symm (e.corners
      o))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass P o
    rw [Equiv.symm_apply_apply]
  right_inv v:=by
    refine Quotient.inductionOn v ?_
    intro o
    change _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass Q (e.corners (e.corners.symm
      o))=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass Q o
    rw [Equiv.apply_symm_apply]

include e in
theorem vertexCount:Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex
  P)=Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex Q):=Nat.card_congr e.vertexEquiv

include e in
theorem eulerCharacteristic_eq:_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic P=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic Q:=by
  have hv:((Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex P):ℕ):ℤ)=(Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex Q):ℤ):=by exact_mod_cast e.vertexCount
  have he:(P.edgeCount:ℤ)=(Q.edgeCount:ℤ):=by
    exact_mod_cast (show P.edgeCount=Q.edgeCount from by simpa using Fintype.card_congr e.edges)
  have hf:(P.faces.length:ℤ)=(Q.faces.length:ℤ):=by
    exact_mod_cast (show P.faces.length=Q.faces.length from by simpa using Fintype.card_congr e.faces)
  unfold _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic
  omega
end EndpointTransport

 theorem finRotate_val_mod {n:ℕ} (i:Fin n):(finRotate n i).val=(i.val+1)%n:=by
  by_cases h:i.val+1<n
  · rw [finRotate_val_of_succ_lt i h,Nat.mod_eq_of_lt h]
  · have hi:i.val+1=n:=by omega
    rw [finRotate_val_of_last i hi,hi,Nat.mod_self]

 theorem finRotate_rev_rotate {n:ℕ} (i:Fin n):
     finRotate n (finRotate n i).rev=i.rev:=by
  apply Fin.ext
  by_cases h:i.val+1<n
  · have hr:(finRotate n i).rev.val+1<n:=by
      rw [Fin.val_rev,finRotate_val_of_succ_lt i h]
      omega
    rw [finRotate_val_of_succ_lt _ hr,Fin.val_rev,finRotate_val_of_succ_lt i h,Fin.val_rev]
    omega
  · have hi:i.val+1=n:=by omega
    have hr:(finRotate n i).rev.val+1=n:=by
      rw [Fin.val_rev,finRotate_val_of_last i hi]
      omega
    rw [finRotate_val_of_last _ hr,Fin.val_rev]
    omega


def unorientedRotationIndex {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
    (hQ:Q.IsSurfaceValid) (f:P.Face) (i:Fin (P.boundary f).length):
    Fin (Q.boundary (e.faceEquiv f)).length:=
  (e.orientedSideIndex hQ f i).cast (Q.orientedBoundary_length _)

 theorem unorientedRotationIndex_next {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
     (hQ:Q.IsSurfaceValid) (f:P.Face) (i:Fin (P.boundary f).length):
     unorientedRotationIndex e hQ f (finRotate _ i)=
       finRotate _ (unorientedRotationIndex e hQ f i):=by
  have hl:=e.boundary_length_eq f
  have hi:(finRotate (P.boundary f).length i).val=
      (i.val+1)%(Q.boundary (e.faceEquiv f)).length:=
    (finRotate_val_mod i).trans (congrArg (fun n:ℕ=>(i.val+1)%n) hl)
  apply Fin.ext
  rw [finRotate_val_mod]
  simp only [unorientedRotationIndex,Fin.val_cast,UnorientedPresentationIso.orientedSideIndex]
  rw [Q.orientedBoundary_length,hi]
  simp only [Nat.mod_add_mod]
  congr 1
  omega

/-- Correct corner transport after independently reflecting and cyclically rotating faces. -/
def unorientedCornerEquiv {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
    (hQ:Q.IsSurfaceValid):P.BoundaryOccurrence≃Q.BoundaryOccurrence:=
  (e.occurrenceEquiv hQ).trans (Equiv.sigmaCongrRight fun f=>
    if e.reverseFace (e.faceEquiv.symm f) then finRotate (Q.boundary f).length else Equiv.refl _)

 theorem unorientedCornerEquiv_apply {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
     (hQ:Q.IsSurfaceValid) (o:P.BoundaryOccurrence):
     unorientedCornerEquiv e hQ o=if e.reverseFace o.1 then cornerNext Q (e.mapOccurrence hQ o)
       else e.mapOccurrence hQ o:=by
  rcases o with ⟨f,i⟩
  cases hr:e.reverseFace f <;>
    simp [unorientedCornerEquiv,Equiv.sigmaCongrRight,UnorientedPresentationIso.mapOccurrence,
      UnorientedPresentationIso.sideIndex,hr,cornerNext]

 theorem unorientedCornerEquiv_next {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
     (hQ:Q.IsSurfaceValid) (o:P.BoundaryOccurrence):
     unorientedCornerEquiv e hQ (cornerNext P o)=if e.reverseFace o.1 then e.mapOccurrence hQ o
       else cornerNext Q (e.mapOccurrence hQ o):=by
  rcases o with ⟨f,i⟩
  rw [unorientedCornerEquiv_apply]
  cases hr:e.reverseFace f
  · simp only [cornerNext,hr,Bool.false_eq_true,ite_false,UnorientedPresentationIso.mapOccurrence,UnorientedPresentationIso.sideIndex]
    apply congrArg (fun j=>(⟨e.faceEquiv f,j⟩:Q.BoundaryOccurrence))
    change unorientedRotationIndex e hQ f (finRotate _ i)=finRotate _ (unorientedRotationIndex e hQ f i)
    exact unorientedRotationIndex_next e hQ f i
  · simp only [cornerNext,hr,ite_true,UnorientedPresentationIso.mapOccurrence,UnorientedPresentationIso.sideIndex]
    apply congrArg (fun j=>(⟨e.faceEquiv f,j⟩:Q.BoundaryOccurrence))
    change finRotate _ (unorientedRotationIndex e hQ f (finRotate _ i)).rev=
      (unorientedRotationIndex e hQ f i).rev
    rw [unorientedRotationIndex_next,finRotate_rev_rotate]


 theorem unorientedCornerEquiv_initial {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
     (hQ:Q.IsSurfaceValid) (o:P.BoundaryOccurrence):
     unorientedCornerEquiv e hQ (occurrenceInitial P o)=if e.edgeRelabeling.reverse o.edge
       then occurrenceTerminal Q (e.mapOccurrence hQ o) else occurrenceInitial Q (e.mapOccurrence hQ o):=by
  have hd:=e.mapOccurrence_dart hQ o
  cases hs:o.dart with
  | pos a=>
    simp only [occurrenceInitial,hs]
    rw [unorientedCornerEquiv_apply]
    cases hr:e.reverseFace o.1 <;> cases he:e.edgeRelabeling.reverse a <;>
      simp [occurrenceTerminal,hd,hs,hr,he,EdgeRelabeling.mapDart,
        BoundaryOccurrence.edge,edgeOfDart,SignedDart.flip]
  | neg a=>
    simp only [occurrenceInitial,hs]
    rw [unorientedCornerEquiv_next]
    cases hr:e.reverseFace o.1 <;> cases he:e.edgeRelabeling.reverse a <;>
      simp [occurrenceTerminal,hd,hs,hr,he,EdgeRelabeling.mapDart,
        BoundaryOccurrence.edge,edgeOfDart,SignedDart.flip]

 theorem unorientedCornerEquiv_terminal {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
     (hQ:Q.IsSurfaceValid) (o:P.BoundaryOccurrence):
     unorientedCornerEquiv e hQ (occurrenceTerminal P o)=if e.edgeRelabeling.reverse o.edge
       then occurrenceInitial Q (e.mapOccurrence hQ o) else occurrenceTerminal Q (e.mapOccurrence hQ o):=by
  have hd:=e.mapOccurrence_dart hQ o
  cases hs:o.dart with
  | pos a=>
    simp only [occurrenceTerminal,hs]
    rw [unorientedCornerEquiv_next]
    cases hr:e.reverseFace o.1 <;> cases he:e.edgeRelabeling.reverse a <;>
      simp [occurrenceInitial,hd,hs,hr,he,EdgeRelabeling.mapDart,
        BoundaryOccurrence.edge,edgeOfDart,SignedDart.flip]
  | neg a=>
    simp only [occurrenceTerminal,hs]
    rw [unorientedCornerEquiv_apply]
    cases hr:e.reverseFace o.1 <;> cases he:e.edgeRelabeling.reverse a <;>
      simp [occurrenceInitial,hd,hs,hr,he,EdgeRelabeling.mapDart,
        BoundaryOccurrence.edge,edgeOfDart,SignedDart.flip]

/-- A genuine presentation reorientation supplies every endpoint-transport field. -/
def unorientedEndpointTransport {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
    (hQ:Q.IsSurfaceValid):EndpointTransport P Q where
  corners:=unorientedCornerEquiv e hQ
  occurrences:=e.occurrenceEquiv hQ
  edges:=e.edgeEquiv
  faces:=e.faceEquiv
  reverse:=e.edgeRelabeling.reverse
  edge o:=e.mapOccurrence_edge hQ o
  initial o:=unorientedCornerEquiv_initial e hQ o
  terminal o:=unorientedCornerEquiv_terminal e hQ o

 theorem unoriented_eulerCharacteristic {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q)
     (hQ:Q.IsSurfaceValid):eulerCharacteristic P=eulerCharacteristic Q:=
  (unorientedEndpointTransport e hQ).eulerCharacteristic_eq

 theorem signed_eulerCharacteristic {P Q:FiniteCyclicPresentation} (e:SignedPresentationIso P Q)
     (hQ:Q.IsSurfaceValid):eulerCharacteristic P=eulerCharacteristic Q:=
  unoriented_eulerCharacteristic (UnorientedPresentationIso.ofSignedPresentationIso e) hQ

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
