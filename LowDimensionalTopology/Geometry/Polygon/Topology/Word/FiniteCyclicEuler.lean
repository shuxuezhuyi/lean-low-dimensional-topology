/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.FiniteCyclicNormalizationResult
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

/-- The next literal corner of a stored cyclic face boundary. -/
def cornerNext (P:FiniteCyclicPresentation) (o:P.BoundaryOccurrence) :P.BoundaryOccurrence:=
  ⟨o.1,finRotate (P.boundary o.1).length o.2⟩

/-- The initial vertex of the occurrence in the canonical orientation of its edge. -/
def occurrenceInitial (P:FiniteCyclicPresentation) (o:P.BoundaryOccurrence) :P.BoundaryOccurrence:=
  match o.dart with | .pos _ => o | .neg _ => cornerNext P o

/-- The terminal vertex of the occurrence in the canonical orientation of its edge. -/
def occurrenceTerminal (P:FiniteCyclicPresentation) (o:P.BoundaryOccurrence) :P.BoundaryOccurrence:=
  match o.dart with | .pos _ => cornerNext P o | .neg _ => o

/-- The genuine endpoint identifications imposed by equal edge labels. No arbitrary
vertex names are supplied: both endpoints are literal cyclic word positions. -/
inductive CornerIdentification (P:FiniteCyclicPresentation) :P.BoundaryOccurrence→P.BoundaryOccurrence→Prop
  | initial (o p:P.BoundaryOccurrence) (h:o.edge=p.edge) :
      CornerIdentification P (occurrenceInitial P o) (occurrenceInitial P p)
  | terminal (o p:P.BoundaryOccurrence) (h:o.edge=p.edge) :
      CornerIdentification P (occurrenceTerminal P o) (occurrenceTerminal P p)

def cornerSetoid (P:FiniteCyclicPresentation) :Setoid P.BoundaryOccurrence where
  r:=Relation.EqvGen (CornerIdentification P)
  iseqv:=⟨fun o=>Relation.EqvGen.refl o,
    fun h=>Relation.EqvGen.symm _ _ h,fun h k=>Relation.EqvGen.trans _ _ _ h k⟩

/-- The actual finite set of vertices after all polygon edge endpoints are glued. -/
abbrev Vertex (P:FiniteCyclicPresentation) :=Quotient (cornerSetoid P)

def vertexClass (P:FiniteCyclicPresentation) (o:P.BoundaryOccurrence) :Vertex P:=Quotient.mk _ o

instance vertexFinite (P:FiniteCyclicPresentation) :Finite (Vertex P):=
  Finite.of_surjective (vertexClass P) (fun v=>Quotient.inductionOn v fun o=>⟨o,rfl⟩)

theorem vertexClass_surjective (P:FiniteCyclicPresentation) :Function.Surjective (vertexClass P):=
  fun v=>Quotient.inductionOn v fun o=>⟨o,rfl⟩

theorem vertexClass_eq_iff (P:FiniteCyclicPresentation) (o p:P.BoundaryOccurrence) :
    vertexClass P o=vertexClass P p↔Relation.EqvGen (CornerIdentification P) o p:=
  @Quotient.eq _ (cornerSetoid P) o p

theorem vertexClass_initial (P:FiniteCyclicPresentation) (o p:P.BoundaryOccurrence) (h:o.edge=p.edge) :
    vertexClass P (occurrenceInitial P o)=vertexClass P (occurrenceInitial P p):=
  (vertexClass_eq_iff P _ _).mpr (Relation.EqvGen.rel _ _
    (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.CornerIdentification.initial o p h))

theorem vertexClass_terminal (P:FiniteCyclicPresentation) (o p:P.BoundaryOccurrence) (h:o.edge=p.edge) :
    vertexClass P (occurrenceTerminal P o)=vertexClass P (occurrenceTerminal P p):=
  (vertexClass_eq_iff P _ _).mpr (Relation.EqvGen.rel _ _
    (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.CornerIdentification.terminal o p h))

/-- The genuine combinatorial Euler characteristic of the finite cyclic presentation. -/
def eulerCharacteristic (P:FiniteCyclicPresentation) :ℤ:=
  (Nat.card (Vertex P):ℤ)-P.edgeCount+P.faces.length

theorem twoMonogon_cornerNext (o:twoMonogonSphere.BoundaryOccurrence) :
    cornerNext twoMonogonSphere o=o:=by
  have hlen (f:twoMonogonSphere.Face):(twoMonogonSphere.boundary f).length=1:=by
    fin_cases f <;> rfl
  have hs:Subsingleton (Fin (twoMonogonSphere.boundary o.1).length):=by rw [hlen];infer_instance
  cases o with
  | mk f i=>
    change (⟨f,finRotate _ i⟩:twoMonogonSphere.BoundaryOccurrence)=⟨f,i⟩
    exact congrArg (fun j:Fin (twoMonogonSphere.boundary f).length=>
      (⟨f,j⟩:twoMonogonSphere.BoundaryOccurrence)) (hs.elim _ _)

theorem twoMonogon_occurrenceInitial (o:twoMonogonSphere.BoundaryOccurrence) :
    occurrenceInitial twoMonogonSphere o=o:=by
  unfold occurrenceInitial
  split
  · rfl
  · exact twoMonogon_cornerNext o

instance twoMonogonVertexSubsingleton :Subsingleton (Vertex twoMonogonSphere):=by
  constructor
  intro v w
  refine Quotient.inductionOn₂ v w ?_
  intro o p
  change vertexClass twoMonogonSphere o=vertexClass twoMonogonSphere p
  have hh:=vertexClass_initial twoMonogonSphere o p (Subsingleton.elim _ _)
  rwa [twoMonogon_occurrenceInitial,twoMonogon_occurrenceInitial] at hh

instance twoMonogonVertexNonempty :Nonempty (Vertex twoMonogonSphere):=
  ⟨vertexClass twoMonogonSphere ⟨0,⟨0,by decide⟩⟩⟩

theorem twoMonogon_vertexCount :Nat.card (Vertex twoMonogonSphere)=1:=Nat.card_unique

theorem sphere_eulerCharacteristic :eulerCharacteristic NormalForm.sphere.canonicalPresentation=2:=by
  change (Nat.card (Vertex twoMonogonSphere):ℤ)-1+2=2
  rw [twoMonogon_vertexCount]
  norm_num


 theorem finRotate_val_of_succ_lt {n:ℕ} (i:Fin n) (h:i.val+1<n) :
     (finRotate n i).val=i.val+1:=by
  have:=i.neZero
  rw [finRotate_apply]
  exact Fin.val_add_one_of_lt' h

 theorem finRotate_val_of_last {n:ℕ} (i:Fin n) (h:i.val+1=n) :
     (finRotate n i).val=0:=by
  cases n with
  | zero=>exact i.elim0
  | succ n=>
    have hi:i=Fin.last n:=by apply Fin.ext;dsimp;omega
    rw [hi,finRotate_last]
    rfl

 theorem p1_zeroOffset_bound (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence) :
     0<P1.dartWeight a o.dart:=by
  unfold P1.dartWeight
  split <;> norm_num

 theorem p1_weighted_prefix_succ (P:FiniteCyclicPresentation) (a:P.Edge) (f:P.Face)
     (i:Fin (P.boundary f).length) :
     ((P1.faceWeights P a f).take (i.val+1)).sum=
       ((P1.faceWeights P a f).take i.val).sum+P1.dartWeight a ((P.boundary f).get i):=by
  rw [List.take_succ_eq_append_getElem (by simp),List.sum_append,List.sum_singleton]
  congr 1
  exact P1.faceWeights_get P a f i

 theorem p1_cornerNext_within_block (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (k:Fin (P1.dartWeight a o.dart))
     (h:k.val+1<P1.dartWeight a o.dart) :
     cornerNext (P1.expand P a) (P1.expandedOccurrenceAt P a ⟨o,k⟩)=
       P1.expandedOccurrenceAt P a ⟨o,⟨k.val+1,h⟩⟩:=by
  rcases o with ⟨f,i⟩
  have hb:((P1.faceWeights P a f).take i.val).sum+(k.val+1)<
      ((P1.expand P a).boundary (P1.faceEquiv P a f)).length:=
    (P1.expandedOffsetIndex P a f i ⟨k.val+1,h⟩).isLt
  change (⟨P1.faceEquiv P a f,finRotate _ (P1.expandedOffsetIndex P a f i k)⟩:
    (P1.expand P a).BoundaryOccurrence)=⟨_,P1.expandedOffsetIndex P a f i ⟨k.val+1,h⟩⟩
  apply congrArg (fun j=>
    (⟨P1.faceEquiv P a f,j⟩:(P1.expand P a).BoundaryOccurrence))
  apply Fin.ext
  rw [finRotate_val_of_succ_lt _ (by simpa only [P1.expandedOffsetIndex_val,Nat.add_assoc] using hb)]
  rfl

 theorem p1_cornerNext_end_block (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (k:Fin (P1.dartWeight a o.dart))
     (h:k.val+1=P1.dartWeight a o.dart) :
     cornerNext (P1.expand P a) (P1.expandedOccurrenceAt P a ⟨o,k⟩)=
       P1.firstExpandedOccurrence P a (cornerNext P o):=by
  rcases o with ⟨f,i⟩
  change (⟨P1.faceEquiv P a f,finRotate _ (P1.expandedOffsetIndex P a f i k)⟩:
    (P1.expand P a).BoundaryOccurrence)=
      ⟨P1.faceEquiv P a f,P1.expandedStartIndex P a f (finRotate _ i)⟩
  apply congrArg (fun j=>
    (⟨P1.faceEquiv P a f,j⟩:(P1.expand P a).BoundaryOccurrence))
  apply Fin.ext
  by_cases hi:i.val+1<(P.boundary f).length
  · have hx:=finRotate_val_of_succ_lt i hi
    have hs:=p1_weighted_prefix_succ P a f i
    have hb:(P1.expandedOffsetIndex P a f i k).val+1<
        ((P1.expand P a).boundary (P1.faceEquiv P a f)).length:=by
      have hp:((P1.faceWeights P a f).take (i.val+1)).sum<
          ((P1.expand P a).boundary (P1.faceEquiv P a f)).length:=by
        simpa using (P1.expandedStartIndex P a f ⟨i.val+1,hi⟩).isLt
      rw [hs] at hp
      simpa only [P1.expandedOffsetIndex_val,Nat.add_assoc,h,BoundaryOccurrence.dart_mk] using hp
    rw [finRotate_val_of_succ_lt _ hb,P1.expandedStartIndex_val,hx]
    simpa only [P1.expandedOffsetIndex_val,Nat.add_assoc,h,BoundaryOccurrence.dart_mk] using hs.symm
  · have hil:i.val+1=(P.boundary f).length:=by omega
    have hs:=p1_weighted_prefix_succ P a f i
    rw [hil] at hs
    have ht:(P1.faceWeights P a f).take (P.boundary f).length=P1.faceWeights P a f:=
      List.take_of_length_le (by simp)
    rw [ht,P1.faceWeights_sum] at hs
    have hb:(P1.expandedOffsetIndex P a f i k).val+1=
        ((P1.expand P a).boundary (P1.faceEquiv P a f)).length:=by
      simpa only [P1.expandedOffsetIndex_val,Nat.add_assoc,h,BoundaryOccurrence.dart_mk] using hs.symm
    rw [finRotate_val_of_last _ hb,P1.expandedStartIndex_val,finRotate_val_of_last i hil]
    simp


/-- Evaluate endpoint-compatible labels on actual glued vertices. -/
def vertexLift {P:FiniteCyclicPresentation} {X:Type*} (f:P.BoundaryOccurrence→X)
    (hi:∀o p,o.edge=p.edge→f (occurrenceInitial P o)=f (occurrenceInitial P p))
    (ht:∀o p,o.edge=p.edge→f (occurrenceTerminal P o)=f (occurrenceTerminal P p)) :Vertex P→X:=
  Quotient.lift f (by
    intro o p h
    induction h with
    | rel o p h=>cases h with
      | initial o p h=>exact hi o p h
      | terminal o p h=>exact ht o p h
    | refl=>rfl
    | symm _ _ _ ih=>exact ih.symm
    | trans _ _ _ _ _ ih ik=>exact ih.trans ik)

 theorem p1_first_eq_at_zero (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence) :
     P1.firstExpandedOccurrence P a o=
       P1.expandedOccurrenceAt P a ⟨o,P1.zeroOffset a o.dart⟩:=by
  rcases o with ⟨f,i⟩
  apply congrArg (fun j=>(⟨P1.faceEquiv P a f,j⟩:(P1.expand P a).BoundaryOccurrence))
  apply Fin.ext
  simp [P1.expandedStartIndex,P1.expandedOffsetIndex,P1.zeroOffset]

/-- Collapse only the new middle corners to one new vertex; old corners retain
 their genuine original endpoint class. -/
def p1CornerCollapse (P:FiniteCyclicPresentation) (a:P.Edge)
    (o:(P1.expand P a).BoundaryOccurrence):Vertex P⊕Unit:=
  let p:=(P1.expandedOccurrenceEquiv P a).symm o
  if p.2.val=0 then Sum.inl (vertexClass P p.1) else Sum.inr ()

 theorem p1CornerCollapse_at (P:FiniteCyclicPresentation) (a:P.Edge)
     (p:P1.ExpandedSourcePosition P a):
     p1CornerCollapse P a (P1.expandedOccurrenceAt P a p)=
       if p.2.val=0 then Sum.inl (vertexClass P p.1) else Sum.inr ():=by
  unfold p1CornerCollapse
  rw [←P1.expandedOccurrenceEquiv_apply,Equiv.symm_apply_apply]

 theorem p1CornerCollapse_next (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (k:Fin (P1.dartWeight a o.dart)) :
     p1CornerCollapse P a (cornerNext (P1.expand P a) (P1.expandedOccurrenceAt P a ⟨o,k⟩))=
       if k.val+1<P1.dartWeight a o.dart then Sum.inr ()
       else Sum.inl (vertexClass P (cornerNext P o)):=by
  by_cases h:k.val+1<P1.dartWeight a o.dart
  · rw [p1_cornerNext_within_block P a o k h,p1CornerCollapse_at]
    simp [h]
  · have hk:k.val+1=P1.dartWeight a o.dart:=by omega
    rw [p1_cornerNext_end_block P a o k hk,p1_first_eq_at_zero,p1CornerCollapse_at]
    simp [h,P1.zeroOffset]

 theorem p1_collapse_initial_at (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (k:Fin (P1.dartWeight a o.dart)) :
     p1CornerCollapse P a (occurrenceInitial (P1.expand P a) (P1.expandedOccurrenceAt P a ⟨o,k⟩))=
       if (P1.expandedOccurrenceAt P a ⟨o,k⟩).edge=P1.freshEdge P.edgeCount
       then Sum.inr () else Sum.inl (vertexClass P (occurrenceInitial P o)):=by
  have hd:=P1.expandedOccurrenceAt_dart P a ⟨o,k⟩
  cases he:o.dart with
  | pos e=>
    by_cases ha:e=a
    · subst e
      have hk:k.val<2:=by simpa [P1.dartWeight,he,edgeOfDart] using k.isLt
      interval_cases hv:k.val <;>
        simp [occurrenceInitial,hd,BoundaryOccurrence.edge,he,P1.expandDart,
          P1.firstSubedge,P1.freshEdge,P1.dartWeight,edgeOfDart,hv,
          p1CornerCollapse_at,Fin.castSucc_ne_last]
    · have hk:k.val=0:=by have hh:=k.isLt;simp [P1.dartWeight,he,edgeOfDart,ha] at hh;omega
      simp [occurrenceInitial,hd,BoundaryOccurrence.edge,he,P1.expandDart,ha,
        P1.freshEdge,edgeOfDart,hk,p1CornerCollapse_at,Fin.castSucc_ne_last]
  | neg e=>
    by_cases ha:e=a
    · subst e
      have hk:k.val<2:=by simpa [P1.dartWeight,he,edgeOfDart] using k.isLt
      interval_cases hv:k.val <;>
        simp [occurrenceInitial,hd,BoundaryOccurrence.edge,he,P1.expandDart,
          P1.firstSubedge,P1.freshEdge,P1.dartWeight,edgeOfDart,hv,
          p1CornerCollapse_next,Fin.castSucc_ne_last]
    · have hk:k.val=0:=by have hh:=k.isLt;simp [P1.dartWeight,he,edgeOfDart,ha] at hh;omega
      simp [occurrenceInitial,hd,BoundaryOccurrence.edge,he,P1.expandDart,ha,
        P1.freshEdge,P1.dartWeight,edgeOfDart,hk,p1CornerCollapse_next,Fin.castSucc_ne_last]

 theorem p1_collapse_terminal_at (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (k:Fin (P1.dartWeight a o.dart)) :
     p1CornerCollapse P a (occurrenceTerminal (P1.expand P a) (P1.expandedOccurrenceAt P a ⟨o,k⟩))=
       if (P1.expandedOccurrenceAt P a ⟨o,k⟩).edge=P1.firstSubedge a
       then Sum.inr () else Sum.inl (vertexClass P (occurrenceTerminal P o)):=by
  have hd:=P1.expandedOccurrenceAt_dart P a ⟨o,k⟩
  cases he:o.dart with
  | pos e=>
    by_cases ha:e=a
    · subst e
      have hk:k.val<2:=by simpa [P1.dartWeight,he,edgeOfDart] using k.isLt
      interval_cases hv:k.val <;>
        simp [occurrenceTerminal,hd,BoundaryOccurrence.edge,he,P1.expandDart,
          P1.firstSubedge,P1.freshEdge,P1.dartWeight,edgeOfDart,hv,
          p1CornerCollapse_next,(Fin.castSucc_ne_last a).symm]
    · have hk:k.val=0:=by have hh:=k.isLt;simp [P1.dartWeight,he,edgeOfDart,ha] at hh;omega
      simp [occurrenceTerminal,hd,BoundaryOccurrence.edge,he,P1.expandDart,ha,
        P1.firstSubedge,P1.dartWeight,P1.freshEdge,edgeOfDart,hk,p1CornerCollapse_next]
  | neg e=>
    by_cases ha:e=a
    · subst e
      have hk:k.val<2:=by simpa [P1.dartWeight,he,edgeOfDart] using k.isLt
      interval_cases hv:k.val <;>
        simp [occurrenceTerminal,hd,BoundaryOccurrence.edge,he,P1.expandDart,
          P1.firstSubedge,P1.freshEdge,P1.dartWeight,edgeOfDart,hv,
          p1CornerCollapse_at,(Fin.castSucc_ne_last a).symm]
    · have hk:k.val=0:=by have hh:=k.isLt;simp [P1.dartWeight,he,edgeOfDart,ha] at hh;omega
      simp [occurrenceTerminal,hd,BoundaryOccurrence.edge,he,P1.expandDart,ha,
        P1.firstSubedge,P1.freshEdge,P1.dartWeight,edgeOfDart,hk,p1CornerCollapse_at]


 theorem p1_source_edge_eq_of_expanded_edge_eq (P:FiniteCyclicPresentation) (a:P.Edge)
     (p q:P1.ExpandedSourcePosition P a)
     (h:(P1.expandedOccurrenceAt P a p).edge=(P1.expandedOccurrenceAt P a q).edge) :
     p.1.edge=q.1.edge:=by
  rw [P1.expandedOccurrenceAt_edge,P1.expandedOccurrenceAt_edge] at h
  exact P1.sourceEdge_eq_of_expandedSubedge_eq a h

 theorem p1CornerCollapse_initial_compatible (P:FiniteCyclicPresentation) (a:P.Edge)
     (o p:(P1.expand P a).BoundaryOccurrence) (h:o.edge=p.edge) :
     p1CornerCollapse P a (occurrenceInitial (P1.expand P a) o)=
       p1CornerCollapse P a (occurrenceInitial (P1.expand P a) p):=by
  obtain ⟨⟨r,k⟩,hr⟩:=(P1.expandedOccurrenceEquiv P a).surjective o
  obtain ⟨⟨s,l⟩,hs⟩:=(P1.expandedOccurrenceEquiv P a).surjective p
  change P1.expandedOccurrenceAt P a ⟨r,k⟩=o at hr
  change P1.expandedOccurrenceAt P a ⟨s,l⟩=p at hs
  subst o;subst p
  rw [p1_collapse_initial_at,p1_collapse_initial_at,h]
  split
  · rfl
  · exact congrArg Sum.inl (vertexClass_initial P r s
      (p1_source_edge_eq_of_expanded_edge_eq P a _ _ h))

 theorem p1CornerCollapse_terminal_compatible (P:FiniteCyclicPresentation) (a:P.Edge)
     (o p:(P1.expand P a).BoundaryOccurrence) (h:o.edge=p.edge) :
     p1CornerCollapse P a (occurrenceTerminal (P1.expand P a) o)=
       p1CornerCollapse P a (occurrenceTerminal (P1.expand P a) p):=by
  obtain ⟨⟨r,k⟩,hr⟩:=(P1.expandedOccurrenceEquiv P a).surjective o
  obtain ⟨⟨s,l⟩,hs⟩:=(P1.expandedOccurrenceEquiv P a).surjective p
  change P1.expandedOccurrenceAt P a ⟨r,k⟩=o at hr
  change P1.expandedOccurrenceAt P a ⟨s,l⟩=p at hs
  subst o;subst p
  rw [p1_collapse_terminal_at,p1_collapse_terminal_at,h]
  split
  · rfl
  · exact congrArg Sum.inl (vertexClass_terminal P r s
      (p1_source_edge_eq_of_expanded_edge_eq P a _ _ h))

/-- The canonical map from actual vertices after an edge subdivision to old
 vertices together with the one subdividing midpoint. -/
def p1VertexCollapse (P:FiniteCyclicPresentation) (a:P.Edge):Vertex (P1.expand P a)→Vertex P⊕Unit:=
  vertexLift (p1CornerCollapse P a) (p1CornerCollapse_initial_compatible P a)
    (p1CornerCollapse_terminal_compatible P a)

 theorem p1VertexCollapse_class (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:(P1.expand P a).BoundaryOccurrence):
     p1VertexCollapse P a (vertexClass (P1.expand P a) o)=p1CornerCollapse P a o:=rfl

/-- The target occurrence carrying the retained part of a source edge. -/
def p1RetainedOccurrence (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
    (P1.expand P a).BoundaryOccurrence:=
  P1.expandedOccurrenceAt P a ⟨o,if hd:o.dart=.neg a
    then P1.oneOffset a o.dart (by rw [hd];rfl) else P1.zeroOffset a o.dart⟩

/-- The target occurrence ending at the old terminal endpoint. -/
def p1TerminalOccurrence (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
    (P1.expand P a).BoundaryOccurrence:=
  P1.expandedOccurrenceAt P a ⟨o,if hd:o.dart=.pos a
    then P1.oneOffset a o.dart (by rw [hd];rfl) else P1.zeroOffset a o.dart⟩

 theorem p1RetainedOccurrence_edge (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
     (p1RetainedOccurrence P a o).edge=o.edge.castSucc:=by
  cases hd:o.dart with
  | pos e=>
    unfold p1RetainedOccurrence
    rw [BoundaryOccurrence.edge,P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.zeroOffset,P1.expandDart,P1.firstSubedge,BoundaryOccurrence.edge,edgeOfDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,BoundaryOccurrence.edge,edgeOfDart]
  | neg e=>
    unfold p1RetainedOccurrence
    rw [BoundaryOccurrence.edge,P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.oneOffset,P1.expandDart,P1.firstSubedge,BoundaryOccurrence.edge,edgeOfDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,BoundaryOccurrence.edge,edgeOfDart]

 theorem p1TerminalOccurrence_edge (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
     (p1TerminalOccurrence P a o).edge=
       if o.edge=a then P1.freshEdge P.edgeCount else o.edge.castSucc:=by
  cases hd:o.dart with
  | pos e=>
    unfold p1TerminalOccurrence
    rw [BoundaryOccurrence.edge,P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.oneOffset,P1.expandDart,P1.freshEdge,BoundaryOccurrence.edge,edgeOfDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,BoundaryOccurrence.edge,edgeOfDart]
  | neg e=>
    unfold p1TerminalOccurrence
    rw [BoundaryOccurrence.edge,P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.zeroOffset,P1.expandDart,P1.freshEdge,BoundaryOccurrence.edge,edgeOfDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,BoundaryOccurrence.edge,edgeOfDart]

 theorem p1RetainedOccurrence_dart (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
     (p1RetainedOccurrence P a o).dart=P1.castSuccDart o.dart:=by
  cases hd:o.dart with
  | pos e=>
    unfold p1RetainedOccurrence
    rw [P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.zeroOffset,P1.expandDart,P1.firstSubedge,P1.castSuccDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,P1.castSuccDart]
  | neg e=>
    unfold p1RetainedOccurrence
    rw [P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.oneOffset,P1.expandDart,P1.firstSubedge,P1.castSuccDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,P1.castSuccDart]


 theorem p1Retained_initial (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
     occurrenceInitial (P1.expand P a) (p1RetainedOccurrence P a o)=
       P1.firstExpandedOccurrence P a (occurrenceInitial P o):=by
  have hd:=p1RetainedOccurrence_dart P a o
  cases ho:o.dart with
  | pos e=>
    simp only [occurrenceInitial,hd,ho,P1.castSuccDart]
    simpa [p1RetainedOccurrence,ho] using
      (p1_first_eq_at_zero P a o).symm
  | neg e=>
    simp only [occurrenceInitial,hd,ho,P1.castSuccDart]
    by_cases he:e=a
    · subst e
      have hx:p1RetainedOccurrence P a o=
          P1.expandedOccurrenceAt P a ⟨o,P1.oneOffset a o.dart (by rw [ho];rfl)⟩:=by
        simp [p1RetainedOccurrence,ho]
      rw [hx]
      apply p1_cornerNext_end_block
      simp [P1.oneOffset,P1.dartWeight,ho,edgeOfDart]
    · have hx:p1RetainedOccurrence P a o=
          P1.expandedOccurrenceAt P a ⟨o,P1.zeroOffset a o.dart⟩:=by
        simp [p1RetainedOccurrence,ho,he]
      rw [hx]
      apply p1_cornerNext_end_block
      simp [P1.zeroOffset,P1.dartWeight,ho,edgeOfDart,he]

 theorem p1TerminalOccurrence_dart (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
     (p1TerminalOccurrence P a o).dart=
       if o.edge=a then (match o.dart with
         | .pos _ => .pos (P1.freshEdge P.edgeCount)
         | .neg _ => .neg (P1.freshEdge P.edgeCount)) else P1.castSuccDart o.dart:=by
  cases hd:o.dart with
  | pos e=>
    unfold p1TerminalOccurrence
    rw [P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.oneOffset,P1.expandDart,P1.freshEdge,BoundaryOccurrence.edge,edgeOfDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,BoundaryOccurrence.edge,edgeOfDart,P1.castSuccDart]
  | neg e=>
    unfold p1TerminalOccurrence
    rw [P1.expandedOccurrenceAt_dart]
    by_cases ha:e=a
    · subst e;simp [hd,P1.zeroOffset,P1.expandDart,P1.freshEdge,BoundaryOccurrence.edge,edgeOfDart]
    · simp [hd,P1.zeroOffset,P1.expandDart,ha,BoundaryOccurrence.edge,edgeOfDart,P1.castSuccDart]


 theorem p1Terminal_terminal (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
     occurrenceTerminal (P1.expand P a) (p1TerminalOccurrence P a o)=
       P1.firstExpandedOccurrence P a (occurrenceTerminal P o):=by
  have hd:=p1TerminalOccurrence_dart P a o
  cases ho:o.dart with
  | pos e=>
    by_cases he:e=a
    · subst e
      have ht:(p1TerminalOccurrence P a o).dart=.pos (P1.freshEdge P.edgeCount):=by
        simpa [BoundaryOccurrence.edge,ho,edgeOfDart] using hd
      simp only [occurrenceTerminal,ht,ho]
      have hx:p1TerminalOccurrence P a o=
          P1.expandedOccurrenceAt P a ⟨o,P1.oneOffset a o.dart (by rw [ho];rfl)⟩:=by
        simp [p1TerminalOccurrence,ho]
      rw [hx]
      apply p1_cornerNext_end_block
      simp [P1.oneOffset,P1.dartWeight,ho,edgeOfDart]
    · have ht:(p1TerminalOccurrence P a o).dart=.pos e.castSucc:=by
        simpa [BoundaryOccurrence.edge,ho,edgeOfDart,he,P1.castSuccDart] using hd
      simp only [occurrenceTerminal,ht,ho]
      have hx:p1TerminalOccurrence P a o=
          P1.expandedOccurrenceAt P a ⟨o,P1.zeroOffset a o.dart⟩:=by
        simp [p1TerminalOccurrence,ho,he]
      rw [hx]
      apply p1_cornerNext_end_block
      simp [P1.zeroOffset,P1.dartWeight,ho,edgeOfDart,he]
  | neg e=>
    have ht:∃d,(p1TerminalOccurrence P a o).dart=.neg d:=by
      by_cases he:e=a
      · refine ⟨P1.freshEdge P.edgeCount,?_⟩
        simpa [BoundaryOccurrence.edge,ho,edgeOfDart,he] using hd
      · refine ⟨e.castSucc,?_⟩
        simpa [BoundaryOccurrence.edge,ho,edgeOfDart,he,P1.castSuccDart] using hd
    obtain ⟨d,ht⟩:=ht
    simp only [occurrenceTerminal,ht,ho]
    simpa [p1TerminalOccurrence,ho] using (p1_first_eq_at_zero P a o).symm


 theorem p1OldCorners_initial_compatible (P:FiniteCyclicPresentation) (a:P.Edge)
     (o p:P.BoundaryOccurrence) (h:o.edge=p.edge):
     vertexClass (P1.expand P a) (P1.firstExpandedOccurrence P a (occurrenceInitial P o))=
       vertexClass (P1.expand P a) (P1.firstExpandedOccurrence P a (occurrenceInitial P p)):=by
  rw [←p1Retained_initial,←p1Retained_initial]
  apply vertexClass_initial
  rw [p1RetainedOccurrence_edge,p1RetainedOccurrence_edge,h]

 theorem p1OldCorners_terminal_compatible (P:FiniteCyclicPresentation) (a:P.Edge)
     (o p:P.BoundaryOccurrence) (h:o.edge=p.edge):
     vertexClass (P1.expand P a) (P1.firstExpandedOccurrence P a (occurrenceTerminal P o))=
       vertexClass (P1.expand P a) (P1.firstExpandedOccurrence P a (occurrenceTerminal P p)):=by
  rw [←p1Terminal_terminal,←p1Terminal_terminal]
  apply vertexClass_terminal
  rw [p1TerminalOccurrence_edge,p1TerminalOccurrence_edge,h]

/-- Send genuine old vertices to their literal old corners in the subdivision. -/
def p1OldVertexEmbedding (P:FiniteCyclicPresentation) (a:P.Edge):Vertex P→Vertex (P1.expand P a):=
  vertexLift (fun o=>vertexClass (P1.expand P a) (P1.firstExpandedOccurrence P a o))
    (p1OldCorners_initial_compatible P a) (p1OldCorners_terminal_compatible P a)

 theorem p1OldVertexEmbedding_class (P:FiniteCyclicPresentation) (a:P.Edge) (o:P.BoundaryOccurrence):
     p1OldVertexEmbedding P a (vertexClass P o)=
       vertexClass (P1.expand P a) (P1.firstExpandedOccurrence P a o):=rfl

 theorem p1VertexCollapse_old (P:FiniteCyclicPresentation) (a:P.Edge) (v:Vertex P):
     p1VertexCollapse P a (p1OldVertexEmbedding P a v)=Sum.inl v:=by
  refine Quotient.inductionOn v ?_
  intro o
  change p1VertexCollapse P a (p1OldVertexEmbedding P a (vertexClass P o))=Sum.inl (vertexClass P o)
  rw [p1OldVertexEmbedding_class,p1VertexCollapse_class,p1_first_eq_at_zero,p1CornerCollapse_at]
  simp [P1.zeroOffset]

 theorem p1OldVertexEmbedding_injective (P:FiniteCyclicPresentation) (a:P.Edge):
     Function.Injective (p1OldVertexEmbedding P a):=by
  intro v w h
  have hh:=congrArg (p1VertexCollapse P a) h
  simpa only [p1VertexCollapse_old,Sum.inl.injEq] using hh

/-- The literal new midpoint corner at a selected old occurrence. -/
def p1MiddleOccurrence (P:FiniteCyclicPresentation) (a:P.Edge)
    (o:P.BoundaryOccurrence) (h:o.edge=a):(P1.expand P a).BoundaryOccurrence:=
  P1.expandedOccurrenceAt P a ⟨o,P1.oneOffset a o.dart h⟩

 theorem p1VertexCollapse_middle (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (h:o.edge=a):
     p1VertexCollapse P a (vertexClass (P1.expand P a) (p1MiddleOccurrence P a o h))=Sum.inr ():=by
  rw [p1VertexCollapse_class,p1MiddleOccurrence,p1CornerCollapse_at]
  simp [P1.oneOffset]


 theorem p1Retained_terminal_selected (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (h:o.edge=a):
     occurrenceTerminal (P1.expand P a) (p1RetainedOccurrence P a o)=
       p1MiddleOccurrence P a o h:=by
  have hd:=p1RetainedOccurrence_dart P a o
  cases ho:o.dart with
  | pos e=>
    have he:e=a:=by simpa only [BoundaryOccurrence.edge,ho,edgeOfDart] using h
    subst e
    simp only [occurrenceTerminal,hd,ho,P1.castSuccDart]
    have hx:p1RetainedOccurrence P a o=P1.expandedOccurrenceAt P a ⟨o,P1.zeroOffset a o.dart⟩:=by
      simp [p1RetainedOccurrence,ho]
    rw [hx,p1_cornerNext_within_block P a o (P1.zeroOffset a o.dart)
      (by simp [P1.zeroOffset,P1.dartWeight,ho,edgeOfDart])]
    unfold p1MiddleOccurrence
    apply congrArg (fun k:Fin (P1.dartWeight a o.dart)=>P1.expandedOccurrenceAt P a ⟨o,k⟩)
    apply Fin.ext
    rfl
  | neg e=>
    have he:e=a:=by simpa only [BoundaryOccurrence.edge,ho,edgeOfDart] using h
    subst e
    simp only [occurrenceTerminal,hd,ho,P1.castSuccDart]
    simp [p1RetainedOccurrence,p1MiddleOccurrence,ho]

 theorem p1Middle_vertexClass_eq (P:FiniteCyclicPresentation) (a:P.Edge)
     (o p:P.BoundaryOccurrence) (ho:o.edge=a) (hp:p.edge=a):
     vertexClass (P1.expand P a) (p1MiddleOccurrence P a o ho)=
       vertexClass (P1.expand P a) (p1MiddleOccurrence P a p hp):=by
  rw [←p1Retained_terminal_selected,←p1Retained_terminal_selected]
  apply vertexClass_terminal
  rw [p1RetainedOccurrence_edge,p1RetainedOccurrence_edge,ho,hp]

/-- The inverse to collapse uses a genuine occurrence of the subdivided edge. -/
def p1VertexExpand (P:FiniteCyclicPresentation) (a:P.Edge)
    (o:P.BoundaryOccurrence) (h:o.edge=a):Vertex P⊕Unit→Vertex (P1.expand P a)
  | .inl v=>p1OldVertexEmbedding P a v
  | .inr _=>vertexClass (P1.expand P a) (p1MiddleOccurrence P a o h)

 theorem p1Collapse_expand (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (h:o.edge=a) (v:Vertex P⊕Unit):
     p1VertexCollapse P a (p1VertexExpand P a o h v)=v:=by
  cases v with
  | inl v=>exact p1VertexCollapse_old P a v
  | inr u=>cases u;exact p1VertexCollapse_middle P a o h

 theorem p1Expand_collapse (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (h:o.edge=a) (v:Vertex (P1.expand P a)):
     p1VertexExpand P a o h (p1VertexCollapse P a v)=v:=by
  refine Quotient.inductionOn v ?_
  intro q
  change p1VertexExpand P a o h (p1VertexCollapse P a (vertexClass (P1.expand P a) q))=
    vertexClass (P1.expand P a) q
  obtain ⟨⟨p,k⟩,hp⟩:=(P1.expandedOccurrenceEquiv P a).surjective q
  change P1.expandedOccurrenceAt P a ⟨p,k⟩=q at hp
  subst q
  rw [p1VertexCollapse_class,p1CornerCollapse_at]
  by_cases hk:k.val=0
  · rw [ite_eq_left hk]
    change p1OldVertexEmbedding P a (vertexClass P p)=
      vertexClass (P1.expand P a) (P1.expandedOccurrenceAt P a ⟨p,k⟩)
    rw [p1OldVertexEmbedding_class,p1_first_eq_at_zero]
    have hkz:k=P1.zeroOffset a p.dart:=by
      apply Fin.ext
      simpa only [P1.zeroOffset] using hk
    rw [hkz]
  · rw [ite_eq_right hk]
    have hw:P1.dartWeight a p.dart=2:=by
      by_cases he:edgeOfDart p.dart=a
      · simp only [P1.dartWeight,ite_eq_left he]
      · have hl:k.val<1:=by simpa only [P1.dartWeight,ite_eq_right he] using k.isLt
        omega
    have hp:p.edge=a:=(P1.dartWeight_eq_two_iff a p.dart).mp hw
    have hv:k=P1.oneOffset a p.dart hp:=by
      apply Fin.ext
      have hl:k.val<2:=by simpa only [hw] using k.isLt
      change k.val=1
      omega
    rw [hv]
    exact p1Middle_vertexClass_eq P a o p h hp

/-- An ordinary edge subdivision adds exactly one genuine glued vertex. -/
def p1VertexEquiv (P:FiniteCyclicPresentation) (a:P.Edge)
    (o:P.BoundaryOccurrence) (h:o.edge=a):Vertex (P1.expand P a)≃Vertex P⊕Unit where
  toFun:=p1VertexCollapse P a
  invFun:=p1VertexExpand P a o h
  left_inv:=p1Expand_collapse P a o h
  right_inv:=p1Collapse_expand P a o h

 theorem p1_vertexCount (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (h:o.edge=a):
     Nat.card (Vertex (P1.expand P a))=Nat.card (Vertex P)+1:=by
  simpa using Nat.card_congr (p1VertexEquiv P a o h)


 theorem occurrence_exists_of_valid (P:FiniteCyclicPresentation) (h:P.IsSurfaceValid) (a:P.Edge):
     ∃o:P.BoundaryOccurrence,o.edge=a:=by
  have hm:0<(P.edgeOccurrences a).card:=by
    rw [P.card_edgeOccurrences]
    rcases h.2.2.2 a with he|he <;> omega
  obtain ⟨o,ho⟩:=Finset.card_pos.mp hm
  exact ⟨o,(P.mem_edgeOccurrences a o).mp ho⟩

 theorem p1_eulerCharacteristic_of_occurrence (P:FiniteCyclicPresentation) (a:P.Edge)
     (o:P.BoundaryOccurrence) (h:o.edge=a):
     eulerCharacteristic (P1.expand P a)=eulerCharacteristic P:=by
  unfold eulerCharacteristic
  rw [p1_vertexCount P a o h,P1.expand_faces_length,P1.expand_edgeCount]
  push_cast
  ring

 theorem p1_eulerCharacteristic (P:FiniteCyclicPresentation) (a:P.Edge) (h:P.IsSurfaceValid):
     eulerCharacteristic (P1.expand P a)=eulerCharacteristic P:=by
  obtain ⟨o,ho⟩:=occurrence_exists_of_valid P h a
  exact p1_eulerCharacteristic_of_occurrence P a o ho

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
