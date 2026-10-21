/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicOccurrenceGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCorners
/-!
# Word vertices and raw corner classes

Occurrence indices preserve cyclic succession and the original side partner.
The generated word-corner relation is exactly the raw endpoint relation,
yielding a bijection between word vertices and raw corner classes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise

def originalCyclicCornerIndex {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    (originalCyclicPresentation J e).presentation.BoundaryOccurrence≃ZMod J.n :=
  (originalCyclicOccurrenceIndex J e).trans (originalCyclicFinIndex J)

theorem originalCyclicCornerIndex_next {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    originalCyclicCornerIndex J e (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext
      (originalCyclicPresentation J e).presentation o)=
      originalCyclicCornerIndex J e o+1 := by
  have hi : originalCyclicOccurrenceIndex J e (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext
    (originalCyclicPresentation J e).presentation o)=
      finRotate J.n (originalCyclicOccurrenceIndex J e o) := by
    apply Fin.ext
    change (finRotate ((originalCyclicPresentation J e).presentation.boundary o.1).length o.2).val=
      (finRotate J.n (originalCyclicOccurrenceIndex J e o)).val
    have hlen:=originalCyclicFaceBoundary_length J e o.1
    by_cases h : o.2.val+1<J.n
    · rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_succ_lt _ (by simpa only [hlen] using h),
        _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_succ_lt _ (by simpa only [originalCyclicOccurrenceIndex_val] using h)]
      rfl
    · have ho : o.2.val<J.n:=by simpa only [hlen] using o.2.isLt
      have hlast : o.2.val+1=J.n:=by omega
      rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_last _ (by simpa only [hlen] using hlast),
        _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.finRotate_val_of_last _ (by simpa only [originalCyclicOccurrenceIndex_val] using hlast)]
  change originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e
    (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext (originalCyclicPresentation J
      e).presentation o))=
      originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e o)+1
  rw [hi]
  let : NeZero J.n:=⟨by have h:=J.three_le;omega⟩
  change (ZMod.finEquiv J.n) (finRotate J.n _)=(ZMod.finEquiv J.n) _+1
  simp only [finRotate_apply,map_add,map_one]


theorem originalCyclicCornerIndex_symm_next {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) (i : ZMod J.n) :
    (originalCyclicCornerIndex J e).symm (i+1)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext (originalCyclicPresentation J e).presentation ((originalCyclicCornerIndex J e).symm i) := by
  apply (originalCyclicCornerIndex J e).injective
  simp only [Equiv.apply_symm_apply,originalCyclicCornerIndex_next]

def originalCyclicCornerPartner {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    (originalCyclicPresentation J e).presentation.BoundaryOccurrence :=
  (originalCyclicCornerIndex J e).symm
    (originalCyclicPairIndex J e (originalCyclicCornerIndex J e o))

theorem originalCyclicCornerPartner_index {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    originalCyclicCornerIndex J e (originalCyclicCornerPartner J e o)=
      originalCyclicPairIndex J e (originalCyclicCornerIndex J e o) :=
  (originalCyclicCornerIndex J e).apply_symm_apply _

theorem originalCyclicCornerPartner_ne {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    originalCyclicCornerPartner J e o≠o := by
  intro h
  have h':=congrArg (originalCyclicCornerIndex J e) h
  rw [originalCyclicCornerPartner_index] at h'
  exact originalCyclicPairIndex_ne_self J e _ h'

theorem originalCyclicOccurrence_not_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    ¬(originalCyclicPresentation J e).presentation.IsBoundaryEdge o.edge := by
  intro h
  have h2:=originalCyclicPresentation_closed J e o.edge
  change (originalCyclicPresentation J e).presentation.edgeMultiplicity o.edge=1 at h
  omega

theorem originalCyclicCornerPartner_dart {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    (originalCyclicCornerPartner J e o).dart=o.dart.flip := by
  obtain ⟨b,hb⟩:=(originalCyclicPresentation J e).valid.exists_pairing_source o
    (originalCyclicOccurrence_not_boundary J e o)
  have hd : b.target.dart=b.source.dart.flip := by
    simpa only [originalCyclicBoundaryPairing_direction J e b] using b.compatible
  have hidx:=congrArg (originalCyclicFinIndex J) (originalCyclicBoundaryPairing_target_index J e b)
  rw [originalCyclicFinPair_apply] at hidx
  have hp : b.target=originalCyclicCornerPartner J e o := by
    apply (originalCyclicCornerIndex J e).injective
    rw [originalCyclicCornerPartner_index]
    simpa only [originalCyclicCornerIndex,Equiv.trans_apply,hb] using hidx
  rw [hp,hb] at hd
  exact hd

theorem originalCyclicOccurrence_edge_eq_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o q : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    o.edge=q.edge ↔ q=o ∨ q=originalCyclicCornerPartner J e o := by
  have hedge : (originalCyclicCornerPartner J e o).edge=o.edge := by
    unfold FiniteCyclicPresentation.BoundaryOccurrence.edge
    rw [originalCyclicCornerPartner_dart]
    cases o.dart <;> rfl
  constructor
  · intro hoq
    by_cases hqo : q=o
    · exact Or.inl hqo
    obtain ⟨r,_hr,hunique⟩:=(originalCyclicPresentation J e).valid.exists_unique_partner o
      (originalCyclicOccurrence_not_boundary J e o)
    exact Or.inr ((hunique q ⟨Ne.symm hqo,hoq.symm⟩).trans
      (hunique (originalCyclicCornerPartner J e o)
        ⟨Ne.symm (originalCyclicCornerPartner_ne J e o),hedge⟩).symm)
  · rintro (rfl|rfl)
    · rfl
    · exact hedge.symm


theorem originalCyclicCornerPartner_involutive {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    originalCyclicCornerPartner J e (originalCyclicCornerPartner J e o)=o := by
  apply (originalCyclicCornerIndex J e).injective
  simp only [originalCyclicCornerPartner_index]
  exact originalCyclicPairIndex_involutive J e _

theorem originalCyclicCorner_vertex_paired_left {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J
      e).presentation o=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J
        e).presentation
        (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext (originalCyclicPresentation J e).presentation (originalCyclicCornerPartner J e o)) := by
  have hflip:=originalCyclicCornerPartner_dart J e o
  have hedge : o.edge=(originalCyclicCornerPartner J e o).edge:=
    (originalCyclicOccurrence_edge_eq_iff J e o _).mpr (Or.inr rfl)
  cases hd : o.dart with
  | pos a=>
    have hp : (originalCyclicCornerPartner J e o).dart=.neg a:=by
      simpa only [hd,SignedDart.flip] using hflip
    simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial,hd,hp] using
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_initial (originalCyclicPresentation J
        e).presentation o
        (originalCyclicCornerPartner J e o) hedge
  | neg a=>
    have hp : (originalCyclicCornerPartner J e o).dart=.pos a:=by
      simpa only [hd,SignedDart.flip] using hflip
    simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal,hd,hp] using
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass_terminal (originalCyclicPresentation J
        e).presentation o
        (originalCyclicCornerPartner J e o) hedge

theorem originalCyclicCorner_vertex_paired_right {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J
      e).presentation
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext (originalCyclicPresentation J
        e).presentation o)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J e).presentation (originalCyclicCornerPartner J e o) := by
  have h:=originalCyclicCorner_vertex_paired_left J e (originalCyclicCornerPartner J e o)
  rw [originalCyclicCornerPartner_involutive] at h
  exact h.symm

theorem originalRawCornerStep_vertex_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) {i j : ZMod J.n}
    (h : originalRawCornerStep J e i j) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J
      e).presentation ((originalCyclicCornerIndex J e).symm i)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J e).presentation ((originalCyclicCornerIndex J e).symm j) := by
  rcases h with ⟨k,h⟩
  rcases h with ⟨hi,hj⟩|⟨hi,hj⟩
  · rw [hi,hj,originalCyclicCornerIndex_symm_next]
    simpa only [originalCyclicCornerPartner,Equiv.apply_symm_apply] using
      originalCyclicCorner_vertex_paired_left J e ((originalCyclicCornerIndex J e).symm k)
  · rw [hi,hj,originalCyclicCornerIndex_symm_next]
    simpa only [originalCyclicCornerPartner,Equiv.apply_symm_apply] using
      originalCyclicCorner_vertex_paired_right J e ((originalCyclicCornerIndex J e).symm k)


theorem originalCornerIdentification_rawChain {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    {o q : (originalCyclicPresentation J e).presentation.BoundaryOccurrence}
    (h : _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.CornerIdentification (originalCyclicPresentation
      J e).presentation o q) :
    Relation.EqvGen (originalRawCornerStep J e)
      (originalCyclicCornerIndex J e o) (originalCyclicCornerIndex J e q) := by
  let C:=(originalCyclicPresentation J e).presentation
  have hLeft (o:C.BoundaryOccurrence) : Relation.EqvGen (originalRawCornerStep J e)
      (originalCyclicCornerIndex J e o)
      (originalCyclicCornerIndex J e (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext C (originalCyclicCornerPartner J e o))) := by
    rw [originalCyclicCornerIndex_next,originalCyclicCornerPartner_index]
    exact Relation.EqvGen.rel _ _ ⟨originalCyclicCornerIndex J e o,Or.inl ⟨rfl,rfl⟩⟩
  have hRight (o:C.BoundaryOccurrence) : Relation.EqvGen (originalRawCornerStep J e)
      (originalCyclicCornerIndex J e (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.cornerNext C o))
      (originalCyclicCornerIndex J e (originalCyclicCornerPartner J e o)) := by
    rw [originalCyclicCornerIndex_next,originalCyclicCornerPartner_index]
    exact Relation.EqvGen.rel _ _ ⟨originalCyclicCornerIndex J e o,Or.inr ⟨rfl,rfl⟩⟩
  cases h with
  | initial o q hedge=>
    rcases (originalCyclicOccurrence_edge_eq_iff J e o q).mp hedge with rfl|rfl
    · exact Relation.EqvGen.refl _
    · have hf:=originalCyclicCornerPartner_dart J e o
      cases hd:o.dart with
      | pos a=>
        have hp:(originalCyclicCornerPartner J e o).dart=.neg a:=by
          simpa only [hd,SignedDart.flip] using hf
        simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial,hd,hp] using hLeft o
      | neg a=>
        have hp:(originalCyclicCornerPartner J e o).dart=.pos a:=by
          simpa only [hd,SignedDart.flip] using hf
        simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceInitial,hd,hp] using hRight o
  | terminal o q hedge=>
    rcases (originalCyclicOccurrence_edge_eq_iff J e o q).mp hedge with rfl|rfl
    · exact Relation.EqvGen.refl _
    · have hf:=originalCyclicCornerPartner_dart J e o
      cases hd:o.dart with
      | pos a=>
        have hp:(originalCyclicCornerPartner J e o).dart=.neg a:=by
          simpa only [hd,SignedDart.flip] using hf
        simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal,hd,hp] using hRight o
      | neg a=>
        have hp:(originalCyclicCornerPartner J e o).dart=.pos a:=by
          simpa only [hd,SignedDart.flip] using hf
        simpa only [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.occurrenceTerminal,hd,hp] using hLeft o


theorem originalCornerChain_rawChain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD)
    {o q : (originalCyclicPresentation J e).presentation.BoundaryOccurrence}
    (h : Relation.EqvGen (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.CornerIdentification
      (originalCyclicPresentation J e).presentation) o q) :
    Relation.EqvGen (originalRawCornerStep J e)
      (originalCyclicCornerIndex J e o) (originalCyclicCornerIndex J e q) := by
  induction h with
  | rel o q h=>exact originalCornerIdentification_rawChain J e h
  | refl o=>exact Relation.EqvGen.refl _
  | symm o q h ih=>exact Relation.EqvGen.symm _ _ ih
  | trans o q r h1 h2 ih1 ih2=>exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem originalRawCornerChain_vertex_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) {i j : ZMod J.n}
    (h : Relation.EqvGen (originalRawCornerStep J e) i j) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J
      e).presentation ((originalCyclicCornerIndex J e).symm i)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J e).presentation ((originalCyclicCornerIndex J e).symm j) := by
  induction h with
  | rel i j h=>exact originalRawCornerStep_vertex_eq J e h
  | refl i=>rfl
  | symm i j h ih=>exact ih.symm
  | trans i j k h1 h2 ih1 ih2=>exact ih1.trans ih2

def originalRawCornerSetoid {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) : Setoid (ZMod J.n) :=
  Relation.EqvGen.setoid (originalRawCornerStep J e)

/-- The literal word's actual endpoint quotient is exactly the raw geometric side-pair endpoint quotient, rather than an arbitrary vertex labeling. -/
def originalCyclicVertexRawEquiv {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
      e).presentation≃Quotient (originalRawCornerSetoid J e) where
  toFun:=Quotient.lift (fun o=>Quotient.mk _ (originalCyclicCornerIndex J e o))
    (fun _ _ h=>Quotient.sound (originalCornerChain_rawChain J e h))
  invFun:=Quotient.lift (fun i=>_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass
    (originalCyclicPresentation J e).presentation
    ((originalCyclicCornerIndex J e).symm i)) (fun _ _ h=>originalRawCornerChain_vertex_eq J e h)
  left_inv v:=Quotient.inductionOn v fun o=>by
    change _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J
      e).presentation
      ((originalCyclicCornerIndex J e).symm (originalCyclicCornerIndex J e o))=
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.vertexClass (originalCyclicPresentation J
        e).presentation o
    rw [Equiv.symm_apply_apply]
  right_inv v:=Quotient.inductionOn v fun i=>by
    change Quotient.mk (originalRawCornerSetoid J e)
      (originalCyclicCornerIndex J e ((originalCyclicCornerIndex J e).symm i))=
      Quotient.mk (originalRawCornerSetoid J e) i
    rw [Equiv.apply_symm_apply]

theorem originalCyclicVertex_card_rawCorners {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
      e).presentation)=
      Nat.card (Quotient (originalRawCornerSetoid J e)) :=
  Nat.card_congr (originalCyclicVertexRawEquiv J e)

end LowDimensionalTopology.Geometry.Fuchsian
