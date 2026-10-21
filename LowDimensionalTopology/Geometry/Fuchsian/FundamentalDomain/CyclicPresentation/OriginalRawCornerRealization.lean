/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicRawVertices
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicPreGeometry
public import LowDimensionalTopology.Geometry.Polygon.Topology.PolygonCellSideCollision
/-!
# Realizing raw corners faithfully

Raw corner labels, with noncorners left unmarked, are invariant under every
stored face gluing. They descend to the word realization and give a left
inverse to the natural corner map, proving its exact endpoint-relation kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Topology
open scoped Complex.UnitDisc Classical
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
section RawWordCorners
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} {hD : IsConvexFuchsianPolygon P D}
    (J : PolygonalCircle) (e : ZMod J.n≃OriginalRefinedSide hD)

/-- A genuine corner in the actual single face has its actual raw endpoint class; every other face point is left unmarked. -/
def originalCyclicRawCornerPreLabel (z : PolygonCell J.n) :
    Option (Quotient (originalRawCornerSetoid J e)) :=
  if hz : ∃i : Fin J.n,PolygonCell.side i 0=z then
    some (Quotient.mk _ (originalCyclicFinIndex J (Classical.choose hz)))
  else none

theorem originalCyclicRawCornerPreLabel_zero (i : Fin J.n) :
    originalCyclicRawCornerPreLabel J e (PolygonCell.side i 0)=
      some (Quotient.mk _ (originalCyclicFinIndex J i)) := by
  have hz : ∃j : Fin J.n,PolygonCell.side j 0=PolygonCell.side i 0:=⟨i,rfl⟩
  rw [originalCyclicRawCornerPreLabel,dite_eq_left hz]
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.PolygonCellCollision.side_zero_injective (Classical.choose_spec
    hz)]

theorem originalCyclicRawCornerPreLabel_side (i : Fin J.n) (t : unitInterval) :
    originalCyclicRawCornerPreLabel J e (PolygonCell.side i t)=
      if t=0 then some (Quotient.mk _ (originalCyclicFinIndex J i))
      else if t=1 then some (Quotient.mk _ (originalCyclicFinIndex J i+1)) else none := by
  by_cases h0 : t=0
  · rw [h0,ite_eq_left rfl,originalCyclicRawCornerPreLabel_zero]
  rw [ite_eq_right h0]
  by_cases h1 : t=1
  · rw [h1,ite_eq_left rfl,PolygonCell.side_one_eq_rotate_zero,originalCyclicRawCornerPreLabel_zero,
      originalCyclicFinIndex_rotate]
  rw [ite_eq_right h1,originalCyclicRawCornerPreLabel,dite_eq_right]
  rintro ⟨j,hj⟩
  rcases (_root_.LowDimensionalTopology.Geometry.Surfaces.PolygonCellCollision.side_eq_iff i j t
    0).mp hj.symm with h|h|h
  · exact h0 h.2
  · exact h1 h.1
  · exact h0 h.1

/-- The true original compatible gluing preserves the literal raw corner label and never turns a noncorner point into a corner. -/
theorem originalCyclicRawCornerPreLabel_pairing
    (pairing : (originalCyclicPresentation J e).presentation.BoundaryPairing) (t : unitInterval) :
    originalCyclicRawCornerPreLabel J e (originalCyclicPreFaceHomeomorph J e
      (pairing.identification.source.point t))=
    originalCyclicRawCornerPreLabel J e (originalCyclicPreFaceHomeomorph J e
      (pairing.identification.target.point (pairing.identification.parameter t))) := by
  have hd : pairing.direction=PolygonGluing.ParameterDirection.opposite:=
    originalCyclicBoundaryPairing_direction J e pairing
  have hpar : pairing.identification.parameter t=unitInterval.symm t:=by
    change pairing.direction.homeomorph t=unitInterval.symm t
    rw [hd]
    rfl
  rw [hpar]
  change originalCyclicRawCornerPreLabel J e (originalCyclicPreFaceHomeomorph J e
    (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.source).point t))=
    originalCyclicRawCornerPreLabel J e (originalCyclicPreFaceHomeomorph J e
      (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.target).point (unitInterval.symm t)))
  rw [originalCyclicPreFaceHomeomorph_side,originalCyclicPreFaceHomeomorph_side,
    originalCyclicRawCornerPreLabel_side,originalCyclicRawCornerPreLabel_side,
    originalCyclicBoundaryPairing_target_index,originalCyclicFinPair_apply]
  have h10 : (unitInterval.symm t=1)↔t=0:=by
    constructor <;> intro h
    · exact unitInterval.symm_involutive.injective (h.trans unitInterval.symm_zero.symm)
    · simpa only [h] using unitInterval.symm_zero
  have h01 : (unitInterval.symm t=0)↔t=1:=by
    constructor <;> intro h
    · exact unitInterval.symm_involutive.injective (h.trans unitInterval.symm_one.symm)
    · simpa only [h] using unitInterval.symm_one
  by_cases h0 : t=0
  · rw [ite_eq_left h0,ite_eq_right (by intro h;exact zero_ne_one (h0.symm.trans (h01.mp h))),ite_eq_left (h10.mpr h0)]
    congr 1
    exact Quotient.sound (Relation.EqvGen.rel _ _
      ⟨originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e pairing.source),Or.inl ⟨rfl,rfl⟩⟩)
  by_cases h1 : t=1
  · rw [ite_eq_right h0,ite_eq_left h1,ite_eq_left (h01.mpr h1)]
    congr 1
    exact Quotient.sound (Relation.EqvGen.rel _ _
      ⟨originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e pairing.source),Or.inr ⟨rfl,rfl⟩⟩)
  rw [ite_eq_right h0,ite_eq_right h1,ite_eq_right (fun h=>h1 (h01.mp h)),ite_eq_right (fun h=>h0 (h10.mp h))]

/-- The actual raw endpoint label descends through every genuine stored face gluing. -/
def originalCyclicRawCornerWordLabel :
    (originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid → Option (Quotient (originalRawCornerSetoid J e)) :=
  Quotient.lift (fun x=>originalCyclicRawCornerPreLabel J e (originalCyclicPreFaceHomeomorph J e x)) (by
    intro a b h
    change Relation.EqvGen (PolygonGluing.Generator
      ((originalCyclicPresentation J e).presentation.polygonalIdentifications
        (originalCyclicPresentation J e).valid)) a b at h
    induction h with
    | rel a b h=>
      cases h with
      | glue identification hi t=>
        obtain ⟨pairing,rfl⟩:=hi
        exact originalCyclicRawCornerPreLabel_pairing J e pairing t
    | refl a=>rfl
    | symm a b _ ih=>exact ih.symm
    | trans a b c _ _ ih1 ih2=>exact ih1.trans ih2)

/-- The actual image in the faithful word realization of the stored corner with the given original raw index. -/
def originalCyclicRawCornerIndexPoint (i : ZMod J.n) :
    (originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid :=
  (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
    (((originalCyclicPresentation J e).presentation.occurrenceSide
      ((originalCyclicCornerIndex J e).symm i)).point 0)

theorem originalCyclicRawCornerIndexPoint_occurrence
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    originalCyclicRawCornerIndexPoint J e (originalCyclicCornerIndex J e o)=
      (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
        (((originalCyclicPresentation J e).presentation.occurrenceSide o).point 0) := by
  rw [originalCyclicRawCornerIndexPoint,Equiv.symm_apply_apply]

theorem originalCyclicRawCornerIndexPoint_next
    (o : (originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
        (((originalCyclicPresentation J e).presentation.occurrenceSide o).point 1)=
      originalCyclicRawCornerIndexPoint J e (originalCyclicCornerIndex J e o+1) := by
  rw [←originalCyclicCornerIndex_next,originalCyclicRawCornerIndexPoint_occurrence]
  apply congrArg ((originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid)
  rcases o with ⟨f,i⟩
  exact congrArg (fun z : PolygonCell ((originalCyclicPresentation J e).presentation.boundary f).length=>
    (⟨f,z⟩ : (originalCyclicPresentation J e).presentation.PolygonalPreRealization))
      (PolygonCell.side_one_eq_rotate_zero i)

theorem originalCyclicRawCornerWordLabel_indexPoint (i : ZMod J.n) :
    originalCyclicRawCornerWordLabel J e (originalCyclicRawCornerIndexPoint J e i)=
      some (Quotient.mk (originalRawCornerSetoid J e) i) := by
  change originalCyclicRawCornerPreLabel J e (originalCyclicPreFaceHomeomorph J e
    (((originalCyclicPresentation J e).presentation.occurrenceSide
      ((originalCyclicCornerIndex J e).symm i)).point 0))=_
  rw [originalCyclicPreFaceHomeomorph_side,originalCyclicRawCornerPreLabel_zero]
  congr 1
  congr 1
  exact (originalCyclicCornerIndex J e).apply_symm_apply i

/-- Genuine stored pairings identify the actual raw endpoint generators in the faithful quotient. -/
theorem originalCyclicRawCornerIndexPoint_pairing
    (pairing : (originalCyclicPresentation J e).presentation.BoundaryPairing) :
    originalCyclicRawCornerIndexPoint J e (originalCyclicCornerIndex J e pairing.source)=
      originalCyclicRawCornerIndexPoint J e (originalCyclicCornerIndex J e pairing.target+1) ∧
    originalCyclicRawCornerIndexPoint J e (originalCyclicCornerIndex J e pairing.source+1)=
      originalCyclicRawCornerIndexPoint J e (originalCyclicCornerIndex J e pairing.target) := by
  have hd : pairing.direction=PolygonGluing.ParameterDirection.opposite:=
    originalCyclicBoundaryPairing_direction J e pairing
  have hp (t : unitInterval) : pairing.identification.parameter t=unitInterval.symm t:=by
    change pairing.direction.homeomorph t=unitInterval.symm t
    rw [hd]
    rfl
  constructor
  · have h:=polygonalMk_pairing_eq (originalCyclicPresentation J e).valid pairing 0
    rw [hp,unitInterval.symm_zero] at h
    change (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
      (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.source).point 0)=
      (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
      (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.target).point 1) at h
    rwa [←originalCyclicRawCornerIndexPoint_occurrence,originalCyclicRawCornerIndexPoint_next] at h
  · have h:=polygonalMk_pairing_eq (originalCyclicPresentation J e).valid pairing 1
    rw [hp,unitInterval.symm_one] at h
    change (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
      (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.source).point 1)=
      (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
      (((originalCyclicPresentation J e).presentation.occurrenceSide pairing.target).point 0) at h
    rwa [originalCyclicRawCornerIndexPoint_next,←originalCyclicRawCornerIndexPoint_occurrence] at h

theorem originalCyclicRawCornerIndexPoint_rel {i j : ZMod J.n}
    (hij : originalRawCornerStep J e i j) :
    originalCyclicRawCornerIndexPoint J e i=originalCyclicRawCornerIndexPoint J e j := by
  obtain ⟨k,h⟩:=hij
  let o:=(originalCyclicCornerIndex J e).symm k
  obtain ⟨pairing,hsource⟩:=(originalCyclicPresentation J e).valid.exists_pairing_source o
    (originalCyclicOccurrence_not_boundary J e o)
  have hsrc : originalCyclicCornerIndex J e pairing.source=k:=by
    rw [hsource]
    exact (originalCyclicCornerIndex J e).apply_symm_apply k
  have htgt : originalCyclicCornerIndex J e pairing.target=originalCyclicPairIndex J e k:=by
    change originalCyclicFinIndex J (originalCyclicOccurrenceIndex J e pairing.target)=_
    rw [originalCyclicBoundaryPairing_target_index,originalCyclicFinPair_apply]
    change originalCyclicPairIndex J e (originalCyclicCornerIndex J e pairing.source)=_
    rw [hsrc]
  have hp:=originalCyclicRawCornerIndexPoint_pairing J e pairing
  rw [hsrc,htgt] at hp
  rcases h with h|h
  · exact h.1.symm ▸ h.2.symm ▸ hp.1
  · exact h.1.symm ▸ h.2.symm ▸ hp.2

theorem originalCyclicRawCornerIndexPoint_chain {i j : ZMod J.n}
    (hij : Relation.EqvGen (originalRawCornerStep J e) i j) :
    originalCyclicRawCornerIndexPoint J e i=originalCyclicRawCornerIndexPoint J e j := by
  induction hij with
  | rel i j h=>exact originalCyclicRawCornerIndexPoint_rel J e h
  | refl i=>rfl
  | symm i j _ ih=>exact ih.symm
  | trans i j k _ _ ih1 ih2=>exact ih1.trans ih2

/-- The actual natural corner map from the literal raw endpoint quotient into the unchanged faithful original word surface. -/
def originalCyclicRawCornerPoint : Quotient (originalRawCornerSetoid J e) →
    (originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid :=
  Quotient.lift (originalCyclicRawCornerIndexPoint J e)
    (fun _ _ h=>originalCyclicRawCornerIndexPoint_chain J e h)

theorem originalCyclicRawCornerPoint_mk (i : ZMod J.n) :
    originalCyclicRawCornerPoint J e (Quotient.mk (originalRawCornerSetoid J e) i)=
      (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
        (((originalCyclicPresentation J e).presentation.occurrenceSide
          ((originalCyclicCornerIndex J e).symm i)).point 0) := rfl

/-- The genuine gluing-invariant corner label is a left inverse of the natural actual corner map. -/
theorem originalCyclicRawCornerPoint_label (q : Quotient (originalRawCornerSetoid J e)) :
    originalCyclicRawCornerWordLabel J e (originalCyclicRawCornerPoint J e q)=some q := by
  induction q using Quotient.inductionOn with
  | h i=>exact originalCyclicRawCornerWordLabel_indexPoint J e i

/-- Faithful realization glues no additional corner classes beyond the actual original endpoint relation. -/
theorem originalCyclicRawCornerPoint_injective : Function.Injective (originalCyclicRawCornerPoint J e) := by
  intro q r h
  have hh:=congrArg (originalCyclicRawCornerWordLabel J e) h
  rw [originalCyclicRawCornerPoint_label,originalCyclicRawCornerPoint_label] at hh
  exact Option.some.inj hh

/-- The actual faithful corner-image kernel is exactly the literal original raw endpoint chain. -/
theorem originalCyclicRawCornerIndexPoint_eq_iff (i j : ZMod J.n) :
    originalCyclicRawCornerIndexPoint J e i=originalCyclicRawCornerIndexPoint J e j ↔
      Relation.EqvGen (originalRawCornerStep J e) i j := by
  constructor
  · intro h
    exact Quotient.exact (originalCyclicRawCornerPoint_injective J e h)
  · exact originalCyclicRawCornerIndexPoint_chain J e

end RawWordCorners
end LowDimensionalTopology.Geometry.Fuchsian
