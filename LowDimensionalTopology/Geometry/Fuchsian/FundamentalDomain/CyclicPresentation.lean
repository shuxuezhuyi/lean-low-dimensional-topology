/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicOrderedVertices
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicInvolutionWord
public import LowDimensionalTopology.Geometry.Polygon.Topology.Word.FiniteCyclicEulerGenus
/-!
# Cyclic presentations from refined polygon sides

The refined side involution gives the signed boundary word in its cyclic
occurrence order. The resulting one-face presentation is closed, coherently
orientable and connected, so its polygonal realization has a genus.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
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
open Set
open scoped Complex.UnitDisc

/-- The actual finite list index for the genuine cyclic Jordan boundary. -/
def originalCyclicFinIndex (J:PolygonalCircle) : Fin J.n≃ZMod J.n := by
  let :NeZero J.n:=⟨by have h:=J.three_le;omega⟩
  exact (ZMod.finEquiv J.n).toEquiv

/-- Cyclic successor agrees with addition by one in the original boundary index. -/
theorem originalCyclicFinIndex_rotate (J : PolygonalCircle) (i : Fin J.n) :
    originalCyclicFinIndex J (finRotate J.n i)=originalCyclicFinIndex J i+1 := by
  let : NeZero J.n:=⟨by have h:=J.three_le;omega⟩
  change (ZMod.finEquiv J.n) (finRotate J.n i)=(ZMod.finEquiv J.n) i+1
  simp only [finRotate_apply,map_add,map_one]

/-- Original geometric refined side pairing in the literal finite boundary order. -/
def originalCyclicFinPair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) : Fin J.n:=
  (originalCyclicFinIndex J).symm (originalCyclicPairIndex J e (originalCyclicFinIndex J i))

theorem originalCyclicFinPair_apply {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) :
    originalCyclicFinIndex J (originalCyclicFinPair J e i)=
      originalCyclicPairIndex J e (originalCyclicFinIndex J i):=(originalCyclicFinIndex J).apply_symm_apply _

theorem originalCyclicFinPair_involutive {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : Function.Involutive (originalCyclicFinPair J e) := by
  intro i
  apply (originalCyclicFinIndex J).injective
  rw [originalCyclicFinPair_apply,originalCyclicFinPair_apply]
  exact originalCyclicPairIndex_involutive J e (originalCyclicFinIndex J i)

theorem originalCyclicFinPair_ne_self {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) : originalCyclicFinPair J e i≠i := by
  intro he
  have hi:=congrArg (originalCyclicFinIndex J) he
  rw [originalCyclicFinPair_apply] at hi
  exact originalCyclicPairIndex_ne_self J e (originalCyclicFinIndex J i) hi

/-- The literal original-order word of the actual refined side pairing. A sign encodes its representative within the genuine original pair. -/
def originalCyclicWord {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : List (SignedDart
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.InvolutionPositive (originalCyclicFinPair J e))):=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionWord (originalCyclicFinPair J
    e) (originalCyclicFinPair_involutive J e)
    (originalCyclicFinPair_ne_self J e)

/-- Every genuine original boundary occurrence has exactly its corresponding signed dart. -/
def originalCyclicDart {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin
      J.n) : SignedDart (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.InvolutionPositive
      (originalCyclicFinPair J e)):=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionDartEquiv (originalCyclicFinPair J
    e) (originalCyclicFinPair_involutive J e)
    (originalCyclicFinPair_ne_self J e) i

theorem originalCyclicDart_pair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (i:Fin J.n) :
    originalCyclicDart J e (originalCyclicFinPair J e i)=(originalCyclicDart J e i).flip :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionDartEquiv_pair (originalCyclicFinPair J
    e) (originalCyclicFinPair_involutive J e)
    (originalCyclicFinPair_ne_self J e) i

/-- The stored word retains exactly the original cyclic occurrence order. -/
theorem originalCyclicWord_eq_ofFn {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : originalCyclicWord J e=List.ofFn (originalCyclicDart J e) := rfl

/-- A genuine ordinary-valid finite cyclic presentation constructed from the actual original side involution. -/
def originalCyclicPresentation {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : ValidPresentation:=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionPresentation (originalCyclicFinPair J
    e) (originalCyclicFinPair_involutive J e)
    (originalCyclicFinPair_ne_self J e) (by have h:=J.three_le;omega)

theorem originalCyclicPresentation_closed {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide
      hD) : _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.IsClosed (originalCyclicPresentation J
      e).presentation :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionWord_closed (originalCyclicFinPair J
    e) (originalCyclicFinPair_involutive J e)
    (originalCyclicFinPair_ne_self J e)

theorem originalCyclicPresentation_coherent {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.IsCoherentlyOrientable (originalCyclicPresentation J e).presentation :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionWord_coherent (originalCyclicFinPair J
    e) (originalCyclicFinPair_involutive J e)
    (originalCyclicFinPair_ne_self J e)

/-- Its face-edge incidence is genuinely connected because there is precisely one original face. -/
theorem originalCyclicPresentation_connected {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : (originalCyclicPresentation J e).presentation.IsConnected := by
  refine ⟨⟨0,by simp [originalCyclicPresentation,_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionPresentation,ofOneFaceWord]⟩,?_⟩
  intro f g
  have hlen:(originalCyclicPresentation J e).presentation.faces.length=1:=rfl
  have he:f=g:=by
    apply Fin.ext
    have hf:f.val<1:=f.isLt.trans_le hlen.le
    have hg:g.val<1:=g.isLt.trans_le hlen.le
    omega
  subst g
  exact Relation.ReflTransGen.refl

/-- The actual faithful polygonal realization of the original finite-order pairing word has genuine topological genus and the literal endpoint-quotient Euler characteristic. This statement does not identify that word realization with the original cusp completion. -/
theorem originalCyclicPresentation_genus {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) :
    ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus ((originalCyclicPresentation J
      e).presentation.PolygonalRealization
        (originalCyclicPresentation J e).valid) g ∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J
        e).presentation=2-2*(g:ℤ) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.closed_coherent_connected_genus (originalCyclicPresentation J e)
    (originalCyclicPresentation_connected J e) (originalCyclicPresentation_closed J e)
    (originalCyclicPresentation_coherent J e)

/-- A genuine finite-area original fundamental polygon supplies its actual unchanged refined sides in cyclic order, and the associated faithful word realization has genus and its true Euler characteristic. No equivalence with the original orbit completion or area formula is asserted here. -/
theorem finite_area_original_cyclic_word_genus {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (ha:P.area D≠⊤) : ∃J:PolygonalCircle,∃e:ZMod J.n≃OriginalRefinedSide hD,
      J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
        hD,v.carrier) ∧
      (∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
        originalRefinedEndpointSet hD) ∧
      (∀i,J.edgeSegment i=(e i).planeCarrier) ∧
      ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus ((originalCyclicPresentation J
        e).presentation.PolygonalRealization
        (originalCyclicPresentation J e).valid) g ∧
        _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation=2-2*(g:ℤ) := by
  obtain ⟨J,e,hcarrier,hvertices,hspec⟩:=finite_area_original_cyclic_side_model hD ha
  exact ⟨J,e,hcarrier,hvertices,hspec,originalCyclicPresentation_genus J e⟩
end LowDimensionalTopology.Geometry.Fuchsian
