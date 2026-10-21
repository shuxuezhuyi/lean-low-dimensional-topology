/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicSeparation
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonArea
/-!
# Refined polygon counts and area

Self-paired sides contribute one additional refined boundary occurrence. The
cyclic presentation has the corresponding edge and Euler counts, while its
geometric polygon has the original interior, area and Gauss–Bonnet formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
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

/-- Refinement adds exactly one extra occurrence for each genuine original self-paired side. -/
def originalRefinedSideSplitEquiv {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) :
    OriginalRefinedSide hD ≃ FuchsianPolygonSides P D ⊕
      {s : FuchsianPolygonSides P D // fuchsianPairedSide hD s=s} where
  toFun v := if h : v.val.2=false then .inl v.val.1 else
    .inr ⟨v.val.1,v.property (by cases hb : v.val.2 <;> simp_all)⟩
  invFun v := match v with
    | .inl s => ⟨(s,false),by simp⟩
    | .inr s => ⟨(s.val,true),by intro _;exact s.property⟩
  left_inv v := by
    apply Subtype.ext
    rcases v with ⟨⟨s,b⟩,hv⟩
    cases b <;> simp
  right_inv v := by
    cases v with
    | inl s => simp
    | inr s => simp

theorem originalRefinedSide_card {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) :
    Nat.card (OriginalRefinedSide hD)=Nat.card (FuchsianPolygonSides P D)+
      Nat.card {s : FuchsianPolygonSides P D // fuchsianPairedSide hD s=s} := by
  let : Finite (FuchsianPolygonSides P D) := finite_area_polygon_finite_sides hD ha
  rw [Nat.card_congr (originalRefinedSideSplitEquiv hD),Nat.card_sum]

theorem originalCyclicPresentation_faceCount {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    (originalCyclicPresentation J e).presentation.faces.length=1 := by
  exact ofOneFaceWord_faces_length _

theorem originalCyclicPresentation_edgeCount_twice {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    2*(originalCyclicPresentation J e).presentation.edgeCount=J.n := by
  let p:=originalCyclicFinPair J e
  let E:=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.InvolutionPositive p
  let d:Fin J.n≃SignedDart E:=_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionDartEquiv p
    (originalCyclicFinPair_involutive J e) (originalCyclicFinPair_ne_self J e)
  let s:SignedDart E≃E⊕E:=
    { toFun := fun x=>match x with | .pos a=>.inl a | .neg a=>.inr a
      invFun := fun x=>match x with | .inl a=>.pos a | .inr a=>.neg a
      left_inv := by intro x;cases x <;> rfl
      right_inv := by intro x;cases x <;> rfl }
  have h:=Fintype.card_congr (d.trans s)
  simp only [Fintype.card_fin,Fintype.card_sum] at h
  change 2*Fintype.card E=J.n
  omega

theorem originalCyclicPresentation_edgeCount {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    (originalCyclicPresentation J e).presentation.edgeCount=J.n/2 := by
  have h:=originalCyclicPresentation_edgeCount_twice J e
  omega

theorem originalCyclicPresentation_euler_count {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J
      e).presentation=
      (Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J e).presentation) : ℤ)-(J.n/2 : ℕ)+1 := by
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic,originalCyclicPresentation_faceCount,
    originalCyclicPresentation_edgeCount]
  norm_num

theorem originalCyclicPresentation_genus_count {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus
      ((originalCyclicPresentation J e).presentation.PolygonalRealization
        (originalCyclicPresentation J e).valid) g ∧
      (Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
        e).presentation) : ℤ)-(J.n/2 : ℕ)+1=
        2-2*(g : ℤ) := by
  obtain ⟨g,hg,hχ⟩:=originalCyclicPresentation_genus J e
  exact ⟨g,hg,(originalCyclicPresentation_euler_count J e).symm.trans hχ⟩


/-- The actual cyclic boundary count includes exactly the genuine self-side subdivisions. -/
theorem originalCyclic_sideCount {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    J.n=Nat.card (FuchsianPolygonSides P D)+
      Nat.card {s : FuchsianPolygonSides P D // fuchsianPairedSide hD s=s} := by
  have hc:=Nat.card_congr ((originalCyclicFinIndex J).trans e)
  rw [Nat.card_fin] at hc
  exact hc.trans (originalRefinedSide_card hD ha)

/-- Pairing the two true occurrences yields the original edge count with self-pairing corrected by the actual subdivision. -/
theorem originalCyclicPresentation_original_edgeCount {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    2*(originalCyclicPresentation J e).presentation.edgeCount=
      Nat.card (FuchsianPolygonSides P D)+
      Nat.card {s : FuchsianPolygonSides P D // fuchsianPairedSide hD s=s} :=
  (originalCyclicPresentation_edgeCount_twice J e).trans (originalCyclic_sideCount hD ha J e)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

local instance originalCyclicAreaSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance originalCyclicAreaSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩



def originalCyclicNativeVertices {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD) :
    Fin J.n→𝕔𝔻 := fun i=>originalCyclicVertex hD J hvertices (originalCyclicFinIndex J i)

theorem originalCyclicNativeVertices_edge_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i : Fin J.n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (originalCyclicNativeVertices hD J hvertices) i=
      J.edgeSegment (originalCyclicFinIndex J i) := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge,original_discPolygonKleinPlane_image_segment]
  simp only [originalCyclicNativeVertices,originalCyclicFinIndex_rotate,
    originalCyclicVertex_plane,PolygonalCircle.edgeSegment]

theorem originalCyclicNativeVertices_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonBoundary (originalCyclicNativeVertices hD J hvertices)=
      ⋃s : FuchsianPolygonSides P D,fuchsianSideClosedModel s := by
  have hseg (i : Fin J.n) :
      _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (originalCyclicNativeVertices hD J hvertices) i=
        (e (originalCyclicFinIndex J i)).carrier := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge,originalCyclicNativeVertices,originalCyclicFinIndex_rotate] using
      originalCyclicVertex_side_segment hD J hvertices e hspec (originalCyclicFinIndex J i)
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonBoundary]
  simp_rw [hseg]
  rw [show (⋃i : Fin J.n,(e (originalCyclicFinIndex J i)).carrier)=
      ⋃v : OriginalRefinedSide hD,v.carrier from ?_]
  · exact originalRefinedSide_iUnion_carrier hD
  · ext p
    constructor
    · intro hp
      obtain ⟨i,hi⟩:=mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨e (originalCyclicFinIndex J i),hi⟩
    · intro hp
      obtain ⟨v,hv⟩:=mem_iUnion.mp hp
      obtain ⟨i,rfl⟩:=((originalCyclicFinIndex J).trans e).surjective v
      exact mem_iUnion.mpr ⟨i,hv⟩

def originalCyclicDiscPolygon {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon J.n where
  three_le:=J.three_le
  vertices:=originalCyclicNativeVertices hD J hvertices
  vertices_injective:=(originalCyclicVertex_injective hD J hvertices).comp
    (originalCyclicFinIndex J).injective
  simple_edges:=by
    intro i j hij p hp
    have hi : _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane p∈J.edgeSegment (originalCyclicFinIndex J i) := by
      rw [←originalCyclicNativeVertices_edge_image hD J hvertices i]
      exact mem_image_of_mem _ hp.1
    have hj : _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane p∈J.edgeSegment (originalCyclicFinIndex J j) := by
      rw [←originalCyclicNativeVertices_edge_image hD J hvertices j]
      exact mem_image_of_mem _ hp.2
    have hne:originalCyclicFinIndex J i≠originalCyclicFinIndex J j:=
      (originalCyclicFinIndex J).injective.ne hij
    constructor
    · rcases J.edgeSegment_inter_subset_endpoints hne ⟨hi,hj⟩ with h|h
      · left
        apply _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective
        exact h.trans (originalCyclicVertex_plane hD J hvertices _).symm
      · right
        apply _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective
        rw [originalCyclicNativeVertices,originalCyclicFinIndex_rotate,originalCyclicVertex_plane]
        exact h
    · rcases J.edgeSegment_inter_subset_endpoints hne.symm ⟨hj,hi⟩ with h|h
      · left
        apply _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective
        exact h.trans (originalCyclicVertex_plane hD J hvertices _).symm
      · right
        apply _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane_injective
        rw [originalCyclicNativeVertices,originalCyclicFinIndex_rotate,originalCyclicVertex_plane]
        exact h
  jordanBoundary:=by
    obtain ⟨n,Q,_hI,hB⟩:=finite_area_original_boundary_jordan_model hD ha
    have hb : _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonBoundary (originalCyclicNativeVertices hD J
      hvertices)=Q.boundary:=
      (originalCyclicNativeVertices_boundary hD J hvertices e hspec).trans hB.symm
    obtain ⟨f⟩:=Q.jordanBoundary
    exact ⟨(Homeomorph.setCongr hb).trans f⟩

theorem originalCyclicDiscPolygon_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    (originalCyclicDiscPolygon hD ha J hvertices e hspec).boundary=
      ⋃s : FuchsianPolygonSides P D,fuchsianSideClosedModel s :=
  originalCyclicNativeVertices_boundary hD J hvertices e hspec

theorem originalCyclicDiscPolygon_interior {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    (originalCyclicDiscPolygon hD ha J hvertices e hspec).interior=P.finiteCoordinate '' D := by
  obtain ⟨n,Q,hI,hB⟩:=finite_area_original_boundary_jordan_model hD ha
  have hb : (originalCyclicDiscPolygon hD ha J hvertices e hspec).boundary=Q.boundary:=
    (originalCyclicDiscPolygon_boundary hD ha J hvertices e hspec).trans hB.symm
  rw [←hI]
  unfold _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.complexInterior _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.complexOutside
  unfold _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.complexBoundary
  rw [hb]

theorem originalCyclicDiscPolygon_area {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    (originalCyclicDiscPolygon hD ha J hvertices e hspec).area=P.area D := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.area,originalCyclicDiscPolygon_interior,P.area_apply D
    hD.locallyFinite.fundamental.isOpen.measurableSet]

theorem originalCyclicDiscPolygon_gaussBonnet {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    (P.area D).toReal=((J.n : ℝ)-2)*Real.pi-
      ∑i : Fin J.n,(originalCyclicDiscPolygon hD ha J hvertices e hspec).angle i := by
  rw [←originalCyclicDiscPolygon_area hD ha J hvertices e hspec]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.area_toReal_eq_original_angle_defect _

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise

theorem originalCyclicDiscPolygon_area_euler {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    (P.area D).toReal=2*Real.pi*((Nat.card
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
        e).presentation) : ℝ)-
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J
        e).presentation : ℝ))-
      ∑i : Fin J.n,(originalCyclicDiscPolygon hD ha J hvertices e hspec).angle i := by
  have hG:=originalCyclicDiscPolygon_gaussBonnet hD ha J hvertices e hspec
  have hE : 2*((originalCyclicPresentation J e).presentation.edgeCount : ℝ)=J.n := by
    exact_mod_cast originalCyclicPresentation_edgeCount_twice J e
  have hχZ : _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation=
      (Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
        e).presentation) : ℤ)-
      (originalCyclicPresentation J e).presentation.edgeCount+1 := by
    rw [_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic,originalCyclicPresentation_faceCount]
    norm_num
  have hχ : (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic
    (originalCyclicPresentation J e).presentation : ℝ)=
      (Nat.card (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
        e).presentation) : ℝ)-
      (originalCyclicPresentation J e).presentation.edgeCount+1 := by exact_mod_cast hχZ
  linear_combination hG+2*Real.pi*hχ-Real.pi*hE

/-- The original polygon supplies its own actual refined cyclic model, density area and word genus. The latter is not yet identified here with the original orbit completion. -/
theorem finite_area_original_refined_area_euler {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) :
    ∃J : PolygonalCircle,∃e : ZMod J.n≃OriginalRefinedSide hD,
    ∃hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD,
    ∃hspec : ∀i,J.edgeSegment i=(e i).planeCarrier,
      (originalCyclicDiscPolygon hD ha J hvertices e hspec).interior=P.finiteCoordinate '' D ∧
      (originalCyclicDiscPolygon hD ha J hvertices e hspec).area=P.area D ∧
      2*(originalCyclicPresentation J e).presentation.edgeCount=
        Nat.card (FuchsianPolygonSides P D)+
        Nat.card {s : FuchsianPolygonSides P D // fuchsianPairedSide hD s=s} ∧
      ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus
        ((originalCyclicPresentation J e).presentation.PolygonalRealization
          (originalCyclicPresentation J e).valid) g ∧
        (P.area D).toReal=2*Real.pi*((Nat.card
          (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
            e).presentation) : ℝ)-2+2*(g : ℝ))-
          ∑i : Fin J.n,(originalCyclicDiscPolygon hD ha J hvertices e hspec).angle i := by
  obtain ⟨J,e,_hcarrier,hvertices,hspec⟩:=finite_area_original_cyclic_side_model hD ha
  obtain ⟨g,hg,hχZ⟩:=originalCyclicPresentation_genus J e
  refine ⟨J,e,hvertices,hspec,originalCyclicDiscPolygon_interior hD ha J hvertices e hspec,
    originalCyclicDiscPolygon_area hD ha J hvertices e hspec,
    originalCyclicPresentation_original_edgeCount hD ha J e,g,hg,?_⟩
  have hχ : (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic
    (originalCyclicPresentation J e).presentation : ℝ)=2-2*(g : ℝ) :=
    by exact_mod_cast hχZ
  rw [originalCyclicDiscPolygon_area_euler hD ha J hvertices e hspec,hχ]
  ring
end LowDimensionalTopology.Geometry.Fuchsian
