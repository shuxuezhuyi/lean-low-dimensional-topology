module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.BoundaryPresentation
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.AxisOrbitCurves
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalCollarModels
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.DiscreteSubset
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.DiscPolygonConjugation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawEllipticClasses
public import Mathlib.Analysis.Convex.Combination
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSupportingHalfPlanes
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.Homeomorph.Defs
/-!
# Boundary cycles and area of a Nielsen core

The capped boundary presentation relates vertex and edge cycles to the
elliptic, parabolic and boundary-hyperbolic conjugacy classes of a Fuchsian
group. This module identifies those classes and derives the corresponding
Euler-characteristic and hyperbolic-area formulas.

The boundary-geodesic arguments also identify the compact projected boundary
cycles with complete boundary-line projections. Separate sections retain the
local measurable structures used by the finite-chain and boundary arguments.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace Pointwise


namespace LowDimensionalTopology.Geometry.Fuchsian

section NielsenCyclicCensusArea

section NielsenRawBoundaryEnds
open LeanEval.Topology.ClassificationOfSurfaces
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "σ" => nielsenCyclicCornerEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv

private theorem nielsenRawBoundary_exists_next (i:ZMod J.n) (hi:pairIndex i≠i) :
    (∃n:ℕ,pairIndex ((σ^n) i)=(σ^n) i) ↔
      ∃n:ℕ,pairIndex ((σ^n) (σ i))=(σ^n) (σ i) := by
  constructor
  · rintro ⟨_ | n,hn⟩
    · exact False.elim (hi (by simpa only [pow_zero,Equiv.Perm.one_apply] using hn))
    · exact ⟨n,by simpa only [pow_succ,Equiv.Perm.mul_apply] using hn⟩
  · rintro ⟨n,hn⟩
    exact ⟨n+1,by simpa only [pow_succ,Equiv.Perm.mul_apply] using hn⟩

/-- Follow only genuine old corner identifications until a boundary vertex is reached, if one exists. -/
def nielsenRawBoundaryTarget (i:ZMod J.n) : Option B := by
  classical
  exact if h:∃n:ℕ,pairIndex ((σ^n) i)=(σ^n) i then
    some ⟨(σ^(Nat.find h)) i,Nat.find_spec h⟩ else none
local notation "target" => nielsenRawBoundaryTarget hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenRawBoundaryTarget_boundary (b:B) : target b.val=some b := by
  classical
  have hex:∃n:ℕ,pairIndex ((σ^n) b.val)=(σ^n) b.val:=⟨0,by simpa only [pow_zero,Equiv.Perm.one_apply] using b.property⟩
  have h0:Nat.find hex=0:=Nat.le_zero.mp (Nat.find_min' hex (by simpa only [pow_zero,Equiv.Perm.one_apply] using b.property))
  unfold nielsenRawBoundaryTarget
  rw [dite_eq_left hex]
  apply congrArg some
  apply Subtype.ext
  change (σ^(Nat.find hex)) b.val=b.val
  rw [h0,pow_zero,Equiv.Perm.one_apply]

theorem nielsenRawBoundaryTarget_step {i j:ZMod J.n} (hij:step i j) : target i=target j := by
  classical
  obtain ⟨hi,rfl⟩:=hij
  have he:=nielsenRawBoundary_exists_next hD hNE hFG hfin w hwD hwN J hc hv i hi
  by_cases h0:∃n:ℕ,pairIndex ((σ^n) i)=(σ^n) i
  · have h1:=he.mp h0
    have hpos:0<Nat.find h0:=by
      by_contra hn
      have hz:Nat.find h0=0:=Nat.eq_zero_of_not_pos hn
      have hh:=Nat.find_spec h0
      rw [hz,pow_zero,Equiv.Perm.one_apply] at hh
      exact hi hh
    have hle:Nat.find h0≤Nat.find h1+1:=Nat.find_min' h0 (by
      simpa only [pow_succ,Equiv.Perm.mul_apply] using Nat.find_spec h1)
    have hs:Nat.find h0-1+1=Nat.find h0:=by omega
    have hle':Nat.find h1≤Nat.find h0-1:=Nat.find_min' h1 (by
      have hh:=Nat.find_spec h0
      rw [←hs,pow_succ,Equiv.Perm.mul_apply] at hh
      exact hh)
    have ht:Nat.find h0=Nat.find h1+1:=by omega
    unfold nielsenRawBoundaryTarget
    rw [dite_eq_left h0,dite_eq_left h1]
    apply congrArg some
    apply Subtype.ext
    change (σ^(Nat.find h0)) i=(σ^(Nat.find h1)) (σ i)
    rw [ht,pow_succ,Equiv.Perm.mul_apply]
  · have h1:¬∃n:ℕ,pairIndex ((σ^n) (σ i))=(σ^n) (σ i):=fun h=>h0 (he.mpr h)
    unfold nielsenRawBoundaryTarget
    rw [dite_eq_right h0,dite_eq_right h1]

theorem nielsenRawBoundaryTarget_chain {i j:ZMod J.n} (hij:Relation.EqvGen step i j) : target i=target j := by
  induction hij with
  | rel i j h => exact nielsenRawBoundaryTarget_step hD hNE hFG hfin w hwD hwN J hc hv h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- A raw boundary vertex has exactly one outgoing unpaired edge; capping does not identify distinct boundary vertices. -/
theorem nielsenRawBoundaryVertex_injective :
    Function.Injective (fun b:B=>(Quotient.mk _ b.val:V)) := by
  intro b c hbc
  have hc:target b.val=target c.val:=nielsenRawBoundaryTarget_chain hD hNE hFG hfin w hwD hwN J hc hv (Quotient.exact
    hbc)
  rw [nielsenRawBoundaryTarget_boundary,nielsenRawBoundaryTarget_boundary] at hc
  exact Option.some.inj hc

def nielsenRawBoundaryVertices : Set V := Set.range (fun b:B=>(Quotient.mk _ b.val:V))

def nielsenRawBoundaryVertexEquiv : B≃nielsenRawBoundaryVertices hD hNE hFG hfin w hwD hwN J hc hv :=
  Equiv.ofInjective _ (nielsenRawBoundaryVertex_injective hD hNE hFG hfin w hwD hwN J hc hv)

theorem nielsenRawBoundaryVertex_count :
    Nat.card (nielsenRawBoundaryVertices hD hNE hFG hfin w hwD hwN J hc hv)=Fintype.card B := by
  rw [←Nat.card_congr (nielsenRawBoundaryVertexEquiv hD hNE hFG hfin w hwD hwN J hc hv),Nat.card_eq_fintype_card]

end NielsenRawBoundaryEnds

section NielsenCappedEdgeCount
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "O" => NielsenCapOccurrence hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "d" => nielsenCapFiniteDartEquiv hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedPresentation_edgeCount_twice : 2*(Pcap).edgeCount=J.n+Fintype.card B := by
  let E:=Fin (Pcap).edgeCount
  let s:SignedDart E≃E⊕E:=
    { toFun := fun x=>match x with | .pos a=>.inl a | .neg a=>.inr a
      invFun := fun x=>match x with | .inl a=>.pos a | .inr a=>.neg a
      left_inv := by intro x;cases x <;> rfl
      right_inv := by intro x;cases x <;> rfl }
  have h:=Fintype.card_congr ((d).trans s)
  have hO:Fintype.card O=J.n+Fintype.card B:=by
    change Fintype.card (ZMod J.n⊕B)=_
    rw [Fintype.card_sum,ZMod.card]
  rw [hO,Fintype.card_sum,Fintype.card_fin] at h
  omega

end NielsenCappedEdgeCount

section NielsenCyclicCoreArea
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
local instance nielsenCyclicCoreAreaSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenCyclicCoreAreaSphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv

def nielsenCyclicNativeVertices : Fin J.n→𝕔𝔻 :=
  fun i=>vertex (originalCyclicFinIndex J i)
local notation "vtxs" => nielsenCyclicNativeVertices hD hNE hFG J hv

theorem nielsenCyclicNativeVertices_edge_plane (i:Fin J.n) :
    Polygon.discPolygonKleinPlane '' Polygon.discPolygonEdge vtxs i=J.edgeSegment (originalCyclicFinIndex J i) := by
  rw [Polygon.discPolygonEdge,original_discPolygonKleinPlane_image_segment]
  simp only [nielsenCyclicNativeVertices,originalCyclicFinIndex_rotate,
    nielsenCyclicVertex_plane,PolygonalCircle.edgeSegment]

theorem nielsenCyclicNativeVertices_boundary_plane :
    Polygon.discPolygonKleinPlane '' Polygon.discPolygonBoundary vtxs=J.carrier := by
  rw [Polygon.discPolygonBoundary,image_iUnion]
  simp_rw [nielsenCyclicNativeVertices_edge_plane]
  change (⋃i:Fin J.n,J.edgeSegment (originalCyclicFinIndex J i))=⋃i:ZMod J.n,J.edgeSegment i
  exact (originalCyclicFinIndex J).surjective.iUnion_comp _

include hfin w hwD hwN hc

theorem nielsenCyclicNativeVertices_boundary_klein :
    Hyperbolic.closedKleinCoordinate '' Polygon.discPolygonBoundary vtxs=
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
  let e:=PolygonalCircle.planeComplexEquiv
  calc
    Hyperbolic.closedKleinCoordinate '' Polygon.discPolygonBoundary vtxs=
        e '' (Polygon.discPolygonKleinPlane '' Polygon.discPolygonBoundary vtxs) := by
      rw [image_image]
      congr 1
      funext p
      exact (e.apply_symm_apply (Hyperbolic.closedKleinCoordinate p)).symm
    _=frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) := by
      rw [nielsenCyclicNativeVertices_boundary_plane,hc,image_image]
      have hecomp:(fun x=>e (Polygon.discPolygonKleinPlane x))=Hyperbolic.closedKleinCoordinate:=by
        funext p
        exact e.apply_symm_apply (Hyperbolic.closedKleinCoordinate p)
      rw [hecomp]
      rw [image_iUnion]
      change (⋃i:NielsenRefinedSide hD hNE⊕NielsenUnpairedSide P hNE D,
        Hyperbolic.closedKleinCoordinate '' NielsenBoundarySide.carrier i)=_
      rw [iUnion_sum]
      exact (nielsenCore_boundary_eq_positive_carriers hD hNE hFG hfin w hwD hwN).symm

def nielsenCyclicDiscPolygon : Polygon.DiscPolygon J.n where
  three_le:=J.three_le
  vertices:=vtxs
  vertices_injective:=(nielsenCyclicVertex_injective hD hNE hFG J hv).comp
    (originalCyclicFinIndex J).injective
  simple_edges:=by
    intro i j hij p hp
    have hi:Polygon.discPolygonKleinPlane p∈J.edgeSegment (originalCyclicFinIndex J i):=by
      rw [←nielsenCyclicNativeVertices_edge_plane hD hNE hFG J hv i]
      exact mem_image_of_mem _ hp.1
    have hj:Polygon.discPolygonKleinPlane p∈J.edgeSegment (originalCyclicFinIndex J j):=by
      rw [←nielsenCyclicNativeVertices_edge_plane hD hNE hFG J hv j]
      exact mem_image_of_mem _ hp.2
    have hne:originalCyclicFinIndex J i≠originalCyclicFinIndex J j:=
      (originalCyclicFinIndex J).injective.ne hij
    constructor
    · rcases J.edgeSegment_inter_subset_endpoints hne ⟨hi,hj⟩ with h|h
      · left
        apply Polygon.discPolygonKleinPlane_injective
        exact h.trans (nielsenCyclicVertex_plane hD hNE hFG J hv _).symm
      · right
        apply Polygon.discPolygonKleinPlane_injective
        rw [nielsenCyclicNativeVertices,originalCyclicFinIndex_rotate,nielsenCyclicVertex_plane]
        exact h
    · rcases J.edgeSegment_inter_subset_endpoints hne.symm ⟨hj,hi⟩ with h|h
      · left
        apply Polygon.discPolygonKleinPlane_injective
        exact h.trans (nielsenCyclicVertex_plane hD hNE hFG J hv _).symm
      · right
        apply Polygon.discPolygonKleinPlane_injective
        rw [nielsenCyclicNativeVertices,originalCyclicFinIndex_rotate,nielsenCyclicVertex_plane]
        exact h
  jordanBoundary:=by
    have ha:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
    obtain ⟨n,S,hK,_hI⟩:=nielsenCore_actual_cyclic_model hD hNE ha hfin w hwD hwN
    have hb:Polygon.discPolygonBoundary vtxs=S.toDiscPolygon.boundary:=by
      apply Hyperbolic.closedKleinCoordinate_injective.image_injective
      rw [nielsenCyclicNativeVertices_boundary_klein hD hNE hFG hfin w hwD hwN J hc hv]
      exact (hK ▸ S.toCenteredData.boundary_image_eq_frontier).symm
    obtain ⟨f⟩:=S.toDiscPolygon.jordanBoundary
    exact ⟨(Homeomorph.setCongr hb).trans f⟩
local notation "Q" => nielsenCyclicDiscPolygon hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicDiscPolygon_interior :
    (Q).interior=P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE) := by
  have ha:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
  obtain ⟨n,S,hK,hI⟩:=nielsenCore_actual_cyclic_model hD hNE ha hfin w hwD hwN
  have hb:(Q).boundary=S.toDiscPolygon.boundary:=by
    apply Hyperbolic.closedKleinCoordinate_injective.image_injective
    change Hyperbolic.closedKleinCoordinate '' Polygon.discPolygonBoundary vtxs=_
    rw [nielsenCyclicNativeVertices_boundary_klein hD hNE hFG hfin w hwD hwN J hc hv]
    exact (hK ▸ S.toCenteredData.boundary_image_eq_frontier).symm
  rw [←hI]
  unfold Polygon.DiscPolygon.interior Polygon.DiscPolygon.complexInterior Polygon.DiscPolygon.complexOutside
  unfold Polygon.DiscPolygon.complexBoundary
  rw [hb]

theorem nielsenCyclicDiscPolygon_area : (Q).area=fuchsianNielsenCoreArea P hNE D := by
  rw [Polygon.DiscPolygon.area,nielsenCyclicDiscPolygon_interior]
  exact (P.area_apply _ (hD.locallyFinite.fundamental.isOpen.inter
    (fuchsianNielsenCore_isOpen P hNE)).measurableSet).symm

theorem nielsenCyclicDiscPolygon_gaussBonnet :
    (fuchsianNielsenCoreArea P hNE D).toReal=((J.n:ℝ)-2)*Real.pi-
      ∑i:Fin J.n,(Q).angle i := by
  rw [←nielsenCyclicDiscPolygon_area hD hNE hFG hfin w hwD hwN J hc hv]
  exact Polygon.DiscPolygon.area_toReal_eq_original_angle_defect _

theorem nielsenCyclicDiscPolygon_angle_eq_fuchsian (i:Fin J.n) (x:P.domain.carrier)
    (hx:(Q).vertices i=Hyperbolic.discToClosedModel (P.finiteCoordinate x)) :
    (Q).angle i=fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) x := by
  have hI:=nielsenCyclicDiscPolygon_interior hD hNE hFG hfin w hwD hwN J hc hv
  have hQ:(Q).IsConvex:=by
    change Hyperbolic.DiscHConvex (Q).interior
    rw [hI]
    exact nielsenCore_inter_native_convex hD hNE
  have hCF:(Q).finiteCarrier=P.finiteCoordinate '' closure (D∩fuchsianNielsenCore P hNE):=by
    rw [Polygon.DiscPolygon.finiteCarrier_eq_closure,hI,←P.finiteCoordinate.image_closure]
  calc
    _=Hyperbolic.discSubtendedAngle (Q).finiteCarrier (P.finiteCoordinate x):=
      convexPolygon_angle_eq_subtended (Q) hQ i (P.finiteCoordinate x) hx
    _=_:=by rw [hCF];rfl

end NielsenCyclicCoreArea

section NielsenCyclicCappedAreaEuler
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "Q" => nielsenCyclicDiscPolygon hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicDiscPolygon_area_rawEuler :
    (fuchsianNielsenCoreArea P hNE D).toReal=
      2*Real.pi*((Nat.card V:ℝ)-(Surfaces.CyclicSurface.eulerCharacteristic (Pcap):ℝ)+
        Fintype.card C-(Fintype.card B:ℝ)/2)-∑i:Fin J.n,(Q).angle i := by
  have hG:=nielsenCyclicDiscPolygon_gaussBonnet hD hNE hFG hfin w hwD hwN J hc hv
  have hχ:(Surfaces.CyclicSurface.eulerCharacteristic (Pcap):ℝ)=
      (Nat.card V:ℝ)-(Pcap).edgeCount+1+Fintype.card C:=by
    exact_mod_cast nielsenCappedPresentation_rawEuler hD hNE hFG hfin w hwD hwN J hc hv
  have hE:2*((Pcap).edgeCount:ℝ)=(J.n:ℝ)+Fintype.card B:=by
    exact_mod_cast nielsenCappedPresentation_edgeCount_twice hD hNE hFG hfin w hwD hwN J hc hv
  linear_combination hG+2*Real.pi*hχ-Real.pi*hE

theorem nielsenCyclicDiscPolygon_angle_original (i:Fin J.n) :
    (Q).angle i=
      if hi:‖((Q).vertices i:ℂ)‖<1 then
        fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE)
          (P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint ((Q).vertices i) hi))
      else 0 := by
  classical
  by_cases hi:‖((Q).vertices i:ℂ)‖<1
  · rw [dite_eq_left hi]
    apply nielsenCyclicDiscPolygon_angle_eq_fuchsian hD hNE hFG hfin w hwD hwN J hc hv i
    rw [P.finiteCoordinate.apply_symm_apply]
    exact (Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
  · rw [dite_eq_right hi]
    exact (Q).angle_of_ideal i (le_antisymm ((Q).vertices i).norm_le_one (le_of_not_gt hi))

/-- The true Nielsen density area and true Haar corner angles are related to the derived cap-word genus. Identification with the geometric filled quotient is not assumed here. -/
theorem nielsenCyclicDiscPolygon_genus_angular_area :
    ∃g,Surfaces.HasTopologicalGenus ((Pcap).PolygonalRealization
      (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      (fuchsianNielsenCoreArea P hNE D).toReal=
        2*Real.pi*((Nat.card V:ℝ)-2+2*(g:ℝ)+Fintype.card C-(Fintype.card B:ℝ)/2)-
        ∑i:Fin J.n,
          if hi:‖((Q).vertices i:ℂ)‖<1 then
            fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE)
              (P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint ((Q).vertices i) hi))
          else 0 := by
  obtain ⟨g,hg,hχ⟩:=nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv
  refine ⟨g,hg,?_⟩
  have hχR:(Surfaces.CyclicSurface.eulerCharacteristic (Pcap):ℝ)=2-2*(g:ℝ):=by exact_mod_cast hχ
  rw [nielsenCyclicDiscPolygon_area_rawEuler hD hNE hFG hfin w hwD hwN J hc hv,hχR]
  have hsum:(∑i:Fin J.n,(Q).angle i)=∑i:Fin J.n,
      if hi:‖((Q).vertices i:ℂ)‖<1 then
        fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE)
          (P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint ((Q).vertices i) hi)) else 0:=by
    apply Finset.sum_congr rfl
    intro i _hi
    exact nielsenCyclicDiscPolygon_angle_original hD hNE hFG hfin w hwD hwN J hc hv i
  rw [hsum]
  ring

end NielsenCyclicCappedAreaEuler

end NielsenCyclicCensusArea
section NielsenIncidentTileChains

/-- At an actual finite core frontier point, the incident original tiles are connected by positive intersections of their genuine core clips. -/
theorem IsConvexFuchsianPolygon.nielsenCore_incident_tile_nontrivial_chains
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) (x : P.domain.carrier)
    (hxN : x∈frontier (fuchsianNielsenCore P hNE))
    (g k : H) (hg : x∈fuchsianDomainTile P D g) (hk : x∈fuchsianDomainTile P D k) :
    Relation.EqvGen (fun a b:H=>
      x∈fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) a ∧
      x∈fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) b ∧
      (fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) a ∩
        fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) b).Nontrivial) g k := by
  classical
  let Q:=D∩fuchsianNielsenCore P hNE
  let I:={a:H // x∈fuchsianDomainTile P D a}
  let : Finite I:=(hD.locallyFinite.incident_finite x).to_subtype
  let F:=normalizedPolygonKleinCoordinate P x
  have hF : Topology.IsOpenEmbedding F:=normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have hFx : F x=0:=normalizedPolygonKleinCoordinate_self P x
  have hxcl : x∈closure (fuchsianNielsenCore P hNE):=frontier_subset_closure hxN
  have hxnot : x∉fuchsianNielsenCore P hNE:=by
    exact ((fuchsianNielsenCore_isOpen P hNE).frontier_eq ▸ hxN).2
  have hcut (a:I) : x∈fuchsianDomainTile P Q a.val:=by
    rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN]
    exact ⟨a.property,hxcl⟩
  have hconv : Convex ℝ (F '' fuchsianNielsenCore P hNE):=by
    have he : F '' fuchsianNielsenCore P hNE=
        Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' fuchsianNielsenCore P hNE):=by
      rw [image_image]
      rfl
    rw [he]
    apply (Hyperbolic.discHConvex_iff_klein_convex _).mp
    change Hyperbolic.DiscHConvex ((fun z=>Hyperbolic.discOriginNormalizer (P.finiteCoordinate x)
      (P.finiteCoordinate z)) '' fuchsianNielsenCore P hNE)
    rw [←image_image]
    exact (fuchsianNielsenCore_convex P hNE).isometry_image (Hyperbolic.discOriginNormalizer_isometry _)
  obtain ⟨K,_hK,hKx,_hI,hcov,_havoid⟩:=hD.locallyFinite.finite_neighborhood_star x
  obtain ⟨O,hOK,hOo,hxO⟩:=mem_nhds_iff.mp hKx
  have h0O : (0:ℂ)∈F '' O:=⟨x,hxO,hFx⟩
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp (hF.isOpenMap O hOo) 0 h0O
  let T:=Metric.ball (0:ℂ) r∩F '' fuchsianNielsenCore P hNE
  let S:=F ⁻¹' T
  have hTrange : T⊆range F:=fun _ hz=>image_subset_range _ _ hz.2
  have hS : IsPreconnected S:=((convex_ball (0:ℂ) r).inter hconv).isPreconnected.preimage_of_isOpenMap
    hF.injective hF.isOpenMap hTrange
  have hxS : x∉S:=by
    intro hxS
    obtain ⟨y,hyN,hyx⟩:=hxS.2
    exact hxnot (hF.injective hyx ▸ hyN)
  have hcover : S⊆⋃a:I,fuchsianDomainTile P Q a.val:=by
    intro y hy
    obtain ⟨z,hzO,hzy⟩:=hball hy.1
    have hzy' : z=y:=hF.injective hzy
    obtain ⟨a,ha,hay⟩:=mem_iUnion₂.mp (hcov (hOK (hzy' ▸ hzO)))
    refine mem_iUnion.mpr ⟨⟨a,ha⟩,?_⟩
    rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN]
    obtain ⟨u,huN,huy⟩:=hy.2
    exact ⟨hay,subset_closure (hF.injective huy ▸ huN)⟩
  have htile (a:H) : fuchsianDomainTile P Q a=closure (a•Q):=(Homeomorph.smul a).image_closure Q
  have hmeet (a:I) : (S∩fuchsianDomainTile P Q a.val).Nonempty:=by
    have hxU : x∈closure (a.val•Q):=htile a.val ▸ hcut a
    have hxB : x∈F ⁻¹' Metric.ball (0:ℂ) r:=by
      change F x∈Metric.ball (0:ℂ) r
      rw [hFx]
      exact Metric.mem_ball_self hr
    obtain ⟨y,hyB,hyU⟩:=mem_closure_iff.mp hxU
      (F ⁻¹' Metric.ball (0:ℂ) r) (Metric.isOpen_ball.preimage hF.continuous) hxB
    have hyN : y∈fuchsianNielsenCore P hNE:=by
      obtain ⟨z,hzQ,rfl⟩:=hyU
      exact fuchsianNielsenCore_invariant P hNE a.val z hzQ.2
    refine ⟨y,⟨hyB,⟨y,hyN,rfl⟩⟩,?_⟩
    rw [htile]
    exact subset_closure hyU
  have hchain:=finite_closed_cover_nontrivial_chains (fun a:I=>fuchsianDomainTile P Q a.val)
    (fun a=>fuchsianDomainTile_closed P Q a.val) x hcut S hS hxS hcover hmeet
    (⟨g,hg⟩:I) (⟨k,hk⟩:I)
  have hmap (a b:I)
      (hab:Relation.EqvGen (fun u v:I=>
        (fuchsianDomainTile P Q u.val∩fuchsianDomainTile P Q v.val).Nontrivial) a b) :
      Relation.EqvGen (fun u v:H=>x∈fuchsianDomainTile P Q u∧x∈fuchsianDomainTile P Q v∧
        (fuchsianDomainTile P Q u∩fuchsianDomainTile P Q v).Nontrivial) a.val b.val:=by
    induction hab with
    | rel a b hab => exact Relation.EqvGen.rel _ _ ⟨hcut a,hcut b,hab⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  exact hmap _ _ hchain

end NielsenIncidentTileChains


section NielsenTaggedEdgeChains
section NielsenTaggedEdgeRawChain
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "tag" => nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv

/-- The actual endpoint identification on a tagged paired edge gives a literal raw corner chain. -/
theorem nielsenCyclicSideTag_vertex_rawChain
    (v:NielsenRefinedSide hD hNE) (k i j:ZMod J.n) (hk:tag k=Sum.inl v)
    (hi:vertex i∈edge k)
    (he:(P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap
      (vertex i)=vertex j) : Relation.EqvGen step i j := by
  have hp:=nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv k v hk
  have hend:=nielsenCyclicPairIndex_endpoint_reverse hD hNE hFG hfin w hwD hwN J hc hv k v hk
  have hinj:=nielsenCyclicVertex_injective hD hNE hFG J hv
  rcases nielsenCyclicEdge_no_extra_marks hD hNE hFG J hv k (vertex i) hi
    (nielsenCyclicVertex_marked hD hNE hFG J hv i) with hi0|hi1
  · have hik:i=k:=hinj hi0
    subst i
    have hjk:j=pairIndex k+1:=hinj (he.symm.trans hend.1)
    subst j
    exact Relation.EqvGen.rel _ _ ⟨hp.1,rfl⟩
  · have hik:i=k+1:=hinj hi1
    subst i
    have hjk:j=pairIndex k:=hinj (he.symm.trans hend.2)
    subst j
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    refine ⟨?_,?_⟩
    · rw [nielsenCyclicPairIndex_involutive hD hNE hFG hfin w hwD hwN J hc hv k]
      exact hp.1.symm
    · change k+1=pairIndex (pairIndex k)+1
      rw [nielsenCyclicPairIndex_involutive hD hNE hFG hfin w hwD hwN J hc hv k]

end NielsenTaggedEdgeRawChain
end NielsenTaggedEdgeChains

section NielsenFrontierTileChains
open Set Topology Filter MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace Pointwise
local instance nielsenRawChainSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenRawChainSphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

section NielsenFiniteFrontierRawChains
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "tag" => nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv

include hFG in
theorem NielsenBoundarySide.planeCarrier_preperfect (s:NielsenBoundarySide hD hNE) :
    Preperfect s.planeCarrier := by
  obtain ⟨a,b,hab,he⟩:=s.carrier_eq_segment hFG
  let e:=LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm
  have hplane:s.planeCarrier=segment ℝ (Polygon.discPolygonKleinPlane a) (Polygon.discPolygonKleinPlane b) := by
    change Polygon.discPolygonKleinPlane '' s.carrier=_
    rw [he]
    change (e ∘ Hyperbolic.closedKleinCoordinate) '' Hyperbolic.closedModelDiscHSegment a b=_
    simp only [Function.comp_def]
    rw [←image_image e Hyperbolic.closedKleinCoordinate]
    rw [Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  rw [hplane]
  exact (convex_segment _ _).isPreconnected.preperfect_of_nontrivial
    ⟨_,left_mem_segment ℝ _ _,_,right_mem_segment ℝ _ _,Polygon.discPolygonKleinPlane_injective.ne hab⟩

theorem nielsenBoundarySide_point_mem_tagged_cyclic_edge
    (s:NielsenBoundarySide hD hNE) (p:𝕔𝔻) (hp:p∈s.carrier) :
    ∃k:ZMod J.n,tag k=s ∧ p∈edge k := by
  classical
  let T:Set LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane:=
    ⋃k:{k:ZMod J.n // tag k=s},J.edgeSegment k.val
  let E:Set LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane:=
    ⋃k:{k:ZMod J.n // tag k≠s},Polygon.discPolygonKleinPlane '' (s.carrier∩(tag k.val).carrier)
  have hT:IsClosed T:=isClosed_iUnion_of_finite (fun k=>J.isClosed_edgeSegment k.val)
  have hE:E.Finite:=Set.finite_iUnion (fun k=>
    (NielsenBoundarySide.inter_finite hD hNE w hwD hwN s (tag k.val) (Ne.symm k.property)).image _)
  have hcover:s.planeCarrier⊆T∪E := by
    rintro z ⟨q,hq,rfl⟩
    have hz:Polygon.discPolygonKleinPlane q∈J.carrier:=by
      rw [hc]
      exact ⟨q,mem_iUnion.mpr ⟨s,hq⟩,rfl⟩
    obtain ⟨k,hk⟩:=mem_iUnion.mp hz
    by_cases he:tag k=s
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k,he⟩,hk⟩)
    · right
      apply mem_iUnion.mpr
      refine ⟨⟨k,he⟩,q,⟨hq,?_⟩,rfl⟩
      apply nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv k
      apply Polygon.discPolygonKleinPlane_injective.mem_set_image.mp
      rw [nielsenCyclicEdge_plane]
      exact hk
  have hpT:Polygon.discPolygonKleinPlane p∈T := by
    by_contra hn
    have hacc:AccPt (Polygon.discPolygonKleinPlane p) (𝓟 (Tᶜ∩s.planeCarrier)):=
      (NielsenBoundarySide.planeCarrier_preperfect hD hNE hFG s).open_inter hT.isOpen_compl _ ⟨hn,p,hp,rfl⟩
    have hf:(Tᶜ∩s.planeCarrier).Finite:=hE.subset (fun _ hz=>(hcover hz.2).resolve_left hz.1)
    exact Set.Infinite.of_accPt hacc hf
  obtain ⟨k,hk⟩:=mem_iUnion.mp hpT
  refine ⟨k.val,k.property,?_⟩
  apply Polygon.discPolygonKleinPlane_injective.mem_set_image.mp
  rw [nielsenCyclicEdge_plane]
  exact hk

theorem originalRefinedSide_iUnion_original_carrier (s:FuchsianPolygonSides P D) :
    (⋃v:{v:OriginalRefinedSide hD // v.val.1=s},v.val.carrier)=fuchsianSideClosedModel s := by
  classical
  apply subset_antisymm
  · intro p hp
    obtain ⟨v,hv⟩:=mem_iUnion.mp hp
    simpa only [v.property] using v.val.carrier_subset_original hv
  · intro p hp
    let v:OriginalRefinedSide hD:=⟨(s,false),by simp only [Bool.false_eq_true,false_implies]⟩
    by_cases hs:fuchsianPairedSide hD s=s
    · let u:OriginalRefinedSide hD:=⟨(s,true),fun _=>hs⟩
      let A:=originalSelfSideSplit hD s hs
      have hv:v.carrier=A.first:=by
        simp only [OriginalRefinedSide.carrier,v,hs,dite_true,Bool.false_eq_true,ite_false]
        rfl
      have hu:u.carrier=A.second:=by
        simp only [OriginalRefinedSide.carrier,u,hs,dite_true,ite_true]
        rfl
      rw [←A.union_inter.1] at hp
      rcases hp with hp|hp
      · exact mem_iUnion.mpr ⟨⟨v,rfl⟩,hv.symm ▸ hp⟩
      · exact mem_iUnion.mpr ⟨⟨u,rfl⟩,hu.symm ▸ hp⟩
    · apply mem_iUnion.mpr
      refine ⟨⟨v,rfl⟩,?_⟩
      simpa only [OriginalRefinedSide.carrier,v,hs,dite_false] using hp

include hFG hfin in
theorem nielsen_original_positive_clip_refined_at_point
    (s:FuchsianPolygonSides P D)
    (hnt:(fuchsianSideClosedModel s∩nielsenClosedCore P hNE).Nontrivial)
    (p:𝕔𝔻) (hp:p∈fuchsianSideClosedModel s∩nielsenClosedCore P hNE) :
    ∃v:NielsenRefinedSide hD hNE,v.val.val.1=s ∧ p∈v.carrier := by
  classical
  let :Fintype (FuchsianPolygonSides P D):=hfin.fintype
  let :Finite (OriginalRefinedSide hD):=by unfold OriginalRefinedSide;infer_instance
  let I:={v:OriginalRefinedSide hD // v.val.1=s}
  let K:=fuchsianSideClosedModel s∩nielsenClosedCore P hNE
  let e:=LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm
  have hN:Convex ℝ (P.kleinCoordinate '' fuchsianNielsenCore P hNE):=by
    simpa only [UnitDiscFuchsianGroup.kleinCoordinate,image_image] using
      (Hyperbolic.discHConvex_iff_klein_convex _).mp (fuchsianNielsenCore_convex P hNE)
  have hK:Convex ℝ (Hyperbolic.closedKleinCoordinate '' K):=by
    rw [show K=fuchsianSideClosedModel s∩nielsenClosedCore P hNE from rfl,
      image_inter Hyperbolic.closedKleinCoordinate_injective,fuchsianSideClosedModel_klein_image,
      nielsenClosedCore,Hyperbolic.discClosedModelClosure,Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
    exact (fuchsianSideClosedModel_klein_geometry s).2.1.inter hN.closure
  have hplane:Convex ℝ (Polygon.discPolygonKleinPlane '' K):=by
    change Convex ℝ ((e ∘ Hyperbolic.closedKleinCoordinate) '' K)
    simp only [Function.comp_def]
    rw [←image_image e Hyperbolic.closedKleinCoordinate]
    exact hK.linear_image e.toLinearEquiv.toLinearMap
  have hpre:Preperfect (Polygon.discPolygonKleinPlane '' K):=
    hplane.isPreconnected.preperfect_of_nontrivial (hnt.image Polygon.discPolygonKleinPlane_injective)
  let T:Set LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane:=
    ⋃v:{v:I // (nielsenRefinedSideCarrier hNE v.val).Nontrivial},
      Polygon.discPolygonKleinPlane '' nielsenRefinedSideCarrier hNE v.val.val
  let E:Set LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane:=
    ⋃v:I,if (nielsenRefinedSideCarrier hNE v.val).Nontrivial then ∅ else
      Polygon.discPolygonKleinPlane '' nielsenRefinedSideCarrier hNE v.val
  have hT:IsClosed T:=by
    apply isClosed_iUnion_of_finite
    intro v
    let u:NielsenRefinedSide hD hNE:=⟨v.val.val,v.property⟩
    exact NielsenBoundarySide.planeCarrier_isClosed hFG (Sum.inl u:NielsenBoundarySide hD hNE)
  have hE:E.Finite:=by
    apply Set.finite_iUnion
    intro v
    split_ifs with he
    · exact finite_empty
    · apply Set.Finite.image
      apply Set.Subsingleton.finite
      intro a ha b hb
      by_contra hab
      exact he ⟨a,ha,b,hb,hab⟩
  have hcover:Polygon.discPolygonKleinPlane '' K⊆T∪E := by
    rintro z ⟨q,hq,rfl⟩
    have hqR:q∈⋃v:I,v.val.carrier:=by
      rw [originalRefinedSide_iUnion_original_carrier hD s]
      exact hq.1
    obtain ⟨v,hv⟩:=mem_iUnion.mp hqR
    have hqv:q∈nielsenRefinedSideCarrier hNE v.val:=⟨hv,hq.2⟩
    by_cases he:(nielsenRefinedSideCarrier hNE v.val).Nontrivial
    · exact Or.inl (mem_iUnion.mpr ⟨⟨v,he⟩,q,hqv,rfl⟩)
    · right
      exact mem_iUnion.mpr ⟨v,by rw [ite_eq_right he];exact ⟨q,hqv,rfl⟩⟩
  have hpT:Polygon.discPolygonKleinPlane p∈T := by
    by_contra hn
    have hacc:AccPt (Polygon.discPolygonKleinPlane p) (𝓟 (Tᶜ∩Polygon.discPolygonKleinPlane '' K)):=
      hpre.open_inter hT.isOpen_compl _ ⟨hn,p,hp,rfl⟩
    exact Set.Infinite.of_accPt hacc (hE.subset (fun _ hz=>(hcover hz.2).resolve_left hz.1))
  obtain ⟨v,q,hq,hqp⟩:=mem_iUnion.mp hpT
  exact ⟨⟨v.val.val,v.property⟩,v.val.property,Polygon.discPolygonKleinPlane_injective hqp ▸ hq⟩

include w hwD hwN in
theorem nielsenCore_frontier_orbit_marked_vertex
    (i:ZMod J.n) (x y:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hyD:y∈closure D) (hyN:y∈frontier (fuchsianNielsenCore P hNE))
    (g:H) (hg:g•x=y) :
    ∃j:ZMod J.n,Hyperbolic.discToClosedModel (P.finiteCoordinate y)=vertex j := by
  have hyC:y∈closure (D∩fuchsianNielsenCore P hNE):=by
    rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
    exact ⟨hyD,frontier_subset_closure hyN⟩
  have hyF:y∈frontier (D∩fuchsianNielsenCore P hNE):=by
    rw [(hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)).frontier_eq]
    exact ⟨hyC,fun hy=>((fuchsianNielsenCore_isOpen P hNE).frontier_eq ▸ hyN).2 hy.2⟩
  have himg:(P.compactifiedAction g).closedMap (vertex i)=Hyperbolic.discToClosedModel (P.finiteCoordinate y):=by
    rw [←hx,P.compactifiedAction_finite,hg]
  have hyB:Hyperbolic.closedKleinCoordinate ((P.compactifiedAction g).closedMap (vertex i))∈
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)):=by
    rw [himg]
    exact (nielsenCore_klein_finite_frontier hD hNE w hwD hwN y).mpr hyF
  have hm:=nielsenBoundaryMarkSaturation_map_mem P hNE D
    (nielsenBoundarySeedMarks hD hNE hFG) g (vertex i)
    (nielsenCyclicVertex_marked hD hNE hFG J hv i) hyB
  rw [himg] at hm
  obtain ⟨j,hj⟩:=(hv (Polygon.discPolygonKleinPlane (Hyperbolic.discToClosedModel (P.finiteCoordinate y)))).mpr
    ⟨_,hm,rfl⟩
  refine ⟨j,Polygon.discPolygonKleinPlane_injective ?_⟩
  exact hj.symm.trans (nielsenCyclicVertex_plane hD hNE hFG J hv j).symm

theorem nielsenCore_positive_incident_pair_rawChain
    (x:P.domain.carrier) (a b:H)
    (haa:x∈fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) a)
    (hbb:x∈fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) b)
    (hab:(fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) a∩
      fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) b).Nontrivial)
    (i j:ZMod J.n)
    (hi:Hyperbolic.discToClosedModel (P.finiteCoordinate (a⁻¹•x))=vertex i)
    (hj:Hyperbolic.discToClosedModel (P.finiteCoordinate (b⁻¹•x))=vertex j) :
    Relation.EqvGen step i j := by
  classical
  by_cases he:a=b
  · have hij:i=j:=nielsenCyclicVertex_injective hD hNE hFG J hv
      (hi.symm.trans (he ▸ hj))
    subst j
    exact Relation.EqvGen.refl _
  let Q:=D∩fuchsianNielsenCore P hNE
  let g:=a⁻¹*b
  have hgne:g≠1:=fun hh=>he (inv_mul_eq_one.mp hh)
  have hT:(closure Q∩fuchsianDomainTile P Q g).Nontrivial:=by
    have hh:=hab.image (MulAction.injective a⁻¹)
    change (a⁻¹•(a•closure Q∩b•closure Q)).Nontrivial at hh
    rw [smul_set_inter,inv_smul_smul,←mul_smul] at hh
    exact hh
  have hsub:∀k:H,fuchsianDomainTile P Q k⊆fuchsianDomainTile P D k:=by
    intro k z hz
    rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN] at hz
    exact hz.1
  have hSide: (closure D∩fuchsianDomainTile P D g).Nontrivial:=by
    apply hT.mono
    intro z hz
    exact ⟨closure_mono inter_subset_left hz.1,hsub g hz.2⟩
  let s:FuchsianPolygonSides P D:=⟨closure D∩fuchsianDomainTile P D g,
    hD.side_of_nontrivial_intersection hgne hSide⟩
  have hsel:fuchsianSideElement hD s=g:=
    (hD.existsUnique_side_element s.property).unique (fuchsianSideElement_spec hD s) ⟨hgne,rfl⟩
  let F:=fun z:P.domain.carrier=>Hyperbolic.discToClosedModel (P.finiteCoordinate z)
  have hFinj:Function.Injective F:=Hyperbolic.isEmbedding_discToClosedModel.injective.comp P.finiteCoordinate.injective
  have hCore:∀z∈closure (fuchsianNielsenCore P hNE),F z∈nielsenClosedCore P hNE:=by
    intro z hz
    apply mem_closure_image Hyperbolic.isEmbedding_discToClosedModel.continuous.continuousAt
    rw [←P.finiteCoordinate.image_closure]
    exact ⟨z,hz,rfl⟩
  have hST:∀z∈closure Q∩fuchsianDomainTile P Q g,
      F z∈fuchsianSideClosedModel s∩nielsenClosedCore P hNE:=by
    intro z hz
    exact ⟨(mem_fuchsianSideClosedModel_finite s z).mpr
      ⟨closure_mono inter_subset_left hz.1,hsub g hz.2⟩,
      hCore z (closure_mono inter_subset_right hz.1)⟩
  have hnt:(fuchsianSideClosedModel s∩nielsenClosedCore P hNE).Nontrivial:=
    (hT.image hFinj).mono (by rintro _ ⟨z,hz,rfl⟩;exact hST z hz)
  have hpa:a⁻¹•x∈closure Q:=by
    simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using haa
  have hpb:b⁻¹•x∈closure Q:=by
    simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using hbb
  have hpg:a⁻¹•x∈fuchsianDomainTile P Q g:=
    ⟨b⁻¹•x,hpb,by simp only [g,mul_smul,smul_inv_smul]⟩
  obtain ⟨v,hvs,hpv⟩:=nielsen_original_positive_clip_refined_at_point hD hNE hFG hfin s hnt
    (F (a⁻¹•x)) (hST _ ⟨hpa,hpg⟩)
  obtain ⟨k,hk,hik⟩:=nielsenBoundarySide_point_mem_tagged_cyclic_edge hD hNE hFG hfin
    w hwD hwN J hc hv (Sum.inl v) (vertex i) (hi ▸ hpv)
  apply nielsenCyclicSideTag_vertex_rawChain hD hNE hFG hfin w hwD hwN J hc hv v k i j hk hik
  rw [hvs,hsel,←hi,P.compactifiedAction_finite]
  simpa only [g,mul_inv_rev,inv_inv,mul_smul,smul_inv_smul] using hj

theorem nielsenCoreFiniteFrontierCorner_orbit_rawChain
    (i j:ZMod J.n) (x y:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hy:Hyperbolic.discToClosedModel (P.finiteCoordinate y)=vertex j)
    (hxN:x∈frontier (fuchsianNielsenCore P hNE))
    (_hyN:y∈frontier (fuchsianNielsenCore P hNE))
    (horbit:∃g:H,g•x=y) : Relation.EqvGen step i j := by
  classical
  let Q:=D∩fuchsianNielsenCore P hNE
  let R:=fun a b:H=>x∈fuchsianDomainTile P Q a∧x∈fuchsianDomainTile P Q b∧
    (fuchsianDomainTile P Q a∩fuchsianDomainTile P Q b).Nontrivial
  have hclosure (k:ZMod J.n) (z:P.domain.carrier)
      (hz:Hyperbolic.discToClosedModel (P.finiteCoordinate z)=vertex k) : z∈closure Q:=by
    have hmark:=nielsenCyclicVertex_marked hD hNE hFG J hv k
    have hB:=nielsenBoundaryMarkSaturation_subset_boundary P hNE D
      (nielsenBoundarySeedMarks hD hNE hFG) ⟨vertex k,hmark,rfl⟩
    rw [←hz] at hB
    exact frontier_subset_closure ((nielsenCore_klein_finite_frontier hD hNE w hwD hwN z).mp hB)
  have hmem {a b:H} (h:Relation.EqvGen R a b) :
      x∈fuchsianDomainTile P Q a↔x∈fuchsianDomainTile P Q b:=by
    induction h with
    | rel a b hab => exact ⟨fun _=>hab.2.1,fun _=>hab.1⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  have hindex (a:H) (ha:x∈fuchsianDomainTile P Q a) :
      ∃k:ZMod J.n,Hyperbolic.discToClosedModel (P.finiteCoordinate (a⁻¹•x))=vertex k:=by
    have haQ:a⁻¹•x∈closure Q:=by
      simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using ha
    have haN:a⁻¹•x∈frontier (fuchsianNielsenCore P hNE):=by
      rw [←fuchsianNielsenCore_smul_frontier P hNE a⁻¹]
      exact mem_smul_set.mpr ⟨x,hxN,rfl⟩
    exact nielsenCore_frontier_orbit_marked_vertex hD hNE hFG w hwD hwN J hv i x (a⁻¹•x) hx
      (closure_mono inter_subset_left haQ) haN a⁻¹ rfl
  have hmap {a b:H} (h:Relation.EqvGen R a b) :
      x∈fuchsianDomainTile P Q a→∀k l:ZMod J.n,
        Hyperbolic.discToClosedModel (P.finiteCoordinate (a⁻¹•x))=vertex k→
        Hyperbolic.discToClosedModel (P.finiteCoordinate (b⁻¹•x))=vertex l→Relation.EqvGen step k l:=by
    induction h with
    | rel a b hab =>
      intro _ k l hk hl
      exact nielsenCore_positive_incident_pair_rawChain hD hNE hFG hfin w hwD hwN J hc hv
        x a b hab.1 hab.2.1 hab.2.2 k l hk hl
    | refl a =>
      intro _ k l hk hl
      have hkl:k=l:=nielsenCyclicVertex_injective hD hNE hFG J hv (hk.symm.trans hl)
      subst l
      exact Relation.EqvGen.refl _
    | symm a b hab ih =>
      intro hb k l hk hl
      exact Relation.EqvGen.symm _ _ (ih ((hmem hab).mpr hb) l k hl hk)
    | trans a b c hab _hbc ih1 ih2 =>
      intro ha k l hk hl
      have hb:=(hmem hab).mp ha
      obtain ⟨m,hm⟩:=hindex b hb
      exact Relation.EqvGen.trans _ _ _ (ih1 ha k m hk hm) (ih2 hb m l hm hl)
  obtain ⟨g,hg⟩:=horbit
  have hxQ:=hclosure i x hx
  have hyQ:=hclosure j y hy
  have h1:x∈fuchsianDomainTile P D (1:H):=by
    simpa only [fuchsianDomainTile,one_smul] using closure_mono inter_subset_left hxQ
  have hgI:x∈fuchsianDomainTile P D g⁻¹:=by
    refine ⟨y,closure_mono inter_subset_left hyQ,?_⟩
    change g⁻¹•y=x
    rw [←hg,inv_smul_smul]
  have hchain:=IsConvexFuchsianPolygon.nielsenCore_incident_tile_nontrivial_chains
    hD hNE w hwD hwN x hxN 1 g⁻¹ h1 hgI
  have h1Q:x∈fuchsianDomainTile P Q (1:H):=by simpa only [fuchsianDomainTile,one_smul] using hxQ
  apply hmap hchain h1Q i j
  · simpa only [inv_one,one_smul] using hx
  · simpa only [inv_inv,hg] using hy

end NielsenFiniteFrontierRawChains
end NielsenFrontierTileChains

section NielsenBoundaryGeodesics

theorem boundaryHyperbolic_normalized_axis_stable
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hinf : (∞:OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (f : H) (hf : IsBoundaryHyperbolic D f)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A=q*f.val*q⁻¹)
    (hAn : Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) :
    Surfaces.MobiusStableSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)
      (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier) := by
  obtain ⟨G,hGF,hGA⟩ := boundaryHyperbolic_normalized_gap D hNE q hq hinf f hf A hA hAn ht
  have hAH : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A):=(Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mpr ht
  intro g hg
  obtain ⟨k,hk,rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H g).mp hg
  let kH : H:=⟨k,hk⟩
  have hpres : (q*k*q⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    rw [←hq,Mobius.stableAxis_conjugate_image,q.val.injective.image_injective.eq_iff]
    exact D.image_eq kH
  obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  let C:=B*A*B⁻¹
  have hC : Hyperbolic.realSLMobius C=q*(kH*f*kH⁻¹).val*q⁻¹ := by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv,hB,hA]
    change (q*k*q⁻¹)*(q*f.val*q⁻¹)*(q*k*q⁻¹)⁻¹=q*(k*f.val*k⁻¹)*q⁻¹
    group
  have hCH : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius C) := by
    dsimp only [C]
    simpa only [map_mul,map_inv] using Mobius.mobiusHyperbolic_conjugation_forward _ (Hyperbolic.realSLMobius B) hAH
  have hCn : Hyperbolic.realSLMobius C≠1:=hCH.1.1
  have hCt := (Hyperbolic.realSLMobius_hyperbolic_iff C hCn).mp hCH
  obtain ⟨J,hJF,hJC⟩ := boundaryHyperbolic_normalized_gap D hNE q hq hinf
    (kH*f*kH⁻¹) (hf.conjugate kH) C hC hCn hCt
  have himage : (q*k*q⁻¹).val ''
      (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier)=
      Hyperbolic.extendedHalfPlanePoint '' J.line.carrier := by
    rw [←hB,hJC]
    exact (nativeHyperbolicAxisSphere_conjugation A B hAH).symm
  rw [himage,←hGA]
  by_cases hGI : G.carrier=J.carrier
  · exact Or.inl (congrArg (fun L : Hyperbolic.HalfPlaneLine=>Hyperbolic.extendedHalfPlanePoint '' L.carrier)
      (nielsenGap_line_eq_of_carrier_eq J G hGI.symm))
  · have hd:=Auxiliary.Topology.nielsenRealGapFamily_pairwiseDisjoint
      (Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet
        (DiscreteGroups.Action.Actions.subgroupConjugate q H))) hGF hJF hGI
    rcases Hyperbolic.nielsen_gap_lines_eq_or_disjoint G J hd with he|hd
    · exact Or.inl (congrArg (fun L : Hyperbolic.HalfPlaneLine=>Hyperbolic.extendedHalfPlanePoint '' L.carrier) he.symm)
    · exact Or.inr ((Set.disjoint_image_iff Mobius.halfPlaneBoundaryPoint_injective).mpr hd.symm)

/-- Changing the actual half-plane chart changes only the representation
of the same complete original hyperbolic axis. -/
theorem boundary_axis_carrier_image_in_chart
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup} (M : FuchsianAxisModel D f)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A=q*f*q⁻¹)
    (hAn : Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) :
    q.val '' M.carrier=Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier := by
  let p:=q*D.halfPlaneNormalizer⁻¹
  have hp : p.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    calc
      _=q.val '' (D.halfPlaneNormalizer⁻¹.val '' Hyperbolic.openHalfPlaneSet) := by
        rw [image_image]
        rfl
      _=q.val '' D.carrier := by
        rw [←D.halfPlaneNormalizer_image]
        change q.val '' (D.halfPlaneNormalizer.val.symm '' (D.halfPlaneNormalizer.val '' D.carrier))=_
        rw [D.halfPlaneNormalizer.val.symm_image_image]
      _=Hyperbolic.openHalfPlaneSet := hq
  obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL p hp
  let C:=B*M.matrix*B⁻¹
  have hC : Hyperbolic.realSLMobius C=Hyperbolic.realSLMobius A := by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv,hB,M.projection,hA]
    dsimp only [p]
    group
  have hCn : Hyperbolic.realSLMobius C≠1:=hC ▸ hAn
  have hCt : 4<(Matrix.trace C.val)^2 :=
    (Hyperbolic.realSLMobius_hyperbolic_iff C hCn).mp (hC ▸ (Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mpr ht)
  have he : Hyperbolic.hHyperbolicAxis C hCn hCt=Hyperbolic.hHyperbolicAxis A hAn ht :=
    hHyperbolicAxis_eq_of_realSLMobius_eq C A hCn hAn hCt ht hC
  have him : q.val '' M.carrier=p.val '' M.nativeCarrier := by
    rw [←M.carrier_image,image_image]
    change q.val '' M.carrier=(fun z=>p.val (D.halfPlaneNormalizer.val z)) '' M.carrier
    congr 1
    funext z
    change q • z=(q*D.halfPlaneNormalizer⁻¹) • (D.halfPlaneNormalizer • z)
    simp only [mul_smul,inv_smul_smul]
  rw [him,←hB]
  change (Hyperbolic.realSLMobius B).val '' nativeHyperbolicAxisSphere M.matrix
    ((Hyperbolic.realSLMobius_hyperbolic_iff M.matrix M.nontrivial).mpr M.trace_gt)=_
  rw [←nativeHyperbolicAxisSphere_conjugation]
  change Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis C hCn hCt).carrier=_
  rw [he]

/-- A genuine boundary hyperbolic has a stable actual full axis in its
original disc, with elliptic elements elsewhere in the group allowed. -/
theorem boundaryHyperbolic_axis_stable
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    (hNE : DiscreteGroups.IsNonElementary H)
    {f : H}
    (hf : IsBoundaryHyperbolic D f)
    (M : FuchsianAxisModel D f.val) : Surfaces.MobiusStableSet H M.carrier := by
  let q:=D.nielsenArcNormalizer hNE
  have hq:=D.nielsenArcNormalizer_image hNE
  have hinf:=D.nielsenArcNormalizer_limit hNE
  have hpres : (q*f.val*q⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    rw [←hq,Mobius.stableAxis_conjugate_image,q.val.injective.image_injective.eq_iff]
    exact D.image_eq f
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  have hAH : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A) := by
    rw [hA]
    exact Mobius.mobiusHyperbolic_conjugation_forward _ q hf.hyperbolic
  have hAn:=hAH.1.1
  have ht:=(Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAH
  apply (mobiusStableSet_conjugation H M.carrier q).mp
  rw [boundary_axis_carrier_image_in_chart M q hq A hA hAn ht]
  exact boundaryHyperbolic_normalized_axis_stable D hNE q hq hinf f hf A hA hAn ht

/-- An actual endpoint exchange preserving the true imaginary geodesic has negative real reciprocal multiplier. -/
theorem boundaryAxis_exchange_negative_reciprocal (f : Mobius.complexMobiusGroup)
    (hL : f.val '' Hyperbolic.extendedImaginaryAxis = Hyperbolic.extendedImaginaryAxis)
    (hz : f.val (0 : ℂ) = ∞) (hi : f.val ∞ = (0 : ℂ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ≠ 0 →  f.val z = ((-(r : ℂ) * z⁻¹ : ℂ) : Mobius.ExtendedComplex) := by
  have hp : f ∈ DiscreteGroups.mobiusZeroInftyPairStabilizer := by
    change f.val '' ({((0 : ℂ) : Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex) = _
    simp only [Set.image_insert_eq,Set.image_singleton,hz,hi,Set.pair_comm]
  obtain ⟨a,ha | ha⟩ := DiscreteGroups.mobius_zeroInftyPair_normal_form ⟨f,hp⟩
  · change f = Mobius.mobiusScaling a at ha
    rw [ha,DiscreteGroups.mobiusScaling_zero] at hz
    exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ)) hz)
  · change f = Mobius.mobiusScaling a * DiscreteGroups.mobiusReciprocal at ha
    have hI : ((Complex.I : ℂ) : Mobius.ExtendedComplex) ∈ Hyperbolic.extendedImaginaryAxis := by
      refine ⟨0, ?_⟩
      simp [Hyperbolic.extendedHalfPlanePoint, Hyperbolic.imaginaryAxisParam_coe]
    have hFI : f.val ((Complex.I : ℂ) : Mobius.ExtendedComplex) ∈ Hyperbolic.extendedImaginaryAxis :=
      hL ▸ ⟨_, hI, rfl⟩
    obtain ⟨t,ht⟩ := hFI
    rw [ha] at ht
    have he : (Real.exp t : ℂ) * Complex.I = (a : ℂ) * (-Complex.I) := by
      change Hyperbolic.extendedHalfPlanePoint (Hyperbolic.imaginaryAxisParam t) =
        (Mobius.mobiusScaling a).val (DiscreteGroups.mobiusReciprocal.val (Complex.I : ℂ)) at ht
      rw [DiscreteGroups.mobiusReciprocal_coe Complex.I Complex.I_ne_zero,Mobius.mobiusScaling_coe] at ht
      simpa only [Hyperbolic.extendedHalfPlanePoint,Hyperbolic.imaginaryAxisParam_coe,Complex.inv_I] using OnePoint.coe_injective ht
    have har : (a : ℂ) = -(Real.exp t : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      calc
        (a : ℂ) * Complex.I = -((a : ℂ) * (-Complex.I)) := by ring
        _ = -((Real.exp t : ℂ) * Complex.I) := by rw [he]
        _ = -(Real.exp t : ℂ) * Complex.I := by ring
    refine ⟨Real.exp t,Real.exp_pos t,?_⟩
    intro z hzn
    rw [ha]
    change (Mobius.mobiusScaling a).val (DiscreteGroups.mobiusReciprocal.val z) = _
    rw [DiscreteGroups.mobiusReciprocal_coe z hzn,Mobius.mobiusScaling_coe,har]

/-- A true invariant nonempty subset lying strictly on one side of the imaginary geodesic rules out endpoint exchange. -/
theorem boundaryAxis_endpoints_fixed_of_invariant_side
    (f : Mobius.complexMobiusGroup)
    (hH : f.val '' Hyperbolic.openHalfPlaneSet = Hyperbolic.openHalfPlaneSet)
    (hL : f.val '' Hyperbolic.extendedImaginaryAxis = Hyperbolic.extendedImaginaryAxis)
    (S : Set ℍ) (hne : S.Nonempty)
    (hside : (∀ z ∈ S, 0 < z.re) ∨ (∀ z ∈ S, z.re < 0))
    (hS : f.val '' (Hyperbolic.extendedHalfPlanePoint '' S) = Hyperbolic.extendedHalfPlanePoint '' S) :
    f.val (0 : ℂ) = (0 : ℂ) ∧ f.val ∞ = ∞ := by
  rcases DiscreteGroups.mobius_zeroInftyPair_cases ⟨f,Surfaces.stableAxis_mobius_endpoints_preserved f hH
    hL⟩ with hfix | hswap
  · exact hfix
  · change f.val (0 : ℂ) = ∞ ∧ f.val ∞ = (0 : ℂ) at hswap
    obtain ⟨r,hr,hformula⟩ := boundaryAxis_exchange_negative_reciprocal f hL hswap.1 hswap.2
    obtain ⟨z,hz⟩ := hne
    have hFz : f.val (Hyperbolic.extendedHalfPlanePoint z) ∈ Hyperbolic.extendedHalfPlanePoint '' S := by
      rw [←hS]
      exact mem_image_of_mem _ (mem_image_of_mem _ hz)
    obtain ⟨w,hw,he⟩ := hFz
    have hzn : (z : ℂ) ≠ 0 := z.ne_zero
    have hc : (w : ℂ) = -(r : ℂ) * (z : ℂ)⁻¹ := by
      apply OnePoint.coe_injective
      exact he.trans (hformula z hzn)
    have hre : w.re = -r * z.re / Complex.normSq (z : ℂ) := by
      rw [show w.re = (w : ℂ).re from rfl,hc]
      simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.inv_re,
        Complex.neg_im,Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
      rw [UpperHalfPlane.coe_re]
      ring
    have hnorm : 0 < Complex.normSq (z : ℂ) := Complex.normSq_pos.mpr hzn
    rcases hside with hpos | hneg
    · have hzp := hpos z hz
      have hwp := hpos w hw
      have hright : -r * z.re / Complex.normSq (z : ℂ) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) hzp) hnorm
      linarith
    · have hzp := hneg z hz
      have hwp := hneg w hw
      have hright : 0 < -r * z.re / Complex.normSq (z : ℂ) :=
        div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hr) hzp) hnorm
      linarith

/-- Elliptics anywhere else in the group impose no restriction: this conclusion only uses the actual invariant one-sided set for this axis stabilizer element. -/
theorem boundaryAxis_not_elliptic_of_invariant_side
    (f : Mobius.complexMobiusGroup)
    (hH : f.val '' Hyperbolic.openHalfPlaneSet = Hyperbolic.openHalfPlaneSet)
    (hL : f.val '' Hyperbolic.extendedImaginaryAxis = Hyperbolic.extendedImaginaryAxis)
    (S : Set ℍ) (hne : S.Nonempty)
    (hside : (∀ z ∈ S, 0 < z.re) ∨ (∀ z ∈ S, z.re < 0))
    (hS : f.val '' (Hyperbolic.extendedHalfPlanePoint '' S) = Hyperbolic.extendedHalfPlanePoint '' S) :
    ¬Mobius.MobiusElliptic f := by
  intro hf
  have hi := (boundaryAxis_endpoints_fixed_of_invariant_side f hH hL S hne hside hS).2
  apply Mobius.mobiusElliptic_fixed_not_mem_disc_frontier f hf Hyperbolic.openHalfPlaneSet_isComplexOpenDisc hH hi
  rw [nielsen_openHalfPlane_frontier]
  simp [Hyperbolic.halfPlaneIdealBoundary]


/-- In the genuine half-plane chart, every element of the full boundary
axis stabilizer is nonelliptic. The invariant one-sided set used here is
the independently constructed actual Nielsen region. -/
theorem boundaryHyperbolic_normalized_axis_stabilizer_no_elliptics
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hinf : (∞:OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (f : H) (hf : IsBoundaryHyperbolic D f)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A=q*f.val*q⁻¹)
    (hAn : Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2)
    (g : Mobius.complexMobiusGroup)
    (hg : g∈DiscreteGroups.Action.Actions.subgroupConjugate q H)
    (hgL : g.val '' (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier)=
      Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier) : ¬Mobius.MobiusElliptic g := by
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate q H
  let Λ:=DiscreteGroups.mobiusLimitSet K
  let N:=Hyperbolic.nielsenHalfPlaneArcRegion Λ
  obtain ⟨G,hGF,hGA⟩ := boundaryHyperbolic_normalized_gap D hNE q hq hinf f hf A hA hAn ht
  have hGArc : Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈Hyperbolic.nielsenHalfPlaneArcFamily Λ := by
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨G.carrier,hGF,rfl⟩
  have hN : N.Nonempty :=
    (D.nielsenConjugate q).nielsenHalfPlaneArcRegion_nonempty hq (hNE.conjugation q) hinf
  have hsub : N⊆G.keptSide:=fun z hz=>hz G hGArc
  have hNInv : g.val '' (Hyperbolic.extendedHalfPlanePoint '' N)=Hyperbolic.extendedHalfPlanePoint '' N := by
    have hi:=(D.nielsenConjugate q).nielsenHalfPlaneArcRegion_invariant hq (hNE.conjugation q) hinf
    apply subset_antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact hi ⟨g,hg⟩ p hp
    · intro p hp
      refine ⟨g⁻¹.val p,hi ⟨g⁻¹,K.inv_mem hg⟩ p hp,?_⟩
      exact g.val.apply_symm_apply p
  obtain ⟨s,k,hk,hk1,hAxis,_hT,_hact⟩ := Hyperbolic.hHyperbolicAxis_normalizer A hAn ht
  have hline : (fun z : ℍ=>s • z) '' G.line.carrier=(Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    rw [hGA,hAxis]
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hz
      refine ⟨s⁻¹ • z,?_,smul_inv_smul _ _⟩
      change (s • (s⁻¹ • z)).re=0
      simpa only [smul_inv_smul] using (show z.re=0 from hz)
  obtain ⟨w,hw⟩ := hN
  have hwG:=hsub hw
  have hwNot : w∉G.line.carrier:=fun h=>Set.disjoint_left.mp G.keptSide_disjoint_line hwG h
  have hsNot : (s • w).re≠0 := by
    intro he
    have hh : s • w∈(fun z : ℍ=>s • z) '' G.line.carrier := by rw [hline];exact he
    obtain ⟨v,hv,hvEq⟩ := hh
    exact hwNot ((isometry_smul ℍ s).injective hvEq ▸ hv)
  let S:=(fun z : ℍ=>s • z) '' N
  have hS : S.Nonempty:=⟨s • w,mem_image_of_mem _ hw⟩
  have hside : (∀z∈S,0<z.re) ∨ (∀z∈S,z.re<0) := by
    have hc : (fun z : ℍ=>s • z) '' G.keptSide=Hyperbolic.openHHalfPlane (.vertical 0) (s • w) := by
      rw [G.keptSide_eq_openHalfPlane w hwG]
      exact Hyperbolic.realGL_image_openHalfPlane (Matrix.SpecialLinearGroup.mapGL ℝ s) _ _ hline w hwNot
    have hSS : S⊆Hyperbolic.openHHalfPlane (.vertical 0) (s • w):=hc ▸ image_mono hsub
    rcases lt_or_gt_of_ne hsNot with hn|hp
    · right
      rw [Hyperbolic.hReCutLt_eq_openHalfPlane 0 (s • w) hn] at hSS
      exact hSS
    · left
      rw [Hyperbolic.openHHalfPlane_vertical_gt 0 (s • w) hp] at hSS
      exact hSS
  let b:=Hyperbolic.realSLMobius s
  have hbH : b.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := realSLMobius_image_openHalfPlane s
  have hbL : b.val '' (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier)=
      Hyperbolic.extendedImaginaryAxis := by
    rw [Hyperbolic.halfPlaneSpherePoint_image_realSL,←hGA,hline]
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨Real.log z.im,?_⟩
      change Hyperbolic.extendedHalfPlanePoint (Hyperbolic.imaginaryAxisParam (Real.log
        z.im))=Hyperbolic.extendedHalfPlanePoint z
      apply congrArg Hyperbolic.extendedHalfPlanePoint
      apply UpperHalfPlane.ext_re_im
      · exact (show z.re=0 from hz).symm
      · exact Real.exp_log z.im_pos
    · rintro ⟨t,rfl⟩
      exact ⟨Hyperbolic.imaginaryAxisParam t,rfl,rfl⟩
  have hbN : b.val '' (Hyperbolic.extendedHalfPlanePoint '' N)=Hyperbolic.extendedHalfPlanePoint '' S := by
    rw [Hyperbolic.halfPlaneSpherePoint_image_realSL]
  have hgH : g.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    obtain ⟨a,ha,rfl⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H g).mp hg
    rw [←hq,Mobius.stableAxis_conjugate_image,q.val.injective.image_injective.eq_iff]
    exact D.image_eq ⟨a,ha⟩
  have hconjH : (b*g*b⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    simpa only [hbH,hgH] using Mobius.stableAxis_conjugate_image b g Hyperbolic.openHalfPlaneSet
  have hconjL : (b*g*b⁻¹).val '' Hyperbolic.extendedImaginaryAxis=Hyperbolic.extendedImaginaryAxis := by
    simpa only [hbL,hgL] using Mobius.stableAxis_conjugate_image b g
      (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier)
  have hconjN : (b*g*b⁻¹).val '' (Hyperbolic.extendedHalfPlanePoint '' S)=Hyperbolic.extendedHalfPlanePoint '' S := by
    simpa only [hbN,hNInv] using Mobius.stableAxis_conjugate_image b g (Hyperbolic.extendedHalfPlanePoint '' N)
  exact fun he=>boundaryAxis_not_elliptic_of_invariant_side _ hconjH hconjL S hS hside hconjN
    ((Mobius.mobiusElliptic_conjugation g b).mpr he)

/-- The actual full axis stabilizer contains no elliptics even when the
whole original Fuchsian group does contain elliptic elements. -/
theorem boundaryHyperbolic_axis_stabilizer_no_elliptics
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    (hNE : DiscreteGroups.IsNonElementary H)
    {f : H}
    (hf : IsBoundaryHyperbolic D f)
    (M : FuchsianAxisModel D f.val)
    (g : Mobius.complexMobiusGroup) (hg : g∈Surfaces.mobiusSetStabilizer H M.carrier) : ¬Mobius.MobiusElliptic g := by
  let q:=D.nielsenArcNormalizer hNE
  have hq:=D.nielsenArcNormalizer_image hNE
  have hinf:=D.nielsenArcNormalizer_limit hNE
  have hpres : (q*f.val*q⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    rw [←hq,Mobius.stableAxis_conjugate_image,q.val.injective.image_injective.eq_iff]
    exact D.image_eq f
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  have hAH : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A) := by
    rw [hA]
    exact Mobius.mobiusHyperbolic_conjugation_forward _ q hf.hyperbolic
  have hAn:=hAH.1.1
  have ht:=(Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAH
  have hgq : q*g*q⁻¹∈DiscreteGroups.Action.Actions.subgroupConjugate q H:=
    (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g,hg.1,rfl⟩
  have hgL : (q*g*q⁻¹).val '' (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier)=
      Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hAn ht).carrier := by
    rw [←boundary_axis_carrier_image_in_chart M q hq A hA hAn ht]
    have hgS : g.val '' M.carrier=M.carrier:=(Surfaces.mem_mobiusSetStabilizer H M.carrier g).mp hg |>.2
    simpa only [hgS] using Mobius.stableAxis_conjugate_image q g M.carrier
  exact fun he=>boundaryHyperbolic_normalized_axis_stabilizer_no_elliptics
    D hNE q hq hinf f hf A hA hAn ht (q*g*q⁻¹) hgq hgL
    ((Mobius.mobiusElliptic_conjugation g q).mpr he)

/-- The full actual boundary-axis stabilizer is generated by a genuine
hyperbolic element, and its actual orbit quotient is a circle. -/
theorem boundaryHyperbolic_axis_quotient_circle
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    (hNE : DiscreteGroups.IsNonElementary H)
    {f : H}
    (hf : IsBoundaryHyperbolic D f)
    (M : FuchsianAxisModel D f.val) :
    (∃g : Mobius.complexMobiusGroup,Mobius.MobiusHyperbolic g ∧
      Surfaces.mobiusSetStabilizer H M.carrier=Subgroup.zpowers g) ∧
      Nonempty (SphereSetOrbitQuotient H M.carrier ≃ₜ Circle) := by
  let K:=Surfaces.mobiusSetStabilizer H M.carrier
  let S:=stabilizerStableSubset D.domain M.carrier M.carrier_subset_domain
  have hKH : K≤H:=Surfaces.mobiusSetStabilizer_le H M.carrier
  have hfK : f.val∈K:=⟨f.property,M.carrier_invariant⟩
  have hH : ∀g∈DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer K,
      g.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    intro g hg
    obtain ⟨a,ha,rfl⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff D.halfPlaneNormalizer K g).mp hg
    exact D.normalizedGroup_preserves_halfPlane _
      ((DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff D.halfPlaneNormalizer H _).mpr ⟨a,hKH ha,rfl⟩)
  have hmem : Hyperbolic.realSLMobius M.matrix∈DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer K := by
    rw [M.projection]
    exact (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff D.halfPlaneNormalizer K _).mpr ⟨f.val,hfK,rfl⟩
  obtain ⟨⟨g,hg,hgen⟩,⟨C⟩⟩ := stableSubset_axis_quotient_circle S
    (restrictMobiusDomain_discontinuous D.domain K hKH D.discontinuous)
    (boundaryHyperbolic_axis_stabilizer_no_elliptics hNE hf M)
    D.halfPlaneNormalizer hH M.matrix M.nontrivial M.trace_gt M.carrier_image hmem
  have hSK : S.stabilizer=K:=stabilizerStableSubset_stabilizer D.domain M.carrier _
  exact ⟨⟨g,hg,hSK.symm.trans hgen⟩,
    ⟨(stabilizerStableSubset_quotientHomeomorph D.domain M.carrier _).symm.trans C⟩⟩

/-- The circle made from the true complete boundary axis embeds naturally
in the original whole-group quotient, with its literal projection map. -/
theorem boundaryHyperbolic_axis_embedded_circle
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    (hNE : DiscreteGroups.IsNonElementary H)
    {f : H}
    (hf : IsBoundaryHyperbolic D f)
    (M : FuchsianAxisModel D f.val) :
    ∃C : SphereSetOrbitQuotient H M.carrier ≃ₜ Circle,
      Topology.IsEmbedding (sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain ∘ C.symm) ∧
      ∀p : M.carrier,
        (sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain ∘ C.symm)
          (C (_root_.Quotient.mk _ p))=Surfaces.mobiusDiscDomainProjection D.domain M.carrier M.carrier_subset_domain p := by
  obtain ⟨_,⟨C⟩⟩ := boundaryHyperbolic_axis_quotient_circle hNE hf M
  have hstable:=boundaryHyperbolic_axis_stable hNE hf M
  let : CompactSpace (SphereSetOrbitQuotient H M.carrier):=C.symm.compactSpace
  let : T2Space (Surfaces.MobiusDomainQuotient D.domain):=Surfaces.mobiusDomainQuotient_t2 D.domain D.discontinuous
  have he : Topology.IsEmbedding (sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain) :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (sphereSetOrbitMap_continuous D.domain M.carrier M.carrier_subset_domain)
      (sphereSetOrbitMap_injective_of_stable D.domain M.carrier M.carrier_subset_domain hstable)
      (sphereSetOrbitMap_continuous D.domain M.carrier M.carrier_subset_domain).isClosedMap).isEmbedding
  refine ⟨C,he.comp C.symm.isEmbedding,?_⟩
  intro p
  simp only [Function.comp_apply,Homeomorph.symm_apply_apply]
  rfl

/-- An original group element commuting with the actual hyperbolic element
preserves its entire actual original-disc axis. -/
theorem boundary_axis_invariant_of_commute
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    {f : Mobius.complexMobiusGroup} (M : FuchsianAxisModel D f)
    (g : Mobius.complexMobiusGroup) (hg : g∈H) (hcomm : Commute g f) :
    g.val '' M.carrier=M.carrier := by
  let q:=D.halfPlaneNormalizer
  obtain ⟨B,hB⟩ := D.normalizedGroup_exists_realSL (q*g*q⁻¹)
    ((DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g,hg,rfl⟩)
  let C:=B*M.matrix*B⁻¹
  have hconj : g*f*g⁻¹=f := by
    rw [hcomm.eq,mul_assoc,mul_inv_cancel,mul_one]
  have hC : Hyperbolic.realSLMobius C=Hyperbolic.realSLMobius M.matrix := by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv,hB,M.projection]
    change (q*g*q⁻¹)*(q*f*q⁻¹)*(q*g*q⁻¹)⁻¹=q*f*q⁻¹
    calc
      _=q*(g*f*g⁻¹)*q⁻¹ := by group
      _=q*f*q⁻¹ := by rw [hconj]
  have hCH : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius C) :=
    hC ▸ (Hyperbolic.realSLMobius_hyperbolic_iff M.matrix M.nontrivial).mpr M.trace_gt
  have hCt:=(Hyperbolic.realSLMobius_hyperbolic_iff C hCH.1.1).mp hCH
  have he:=hHyperbolicAxis_eq_of_realSLMobius_eq C M.matrix hCH.1.1 M.nontrivial
    hCt M.trace_gt hC
  have hn : (q*g*q⁻¹).val '' M.nativeCarrier=M.nativeCarrier := by
    rw [←hB]
    change (Hyperbolic.realSLMobius B).val '' nativeHyperbolicAxisSphere M.matrix
      ((Hyperbolic.realSLMobius_hyperbolic_iff M.matrix M.nontrivial).mpr M.trace_gt)=_
    rw [←nativeHyperbolicAxisSphere_conjugation]
    change Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis C hCH.1.1 hCt).carrier=M.nativeCarrier
    rw [he]
    rfl
  have him:=Mobius.stableAxis_conjugate_image q g M.carrier
  rw [M.carrier_image] at him
  exact q.val.injective.image_injective (him.symm.trans (hn.trans M.carrier_image.symm))

/-- The actual full stabilizer of a boundary axis is a maximal cyclic
subgroup of the original group, without an ambient elliptic exclusion. -/
theorem boundaryHyperbolic_axis_stabilizer_maximalCyclic
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    (hNE : DiscreteGroups.IsNonElementary H)
    {f : H}
    (hf : IsBoundaryHyperbolic D f)
    (M : FuchsianAxisModel D f.val) :
    IsMaximalCyclicIn H (Surfaces.mobiusSetStabilizer H M.carrier) := by
  obtain ⟨⟨g,_hg,hgen⟩,_⟩ := boundaryHyperbolic_axis_quotient_circle hNE hf M
  have hcyc : IsCyclic (Surfaces.mobiusSetStabilizer H M.carrier) := by
    rw [hgen]
    infer_instance
  refine ⟨Surfaces.mobiusSetStabilizer_le H M.carrier,hcyc,?_⟩
  intro L hLH hLc hKL
  apply le_antisymm _ hKL
  intro a ha
  refine ⟨hLH ha,?_⟩
  exact boundary_axis_invariant_of_commute M a (hLH ha)
    (cyclic_mobius_commute L hLc a f.val ha (hKL ⟨f.property,M.carrier_invariant⟩))

/-- At either genuine hyperbolic ideal fixed point, the full point
stabilizer equals the full actual boundary-axis stabilizer. -/
theorem boundaryHyperbolic_axis_stabilizer_eq_endpoint_stabilizer
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    (hNE : DiscreteGroups.IsNonElementary H)
    {f : H}
    (hf : IsBoundaryHyperbolic D f)
    (M : FuchsianAxisModel D f.val)
    (ξ : Mobius.ExtendedComplex)
    (hfix : f.val.val ξ=ξ) :
    Surfaces.mobiusSetStabilizer H M.carrier=DiscreteGroups.mobiusBoundaryStabilizer H ξ :=
  maximalCyclic_eq_boundaryStabilizer_of_fixed D _
    (boundaryHyperbolic_axis_stabilizer_maximalCyclic hNE hf M)
    f.val ⟨f.property,M.carrier_invariant⟩ hf.hyperbolic.1.1 ξ hfix

/-- A boundary hyperbolic in the actual original group produces its full
cyclic boundary-axis quotient and a naturally embedded physical circle in
the actual whole-domain quotient. No elliptic-free hypothesis is used. -/
theorem boundaryHyperbolic_original_boundary_loop
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (f : H)
    (hf : IsBoundaryHyperbolic D f) :
    ∃M : FuchsianAxisModel D f.val,
      Surfaces.MobiusStableSet H M.carrier ∧
      IsMaximalCyclicIn H (Surfaces.mobiusSetStabilizer H M.carrier) ∧
      (∀ξ : Mobius.ExtendedComplex,f.val.val ξ=ξ →
        Surfaces.mobiusSetStabilizer H M.carrier=DiscreteGroups.mobiusBoundaryStabilizer H ξ) ∧
      ∃C : SphereSetOrbitQuotient H M.carrier ≃ₜ Circle,
        Topology.IsEmbedding (sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain ∘ C.symm) ∧
        Set.range (sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain ∘ C.symm)=
          Set.range (Surfaces.mobiusDiscDomainProjection D.domain M.carrier M.carrier_subset_domain) ∧
        ∀p : M.carrier,
          (sphereSetOrbitMap D.domain M.carrier M.carrier_subset_domain ∘ C.symm)
            (C (_root_.Quotient.mk _ p))=
            Surfaces.mobiusDiscDomainProjection D.domain M.carrier M.carrier_subset_domain p := by
  obtain ⟨M⟩ := D.axisModel_exists f.val f.property hf.hyperbolic
  obtain ⟨C,he,hπ⟩ := boundaryHyperbolic_axis_embedded_circle hNE hf M
  refine ⟨M,boundaryHyperbolic_axis_stable hNE hf M,
    boundaryHyperbolic_axis_stabilizer_maximalCyclic hNE hf M,
    boundaryHyperbolic_axis_stabilizer_eq_endpoint_stabilizer hNE hf M,C,he,?_,hπ⟩
  rw [Set.range_comp,C.symm.surjective.range_eq,image_univ]
  exact sphereSetOrbitMap_range D.domain M.carrier M.carrier_subset_domain


/-- The actual boundary-line family is locally finite in the original domain. -/
theorem nielsenBoundary_original_lines_locallyFinite
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    LocallyFinite (fun L : nielsenBoundaryDiscLineFamily P hNE =>
      P.finiteCoordinate.symm '' L.val.carrier) := by
  classical
  intro x
  obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
  have hf := nielsenBoundaryDiscLineFamily_compact_hits_finite P hNE K hK
  refine ⟨K,hxK,?_⟩
  apply (hf.preimage (f:=fun L : nielsenBoundaryDiscLineFamily P hNE => L.val)
    Subtype.val_injective.injOn).subset
  rintro L ⟨y,⟨z,hz,rfl⟩,hyK⟩
  exact ⟨L.property,z,hz,P.finiteCoordinate.symm z,hyK,P.finiteCoordinate.apply_symm_apply z⟩

/-- Every complete native line contained in the actual frontier is one of its genuine gap lines. -/
theorem nielsenBoundary_full_line_mem_family
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (L : Hyperbolic.DiscLine)
    (hL : L.carrier ⊆ P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE)) :
    L ∈ nielsenBoundaryDiscLineFamily P hNE := by
  classical
  let S := P.finiteCoordinate.symm '' L.carrier
  have hconn : IsPreconnected S := L.hConvex.isPreconnected.image _ P.finiteCoordinate.symm.continuous.continuousOn
  obtain ⟨z,w,hz,hw,hzw⟩ := L.toHalfPlane.exists_two_points
  have hzL : Hyperbolic.halfPlaneToDisc z ∈ L.carrier := by
    rw [Hyperbolic.DiscLine.mem_carrier,Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    exact hz
  have hxF := hL hzL
  rw [nielsenBoundaryDiscLineFamily_frontier_cover P hNE] at hxF
  obtain ⟨M,hh⟩ := mem_iUnion.mp hxF
  obtain ⟨hM,hxM⟩ := mem_iUnion.mp hh
  let I := nielsenBoundaryDiscLineFamily P hNE
  let C : I →  Set P.domain.carrier := fun N => P.finiteCoordinate.symm '' N.val.carrier
  let m : I := ⟨M,hM⟩
  have hlf : LocallyFinite C := nielsenBoundary_original_lines_locallyFinite P hNE
  have hclosed : ∀N : I, IsClosed (C N) := fun N => P.finiteCoordinate.symm.isClosedMap _ N.val.isClosed_carrier
  have hother : IsClosed (⋃N : {N:I // N≠m},C N.val) :=
    (hlf.comp_injective (Subtype.val_injective (p:=fun N:I => N≠m))).isClosed_iUnion (fun N => hclosed N.val)
  have hcover : S ⊆ C m ∪ ⋃N : {N:I // N≠m},C N.val := by
    rintro y ⟨v,hv,rfl⟩
    have hvF := hL hv
    rw [nielsenBoundaryDiscLineFamily_frontier_cover P hNE] at hvF
    obtain ⟨N,hh⟩ := mem_iUnion.mp hvF
    obtain ⟨hN,hvN⟩ := mem_iUnion.mp hh
    by_cases he : (⟨N,hN⟩:I)=m
    · left
      have hCN : C ⟨N,hN⟩=C m := congrArg C he
      rw [←hCN]
      exact ⟨v,hvN,rfl⟩
    · right
      exact mem_iUnion.mpr ⟨⟨⟨N,hN⟩,he⟩,v,hvN,rfl⟩
  have hdisj : Disjoint (C m) (⋃N : {N:I // N≠m},C N.val) := by
    apply disjoint_left.mpr
    rintro y hy hm
    obtain ⟨N,hN⟩ := mem_iUnion.mp hm
    obtain ⟨u,hu,huEq⟩ := hy
    obtain ⟨v,hv,hvEq⟩ := hN
    have heuv : u=v := P.finiteCoordinate.symm.injective (huEq.trans hvEq.symm)
    have hd := nielsenBoundaryDiscLineFamily_pairwise_disjoint P hNE m.property N.val.property
      (fun he => N.property (Subtype.ext he.symm))
    exact disjoint_left.mp hd hu (heuv.symm ▸ hv)
  have hsub : S ⊆ C m := by
    intro y hy
    by_contra hyn
    have hyo := (hcover hy).resolve_left hyn
    obtain ⟨v,_hvS,hvM,hvO⟩ := isPreconnected_closed_iff.mp hconn (C m)
      (⋃N : {N:I // N≠m},C N.val) (hclosed m) hother hcover
      ⟨P.finiteCoordinate.symm (Hyperbolic.halfPlaneToDisc z),⟨Hyperbolic.halfPlaneToDisc z,hzL,rfl⟩,
        Hyperbolic.halfPlaneToDisc z,hxM,rfl⟩ ⟨y,hy,hyo⟩
    exact disjoint_left.mp hdisj hvM hvO
  have hLM : L=M := by
    apply Hyperbolic.DiscLine.toHalfPlane_injective
    have hsubNative : L.carrier⊆M.carrier := by
      intro v hv
      obtain ⟨u,hu,huEq⟩ := hsub ⟨v,hv,rfl⟩
      exact P.finiteCoordinate.symm.injective huEq ▸ hu
    apply L.toHalfPlane.eq_of_two_points M.toHalfPlane hzw hz hw
    · simpa only [Hyperbolic.discToHalfPlane_halfPlaneToDisc] using
        (Hyperbolic.DiscLine.mem_carrier M (Hyperbolic.halfPlaneToDisc z)).mp (hsubNative hzL)
    · have hwL : Hyperbolic.halfPlaneToDisc w∈L.carrier := by
        rw [Hyperbolic.DiscLine.mem_carrier,Hyperbolic.discToHalfPlane_halfPlaneToDisc]
        exact hw
      simpa only [Hyperbolic.discToHalfPlane_halfPlaneToDisc] using
        (Hyperbolic.DiscLine.mem_carrier M (Hyperbolic.halfPlaneToDisc w)).mp (hsubNative hwL)
  exact hLM ▸ hM

/-- The original group permutes complete ordinary-gap boundary lines. -/
theorem nielsenBoundary_original_line_image
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (L : Hyperbolic.DiscLine)
    (hL : L∈nielsenBoundaryDiscLineFamily P hNE) (g : H) :
    ∃M∈nielsenBoundaryDiscLineFamily P hNE,
      g • (P.finiteCoordinate.symm '' L.carrier)=P.finiteCoordinate.symm '' M.carrier := by
  obtain ⟨M,hM⟩ := Hyperbolic.disc_isometry_image_hLine (P.discAction_isometry g) L
  have hMF : M.carrier⊆P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE) := by
    intro z hz
    rw [←hM] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    obtain ⟨x,hx,hxu⟩ := nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hu
    have hxg : g • x∈frontier (fuchsianNielsenCore P hNE) := by
      rw [←fuchsianNielsenCore_smul_frontier P hNE g]
      exact ⟨x,hx,rfl⟩
    refine ⟨g • x,hxg,?_⟩
    change P.finiteCoordinate (g • x)=P.finiteCoordinate (g • P.finiteCoordinate.symm u)
    rw [←hxu,P.finiteCoordinate.symm_apply_apply]
  refine ⟨M,nielsenBoundary_full_line_mem_family P hNE M hMF,?_⟩
  apply P.finiteCoordinate.injective.image_injective
  rw [P.discAction_image]
  simpa only [image_image,Homeomorph.apply_symm_apply,Set.image_id'] using hM

/-- A genuine complete native geodesic is noncompact in the physical disc. -/
theorem nielsenBoundary_original_line_not_compact
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (L : Hyperbolic.DiscLine) :
    ¬IsCompact (P.finiteCoordinate.symm '' L.carrier) := by
  let := Hyperbolic.discHyperbolicMetric
  intro hc
  have hcD : IsCompact L.carrier := P.finiteCoordinate.symm.isCompact_image.mp hc
  have hcH : IsCompact L.toHalfPlane.carrier := by
    have he : Hyperbolic.discToHalfPlane '' L.carrier=L.toHalfPlane.carrier := by
      rw [L.carrier_eq_cayley_image_halfPlane,image_image]
      simp only [Hyperbolic.discToHalfPlane_halfPlaneToDisc,Set.image_id']
    rw [←he]
    exact hcD.image Hyperbolic.inverse_cayley_isometry.continuous
  obtain ⟨γ,hγ,hrange⟩ := L.toHalfPlane.exists_isometric_param
  have hcR : IsCompact (univ:Set ℝ) := by
    have h := hγ.isClosedEmbedding.isCompact_preimage hcH
    simpa only [←hrange,preimage_range] using h
  exact noncompact_univ ℝ hcR
/-- Compact original polygon pieces and the finite true active-line family force a
nonidentity element in every full ordinary-gap-line stabilizer. -/
theorem finitelyGenerated_nielsen_boundary_line_stabilizer_nontrivial_at
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (L : Hyperbolic.DiscLine) (hL : L∈nielsenBoundaryDiscLineFamily P hNE) :
    ∃g:H,g≠1 ∧ g • (P.finiteCoordinate.symm '' L.carrier)=P.finiteCoordinate.symm '' L.carrier := by
  classical
  let S (M : Hyperbolic.DiscLine) : Set P.domain.carrier := P.finiteCoordinate.symm '' M.carrier
  let A := {M:Hyperbolic.DiscLine | M∈nielsenBoundaryDiscLineFamily P hNE ∧
    (M.carrier∩P.finiteCoordinate '' closure (D∩fuchsianNielsenCore P hNE)).Nonempty}
  have hA : A.Finite := finite_nielsenCore_boundary_lines hD hNE
    (finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental) w hwD hwN
  by_contra hnone
  have htriv : ∀g:H,g • S L=S L→  g = 1 := by
    intro g hg
    by_contra hne
    exact hnone ⟨g,hne,hg⟩
  have hUnique : ∀M:Hyperbolic.DiscLine,∀g k:H,g • S M=S L→ k • S M=S L→ g=k := by
    intro M g k hg hk
    have hinv : k⁻¹ • S L=S M := by rw [←hk,inv_smul_smul]
    have hs : (g*k⁻¹) • S L=S L := by rw [mul_smul,hinv,hg]
    exact mul_inv_eq_one.mp (htriv (g*k⁻¹) hs)
  let R := {M:Hyperbolic.DiscLine | M∈A ∧ ∃g:H,g • S M=S L}
  have hR : R.Finite := hA.subset (fun _ h=>h.1)
  let : Fintype R := hR.fintype
  choose σ hσ using fun M:R=>M.property.2
  have hclip : ∀M:R,IsCompact (S M.val∩closure D) := by
    intro M
    have hc := nielsenUnpairedNativeCarrier_isCompact P hNE hFG hD M.val M.property.1.1
    apply P.finiteCoordinate.isEmbedding.isCompact_iff.mpr
    convert hc using 1
    dsimp [nielsenUnpairedNativeCarrier,S]
    rw [image_inter P.finiteCoordinate.injective]
    simp only [image_image,Homeomorph.apply_symm_apply,Set.image_id']
  let K : Set P.domain.carrier := ⋃M:R,σ M • (S M.val∩closure D)
  have hK : IsCompact K := isCompact_iUnion (fun M:R=>(hclip M).image (Homeomorph.smul (σ M)).continuous)
  have he : S L=K := by
    apply subset_antisymm
    · intro x hx
      have hcov : x∈⋃g:H,(fun y:P.domain.carrier=>g • y) '' closure D := by
        rw [hD.locallyFinite.fundamental.closure_cover]
        trivial
      obtain ⟨g,y,hyD,hgy⟩ := mem_iUnion.mp hcov
      change g • y=x at hgy
      obtain ⟨M,hM,hgM⟩ := nielsenBoundary_original_line_image P hNE L hL g⁻¹
      change g⁻¹ • S L=S M at hgM
      have hyM : y∈S M := by
        rw [←hgM]
        refine ⟨x,hx,?_⟩
        change g⁻¹ • x=y
        rw [←hgy,inv_smul_smul]
      have hyN : y∈frontier (fuchsianNielsenCore P hNE) := by
        obtain ⟨v,hv,hvy⟩ := hyM
        obtain ⟨u,hu,huv⟩ := nielsenBoundaryDiscLineFamily_subset_frontier P hNE M hM hv
        have huy : u=y := by
          apply P.finiteCoordinate.injective
          rw [huv,←hvy,P.finiteCoordinate.apply_symm_apply]
        exact huy ▸ hu
      have hyQ : y∈closure (D∩fuchsianNielsenCore P hNE) := by
        rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
        exact ⟨hyD,frontier_subset_closure hyN⟩
      have hMy : P.finiteCoordinate y∈M.carrier := by
        obtain ⟨v,hv,hvy⟩ := hyM
        simpa only [←hvy,P.finiteCoordinate.apply_symm_apply] using hv
      have hMA : M∈A := ⟨hM,P.finiteCoordinate y,hMy,y,hyQ,rfl⟩
      have hgimage : g • S M=S L := by rw [←hgM,smul_inv_smul]
      let m : R := ⟨M,hMA,g,hgimage⟩
      have hsig : σ m=g := hUnique M (σ m) g (hσ m) hgimage
      refine mem_iUnion.mpr ⟨m,?_⟩
      rw [hsig]
      exact ⟨y,⟨hyM,hyD⟩,hgy⟩
    · intro x hx
      obtain ⟨M,hxM⟩ := mem_iUnion.mp hx
      rw [←hσ M]
      exact Set.smul_set_mono inter_subset_left hxM
  have hc : IsCompact (S L) := by rw [he];exact hK
  exact nielsenBoundary_original_line_not_compact P L hc

/-- Every genuine Nielsen boundary line of the original finitely generated group
has a nontrivial actual full stabilizer, with no supplied periodicity or return word. -/
theorem finitelyGenerated_nielsen_boundary_line_stabilizer_nontrivial
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (L : Hyperbolic.DiscLine) (hL : L∈nielsenBoundaryDiscLineFamily P hNE) :
    ∃g:H,g≠1 ∧ g • (P.finiteCoordinate.symm '' L.carrier)=P.finiteCoordinate.symm '' L.carrier := by
  obtain ⟨w,hw,hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  exact finitelyGenerated_nielsen_boundary_line_stabilizer_nontrivial_at P hNE hFG
    (dirichletDomain_isConvexFuchsianPolygon P w hw) w (dirichletDomain_center_mem P w hw) hwN L hL


/-- A nonidentity stabilizer of a true ordinary-gap line is hyperbolic.
The genuine invariant Nielsen region, rather than an ellipse-free ambient group,
prevents the endpoint-flipping involution. -/
theorem nielsen_gap_line_stabilizer_hyperbolic
    {K : Subgroup Mobius.complexMobiusGroup} (E : FuchsianDisc K)
    (hE : E.carrier=Hyperbolic.openHalfPlaneSet)
    (hNE : DiscreteGroups.IsNonElementary K)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet K)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hGF : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet
      (DiscreteGroups.mobiusLimitSet K)))
    (g : K) (hgn : g≠1)
    (hgL : g.val.val '' (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)=
      Hyperbolic.extendedHalfPlanePoint '' G.line.carrier) : Mobius.MobiusHyperbolic g.val := by
  let Λ := DiscreteGroups.mobiusLimitSet K
  let N := Hyperbolic.nielsenHalfPlaneArcRegion Λ
  have hGArc : Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈Hyperbolic.nielsenHalfPlaneArcFamily Λ := by
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨G.carrier,hGF,rfl⟩
  have hN : N.Nonempty := E.nielsenHalfPlaneArcRegion_nonempty hE hNE hinf
  have hsub : N⊆G.keptSide := fun z hz=>hz G hGArc
  have hNInv : g.val.val '' (Hyperbolic.extendedHalfPlanePoint '' N)=Hyperbolic.extendedHalfPlanePoint '' N := by
    have hi := E.nielsenHalfPlaneArcRegion_invariant hE hNE hinf
    apply subset_antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact hi g p hp
    · intro p hp
      refine ⟨g⁻¹.val.val p,hi g⁻¹ p hp,?_⟩
      exact g.val.val.apply_symm_apply p
  obtain ⟨s,hs⟩ := G.line.exists_SL_normalizer
  have hline : (fun z : ℍ=>s • z) '' G.line.carrier=(Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    have h := congrArg Hyperbolic.HalfPlaneLine.carrier hs
    rw [G.line.realGLMap_carrier] at h
    exact h
  obtain ⟨w,hw⟩ := hN
  have hwG := hsub hw
  have hwNot : w∉G.line.carrier := fun h=>Set.disjoint_left.mp G.keptSide_disjoint_line hwG h
  have hsNot : (s • w).re≠0 := by
    intro he
    have hh : s • w∈(fun z : ℍ=>s • z) '' G.line.carrier := by rw [hline];exact he
    obtain ⟨v,hv,hvEq⟩ := hh
    exact hwNot ((isometry_smul ℍ s).injective hvEq ▸ hv)
  let S := (fun z : ℍ=>s • z) '' N
  have hS : S.Nonempty := ⟨s • w,mem_image_of_mem _ hw⟩
  have hside : (∀z∈S,0<z.re) ∨ (∀z∈S,z.re<0) := by
    have hc : (fun z : ℍ=>s • z) '' G.keptSide=Hyperbolic.openHHalfPlane (.vertical 0) (s • w) := by
      rw [G.keptSide_eq_openHalfPlane w hwG]
      exact Hyperbolic.realGL_image_openHalfPlane (Matrix.SpecialLinearGroup.mapGL ℝ s) _ _ hline w hwNot
    have hSS : S⊆Hyperbolic.openHHalfPlane (.vertical 0) (s • w) := hc ▸ image_mono hsub
    rcases lt_or_gt_of_ne hsNot with hn|hp
    · right
      rw [Hyperbolic.hReCutLt_eq_openHalfPlane 0 (s • w) hn] at hSS
      exact hSS
    · left
      rw [Hyperbolic.openHHalfPlane_vertical_gt 0 (s • w) hp] at hSS
      exact hSS
  let b := Hyperbolic.realSLMobius s
  have hbH : b.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := realSLMobius_image_openHalfPlane s
  have hbL : b.val '' (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)=Hyperbolic.extendedImaginaryAxis := by
    rw [Hyperbolic.halfPlaneSpherePoint_image_realSL,hline]
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨Real.log z.im,?_⟩
      apply congrArg Hyperbolic.extendedHalfPlanePoint
      apply UpperHalfPlane.ext_re_im
      · exact (show z.re=0 from hz).symm
      · exact Real.exp_log z.im_pos
    · rintro ⟨t,rfl⟩
      exact ⟨Hyperbolic.imaginaryAxisParam t,rfl,rfl⟩
  have hbN : b.val '' (Hyperbolic.extendedHalfPlanePoint '' N)=Hyperbolic.extendedHalfPlanePoint '' S := by
    rw [Hyperbolic.halfPlaneSpherePoint_image_realSL]
  have hgH : g.val.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by simpa only [hE] using E.image_eq g
  have hcH : (b*g.val*b⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    simpa only [hbH,hgH] using Mobius.stableAxis_conjugate_image b g.val Hyperbolic.openHalfPlaneSet
  have hcL : (b*g.val*b⁻¹).val '' Hyperbolic.extendedImaginaryAxis=Hyperbolic.extendedImaginaryAxis := by
    simpa only [hbL,hgL] using Mobius.stableAxis_conjugate_image b g.val (Hyperbolic.extendedHalfPlanePoint ''
      G.line.carrier)
  have hcN : (b*g.val*b⁻¹).val '' (Hyperbolic.extendedHalfPlanePoint '' S)=Hyperbolic.extendedHalfPlanePoint '' S := by
    simpa only [hbN,hNInv] using Mobius.stableAxis_conjugate_image b g.val (Hyperbolic.extendedHalfPlanePoint '' N)
  have hfix := boundaryAxis_endpoints_fixed_of_invariant_side _ hcH hcL S hS hside hcN
  have hcne : b*g.val*b⁻¹≠1 := by
    intro hh
    apply hgn
    apply Subtype.val_injective
    change g.val=(1:Mobius.complexMobiusGroup)
    have h := congrArg (fun f:Mobius.complexMobiusGroup=>b⁻¹*f*b) hh
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using h
  have hcHyper : Mobius.MobiusHyperbolic (b*g.val*b⁻¹) := by
    rcases Mobius.mobius_nonidentity_type_trichotomy _ hcne with hp|hl|he
    · obtain ⟨a,ha⟩ := hp.2
      exact False.elim ((OnePoint.coe_ne_infty (0:ℂ))
        (((ha _).mp hfix.1).trans ((ha _).mp hfix.2).symm))
    · exact ⟨hl,Hyperbolic.openHalfPlaneSet,Hyperbolic.openHalfPlaneSet_isComplexOpenDisc,hcH⟩
    · exact False.elim (boundaryAxis_not_elliptic_of_invariant_side _ hcH hcL S hS hside hcN he)
  exact (Mobius.mobiusHyperbolic_conjugation g.val b).mp hcHyper


/-- A genuine complete gap-line stabilizer preserves its actual maximal ordinary arc. -/
theorem nielsen_gap_line_stabilizer_interval
    {K : Subgroup Mobius.complexMobiusGroup} (E : FuchsianDisc K)
    (hE : E.carrier=Hyperbolic.openHalfPlaneSet)
    (hNE : DiscreteGroups.IsNonElementary K)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet K)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hGF : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet
      (DiscreteGroups.mobiusLimitSet K)))
    (g : K) (hgn : g≠1)
    (hgL : g.val.val '' (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)=Hyperbolic.extendedHalfPlanePoint ''
      G.line.carrier) :
    IsFuchsianIntervalOfDiscontinuity E (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier) ∧
      g.val.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=Hyperbolic.nielsenRealBoundaryPoint '' G.carrier := by
  classical
  let Λ:=DiscreteGroups.mobiusLimitSet K
  have hArc : Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈Hyperbolic.nielsenHalfPlaneArcFamily Λ := by
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨G.carrier,hGF,rfl⟩
  have hOrd : fuchsianBoundaryOrdinarySet E=Hyperbolic.halfPlaneIdealBoundary\Λ := by
    rw [fuchsianBoundaryOrdinarySet,fuchsianLimitSet_eq_nonElementary K hNE,hE,nielsen_openHalfPlane_frontier]
  have hI : IsFuchsianIntervalOfDiscontinuity E (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier) := by
    refine ⟨?_,?_⟩
    · simpa only [hOrd,Hyperbolic.nielsenHalfPlaneArcFamily,Set.mem_ofPred_eq] using hArc
    · intro hh
      have hi : (∞:Mobius.ExtendedComplex)∈frontier E.carrier := by
        rw [hE,nielsen_openHalfPlane_frontier]
        simp [Hyperbolic.halfPlaneIdealBoundary]
      obtain ⟨x,_hx,hxi⟩ := hh.symm ▸ hi
      exact (OnePoint.coe_ne_infty (x:ℂ)) hxi
  refine ⟨hI,?_⟩
  have hH : g.val.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by simpa only [hE] using E.image_eq g
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL g.val hH
  have hHyper := nielsen_gap_line_stabilizer_hyperbolic E hE hNE hinf G hGF g hgn hgL
  have hAn : Hyperbolic.realSLMobius A≠1 := hA ▸ hHyper.1.1
  have ht := (Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp (hA ▸ hHyper)
  have hMap : (A•· : ℍ→ ℍ) '' G.line.carrier=G.line.carrier := by
    apply nielsen_halfPlanePoint_isOpenEmbedding.injective.image_injective
    rw [←Hyperbolic.halfPlaneSpherePoint_image_realSL,hA,hgL]
  have hAxis := Hyperbolic.hHyperbolicAxis_unique_invariant A hAn ht G.line hMap
  have hEnds : G.line.idealEndpoints=Function.fixedPoints g.val.val := by
    rw [hAxis,Hyperbolic.hHyperbolicAxis_idealEndpoints,hA]
  have hFix : ∀p∈G.line.idealEndpoints,g.val.val p=p := by
    intro p hp
    change p∈Function.fixedPoints g.val.val
    rw [←hEnds]
    exact hp
  cases G with
  | bounded a b hab =>
    have haFix : g.val.val (Hyperbolic.nielsenRealBoundaryPoint a)=Hyperbolic.nielsenRealBoundaryPoint a :=
      hFix _ (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inl rfl)
    have hbFix : g.val.val (Hyperbolic.nielsenRealBoundaryPoint b)=Hyperbolic.nielsenRealBoundaryPoint b :=
      hFix _ (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inr rfl)
    have hImageArc : g.val.val '' (Hyperbolic.nielsenRealBoundaryPoint '' (Hyperbolic.NielsenHalfPlaneGap.bounded a b
      hab).carrier)
        ∈Hyperbolic.nielsenHalfPlaneArcFamily Λ := by
      simpa only [hOrd,Hyperbolic.nielsenHalfPlaneArcFamily,Set.mem_ofPred_eq] using (hI.image g).1
    have hiΛ : Λ.Infinite := fun hf=>DiscreteGroups.mobiusLimitSet_not_countable K hNE hf.countable
    obtain ⟨J,hJI⟩ := Hyperbolic.nielsenHalfPlaneArcFamily_exists_gap Λ (DiscreteGroups.mobiusLimitSet_isClosed K)
      (Hyperbolic.nielsenHalfPlaneRealSet_infinite Λ hiΛ (E.nielsenHalfPlane_limit_subset hE) hinf).nonempty
      hinf hImageArc
    have hJReal : J.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet Λ) := by
      rw [←hJI,Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf] at hImageArc
      obtain ⟨S,hS,hSJ⟩ := hImageArc
      exact Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.injective.image_injective hSJ ▸ hS
    have hJsub : J.carrier⊆(Hyperbolic.nielsenHalfPlaneRealSet Λ)ᶜ := by
      obtain ⟨p,hp,hJp⟩ := hJReal
      rw [hJp]
      exact connectedComponentIn_subset _ _
    have hCl (x:ℝ) (hx:x∈closure (Ioo a b))
        (hfx:g.val.val (Hyperbolic.nielsenRealBoundaryPoint x)=Hyperbolic.nielsenRealBoundaryPoint x) : x∈closure J.carrier := by
      rw [Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.isInducing.closure_eq_preimage_closure_image]
      change Hyperbolic.nielsenRealBoundaryPoint x∈closure (Hyperbolic.nielsenRealBoundaryPoint '' J.carrier)
      rw [hJI,←hfx]
      apply mem_closure_image (Mobius.mobiusBoundaryHomeomorph g.val).continuous.continuousAt
      exact mem_closure_image Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.continuous.continuousAt hx
    have haJ : a∈closure J.carrier := hCl a (by rw [closure_Ioo hab.ne];exact left_mem_Icc.mpr hab.le) haFix
    have hbJ : b∈closure J.carrier := hCl b (by rw [closure_Ioo hab.ne];exact right_mem_Icc.mpr hab.le) hbFix
    have hend := nielsen_gap_idealEndpoints_limit_subset Λ hinf (.bounded a b hab) hArc
    have haΛ : a∈Hyperbolic.nielsenHalfPlaneRealSet Λ :=
      hend (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inl rfl)
    have hbΛ : b∈Hyperbolic.nielsenHalfPlaneRealSet Λ :=
      hend (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inr rfl)
    have han : a∉J.carrier := fun h=>hJsub h haΛ
    have hbn : b∉J.carrier := fun h=>hJsub h hbΛ
    have hJG : J.carrier=(Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).carrier := by
      cases J with
      | bounded c d hcd =>
        change a∈closure (Ioo c d) at haJ
        change b∈closure (Ioo c d) at hbJ
        rw [closure_Ioo hcd.ne] at haJ hbJ
        change ¬(c<a ∧ a<d) at han
        change ¬(c<b ∧ b<d) at hbn
        have ha : a=c := by by_contra hn;have hh:c<a:=lt_of_le_of_ne haJ.1 (Ne.symm hn);exact han ⟨hh,hab.trans_le hbJ.2⟩
        have hb : b=d := by by_contra hn;have hh:b<d:=lt_of_le_of_ne hbJ.2 hn;exact hbn ⟨haJ.1.trans_lt hab,hh⟩
        subst c;subst d;rfl
      | left c =>
        change a∈closure (Iio c) at haJ
        change b∈closure (Iio c) at hbJ
        rw [closure_Iio] at haJ hbJ
        exact False.elim (han (show a<c from hab.trans_le hbJ))
      | right c =>
        change a∈closure (Ioi c) at haJ
        change b∈closure (Ioi c) at hbJ
        rw [closure_Ioi] at haJ hbJ
        exact False.elim (hbn (show c<b from haJ.trans_lt hab))
    exact hJI.symm.trans (congrArg (Hyperbolic.nielsenRealBoundaryPoint '' ·) hJG)
  | left b =>
    have hiFix : g.val.val ∞=∞ := hFix _ (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inr rfl)
    have hbFix : g.val.val (Hyperbolic.nielsenRealBoundaryPoint b)=Hyperbolic.nielsenRealBoundaryPoint b :=
      hFix _ (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inl rfl)
    let M:=Matrix.SpecialLinearGroup.mapGL ℝ A
    have hMpos : 0<M.val.det := by change 0<A.val.det;rw [A.property];norm_num
    have hMi : Mobius.fractionalLinear (Hyperbolic.complexifiedRealMobiusMatrix M) ∞=∞ := by
      simpa only [←hA,Hyperbolic.realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,Hyperbolic.realSLMobius_matrix] using hiFix
    obtain ⟨α,β,hα,hF⟩ := Hyperbolic.realMobius_fix_infty_affine M hMpos hMi
    have hF' (x:ℝ) : g.val.val (Hyperbolic.nielsenRealBoundaryPoint x)=Hyperbolic.nielsenRealBoundaryPoint (α*x+β) := by
      simpa only [←hA,Hyperbolic.realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,Hyperbolic.realSLMobius_matrix,Hyperbolic.nielsenRealBoundaryPoint,M] using hF x
    have hb : α*b+β=b := Hyperbolic.realOnePoint_injective ((hF' b).symm.trans hbFix)
    apply subset_antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      rw [hF']
      refine ⟨α*x+β,?_,rfl⟩
      change α*x+β<b
      change x<b at hx
      nlinarith
    · rintro _ ⟨y,hy,rfl⟩
      let x:=(y-β)/α
      have hxy : α*x+β=y := by dsimp [x];field_simp;ring
      refine ⟨Hyperbolic.nielsenRealBoundaryPoint x,⟨x,?_,rfl⟩,?_⟩
      · change x<b
        change y<b at hy
        nlinarith
      · rw [hF',hxy]
  | right b =>
    have hiFix : g.val.val ∞=∞ := hFix _ (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inr rfl)
    have hbFix : g.val.val (Hyperbolic.nielsenRealBoundaryPoint b)=Hyperbolic.nielsenRealBoundaryPoint b :=
      hFix _ (by rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact Or.inl rfl)
    let M:=Matrix.SpecialLinearGroup.mapGL ℝ A
    have hMpos : 0<M.val.det := by change 0<A.val.det;rw [A.property];norm_num
    have hMi : Mobius.fractionalLinear (Hyperbolic.complexifiedRealMobiusMatrix M) ∞=∞ := by
      simpa only [←hA,Hyperbolic.realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,Hyperbolic.realSLMobius_matrix] using hiFix
    obtain ⟨α,β,hα,hF⟩ := Hyperbolic.realMobius_fix_infty_affine M hMpos hMi
    have hF' (x:ℝ) : g.val.val (Hyperbolic.nielsenRealBoundaryPoint x)=Hyperbolic.nielsenRealBoundaryPoint (α*x+β) := by
      simpa only [←hA,Hyperbolic.realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,Hyperbolic.realSLMobius_matrix,Hyperbolic.nielsenRealBoundaryPoint,M] using hF x
    have hb : α*b+β=b := Hyperbolic.realOnePoint_injective ((hF' b).symm.trans hbFix)
    apply subset_antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      rw [hF']
      refine ⟨α*x+β,?_,rfl⟩
      change α*x+β>b
      change x>b at hx
      nlinarith
    · rintro _ ⟨y,hy,rfl⟩
      let x:=(y-β)/α
      have hxy : α*x+β=y := by dsimp [x];field_simp;ring
      refine ⟨Hyperbolic.nielsenRealBoundaryPoint x,⟨x,?_,rfl⟩,?_⟩
      · change x>b
        change y>b at hy
        nlinarith
      · rw [hF',hxy]


/-- Every actual Nielsen boundary line of a finitely generated original group is
the whole true axis of an actual boundary-hyperbolic element. -/
theorem finitelyGenerated_nielsen_boundary_line_boundaryHyperbolic
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (L : Hyperbolic.DiscLine) (hL : L∈nielsenBoundaryDiscLineFamily P hNE) :
    ∃g:H,IsBoundaryHyperbolic P.asFuchsianDisc g ∧
      ∃M:FuchsianAxisModel P.asFuchsianDisc g.val,
        M.carrier=(Subtype.val:P.domain.carrier→ Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier) := by
  classical
  obtain ⟨g,hgn,hgL⟩ := finitelyGenerated_nielsen_boundary_line_stabilizer_nontrivial P hNE hFG L hL
  obtain ⟨G,hGF,hGL⟩ := hL
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  have hq:=P.asFuchsianDisc.nielsenArcNormalizer_image hNE
  have hinf:=P.asFuchsianDisc.nielsenArcNormalizer_limit hNE
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate q H
  let E:=P.asFuchsianDisc.nielsenConjugate q
  have hE:E.carrier=Hyperbolic.openHalfPlaneSet := hq
  let f:K:=⟨q*g.val*q⁻¹,(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g.val,g.property,rfl⟩⟩
  let S:Set Mobius.ExtendedComplex:=(Subtype.val:P.domain.carrier→ Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm
    '' L.carrier)
  have hEll : P.finiteCoordinate.symm '' L.carrier=(nielsenHalfPlaneChart P hNE).symm '' G.line.carrier := by
    rw [←hGL,image_image]
    simp only [Homeomorph.symm_apply_apply,Set.image_id']
  have hPhys : S=nielsenModelSet q G.line.carrier := by
    change (Subtype.val:P.domain.carrier→ Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier)=_
    rw [hEll]
    exact nielsen_gap_chart_line_sphere_image P q hq G
  have hqS : q.val '' S=Hyperbolic.extendedHalfPlanePoint '' G.line.carrier := by
    rw [hPhys,nielsenModelSet]
    simpa only [inv_inv] using nielsen_mobius_inverse_image q⁻¹ (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)
  have hgS : g.val.val '' S=S := by
    apply subset_antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      have hmem : g • x∈P.finiteCoordinate.symm '' L.carrier := by
        rw [←hgL]
        exact ⟨x,hx,rfl⟩
      exact ⟨g • x,hmem,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      have hx' : x∈g • (P.finiteCoordinate.symm '' L.carrier) := by rw [hgL];exact hx
      obtain ⟨y,hy,hgy⟩ := hx'
      refine ⟨y.val,⟨y,hy,rfl⟩,?_⟩
      change (g • y).val=x.val
      exact congrArg Subtype.val hgy
  have hfL : f.val.val '' (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)=Hyperbolic.extendedHalfPlanePoint '' G.line.carrier := by
    have h:=Mobius.stableAxis_conjugate_image q g.val S
    simpa only [hqS,hgS] using h
  have hfn:f≠1 := by
    intro he
    apply hgn
    apply Subtype.val_injective
    change g.val=(1:Mobius.complexMobiusGroup)
    have hh:q*g.val*q⁻¹=1:=congrArg Subtype.val he
    have h:=congrArg (fun k:Mobius.complexMobiusGroup=>q⁻¹*k*q) hh
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using h
  have hfHyper := nielsen_gap_line_stabilizer_hyperbolic E hE (hNE.conjugation q) hinf G hGF f hfn hfL
  obtain ⟨hfI,hfInv⟩ := nielsen_gap_line_stabilizer_interval E hE (hNE.conjugation q) hinf G hGF f hfn hfL
  have hHyper:Mobius.MobiusHyperbolic g.val := (Mobius.mobiusHyperbolic_conjugation g.val q).mp hfHyper
  let I:Set Mobius.ExtendedComplex:=q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)
  have hqI:q.val '' I=Hyperbolic.nielsenRealBoundaryPoint '' G.carrier:=q.val.image_symm_image _
  have hArc : I∈P.asFuchsianDisc.nielsenArcFamily := by
    apply (P.asFuchsianDisc.nielsenArcFamily_gap_mem q hq G).mpr
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨G.carrier,hGF,rfl⟩
  have hOrd : fuchsianBoundaryOrdinarySet P.asFuchsianDisc=
      frontier P.asFuchsianDisc.carrier\DiscreteGroups.mobiusLimitSet H := by
    rw [fuchsianBoundaryOrdinarySet,fuchsianLimitSet_eq_nonElementary H hNE]
  have hIO : IsFuchsianIntervalOfDiscontinuity P.asFuchsianDisc I := by
    refine ⟨?_,?_⟩
    · simpa only [FuchsianDisc.nielsenArcFamily,Set.mem_ofPred_eq,←hOrd] using hArc
    · intro hh
      have hqF:q.val '' frontier P.asFuchsianDisc.carrier=Hyperbolic.halfPlaneIdealBoundary := by
        change (Mobius.mobiusBoundaryHomeomorph q) '' frontier P.asFuchsianDisc.carrier=_
        rw [Homeomorph.image_frontier]
        change frontier (q.val '' P.asFuchsianDisc.carrier)=Hyperbolic.halfPlaneIdealBoundary
        rw [hq,nielsen_openHalfPlane_frontier]
      have hFull:=congrArg (q.val '' ·) hh
      rw [hqI,hqF] at hFull
      have hi:(∞:Mobius.ExtendedComplex)∈Hyperbolic.nielsenRealBoundaryPoint '' G.carrier := by
        rw [hFull]
        simp [Hyperbolic.halfPlaneIdealBoundary]
      obtain ⟨x,_hx,hxi⟩:=hi
      exact OnePoint.coe_ne_infty (x:ℂ) hxi
  have hgI:g.val.val '' I=I := by
    have h:=Mobius.stableAxis_conjugate_image q g.val I
    rw [hqI] at h
    change f.val.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=q.val '' (g.val.val '' I) at h
    rw [hfInv] at h
    exact q.val.injective.image_injective (h.symm.trans hqI.symm)
  have hgBoundary:IsBoundaryHyperbolic P.asFuchsianDisc g:=⟨hHyper,I,hIO,hgI⟩
  obtain ⟨M⟩:=P.asFuchsianDisc.axisModel_exists g.val g.property hHyper
  have hfH:f.val.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by simpa only [hE] using E.image_eq f
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f.val hfH
  have hAn:Hyperbolic.realSLMobius A≠1:=hA ▸ hfHyper.1.1
  have ht:4<(Matrix.trace A.val)^2 := (Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp (hA ▸ hfHyper)
  have hMap:(A•·:ℍ→ ℍ) '' G.line.carrier=G.line.carrier := by
    apply nielsen_halfPlanePoint_isOpenEmbedding.injective.image_injective
    rw [←Hyperbolic.halfPlaneSpherePoint_image_realSL,hA,hfL]
  have hAxis:=Hyperbolic.hHyperbolicAxis_unique_invariant A hAn ht G.line hMap
  have hMC:=boundary_axis_carrier_image_in_chart M q hq A hA hAn ht
  rw [←hAxis] at hMC
  exact ⟨g,hgBoundary,M,q.val.injective.image_injective (hMC.trans hqS.symm)⟩


/-- The actual full Nielsen boundary component has a natural embedded-circle
quotient in the original whole-group orbit surface. -/
theorem finitelyGenerated_nielsen_boundary_line_embedded_circle
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (L : Hyperbolic.DiscLine) (hL : L∈nielsenBoundaryDiscLineFamily P hNE) :
    ∃g:H,IsBoundaryHyperbolic P.asFuchsianDisc g ∧
      ∃M:FuchsianAxisModel P.asFuchsianDisc g.val,
        M.carrier=(Subtype.val:P.domain.carrier→ Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier) ∧
        IsMaximalCyclicIn H (Surfaces.mobiusSetStabilizer H M.carrier) ∧
        ∃C:SphereSetOrbitQuotient H M.carrier≃ₜCircle,
          Topology.IsEmbedding (sphereSetOrbitMap P.asFuchsianDisc.domain M.carrier M.carrier_subset_domain ∘ C.symm) ∧
          ∀p:M.carrier,
            (sphereSetOrbitMap P.asFuchsianDisc.domain M.carrier M.carrier_subset_domain ∘ C.symm)
              (C (_root_.Quotient.mk _ p))=
              Surfaces.mobiusDiscDomainProjection P.asFuchsianDisc.domain M.carrier M.carrier_subset_domain p := by
  obtain ⟨g,hg,M,hM⟩ := finitelyGenerated_nielsen_boundary_line_boundaryHyperbolic P hNE hFG L hL
  obtain ⟨C,hC,hπ⟩ := boundaryHyperbolic_axis_embedded_circle hNE hg M
  exact ⟨g,hg,M,hM,boundaryHyperbolic_axis_stabilizer_maximalCyclic hNE hg M,C,hC,hπ⟩

end NielsenBoundaryGeodesics

section NielsenBoundaryCycleCensus

section NielsenBoundaryVertexOrbits
open LeanEval.Topology.ClassificationOfSurfaces.Moise
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "tag" => nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv

theorem nielsenCyclicBoundaryVertex_finite_frontier (b:B) :
    ∃x:P.domain.carrier,Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex b.val ∧
      x∈frontier (fuchsianNielsenCore P hNE) := by
  obtain ⟨s,hs⟩:=(nielsenCyclicPairIndex_fixed_iff hD hNE hFG hfin w hwD hwN J hc hv b.val).mp b.property
  have hm:vertex b.val∈s.carrier:=by
    have hh:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv b.val
      (Polygon.closedModelDiscHSegment_left_mem (vertex b.val) (vertex (b.val+1)))
    simpa only [hs,NielsenBoundarySide.carrier,Sum.elim_inr] using hh
  obtain ⟨z,hz,hzv⟩:=hm
  refine ⟨P.finiteCoordinate.symm z,?_,?_⟩
  · simpa only [Homeomorph.apply_symm_apply] using hzv
  · obtain ⟨x,hx,hxz⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE s.val s.property.1 hz.1
    rw [←hxz,P.finiteCoordinate.symm_apply_apply]
    exact hx

def nielsenCyclicBoundaryNativePoint (b:B) : P.domain.carrier :=
  Classical.choose (nielsenCyclicBoundaryVertex_finite_frontier hD hNE hFG hfin w hwD hwN J hc hv b)
local notation "point" => nielsenCyclicBoundaryNativePoint hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryNativePoint_spec (b:B) :
    Hyperbolic.discToClosedModel (P.finiteCoordinate (point b))=vertex b.val ∧
      point b∈frontier (fuchsianNielsenCore P hNE) :=
  Classical.choose_spec (nielsenCyclicBoundaryVertex_finite_frontier hD hNE hFG hfin w hwD hwN J hc hv b)

/-- Two distinct outgoing boundary edges cannot have initial vertices in the same actual whole-group orbit. -/
theorem nielsenCyclicBoundaryNativePoint_orbit_iff (b c:B) :
    (∃g:H,g•point b=point c) ↔ b=c := by
  constructor
  · intro hbc
    have hb:=nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b
    have hc':=nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv c
    have hchain:=nielsenCoreFiniteFrontierCorner_orbit_rawChain hD hNE hFG hfin w hwD hwN J hc hv
      b.val c.val (point b) (point c) hb.1 hc'.1 hb.2 hc'.2 hbc
    exact nielsenRawBoundaryVertex_injective hD hNE hFG hfin w hwD hwN J hc hv (Quotient.sound hchain)
  · rintro rfl
    exact ⟨1,one_smul H _⟩

def nielsenCyclicBoundaryVertexProjection
    (b:B) : Surfaces.MobiusDomainQuotient P.domain :=
  Surfaces.mobiusDomainProjection P.domain (point b)

theorem nielsenCyclicBoundaryVertexProjection_injective :
    Function.Injective (nielsenCyclicBoundaryVertexProjection hD hNE hFG hfin w hwD hwN J hc hv) := by
  intro b c hbc
  exact ((nielsenCyclicBoundaryNativePoint_orbit_iff hD hNE hFG hfin w hwD hwN J hc hv c b).mp
    (MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hbc)))).symm

theorem nielsenCyclicBoundaryVertexProjection_card :
    Nat.card (Set.range (nielsenCyclicBoundaryVertexProjection hD hNE hFG hfin w hwD hwN J hc hv))=
      Fintype.card B := by
  rw [←Nat.card_congr (Equiv.ofInjective _
    (nielsenCyclicBoundaryVertexProjection_injective hD hNE hFG hfin w hwD hwN J hc hv)),Nat.card_eq_fintype_card]

end NielsenBoundaryVertexOrbits

section NielsenBoundaryPositiveOrbit
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (hNE:DiscreteGroups.IsNonElementary H)

include hD in
/-- Every true finite core-frontier point has an original orbit representative on a positive, rather than point-only, unpaired segment. -/
theorem nielsenCore_frontier_positive_unpaired_representative
    (x:P.domain.carrier) (hx: x∈frontier (fuchsianNielsenCore P hNE)) :
    ∃g:H,∃s:NielsenUnpairedSide P hNE D,
      P.finiteCoordinate (g•x)∈nielsenUnpairedNativeCarrier P D s.val := by
  classical
  have hxL:P.finiteCoordinate x∈P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE):=
    mem_image_of_mem _ hx
  rw [nielsenBoundaryDiscLineFamily_frontier_cover P hNE] at hxL
  obtain ⟨L,hL,hxL⟩:=mem_iUnion₂.mp hxL
  let S:=P.finiteCoordinate.symm '' L.carrier
  have hxS:x∈S:=by
    exact ⟨P.finiteCoordinate x,hxL,P.finiteCoordinate.symm_apply_apply x⟩
  have hconn:IsPreconnected S:=L.hConvex.isPreconnected.image _ P.finiteCoordinate.symm.continuous.continuousOn
  have hnt:S.Nontrivial:=by
    obtain ⟨u,v,hu,hv,huv⟩:=L.toHalfPlane.exists_two_points
    have huL:Hyperbolic.halfPlaneToDisc u∈L.carrier:=by
      rw [Hyperbolic.DiscLine.mem_carrier,Hyperbolic.discToHalfPlane_halfPlaneToDisc]
      exact hu
    have hvL:Hyperbolic.halfPlaneToDisc v∈L.carrier:=by
      rw [Hyperbolic.DiscLine.mem_carrier,Hyperbolic.discToHalfPlane_halfPlaneToDisc]
      exact hv
    exact ⟨_,⟨_,huL,rfl⟩,_,⟨_,hvL,rfl⟩,
      P.finiteCoordinate.symm.injective.ne (fun he=>huv (by
        simpa only [Hyperbolic.discToHalfPlane_halfPlaneToDisc] using congrArg Hyperbolic.discToHalfPlane he))⟩
  have hpre:Preperfect S:=hconn.preperfect_of_nontrivial hnt
  obtain ⟨K,_hK,hxK,_hI,hcover,_havoid⟩:=hD.locallyFinite.finite_neighborhood_star x
  have hpos:∃a:H,x∈fuchsianDomainTile P D a ∧ (S∩fuchsianDomainTile P D a).Nontrivial:=by
    by_contra hn
    obtain ⟨O,hOK,hOo,hxO⟩:=mem_nhds_iff.mp hxK
    have hlocal:O∩S⊆{x}:=by
      intro y hy
      obtain ⟨a,hax,hay⟩:=mem_iUnion₂.mp (hcover (hOK hy.1))
      by_contra hyx
      exact hn ⟨a,hax,x,⟨hxS,hax⟩,y,⟨hy.2,hay⟩,by
        intro hxy
        exact hyx (mem_singleton_iff.mpr hxy.symm)⟩
    have hacc:AccPt x (𝓟 (O∩S)):=hpre.open_inter hOo x ⟨hxO,hxS⟩
    exact Set.Infinite.of_accPt hacc ((Set.finite_singleton x).subset hlocal)
  obtain ⟨a,hax,hpos⟩:=hpos
  obtain ⟨M,hM,himage⟩:=nielsenBoundary_original_line_image P hNE L hL a⁻¹
  have hnt':(P.finiteCoordinate.symm '' M.carrier∩closure D).Nontrivial:=by
    have hi:=hpos.image (MulAction.injective a⁻¹)
    change (a⁻¹•(S∩a•closure D)).Nontrivial at hi
    rw [smul_set_inter,inv_smul_smul] at hi
    rw [himage] at hi
    exact hi
  have hnative:(nielsenUnpairedNativeCarrier P D M).Nontrivial:=by
    change (M.carrier∩P.finiteCoordinate '' closure D).Nontrivial
    have hi:=hnt'.image P.finiteCoordinate.injective
    rw [image_inter P.finiteCoordinate.injective,image_image] at hi
    simpa only [Homeomorph.apply_symm_apply,Set.image_id'] using hi
  let s:NielsenUnpairedSide P hNE D:=⟨M,hM,hnative⟩
  refine ⟨a⁻¹,s,?_,?_⟩
  · have h: a⁻¹•x∈P.finiteCoordinate.symm '' M.carrier:=by
      rw [←himage]
      exact mem_smul_set.mpr ⟨x,hxS,rfl⟩
    obtain ⟨z,hz,hzx⟩:=h
    rwa [←hzx,P.finiteCoordinate.apply_symm_apply]
  · exact mem_image_of_mem _ (by
      simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using hax)

end NielsenBoundaryPositiveOrbit

/-- The finite frontier of the true core is regular even if elliptic points occur elsewhere in the original group. -/
theorem finitelyGenerated_nielsenCore_frontier_pointOrder_one
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG) (x:P.domain.carrier)
    (hx:x∈frontier (fuchsianNielsenCore P hNE)) : fuchsianPointOrder P x=1 := by
  apply (isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp
  have hxL:P.finiteCoordinate x∈P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE):=
    mem_image_of_mem _ hx
  rw [nielsenBoundaryDiscLineFamily_frontier_cover P hNE] at hxL
  obtain ⟨L,hL,hxL⟩:=mem_iUnion₂.mp hxL
  obtain ⟨f,hf,M,hM⟩:=finitelyGenerated_nielsen_boundary_line_boundaryHyperbolic P hNE hFG L hL
  have hxM:x.val∈M.carrier:=by
    rw [hM]
    exact ⟨x,⟨P.finiteCoordinate x,hxL,P.finiteCoordinate.symm_apply_apply x⟩,rfl⟩
  rintro ⟨g,hg,hfix⟩
  have himage:g.val.val '' M.carrier=M.carrier:=by
    apply (boundaryHyperbolic_axis_stable hNE hf M g.val g.property).resolve_right
    intro hd
    exact disjoint_left.mp hd ⟨x.val,hxM,congrArg Subtype.val hfix⟩ hxM
  exact boundaryHyperbolic_axis_stabilizer_no_elliptics hNE hf M g.val ⟨g.property,himage⟩ hg

theorem nielsen_convex_region_angle_ge_pi_of_full_line
    {S:Set 𝔻} (hS:Hyperbolic.DiscHConvex S) (ho:IsOpen S) (hn:S.Nonempty)
    (L:Hyperbolic.DiscLine) (hL:L.carrier⊆closure S) (z:𝔻) (hz:z∈L.carrier) :
    Real.pi≤Hyperbolic.discSubtendedAngle (closure S) z := by
  obtain ⟨q,hq⟩:=L.toHalfPlane.exists_SL_normalizer
  let F:=Hyperbolic.discSL2Homeomorph q
  let T:=F '' S
  have hF:let :=Hyperbolic.discHyperbolicMetric;Isometry F:=by
    let :=Hyperbolic.discHyperbolicMetric
    exact Hyperbolic.discSL2Action_isometry q
  have hT:Hyperbolic.DiscHConvex T:=hS.isometry_image hF
  have hoT:IsOpen T:=F.isOpenMap S ho
  have hnT:T.Nonempty:=hn.image F
  have hfinite (u:ℍ):F (Hyperbolic.halfPlaneToDisc u)=Hyperbolic.halfPlaneToDisc (q•u):=by
    change Hyperbolic.halfPlaneToDisc (q•Hyperbolic.discToHalfPlane (Hyperbolic.halfPlaneToDisc u))=_
    rw [Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  have hmap:(q•·:ℍ→ℍ) '' L.toHalfPlane.carrier=(Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by
    have hh:=congrArg Hyperbolic.HalfPlaneLine.carrier hq
    rw [Hyperbolic.HalfPlaneLine.realGLMap_carrier] at hh
    exact hh
  have hfull:Hyperbolic.halfPlaneToDisc '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier⊆closure T:=by
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨u,hu,rfl⟩:=hmap.symm ▸ hv
    rw [←hfinite]
    change F (Hyperbolic.halfPlaneToDisc u)∈closure (F '' S)
    rw [←F.image_closure]
    apply mem_image_of_mem
    apply hL
    rw [Hyperbolic.DiscLine.mem_carrier,Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    exact hu
  have hclosed:(Hyperbolic.HalfPlaneLine.vertical 0).toDiscLine.closedCarrier⊆
      closure (Hyperbolic.discToClosedModel '' T):=by
    apply closure_minimal _ isClosed_closure
    rintro _ ⟨u,hu,rfl⟩
    apply image_closure_subset_closure_image Hyperbolic.isEmbedding_discToClosedModel.continuous
    have he:(Hyperbolic.HalfPlaneLine.vertical 0).toDiscLine.carrier=
        Hyperbolic.halfPlaneToDisc '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by
      rw [Hyperbolic.DiscLine.carrier_eq_cayley_image_halfPlane,Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane]
    exact ⟨u,hfull (he ▸ hu),rfl⟩
  have hi:Hyperbolic.closedModelCayleyHomeomorph Hyperbolic.twoIdealInfiniteEndpoint∈closure (Hyperbolic.discToClosedModel '' T):=by
    apply hclosed
    rw [←Hyperbolic.HalfPlaneLine.cayley_image_closedCarrier]
    apply mem_image_of_mem
    apply ((Hyperbolic.HalfPlaneLine.vertical 0).closedCarrier_mem_ideal_iff _
      Hyperbolic.twoIdealInfiniteEndpoint_ideal).mpr
    rw [Hyperbolic.vertical_idealEndpoints]
    exact Or.inr rfl
  let c:=q•Hyperbolic.discToHalfPlane z
  have hc:c∈(Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by
    rw [←hmap]
    exact ⟨Hyperbolic.discToHalfPlane z,(L.mem_carrier z).mp hz,rfl⟩
  have hcre:c.re=0:=hc
  let a:ℍ:=Hyperbolic.metricProbe 0 (c.im/2) (by linarith [c.im_pos])
  have ha:a∈(Hyperbolic.HalfPlaneLine.vertical 0).carrier:=rfl
  have hclosure (u:ℍ) (hu:u∈(Hyperbolic.HalfPlaneLine.vertical 0).carrier) :
      Hyperbolic.discToClosedModel (Hyperbolic.halfPlaneToDisc u)∈closure (Hyperbolic.discToClosedModel '' T):=
    image_closure_subset_closure_image Hyperbolic.isEmbedding_discToClosedModel.continuous
      ⟨Hyperbolic.halfPlaneToDisc u,hfull ⟨u,hu,rfl⟩,rfl⟩
  have hb:=Hyperbolic.discHConvex_region_angle_ge_pi_of_vertical_closure_points hT hoT hnT hi a c
    (by change c.re=0;exact hcre) (by change c.im/2<c.im;linarith [c.im_pos])
    (hclosure a ha) (hclosure c hc)
  have hang:=Hyperbolic.discSubtendedAngle_isometry F hF (closure S) z
  rw [F.image_closure] at hang
  have hFz:F z=Hyperbolic.halfPlaneToDisc c:=rfl
  rw [hFz] at hang
  rwa [hang] at hb

/-- Every actual finite Nielsen boundary point has a true straight Haar angle. -/
theorem fuchsianNielsenCore_frontier_angle_eq_pi
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (x:P.domain.carrier)
    (hx:x∈frontier (fuchsianNielsenCore P hNE)) :
    fuchsianPolygonAngle P (fuchsianNielsenCore P hNE) x=Real.pi := by
  apply le_antisymm (fuchsianNielsenCore_boundary_angle_le_pi P hNE x hx)
  have hxL:P.finiteCoordinate x∈P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE):=
    mem_image_of_mem _ hx
  rw [nielsenBoundaryDiscLineFamily_frontier_cover P hNE] at hxL
  obtain ⟨L,hL,hxL⟩:=mem_iUnion₂.mp hxL
  change Real.pi≤Hyperbolic.discSubtendedAngle (P.finiteCoordinate '' closure (fuchsianNielsenCore P hNE)) _
  rw [P.finiteCoordinate.image_closure]
  apply nielsen_convex_region_angle_ge_pi_of_full_line (fuchsianNielsenCore_convex P hNE)
    (P.finiteCoordinate.isOpenMap _ (fuchsianNielsenCore_isOpen P hNE))
    ((fuchsianNielsenCore_isConnected P hNE).nonempty.image P.finiteCoordinate) L _ _ hxL
  intro z hz
  obtain ⟨y,hy,hyz⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hz
  rw [←P.finiteCoordinate.image_closure]
  exact ⟨y,frontier_subset_closure hy,hyz⟩

section NielsenFrontierBoundaryClasses
open LeanEval.Topology.ClassificationOfSurfaces.Moise
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv

/-- Each actual finite frontier corner belongs to precisely one boundary-vertex raw class; positive clipped segments are derived using the original finite tile star. -/
theorem nielsenCoreFiniteFrontierCorner_boundary_class
    (i:ZMod J.n) (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hxN:x∈frontier (fuchsianNielsenCore P hNE)) :
    ∃!b:B,Relation.EqvGen step i b.val := by
  classical
  obtain ⟨g,s,hgL,hgD⟩:=nielsenCore_frontier_positive_unpaired_representative hD hNE x hxN
  have hyD:g•x∈closure D:=P.finiteCoordinate.injective.mem_set_image.mp hgD
  have hyN:g•x∈frontier (fuchsianNielsenCore P hNE):=by
    rw [←fuchsianNielsenCore_smul_frontier P hNE g]
    exact mem_smul_set.mpr ⟨x,hxN,rfl⟩
  obtain ⟨j,hj⟩:=nielsenCore_frontier_orbit_marked_vertex hD hNE hFG w hwD hwN J hv i x (g•x) hx
    hyD hyN g rfl
  let p:=Hyperbolic.discToClosedModel (P.finiteCoordinate (g•x))
  have hp:p∈s.carrier:=mem_image_of_mem _ (show P.finiteCoordinate (g•x)∈nielsenUnpairedNativeCarrier P D s.val from
    ⟨hgL,hgD⟩)
  obtain ⟨k,hk,hpk⟩:=nielsenBoundarySide_point_mem_tagged_cyclic_edge hD hNE hFG hfin w hwD hwN J hc hv
    (Sum.inr s) p hp
  let b:B:=⟨k,nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv k s hk⟩
  have hpm:p∈nielsenCanonicalBoundaryMarks hD hNE hFG:=by
    change Hyperbolic.discToClosedModel (P.finiteCoordinate (g•x))∈_
    rw [hj]
    exact nielsenCyclicVertex_marked hD hNE hFG J hv j
  have hchain:Relation.EqvGen step i j:=nielsenCoreFiniteFrontierCorner_orbit_rawChain
    hD hNE hFG hfin w hwD hwN J hc hv i j x (g•x) hx hj hxN hyN ⟨g,rfl⟩
  have hex:∃b:B,Relation.EqvGen step i b.val:=by
    rcases nielsenCyclicEdge_no_extra_marks hD hNE hFG J hv k p hpk hpm with he|he
    · have hjk:j=k:=nielsenCyclicVertex_injective hD hNE hFG J hv (hj.symm.trans he)
      refine ⟨b,?_⟩
      change Relation.EqvGen step i k
      exact hjk ▸ hchain
    · have hjk:j=k+1:=nielsenCyclicVertex_injective hD hNE hFG J hv (hj.symm.trans he)
      refine ⟨nielsenCyclicBoundaryNext hD hNE hFG hfin w hwD hwN J hc hv b,?_⟩
      exact Relation.EqvGen.trans _ _ _ (hjk ▸ hchain)
        (nielsenCyclicBoundaryNext_corner_chain hD hNE hFG hfin w hwD hwN J hc hv b)
  obtain ⟨b,hb⟩:=hex
  refine ⟨b,hb,?_⟩
  intro c hc'
  apply nielsenRawBoundaryVertex_injective hD hNE hFG hfin w hwD hwN J hc hv
  exact Quotient.sound (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hc') hb)

end NielsenFrontierBoundaryClasses

section NielsenFrontierCornerAngles
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv
local notation "Q" => nielsenCyclicDiscPolygon hD hNE hFG hfin w hwD hwN J hc hv

include w hwD hwN in
theorem nielsenCyclicFiniteVertex_mem_coreClosure (i:ZMod J.n) (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i) :
    x∈closure (D∩fuchsianNielsenCore P hNE) := by
  have hmark:=nielsenCyclicVertex_marked hD hNE hFG J hv i
  have hB:=nielsenBoundaryMarkSaturation_subset_boundary P hNE D
    (nielsenBoundarySeedMarks hD hNE hFG) ⟨vertex i,hmark,rfl⟩
  rw [←hx] at hB
  exact frontier_subset_closure ((nielsenCore_klein_finite_frontier hD hNE w hwD hwN x).mp hB)

theorem nielsenRawFiniteCornerClass_point_exists
    (i:ZMod J.n)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (j:ZMod J.n) (hij:Relation.EqvGen step i j) :
    ∃y:↥(fuchsianPolygonCycle P D x),vertex j=Hyperbolic.discToClosedModel (P.finiteCoordinate y.val) := by
  obtain ⟨g,hg⟩:=nielsenCoreRawCornerChain_sphereOrbit hD hNE hFG hfin w hwD hwN J hc hv hij
  have hy:vertex j=Hyperbolic.discToClosedModel (P.finiteCoordinate (g•x)):=by
    have hh:(P.compactifiedAction g).closedMap (vertex i)=vertex j:=
      Hyperbolic.isEmbedding_closedDiscToExtended.injective ((P.compactifiedAction_sphere g (vertex i)).trans hg)
    rw [←hx,P.compactifiedAction_finite] at hh
    exact hh.symm
  refine ⟨⟨g•x,closure_mono inter_subset_left
    (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv j (g•x) hy.symm),?_⟩,hy⟩
  exact MulAction.mem_orbit_iff.mpr ⟨g,rfl⟩

def nielsenRawFrontierCornerClassEquiv
    (i:ZMod J.n)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hxN:x∈frontier (fuchsianNielsenCore P hNE)) :
    {j:ZMod J.n // Relation.EqvGen step i j}≃↥(fuchsianPolygonCycle P D x) := by
  let f:{j:ZMod J.n // Relation.EqvGen step i j}→↥(fuchsianPolygonCycle P D x):=fun j=>
    Classical.choose (nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx j.val
      j.property)
  have hf (j:{j:ZMod J.n // Relation.EqvGen step i j}) :
      vertex j.val=Hyperbolic.discToClosedModel (P.finiteCoordinate (f j).val):=
    Classical.choose_spec (nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx j.val
      j.property)
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply nielsenCyclicVertex_injective hD hNE hFG J hv
    exact (hf a).trans ((congrArg (fun y:↥(fuchsianPolygonCycle P D x)=>
      Hyperbolic.discToClosedModel (P.finiteCoordinate y.val)) hab).trans (hf b).symm)
  · intro y
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp y.property.2
    have hyN:y.val∈frontier (fuchsianNielsenCore P hNE):=by
      rw [←hg,←fuchsianNielsenCore_smul_frontier P hNE g]
      exact mem_smul_set.mpr ⟨x,hxN,rfl⟩
    obtain ⟨j,hj⟩:=nielsenCore_frontier_orbit_marked_vertex hD hNE hFG w hwD hwN J hv i x y.val hx
      y.property.1 hyN g hg
    have hij:=nielsenCoreFiniteFrontierCorner_orbit_rawChain hD hNE hFG hfin w hwD hwN J hc hv
      i j x y.val hx hj hxN hyN ⟨g,hg⟩
    refine ⟨⟨j,hij⟩,?_⟩
    apply Subtype.ext
    apply P.finiteCoordinate.injective
    apply Hyperbolic.isEmbedding_discToClosedModel.injective
    exact (hf ⟨j,hij⟩).symm.trans hj.symm

theorem nielsenRawFrontierCornerClassEquiv_spec
    (i:ZMod J.n)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hxN:x∈frontier (fuchsianNielsenCore P hNE))
    (j:{j:ZMod J.n // Relation.EqvGen step i j}) :
    vertex j.val=Hyperbolic.discToClosedModel (P.finiteCoordinate
      (nielsenRawFrontierCornerClassEquiv hD hNE hFG hfin w hwD hwN J hc hv i x hx hxN j).val) :=
  Classical.choose_spec (nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx j.val
    j.property)

theorem nielsenRawFrontierCornerClass_angle_sum
    (i:ZMod J.n)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hxN:x∈frontier (fuchsianNielsenCore P hNE)) :
    ∑j:{j:ZMod J.n // Relation.EqvGen step i j},(Q).angle ((originalCyclicFinIndex J).symm j.val)=Real.pi := by
  classical
  let E:=nielsenRawFrontierCornerClassEquiv hD hNE hFG hfin w hwD hwN J hc hv i x hx hxN
  let F:=(hD.locallyFinite.cycle_finite x).toFinset
  let ec:↥(fuchsianPolygonCycle P D x)≃↥(F:Set P.domain.carrier):=
    Set.equivOfEq (hD.locallyFinite.cycle_finite x).coe_toFinset.symm
  let T:=E.trans ec
  have hAngles (j:{j:ZMod J.n // Relation.EqvGen step i j}) :
      (Q).angle ((originalCyclicFinIndex J).symm j.val)=
        fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) (T j).val:=by
    change (Q).angle ((originalCyclicFinIndex J).symm j.val)=
      fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) (E j).val
    apply nielsenCyclicDiscPolygon_angle_eq_fuchsian hD hNE hFG hfin w hwD hwN J hc hv
    change vertex ((originalCyclicFinIndex J) ((originalCyclicFinIndex J).symm j.val))=_
    rw [Equiv.apply_symm_apply]
    exact nielsenRawFrontierCornerClassEquiv_spec hD hNE hFG hfin w hwD hwN J hc hv i x hx hxN j
  calc
    _=∑j,fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) (T j).val:=by
      apply Finset.sum_congr rfl
      intro j _hj
      exact hAngles j
    _=∑y:↥(F:Set P.domain.carrier),fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y.val:=
      Equiv.sum_comp T (fun y:↥(F:Set P.domain.carrier)=>fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y.val)
    _=∑y∈F,fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y:=Finset.sum_coe_sort _ _
    _=fuchsianPolygonAngle P (fuchsianNielsenCore P hNE) x/fuchsianPointOrder P x:=
      nielsenCore_cycleAngle_sum hD hNE w hwD hwN x (frontier_subset_closure hxN)
    _=Real.pi:=by rw [fuchsianNielsenCore_frontier_angle_eq_pi P hNE x hxN,
      finitelyGenerated_nielsenCore_frontier_pointOrder_one P hNE hFG x hxN,Nat.cast_one,div_one]

end NielsenFrontierCornerAngles



section NielsenInteriorCornerChains
open LeanEval.Topology.ClassificationOfSurfaces.Moise
local instance nielsenInteriorCornerChainSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenInteriorCornerChainSphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv

include w hwD hwN in
theorem nielsenCore_interior_orbit_marked_vertex
    (i:ZMod J.n) (x y:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hxN:x∈fuchsianNielsenCore P hNE) (hyD:y∈closure D)
    (g:H) (hg:g•x=y) :
    ∃j:ZMod J.n,Hyperbolic.discToClosedModel (P.finiteCoordinate y)=vertex j := by
  have hmark:=nielsenCyclicVertex_marked hD hNE hFG J hv i
  have hxB:=nielsenBoundaryMarkSaturation_subset_boundary P hNE D
    (nielsenBoundarySeedMarks hD hNE hFG) ⟨vertex i,hmark,rfl⟩
  rw [←hx] at hxB
  have hxF:=(nielsenCore_klein_finite_frontier hD hNE w hwD hwN x).mp hxB
  have hyN:y∈fuchsianNielsenCore P hNE:=hg ▸ fuchsianNielsenCore_invariant P hNE g x hxN
  have hyC:y∈closure (D∩fuchsianNielsenCore P hNE):=by
    rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
    exact ⟨hyD,subset_closure hyN⟩
  have hyNot:y∉D:=by
    by_cases hgone:g=1
    · have he:x=y:=by simpa only [hgone,one_smul] using hg
      intro hy
      exact ((hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)).frontier_eq ▸ hxF).2
        ⟨he.symm ▸ hy,hxN⟩
    · have hyF:y∈frontier D:=hD.locallyFinite.fundamental.closed_tile_intersection_subset_frontier hgone
          ⟨hyD,x,closure_mono inter_subset_left (frontier_subset_closure hxF),hg⟩
      exact ((hD.locallyFinite.fundamental.isOpen).frontier_eq ▸ hyF).2
  have hyF:y∈frontier (D∩fuchsianNielsenCore P hNE):=by
    rw [(hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)).frontier_eq]
    exact ⟨hyC,fun hy=>hyNot hy.1⟩
  have himg:(P.compactifiedAction g).closedMap (vertex i)=Hyperbolic.discToClosedModel (P.finiteCoordinate y):=by
    rw [←hx,P.compactifiedAction_finite,hg]
  have hyB:Hyperbolic.closedKleinCoordinate ((P.compactifiedAction g).closedMap (vertex i))∈
      frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)):=by
    rw [himg]
    exact (nielsenCore_klein_finite_frontier hD hNE w hwD hwN y).mpr hyF
  have hm:=nielsenBoundaryMarkSaturation_map_mem P hNE D
    (nielsenBoundarySeedMarks hD hNE hFG) g (vertex i) hmark hyB
  rw [himg] at hm
  obtain ⟨j,hj⟩:=(hv (Polygon.discPolygonKleinPlane (Hyperbolic.discToClosedModel (P.finiteCoordinate
    y)))).mpr ⟨_,hm,rfl⟩
  exact ⟨j,Polygon.discPolygonKleinPlane_injective (hj.symm.trans (nielsenCyclicVertex_plane hD hNE hFG J hv j).symm)⟩

include hD w hwD hwN in
theorem nielsenCore_interior_incident_positive_inter
    (x:P.domain.carrier) (hxN:x∈fuchsianNielsenCore P hNE) (a b:H)
    (hax:x∈fuchsianDomainTile P D a) (hbx:x∈fuchsianDomainTile P D b)
    (hab:(fuchsianDomainTile P D a∩fuchsianDomainTile P D b).Nontrivial) :
    (fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) a∩
      fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) b).Nontrivial := by
  let C:=fuchsianDomainTile P D a∩fuchsianDomainTile P D b
  have hconn:IsPreconnected C:=by
    apply (polygonPointCoordinate P x).isPreconnected_image.mp
    rw [image_inter (polygonPointCoordinate P x).injective,polygonPointCoordinate_image_tile,
      polygonPointCoordinate_image_tile]
    apply Hyperbolic.DiscHConvex.isPreconnected
    intro z hz u hu v hv
    exact ⟨(hD.pointCoordinate_smul_convex x a).closure z hz.1 u hu.1 hv,
      (hD.pointCoordinate_smul_convex x b).closure z hz.2 u hu.2 hv⟩
  have hpre:Preperfect C:=hconn.preperfect_of_nontrivial hab
  have hacc:AccPt x (𝓟 (fuchsianNielsenCore P hNE∩C)):=
    hpre.open_inter (fuchsianNielsenCore_isOpen P hNE) x ⟨hxN,hax,hbx⟩
  obtain ⟨u,hu,v,hv,huv⟩:=(Set.Infinite.of_accPt hacc).nontrivial
  rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN,
    nielsenCore_closed_tile_inter hD hNE w hwD hwN]
  exact ⟨u,⟨⟨hu.2.1,subset_closure hu.1⟩,hu.2.2,subset_closure hu.1⟩,
    v,⟨⟨hv.2.1,subset_closure hv.1⟩,hv.2.2,subset_closure hv.1⟩,huv⟩

theorem nielsenCoreFiniteInteriorCorner_orbit_rawChain
    (i j:ZMod J.n) (x y:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hy:Hyperbolic.discToClosedModel (P.finiteCoordinate y)=vertex j)
    (hxN:x∈fuchsianNielsenCore P hNE)
    (horbit:∃g:H,g•x=y) : Relation.EqvGen step i j := by
  classical
  let Q:=D∩fuchsianNielsenCore P hNE
  let R:=fun a b:H=>x∈fuchsianDomainTile P D a∧x∈fuchsianDomainTile P D b∧
    (fuchsianDomainTile P D a∩fuchsianDomainTile P D b).Nontrivial
  have hcut (a:H) (ha:x∈fuchsianDomainTile P D a) : x∈fuchsianDomainTile P Q a:=by
    rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN]
    exact ⟨ha,subset_closure hxN⟩
  have hmem {a b:H} (h:Relation.EqvGen R a b) :
      x∈fuchsianDomainTile P D a↔x∈fuchsianDomainTile P D b:=by
    induction h with
    | rel a b hab => exact ⟨fun _=>hab.2.1,fun _=>hab.1⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  have hindex (a:H) (ha:x∈fuchsianDomainTile P D a) :
      ∃k:ZMod J.n,Hyperbolic.discToClosedModel (P.finiteCoordinate (a⁻¹•x))=vertex k:=by
    exact nielsenCore_interior_orbit_marked_vertex hD hNE hFG w hwD hwN J hv i x (a⁻¹•x) hx hxN
      (by simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using ha) a⁻¹ rfl
  have hmap {a b:H} (h:Relation.EqvGen R a b) :
      x∈fuchsianDomainTile P D a→∀k l:ZMod J.n,
        Hyperbolic.discToClosedModel (P.finiteCoordinate (a⁻¹•x))=vertex k→
        Hyperbolic.discToClosedModel (P.finiteCoordinate (b⁻¹•x))=vertex l→Relation.EqvGen step k l:=by
    induction h with
    | rel a b hab =>
      intro _ k l hk hl
      exact nielsenCore_positive_incident_pair_rawChain hD hNE hFG hfin w hwD hwN J hc hv x a b
        (hcut a hab.1) (hcut b hab.2.1)
        (nielsenCore_interior_incident_positive_inter hD hNE w hwD hwN x hxN a b hab.1 hab.2.1 hab.2.2) k l hk hl
    | refl =>
      intro _ k l hk hl
      have he:k=l:=nielsenCyclicVertex_injective hD hNE hFG J hv (hk.symm.trans hl)
      exact he ▸ Relation.EqvGen.refl _
    | symm _ _ hab ih =>
      intro hb k l hk hl
      exact Relation.EqvGen.symm _ _ (ih ((hmem hab).mpr hb) l k hl hk)
    | trans _ b _ hab _ ih1 ih2 =>
      intro ha k l hk hl
      have hb:=(hmem hab).mp ha
      obtain ⟨m,hm⟩:=hindex b hb
      exact Relation.EqvGen.trans _ _ _ (ih1 ha k m hk hm) (ih2 hb m l hm hl)
  obtain ⟨g,hg⟩:=horbit
  have hxD: x∈closure D:=closure_mono inter_subset_left
    (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv i x hx)
  have hyD:y∈closure D:=closure_mono inter_subset_left
    (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv j y hy)
  have h1:x∈fuchsianDomainTile P D (1:H):=by simpa only [fuchsianDomainTile,one_smul] using hxD
  have hgI:x∈fuchsianDomainTile P D g⁻¹:=by
    refine ⟨y,hyD,?_⟩
    change g⁻¹•y=x
    rw [←hg,inv_smul_smul]
  have hchain:=hD.incident_tile_nontrivial_chains x 1 g⁻¹ h1 hgI
  apply hmap hchain h1 i j
  · simpa only [inv_one,one_smul] using hx
  · simpa only [inv_inv,hg] using hy

end NielsenInteriorCornerChains



section NielsenRawFiniteCornerCycles
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv
local notation "Q" => nielsenCyclicDiscPolygon hD hNE hFG hfin w hwD hwN J hc hv

include w hwD hwN in
theorem nielsenCore_finite_orbit_marked_vertex
    (i:ZMod J.n) (x y:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hyD:y∈closure D)
    (g:H) (hg:g•x=y) :
    ∃j:ZMod J.n,Hyperbolic.discToClosedModel (P.finiteCoordinate y)=vertex j := by
  by_cases hxN:x∈fuchsianNielsenCore P hNE
  · exact nielsenCore_interior_orbit_marked_vertex hD hNE hFG w hwD hwN J hv i x y hx hxN hyD g hg
  · have hcl:=closure_mono inter_subset_right
      (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv i x hx)
    have hxf:x∈frontier (fuchsianNielsenCore P hNE):=by
      rw [(fuchsianNielsenCore_isOpen P hNE).frontier_eq]
      exact ⟨hcl,hxN⟩
    have hyf:y∈frontier (fuchsianNielsenCore P hNE):=by
      rw [←hg,←fuchsianNielsenCore_smul_frontier P hNE g]
      exact mem_smul_set.mpr ⟨x,hxf,rfl⟩
    exact nielsenCore_frontier_orbit_marked_vertex hD hNE hFG w hwD hwN J hv i x y hx hyD hyf g hg

theorem nielsenCoreFiniteCorner_orbit_rawChain
    (i j:ZMod J.n) (x y:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hy:Hyperbolic.discToClosedModel (P.finiteCoordinate y)=vertex j)
    (horbit:∃g:H,g•x=y) : Relation.EqvGen step i j := by
  by_cases hxN:x∈fuchsianNielsenCore P hNE
  · exact nielsenCoreFiniteInteriorCorner_orbit_rawChain hD hNE hFG hfin w hwD hwN J hc hv i j x y hx hy hxN horbit
  · have hcl:=closure_mono inter_subset_right
      (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv i x hx)
    have hxf:x∈frontier (fuchsianNielsenCore P hNE):=by
      rw [(fuchsianNielsenCore_isOpen P hNE).frontier_eq]
      exact ⟨hcl,hxN⟩
    obtain ⟨g,hg⟩:=horbit
    have hyf:y∈frontier (fuchsianNielsenCore P hNE):=by
      rw [←hg,←fuchsianNielsenCore_smul_frontier P hNE g]
      exact mem_smul_set.mpr ⟨x,hxf,rfl⟩
    exact nielsenCoreFiniteFrontierCorner_orbit_rawChain hD hNE hFG hfin w hwD hwN J hc hv i j x y hx hy hxf hyf ⟨g,hg⟩

/-- All finite cut-corner classes, including interior elliptic classes, are the complete literal original orbit cycles. -/
def nielsenRawFiniteCornerClassEquiv
    (i:ZMod J.n)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i) :
    {j:ZMod J.n // Relation.EqvGen step i j}≃↥(fuchsianPolygonCycle P D x) := by
  let f:{j:ZMod J.n // Relation.EqvGen step i j}→↥(fuchsianPolygonCycle P D x):=fun j=>
    Classical.choose (nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx j.val
      j.property)
  have hf (j:{j:ZMod J.n // Relation.EqvGen step i j}) :
      vertex j.val=Hyperbolic.discToClosedModel (P.finiteCoordinate (f j).val):=
    Classical.choose_spec (nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx j.val
      j.property)
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply nielsenCyclicVertex_injective hD hNE hFG J hv
    exact (hf a).trans ((congrArg (fun y:↥(fuchsianPolygonCycle P D x)=>
      Hyperbolic.discToClosedModel (P.finiteCoordinate y.val)) hab).trans (hf b).symm)
  · intro y
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp y.property.2
    obtain ⟨j,hj⟩:=nielsenCore_finite_orbit_marked_vertex hD hNE hFG w hwD hwN J hv i x y.val hx y.property.1 g hg
    have hij:=nielsenCoreFiniteCorner_orbit_rawChain hD hNE hFG hfin w hwD hwN J hc hv i j x y.val hx hj ⟨g,hg⟩
    refine ⟨⟨j,hij⟩,?_⟩
    apply Subtype.ext
    apply P.finiteCoordinate.injective
    apply Hyperbolic.isEmbedding_discToClosedModel.injective
    exact (hf ⟨j,hij⟩).symm.trans hj.symm

theorem nielsenRawFiniteCornerClassEquiv_spec
    (i:ZMod J.n)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (j:{j:ZMod J.n // Relation.EqvGen step i j}) :
    vertex j.val=Hyperbolic.discToClosedModel (P.finiteCoordinate
      (nielsenRawFiniteCornerClassEquiv hD hNE hFG hfin w hwD hwN J hc hv i x hx j).val) :=
  Classical.choose_spec (nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx j.val
    j.property)

theorem nielsenRawFiniteCornerClass_angle_sum
    (i:ZMod J.n)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i) :
    ∑j:{j:ZMod J.n // Relation.EqvGen step i j},(Q).angle ((originalCyclicFinIndex J).symm j.val)=
      fuchsianPolygonAngle P (fuchsianNielsenCore P hNE) x/fuchsianPointOrder P x := by
  classical
  let E:=nielsenRawFiniteCornerClassEquiv hD hNE hFG hfin w hwD hwN J hc hv i x hx
  let F:=(hD.locallyFinite.cycle_finite x).toFinset
  let ec:↥(fuchsianPolygonCycle P D x)≃↥(F:Set P.domain.carrier):=
    Set.equivOfEq (hD.locallyFinite.cycle_finite x).coe_toFinset.symm
  let T:=E.trans ec
  have hAngles (j:{j:ZMod J.n // Relation.EqvGen step i j}) :
      (Q).angle ((originalCyclicFinIndex J).symm j.val)=
        fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) (T j).val:=by
    change (Q).angle ((originalCyclicFinIndex J).symm j.val)=
      fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) (E j).val
    apply nielsenCyclicDiscPolygon_angle_eq_fuchsian hD hNE hFG hfin w hwD hwN J hc hv
    change vertex ((originalCyclicFinIndex J) ((originalCyclicFinIndex J).symm j.val))=_
    rw [Equiv.apply_symm_apply]
    exact nielsenRawFiniteCornerClassEquiv_spec hD hNE hFG hfin w hwD hwN J hc hv i x hx j
  calc
    _=∑j,fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) (T j).val:=by
      apply Finset.sum_congr rfl
      intro j _hj
      exact hAngles j
    _=∑y:↥(F:Set P.domain.carrier),fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y.val:=
      Equiv.sum_comp T (fun y:↥(F:Set P.domain.carrier)=>fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y.val)
    _=∑y∈F,fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y:=Finset.sum_coe_sort _ _
    _=_:=nielsenCore_cycleAngle_sum hD hNE w hwD hwN x (closure_mono inter_subset_right
      (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv i x hx))

end NielsenRawFiniteCornerCycles



theorem fuchsianNielsenCore_interior_angle_eq_two_pi
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (x:P.domain.carrier) (hx:x∈fuchsianNielsenCore P hNE) :
    fuchsianPolygonAngle P (fuchsianNielsenCore P hNE) x=2*Real.pi := by
  apply Hyperbolic.discSubtendedAngle_of_interior
  apply interior_mono (image_mono (subset_closure (s:=fuchsianNielsenCore P hNE)))
  rw [(P.finiteCoordinate.isOpenMap _ (fuchsianNielsenCore_isOpen P hNE)).interior_eq]
  exact mem_image_of_mem _ hx

section NielsenRawCornerWeights
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv
local notation "Q" => nielsenCyclicDiscPolygon hD hNE hFG hfin w hwD hwN J hc hv
local notation "T" => nielsenCoreRawCornerSetoid hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv

/-- Actual finite core points have their reciprocal stabilizer weights, true finite frontier points have half weight, and ideal points have zero weight. -/
def nielsenRawCornerWeight (i:ZMod J.n) : ℝ :=
  if hi:‖(vertex i:ℂ)‖<1 then
    let x:=P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex i) hi)
    if x∈fuchsianNielsenCore P hNE then 1/(fuchsianPointOrder P x:ℝ) else 1/2
  else 0
local notation "weight" => nielsenRawCornerWeight hD hNE hFG J hv

theorem nielsenRawCornerWeight_finite (i:ZMod J.n) (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i) :
    weight i=if x∈fuchsianNielsenCore P hNE then 1/(fuchsianPointOrder P x:ℝ) else 1/2 := by
  have hn:‖(vertex i:ℂ)‖<1:=by rw [←hx];exact (P.finiteCoordinate x).norm_lt_one
  have he:P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex i) hn)=x:=by
    apply P.finiteCoordinate.injective
    rw [P.finiteCoordinate.apply_symm_apply]
    apply Hyperbolic.isEmbedding_discToClosedModel.injective
    exact (Hyperbolic.closedDiscFinitePoint_spec _ hn).trans hx.symm
  rw [nielsenRawCornerWeight,dite_eq_left hn]
  dsimp only
  rw [he]

theorem nielsenRawCorner_finite_iff_rawChain {i j:ZMod J.n} (hij:Relation.EqvGen step i j) :
    ‖(vertex i:ℂ)‖<1 ↔ ‖(vertex j:ℂ)‖<1 := by
  have hf (a b:ZMod J.n) (hab:Relation.EqvGen step a b) (ha:‖(vertex a:ℂ)‖<1) :
      ‖(vertex b:ℂ)‖<1:=by
    let x:=P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex a) ha)
    have hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex a:=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact Hyperbolic.closedDiscFinitePoint_spec _ ha
    obtain ⟨y,hy⟩:=nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv a x hx b hab
    rw [hy]
    exact (P.finiteCoordinate y.val).norm_lt_one
  exact ⟨hf i j hij,hf j i (Relation.EqvGen.symm _ _ hij)⟩

theorem nielsenRawCornerWeight_eq_of_rawChain {i j:ZMod J.n} (hij:Relation.EqvGen step i j) :
    weight i=weight j := by
  by_cases hn:‖(vertex i:ℂ)‖<1
  · let x:=P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex i) hn)
    have hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i:=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact Hyperbolic.closedDiscFinitePoint_spec _ hn
    obtain ⟨y,hy⟩:=nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx j hij
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp y.property.2
    have hN:x∈fuchsianNielsenCore P hNE ↔ y.val∈fuchsianNielsenCore P hNE:=by
      constructor
      · intro hxN
        exact hg ▸ fuchsianNielsenCore_invariant P hNE g x hxN
      · intro hyN
        have hh:=fuchsianNielsenCore_invariant P hNE g⁻¹ y.val hyN
        rwa [←hg,inv_smul_smul] at hh
    rw [nielsenRawCornerWeight_finite hD hNE hFG J hv i x hx,
      nielsenRawCornerWeight_finite hD hNE hFG J hv j y.val hy.symm,
      fuchsianPointOrder_eq_of_mem_cycle P D x y.val y.property]
    exact if_congr hN rfl rfl
  · have hj:¬‖(vertex j:ℂ)‖<1:=fun h=>hn ((nielsenRawCorner_finite_iff_rawChain hD hNE hFG hfin w hwD hwN J hc hv
    hij).mpr h)
    rw [nielsenRawCornerWeight,dite_eq_right hn,nielsenRawCornerWeight,dite_eq_right hj]

def nielsenRawCornerClassWeight : V→ℝ :=
  Quotient.lift weight (fun _ _ h=>nielsenRawCornerWeight_eq_of_rawChain hD hNE hFG hfin w hwD hwN J hc hv h)
local notation "classWeight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenRawCornerClassWeight_mk (i:ZMod J.n) : classWeight (Quotient.mk _ i)=weight i := rfl

theorem nielsenRawCornerClass_angle_sum (i:ZMod J.n) :
    ∑j:{j:ZMod J.n // Relation.EqvGen step i j},(Q).angle ((originalCyclicFinIndex J).symm j.val)=
      2*Real.pi*weight i := by
  by_cases hn:‖(vertex i:ℂ)‖<1
  · let x:=P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex i) hn)
    have hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i:=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact Hyperbolic.closedDiscFinitePoint_spec _ hn
    rw [nielsenRawFiniteCornerClass_angle_sum hD hNE hFG hfin w hwD hwN J hc hv i x hx,
      nielsenRawCornerWeight_finite hD hNE hFG J hv i x hx]
    by_cases hxN:x∈fuchsianNielsenCore P hNE
    · rw [ite_eq_left hxN,fuchsianNielsenCore_interior_angle_eq_two_pi P hNE x hxN]
      ring
    · have hxF:x∈frontier (fuchsianNielsenCore P hNE):=by
        rw [(fuchsianNielsenCore_isOpen P hNE).frontier_eq]
        exact ⟨closure_mono inter_subset_right
          (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv i x hx),hxN⟩
      rw [ite_eq_right hxN,fuchsianNielsenCore_frontier_angle_eq_pi P hNE x hxF,
        finitelyGenerated_nielsenCore_frontier_pointOrder_one P hNE hFG x hxF,Nat.cast_one,div_one]
      ring
  · rw [nielsenRawCornerWeight,dite_eq_right hn,mul_zero]
    apply Finset.sum_eq_zero
    intro j _hj
    have hj:¬‖(vertex j.val:ℂ)‖<1:=fun h=>
      hn ((nielsenRawCorner_finite_iff_rawChain hD hNE hFG hfin w hwD hwN J hc hv j.property).mpr h)
    apply (Q).angle_of_ideal
    change ‖(vertex ((originalCyclicFinIndex J) ((originalCyclicFinIndex J).symm j.val)):ℂ)‖=1
    rw [Equiv.apply_symm_apply]
    exact le_antisymm (vertex j.val).norm_le_one (le_of_not_gt hj)

theorem nielsenRawCornerClass_quotient_angle_sum (q:V) :
    ∑j:{j:ZMod J.n // Quotient.mk (T) j=q},(Q).angle ((originalCyclicFinIndex J).symm j.val)=
      2*Real.pi*classWeight q := by
  refine Quotient.inductionOn q ?_
  intro i
  let E:{j:ZMod J.n // Quotient.mk (T) j=Quotient.mk (T) i}≃
      {j:ZMod J.n // Relation.EqvGen step i j}:=
    Equiv.subtypeEquivRight (fun _=>⟨fun h=>Relation.EqvGen.symm _ _ (Quotient.exact h),
      fun h=>Quotient.sound (Relation.EqvGen.symm _ _ h)⟩)
  calc
    _=∑j:{j:ZMod J.n // Relation.EqvGen step i j},(Q).angle ((originalCyclicFinIndex J).symm j.val):=
      Equiv.sum_comp E (fun j=>(Q).angle ((originalCyclicFinIndex J).symm j.val))
    _=2*Real.pi*weight i:=nielsenRawCornerClass_angle_sum hD hNE hFG hfin w hwD hwN J hc hv i
    _=2*Real.pi*classWeight (Quotient.mk _ i):=rfl

theorem nielsenRawCornerClasses_total_angle :
    ∑i:Fin J.n,(Q).angle i=2*Real.pi*∑q:V,classWeight q := by
  calc
    _=∑j:ZMod J.n,(Q).angle ((originalCyclicFinIndex J).symm j):=
      (Equiv.sum_comp (originalCyclicFinIndex J).symm (Q).angle).symm
    _=∑q:V,∑j:{j:ZMod J.n // Quotient.mk (T) j=q},(Q).angle ((originalCyclicFinIndex J).symm j.val):=
      (Fintype.sum_fiberwise (Quotient.mk (T)) (fun j=>(Q).angle ((originalCyclicFinIndex J).symm j))).symm
    _=∑q:V,2*Real.pi*classWeight q:=by
      apply Finset.sum_congr rfl
      intro q _hq
      exact nielsenRawCornerClass_quotient_angle_sum hD hNE hFG hfin w hwD hwN J hc hv q
    _=2*Real.pi*∑q:V,classWeight q:=(Finset.mul_sum _ _ _).symm

/-- The true Nielsen area is now partitioned by actual reciprocal stabilizers, actual frontier half-weights, and actual ideal zero-weights. -/
theorem nielsenRawCornerClasses_weightedEuler :
    (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
      (-(Surfaces.CyclicSurface.eulerCharacteristic (Pcap):ℝ)+Fintype.card C-(Fintype.card B:ℝ)/2+
        ∑q:V,(1-classWeight q)) := by
  have h:=nielsenCyclicDiscPolygon_area_rawEuler hD hNE hFG hfin w hwD hwN J hc hv
  rw [nielsenRawCornerClasses_total_angle hD hNE hFG hfin w hwD hwN J hc hv] at h
  have hCard:(∑q:V,(1:ℝ))=(Nat.card V:ℝ):=by simp [Nat.card_eq_fintype_card]
  rw [Finset.sum_sub_distrib,hCard]
  linear_combination h

end NielsenRawCornerWeights



section NielsenNonBoundaryWeightedEuler
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "RB" => nielsenRawBoundaryVertices hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenRawCornerClassWeight_boundary (b:B) : weight (Quotient.mk _ b.val)=1/2 := by
  have hb:=nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b
  rw [nielsenRawCornerClassWeight_mk,nielsenRawCornerWeight_finite hD hNE hFG J hv b.val
    (nielsenCyclicBoundaryNativePoint hD hNE hFG hfin w hwD hwN J hc hv b) hb.1]
  exact ite_eq_right (((fuchsianNielsenCore_isOpen P hNE).frontier_eq ▸ hb.2).2)

theorem nielsenRawBoundaryClasses_deficit_sum :
    (∑q:↥(RB),(1-weight q.val))=(Fintype.card B:ℝ)/2 := by
  let E:=nielsenRawBoundaryVertexEquiv hD hNE hFG hfin w hwD hwN J hc hv
  calc
    _=∑b:B,(1-weight (E b).val):=(Equiv.sum_comp E (fun q:↥(RB)=>(1-weight q.val))).symm
    _=∑_b:B,(1/2:ℝ):=by
      apply Finset.sum_congr rfl
      intro b _hb
      change 1-weight (Quotient.mk _ b.val)=1/2
      rw [nielsenRawCornerClassWeight_boundary]
      ring
    _=(Fintype.card B:ℝ)/2:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

/-- Boundary half-weights cancel the genuine unpaired-edge correction, leaving only nonboundary deficits and the actual cap-cycle count. -/
theorem nielsenNonBoundaryRawCorners_weightedEuler :
    (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
      (-(Surfaces.CyclicSurface.eulerCharacteristic (Pcap):ℝ)+Fintype.card C+
        ∑q:{q:V // q∉RB},(1-weight q.val)) := by
  have h:=nielsenRawCornerClasses_weightedEuler hD hNE hFG hfin w hwD hwN J hc hv
  have hsplit:=Fintype.sum_subtype_add_sum_subtype (fun q:V=>q∈RB) (fun q=>1-weight q)
  change (∑q:↥(RB),(1-weight q.val))+
    (∑q:{q:V // q∉RB},(1-weight q.val))=(∑q:V,(1-weight q)) at hsplit
  rw [nielsenRawBoundaryClasses_deficit_sum hD hNE hFG hfin w hwD hwN J hc hv] at hsplit
  rw [←hsplit] at h
  linear_combination h

theorem nielsenNonBoundaryRawCorners_genus_area :
    ∃g,Surfaces.HasTopologicalGenus ((Pcap).PolygonalRealization
      (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
        (2*(g:ℝ)-2+Fintype.card C+∑q:{q:V // q∉RB},(1-weight q.val)) := by
  obtain ⟨g,hg,hχ⟩:=nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv
  refine ⟨g,hg,?_⟩
  have hχR:(Surfaces.CyclicSurface.eulerCharacteristic (Pcap):ℝ)=2-2*(g:ℝ):=by exact_mod_cast hχ
  rw [nielsenNonBoundaryRawCorners_weightedEuler hD hNE hFG hfin w hwD hwN J hc hv,hχR]
  ring

end NielsenNonBoundaryWeightedEuler



/-- Averaging a genuine finite rotation orbit stays in the original convex region and gives the origin. -/
theorem nielsen_finite_rotation_convex_zero
    {G:Type*} [Group G] [Fintype G] (φ:G→*ℂˣ)
    (hφ:∃a:G,φ a≠1) {S:Set ℂ} (hS:Convex ℝ S) (hn:S.Nonempty)
    (hi:∀g:G,∀z∈S,(φ g:ℂ)*z∈S) : (0:ℂ)∈S := by
  classical
  obtain ⟨z,hz⟩:=hn
  obtain ⟨a,ha⟩:=hφ
  let v:G→ℂ:=fun g=>(φ g:ℂ)*z
  have he:(φ a:ℂ)*(∑g:G,v g)=∑g:G,v g:=by
    calc
      _=∑g:G,v (a*g):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _hg
        simp only [v,map_mul,Units.val_mul]
        ring
      _=∑g:G,v g:=Equiv.sum_comp (Equiv.mulLeft a) v
  have hs:∑g:G,v g=0:=by
    have hp:((φ a:ℂ)-1)*(∑g:G,v g)=0:=by linear_combination he
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (fun h=>ha (Units.ext h)))
  have hm:=hS.centerMass_mem (t:=Finset.univ) (w:=fun _g:G=>(1:ℝ)) (z:=v)
    (fun _g _hg=>zero_le_one) (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one];exact_mod_cast Fintype.card_pos)
    (fun g _hg=>hi g z hz)
  simpa only [Finset.centerMass,one_smul,hs,smul_zero] using hm



/-- Genuine unit rotations commute with the actual Klein coordinate. -/
theorem nielsen_klein_rotation (a:ℂˣ) (ha:‖(a:ℂ)‖=1)
    (z v:𝔻) (hv:(v:ℂ)=(a:ℂ)*(z:ℂ)) :
    Hyperbolic.kleinCoordinate v=(a:ℂ)*Hyperbolic.kleinCoordinate z := by
  have hn:‖(v:ℂ)‖=‖(z:ℂ)‖:=by rw [hv,norm_mul,ha,one_mul]
  change Hyperbolic.kleinFormula v=(a:ℂ)*Hyperbolic.kleinFormula z
  unfold Hyperbolic.kleinFormula
  rw [hn,hv]
  ring

/-- A nontrivial actual interior stabilizer forces the origin into the genuine invariant core. -/
theorem nielsen_nontrivial_zero_stabilizer_mem_core
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (z:P.domain.carrier)
    (hz:z.val=((0:ℂ):Mobius.ExtendedComplex))
    (f:H) (hf:f≠1) (hfix:f•z=z) : z∈fuchsianNielsenCore P hNE := by
  classical
  let K:=DiscreteGroups.mobiusBoundaryStabilizer H z.val
  let :Finite K:=(DiscreteGroups.mobiusBoundaryStabilizer_finite H P.discontinuous z.val z.property).to_subtype
  let :=Fintype.ofFinite K
  have hK (k:K):k.val∈H∧k.val.val z.val=z.val:=
    (DiscreteGroups.mem_mobiusBoundaryStabilizer H z.val k.val).mp k.property
  have h0 (k:K):k.val.val (0:ℂ)=(0:ℂ):=by simpa only [hz] using (hK k).2
  have h0all:∀k∈K,k.val (0:ℂ)=(0:ℂ):=fun k hk=>h0 ⟨k,hk⟩
  have hi:K≤Mobius.mobiusInftyStabilizer:=by
    intro k hk
    exact discPreserver_fix_zero_infty k (P.asFuchsianDisc.image_eq ⟨k,(hK ⟨k,hk⟩).1⟩)
      (h0 ⟨k,hk⟩)
  let φ:=Mobius.subgroupMultiplierHom K hi
  have hφ:∃a:K,φ a≠1:=by
    let a:K:=⟨f.val,(DiscreteGroups.mem_mobiusBoundaryStabilizer H z.val f.val).mpr
      ⟨f.property,congrArg Subtype.val hfix⟩⟩
    refine ⟨a,fun he=>hf ?_⟩
    have he':φ a=φ 1:=he.trans (map_one φ).symm
    have ha:=DiscreteGroups.subgroupMultiplierHom_injective_of_fix_zero K hi h0all he'
    apply Subtype.ext
    change f.val=1
    exact congrArg Subtype.val ha
  let S:=P.kleinCoordinate '' fuchsianNielsenCore P hNE
  have hc:Convex ℝ S:=by
    have hc':=(Hyperbolic.discHConvex_iff_klein_convex _).mp (fuchsianNielsenCore_convex P hNE)
    simpa only [S,UnitDiscFuchsianGroup.kleinCoordinate,image_image] using hc'
  have hn:S.Nonempty:=(fuchsianNielsenCore_isConnected P hNE).nonempty.image _
  have hInv:∀k:K,∀u∈S,(φ k:ℂ)*u∈S:=by
    intro k u hu
    obtain ⟨v,hv,rfl⟩:=hu
    let kH:H:=⟨k.val,(hK k).1⟩
    refine ⟨kH•v,fuchsianNielsenCore_invariant P hNE kH v hv,?_⟩
    apply nielsen_klein_rotation (φ k) (DiscreteGroups.finiteMobius_multiplier_unit_norm K hi k)
    apply OnePoint.coe_injective
    rw [P.finiteCoordinate_extended (kH•v)]
    change k.val.val v.val=((φ k:ℂ)*(P.finiteCoordinate v:ℂ):ℂ)
    rw [DiscreteGroups.dilation_multiplier_representation K hi h0all k,←P.finiteCoordinate_extended
      v,Mobius.mobiusScaling_coe]
  obtain ⟨v,hv,hv0⟩:=nielsen_finite_rotation_convex_zero φ hφ hc hn hInv
  have hz0:P.kleinCoordinate z=0:=by
    have hfin:(P.finiteCoordinate z:ℂ)=0:=by
      apply OnePoint.coe_injective
      exact (P.finiteCoordinate_extended z).trans hz
    simp [UnitDiscFuchsianGroup.kleinCoordinate,
      Hyperbolic.kleinCoordinate,
      Hyperbolic.poincareToKlein,
      Hyperbolic.kleinFormula,hfin]
  have hvz:v=z:=P.kleinCoordinate_isOpenEmbedding.injective (hv0.trans hz0.symm)
  exact hvz ▸ hv

/-- Every original nontrivial interior stabilizer lies in the actual Nielsen region. -/
theorem nielsen_nontrivial_stabilizer_mem_core
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (x:P.domain.carrier)
    (f:H)
    (hf:f≠1)
    (hfix:f•x=x) :
    x∈fuchsianNielsenCore P hNE := by
  classical
  obtain ⟨q,hq,hzero⟩:=P.point_normalizer_exists x
  let Q:=P.conjugateData q hq
  let F:=P.conjugateCoordinate q hq
  let E:=DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hfx:E f•F x=F x:=by rw [←P.conjugateCoordinate_equivariant q hq f x,hfix]
  have hfn:E f≠1:=fun he=>hf (E.injective (he.trans (map_one E).symm))
  have hxQ:=nielsen_nontrivial_zero_stabilizer_mem_core Q (hNE.conjugation q)
    (F x) hzero (E f) hfn hfx
  have hdisc:(P.asFuchsianDisc.nielsenConjugate q)=Q.asFuchsianDisc:=by
    have heq (A B:FuchsianDisc (DiscreteGroups.Action.Actions.subgroupConjugate q H))
        (h:A.carrier=B.carrier):A=B:=by
      cases A
      cases B
      cases h
      rfl
    apply heq
    exact hq
  change q.val x.val∈Q.asFuchsianDisc.nielsenRegion (hNE.conjugation q) at hxQ
  rw [←hdisc,←nielsenRegion_conjugation_image P.asFuchsianDisc hNE q] at hxQ
  obtain ⟨y,hy,he⟩:=hxQ
  change x.val∈P.asFuchsianDisc.nielsenRegion hNE
  exact q.val.injective he ▸ hy



/-- A genuine old refined side containing a core interior point has a positive actual clipped segment. -/
theorem nielsenRefinedSideCarrier_nontrivial_of_core_point
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D}
    (hNE:DiscreteGroups.IsNonElementary H)
    (v:OriginalRefinedSide hD)
    (x:P.domain.carrier)
    (hxN:x∈fuchsianNielsenCore P hNE)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈v.carrier) :
    (nielsenRefinedSideCarrier hNE v).Nontrivial := by
  let S:=P.kleinCoordinate '' fuchsianNielsenCore P hNE
  let Kside:=Hyperbolic.closedKleinCoordinate '' v.carrier
  have hS:IsOpen S:=P.kleinCoordinate_isOpenEmbedding.isOpenMap _ (fuchsianNielsenCore_isOpen P hNE)
  have hT:Kside=segment ℝ (Hyperbolic.closedKleinCoordinate v.leftEndpoint) (Hyperbolic.closedKleinCoordinate v.rightEndpoint):=by
    change Hyperbolic.closedKleinCoordinate '' v.carrier=_
    rw [v.carrier_eq_endpoints,Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  have hconn:IsPreconnected Kside:=by rw [hT];exact (convex_segment _ _).isPreconnected
  have hnt:Kside.Nontrivial:=by
    rw [hT]
    exact ⟨_,left_mem_segment ℝ _ _,_,right_mem_segment ℝ _ _,Hyperbolic.closedKleinCoordinate_injective.ne
      v.endpoints_ne⟩
  have hxT:P.kleinCoordinate x∈Kside:=by
    have h:=mem_image_of_mem Hyperbolic.closedKleinCoordinate hx
    simpa only
      [Hyperbolic.closedKleinCoordinate_disc_inclusion,
        UnitDiscFuchsianGroup.kleinCoordinate] using h
  have hinf:(S∩Kside).Infinite:=Set.Infinite.of_accPt
    ((hconn.preperfect_of_nontrivial hnt).open_inter hS _ ⟨mem_image_of_mem _ hxN,hxT⟩)
  obtain ⟨a,ha,b,hb,hab⟩:=hinf.nontrivial
  obtain ⟨a',ha',haa⟩:=ha.2
  obtain ⟨b',hb',hbb⟩:=hb.2
  have hcore (p:𝕔𝔻) (hp:Hyperbolic.closedKleinCoordinate p∈S):p∈nielsenClosedCore P hNE:=by
    obtain ⟨y,hy,hyp⟩:=hp
    have he:Hyperbolic.discToClosedModel (P.finiteCoordinate y)=p:=by
      apply Hyperbolic.closedKleinCoordinate_injective
      simpa only
        [Hyperbolic.closedKleinCoordinate_disc_inclusion,
          UnitDiscFuchsianGroup.kleinCoordinate] using hyp
    rw [←he]
    exact subset_closure (mem_image_of_mem _ (mem_image_of_mem _ hy))
  refine ⟨a',⟨ha',hcore a' (haa.symm ▸ ha.1)⟩,b',⟨hb',hcore b' (hbb.symm ▸ hb.1)⟩,?_⟩
  intro he
  exact hab (haa.symm.trans ((congrArg Hyperbolic.closedKleinCoordinate he).trans hbb))

/-- Every unchanged old refined endpoint inside the real core remains an actual cut-polygon corner. -/
theorem nielsen_original_endpoint_mem_seed_of_core
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG) (x:P.domain.carrier)
    (hxN:x∈fuchsianNielsenCore P hNE)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈originalRefinedEndpointSet hD) :
    Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈nielsenBoundarySeedMarks hD hNE hFG := by
  classical
  obtain ⟨v,hv⟩ : ∃v:OriginalRefinedSide hD,
      Hyperbolic.discToClosedModel (P.finiteCoordinate x)=v.leftEndpoint∨
      Hyperbolic.discToClosedModel (P.finiteCoordinate x)=v.rightEndpoint:=by
    rcases hx with ⟨v,hv⟩|⟨v,hv⟩
    · exact ⟨v,Or.inl hv.symm⟩
    · exact ⟨v,Or.inr hv.symm⟩
  have hxc:Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈v.carrier:=by
    rcases hv with h|h
    · exact h.symm ▸ v.endpoints_mem_carrier.1
    · exact h.symm ▸ v.endpoints_mem_carrier.2
  let s:NielsenBoundarySide hD hNE:=Sum.inl ⟨v,nielsenRefinedSideCarrier_nontrivial_of_core_point hNE v x hxN hxc⟩
  have hxs:Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈s.carrier:=
    ⟨hxc,subset_closure (mem_image_of_mem _ (mem_image_of_mem _ hxN))⟩
  have hsub:s.carrier⊆Hyperbolic.closedModelDiscHSegment v.leftEndpoint v.rightEndpoint:=by
    rw [←v.carrier_eq_endpoints]
    exact inter_subset_left
  have he:=original_closed_subsegment_endpoint (s.leftEndpoint hFG) (s.rightEndpoint hFG)
    v.leftEndpoint v.rightEndpoint _ v.endpoints_ne
    ((s.endpoints_spec hFG).2 ▸ hsub) ((s.endpoints_spec hFG).2 ▸ hxs) hv
  rcases he with he|he
  · exact Or.inl (Or.inl ⟨s,he.symm⟩)
  · exact Or.inl (Or.inr ⟨s,he.symm⟩)

/-- Every actual original elliptic fixed point in the polygon closure is a genuine core marked corner. -/
theorem nielsenEllipticPoint_mem_canonicalMarks
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (x:P.domain.carrier) (hx:x∈closure D) (he:¬IsAccidentalFuchsianPoint P x) :
    Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈nielsenCanonicalBoundaryMarks hD hNE hFG := by
  obtain ⟨f,hf,hfix⟩:=not_not.mp he
  have hxN:=nielsen_nontrivial_stabilizer_mem_core P hNE x f (fun h=>hf.1 (congrArg Subtype.val h)) hfix
  apply nielsenBoundaryMarkSaturation_contains P hNE D _
    (nielsenBoundarySeedMarks_subset_frontier hD hNE hFG w hwD hwN)
  exact nielsen_original_endpoint_mem_seed_of_core hD hNE hFG x hxN
    (originalEllipticPoint_mem_refinedEndpointSet hD x hx he)




section NielsenRawEllipticClasses
open LeanEval.Topology.ClassificationOfSurfaces.Moise
local instance nielsenRawEllipticSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenRawEllipticSphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv
local notation "rawSetoid" => nielsenCoreRawCornerSetoid hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv

def nielsenRawEllipticClass (q:V) : Prop :=
  ∃i:ZMod J.n,∃x:P.domain.carrier,
    Quotient.mk (rawSetoid) i=q ∧ vertex i=Hyperbolic.discToClosedModel (P.finiteCoordinate x) ∧
    ¬IsAccidentalFuchsianPoint P x
local notation "ellipticRaw" => {q:V // nielsenRawEllipticClass hD hNE hFG hfin w hwD hwN J hc hv q}

def nielsenRawEllipticRepresentative (q:ellipticRaw) :
    Σi:ZMod J.n,{x:P.domain.carrier //
      Quotient.mk (rawSetoid) i=q.val ∧ vertex i=Hyperbolic.discToClosedModel (P.finiteCoordinate x) ∧
      ¬IsAccidentalFuchsianPoint P x} := by
  apply Classical.choice
  obtain ⟨i,x,hi,hx,he⟩:=q.property
  exact ⟨⟨i,⟨x,hi,hx,he⟩⟩⟩
local notation "rep" => nielsenRawEllipticRepresentative hD hNE hFG hfin w hwD hwN J hc hv

def nielsenRawEllipticPoint (q:ellipticRaw) :
    fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic := by
  let r:=rep q
  refine ⟨r.2.val.val,fun _=>r.2.val.property,?_⟩
  obtain ⟨f,hf,hfix⟩:=not_not.mp r.2.property.2.2
  exact ⟨f.val,f.property,hf,congrArg Subtype.val hfix⟩
local notation "point" => nielsenRawEllipticPoint hD hNE hFG hfin w hwD hwN J hc hv

def nielsenRawEllipticClassMap : ellipticRaw→FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic :=
  fun q=>(fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic).symm
    (Quotient.mk _ (point q))
local notation "classMap" => nielsenRawEllipticClassMap hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenRawEllipticClassMap_injective : Function.Injective (classMap) := by
  intro q r hqr
  have hquot:Quotient.mk (MulAction.orbitRel H (fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic))
      (point q)=Quotient.mk _ (point r):=
    (fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic).symm.injective hqr
  have horb:=Quotient.exact hquot.symm
  change point r∈MulAction.orbit H (point q) at horb
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
  let a:=rep q
  let b:=rep r
  have hab:g•a.2.val=b.2.val:=Subtype.ext
    (congrArg (fun p:fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic=>p.val) hg)
  have hraw:=nielsenCoreFiniteCorner_orbit_rawChain hD hNE hFG hfin w hwD hwN J hc hv
    a.1 b.1 a.2.val b.2.val a.2.property.2.1.symm b.2.property.2.1.symm ⟨g,hab⟩
  apply Subtype.ext
  exact a.2.property.1.symm.trans ((Quotient.sound hraw).trans b.2.property.1)

theorem nielsenRawEllipticClassMap_surjective : Function.Surjective (classMap) := by
  let E:=fuchsianCyclicConjugacyClassesEquiv P.asFuchsianDisc .elliptic
  have hrep (p:fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic) :
      ∃q,Quotient.mk (MulAction.orbitRel H (fuchsianCyclicFixedPoints P.asFuchsianDisc .elliptic))
        (point q)=Quotient.mk _ p := by
    let x:=originalEllipticPointCoordinate P p
    obtain ⟨y,hy,hyo⟩:=hD.locallyFinite.fundamental.cycle_nonempty x
    obtain ⟨g,hgy⟩:=MulAction.mem_orbit_iff.mp hyo
    have hcoord:originalEllipticPointCoordinate P (g•p)=y:=hgy
    have he:¬IsAccidentalFuchsianPoint P y:=hcoord ▸ originalEllipticPointCoordinate_not_accidental P (g•p)
    have hmark:=nielsenEllipticPoint_mem_canonicalMarks hD hNE hFG w hwD hwN y hy he
    obtain ⟨i,hi⟩:=(hv (Polygon.discPolygonKleinPlane (Hyperbolic.discToClosedModel (P.finiteCoordinate
      y)))).mpr ⟨_,hmark,rfl⟩
    have hvertex:vertex i=Hyperbolic.discToClosedModel (P.finiteCoordinate y):=by
      apply Polygon.discPolygonKleinPlane_injective
      exact (nielsenCyclicVertex_plane hD hNE hFG J hv i).trans hi
    let q:ellipticRaw:=⟨Quotient.mk _ i,⟨i,y,rfl,hvertex,he⟩⟩
    let a:=rep q
    have hai:Relation.EqvGen step a.1 i:=Quotient.exact a.2.property.1
    obtain ⟨b,hb⟩:=nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv
      a.1 a.2.val a.2.property.2.1.symm i hai
    have hby:b.val=y:=P.finiteCoordinate.injective (Hyperbolic.isEmbedding_discToClosedModel.injective (hb.symm.trans
      hvertex))
    obtain ⟨k,hk⟩:=MulAction.mem_orbit_iff.mp b.property.2
    have hpoint:k•point q=g•p:=by
      apply Subtype.ext
      change k.val.val a.2.val.val=g.val.val p.val
      exact (congrArg Subtype.val (hk.trans hby)).trans (congrArg Subtype.val hgy).symm
    refine ⟨q,Quotient.sound ?_⟩
    change point q∈MulAction.orbit H p
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨k⁻¹*g,?_⟩
    rw [mul_smul,←hpoint,inv_smul_smul]
  intro c
  obtain ⟨p,hp⟩:=Quotient.exists_rep (E c)
  obtain ⟨q,hq⟩:=hrep p
  refine ⟨q,E.injective ?_⟩
  change E (E.symm _)=_
  rw [E.apply_symm_apply,hq,hp]

/-- Actual elliptic raw classes give exactly every original maximal elliptic cyclic conjugacy class. -/
def nielsenRawEllipticClassesEquiv : ellipticRaw≃FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic :=
  Equiv.ofBijective (classMap)
    ⟨nielsenRawEllipticClassMap_injective hD hNE hFG hfin w hwD hwN J hc hv,
      nielsenRawEllipticClassMap_surjective hD hNE hFG hfin w hwD hwN J hc hv⟩

theorem nielsenRawEllipticClassMap_order (q:ellipticRaw) :
    fuchsianEllipticClassOrder P.asFuchsianDisc ((classMap) q)=fuchsianPointOrder P (rep q).2.val := by
  let r:=rep q
  change Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H r.2.val.val)=Nat.card (MulAction.stabilizer H r.2.val)
  exact Nat.card_congr (P.stabilizerEquivBoundary r.2.val).symm.toEquiv

theorem nielsenRawEllipticClass_weight (q:ellipticRaw) :
    weight q.val=1/(fuchsianEllipticClassOrder P.asFuchsianDisc ((classMap) q):ℝ) := by
  let r:=rep q
  obtain ⟨f,hf,hfix⟩:=not_not.mp r.2.property.2.2
  have hxN:=nielsen_nontrivial_stabilizer_mem_core P hNE r.2.val f
    (fun he=>hf.1 (congrArg Subtype.val he)) hfix
  rw [←r.2.property.1,nielsenRawCornerClassWeight_mk,
    nielsenRawCornerWeight_finite hD hNE hFG J hv r.1 r.2.val r.2.property.2.1.symm,
    ite_eq_left hxN,nielsenRawEllipticClassMap_order]

end NielsenRawEllipticClasses



section NielsenActualEllipticDeficits
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "step" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv
local notation "rawSetoid" => nielsenCoreRawCornerSetoid hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "RB" => nielsenRawBoundaryVertices hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv
local notation "elliptic" => nielsenRawEllipticClass hD hNE hFG hfin w hwD hwN J hc hv

/-- An actual finite cut corner outside the boundary classes belongs to the open core. -/
theorem nielsenRawFinite_nonBoundary_mem_core (i:ZMod J.n) (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i)
    (hi:Quotient.mk (rawSetoid) i∉RB) : x∈fuchsianNielsenCore P hNE := by
  by_contra hxN
  have hxF:x∈frontier (fuchsianNielsenCore P hNE):=by
    rw [(fuchsianNielsenCore_isOpen P hNE).frontier_eq]
    exact ⟨closure_mono inter_subset_right
      (nielsenCyclicFiniteVertex_mem_coreClosure hD hNE hFG w hwD hwN J hv i x hx),hxN⟩
  obtain ⟨b,hb,_hu⟩:=nielsenCoreFiniteFrontierCorner_boundary_class hD hNE hFG hfin w hwD hwN J hc hv i x hx hxF
  exact hi ⟨b,(Quotient.sound hb).symm⟩

/-- A genuine elliptic cut-corner class cannot be a core boundary class. -/
theorem nielsenRawEllipticClass_not_boundary (q:V) (hq:elliptic q) : q∉RB := by
  obtain ⟨i,x,hi,hx,he⟩:=hq
  obtain ⟨f,hf,hfix⟩:=not_not.mp he
  have hxN:=nielsen_nontrivial_stabilizer_mem_core P hNE x f
    (fun h=>hf.1 (congrArg Subtype.val h)) hfix
  rintro ⟨b,hb⟩
  have hraw:Relation.EqvGen step i b.val:=Quotient.exact (hi.trans hb.symm)
  obtain ⟨y,hy⟩:=nielsenRawFiniteCornerClass_point_exists hD hNE hFG hfin w hwD hwN J hc hv i x hx.symm b.val hraw
  let z:=nielsenCyclicBoundaryNativePoint hD hNE hFG hfin w hwD hwN J hc hv b
  have hz:=nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b
  have hyz:y.val=z:=P.finiteCoordinate.injective (Hyperbolic.isEmbedding_discToClosedModel.injective (hy.symm.trans
    hz.1.symm))
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp y.property.2
  have hzN:z∈fuchsianNielsenCore P hNE:=(hg.trans hyz) ▸ fuchsianNielsenCore_invariant P hNE g x hxN
  exact ((fuchsianNielsenCore_isOpen P hNE).frontier_eq ▸ hz.2).2 hzN

/-- All geometric raw weights lie between zero and one. -/
theorem nielsenRawCornerClassWeight_bounds (q:V) : weight q∈Icc (0:ℝ) 1 := by
  refine Quotient.inductionOn q ?_
  intro i
  change nielsenRawCornerWeight hD hNE hFG J hv i∈Icc (0:ℝ) 1
  unfold nielsenRawCornerWeight
  split_ifs with hi
  · dsimp only
    split_ifs
    · let x:=P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex i) hi)
      have hp:0<(fuchsianPointOrder P x :ℝ):=by exact_mod_cast P.pointOrder_pos x
      have hle:(1:ℝ)≤fuchsianPointOrder P x:=by exact_mod_cast P.pointOrder_pos x
      exact ⟨(one_div_pos.mpr hp).le,(div_le_one hp).mpr hle⟩
    · norm_num
  · norm_num

/-- Among genuine nonboundary classes, weights strictly between zero and one are precisely all actual elliptic classes. -/
theorem nielsenRawEllipticClass_iff_weight (q:V) (hqb:q∉RB) :
    elliptic q ↔ 0<weight q ∧ weight q<1 := by
  constructor
  · intro he
    have h:=nielsenRawEllipticClass_weight hD hNE hFG hfin w hwD hwN J hc hv ⟨q,he⟩
    let c:=nielsenRawEllipticClassMap hD hNE hFG hfin w hwD hwN J hc hv ⟨q,he⟩
    have ht:(1:ℝ)<fuchsianEllipticClassOrder P.asFuchsianDisc c:=by
      exact_mod_cast (show 1<fuchsianEllipticClassOrder P.asFuchsianDisc c from
        lt_of_lt_of_le (by norm_num) (fuchsianEllipticClassOrder_two_le _ _))
    rw [h]
    exact ⟨one_div_pos.mpr (lt_trans zero_lt_one ht),(div_lt_one (lt_trans zero_lt_one ht)).mpr ht⟩
  · intro he
    let i:=q.out
    have hn:‖(vertex i:ℂ)‖<1:=by
      by_contra hn
      have hz:weight q=0:=by
        rw [←Quotient.out_eq q,nielsenRawCornerClassWeight_mk,nielsenRawCornerWeight,dite_eq_right hn]
      rw [hz] at he
      exact lt_irrefl 0 he.1
    let x:=P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex i) hn)
    have hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=vertex i:=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact Hyperbolic.closedDiscFinitePoint_spec _ hn
    have hxN:=nielsenRawFinite_nonBoundary_mem_core hD hNE hFG hfin w hwD hwN J hc hv i x hx
      (by simpa only [i,Quotient.out_eq] using hqb)
    refine ⟨i,x,Quotient.out_eq q,hx.symm,?_⟩
    intro ha
    have hw:=nielsenRawCornerWeight_finite hD hNE hFG J hv i x hx
    change weight (Quotient.mk _ i)=_ at hw
    change weight (Quotient.mk _ q.out)=_ at hw
    rw [Quotient.out_eq,ite_eq_left hxN,(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp ha] at hw
    norm_num at hw
    exact (ne_of_lt he.2) hw


/-- Only genuine ideal zero-weight classes are counted, without identifying them with cusp labels prematurely. -/
def nielsenRawIdealClassCount : ℕ :=
  (Finset.univ.filter (fun q:V=>weight q=0)).card

theorem nielsenRawIdealClass_not_boundary (q:V) (hq:weight q=0) : q∉RB := by
  rintro ⟨b,hb⟩
  have h:=nielsenRawCornerClassWeight_boundary hD hNE hFG hfin w hwD hwN J hc hv b
  change Quotient.mk _ b.val=q at hb
  rw [hb,hq] at h
  norm_num at h

/-- The remaining geometric deficit sum uses all actual original elliptic classes and the genuine ideal zero classes. -/
theorem nielsenNonBoundary_deficits_actual_elliptic :
    let _nielsenActualDeficitEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    ∑q:{q:V // q∉RB},(1-weight q.val)=
      (nielsenRawIdealClassCount hD hNE hFG hfin w hwD hwN J hc hv:ℝ)+
        ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum := by
  let _nielsenActualDeficitEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD hfin
  let _nielsenActualDeficitEllipticFintype : Fintype (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    Fintype.ofFinite _
  have hpoint(q:V):
      (if q∉RB then 1-weight q else 0)=
        (if weight q=0 then 1 else 0)+(if elliptic q then 1-weight q else 0):=by
    by_cases hB:q∈RB
    · have he:¬elliptic q:=fun he=>nielsenRawEllipticClass_not_boundary hD hNE hFG hfin w hwD hwN J hc hv q he hB
      have hz:weight q≠0:=fun hz=>nielsenRawIdealClass_not_boundary hD hNE hFG hfin w hwD hwN J hc hv q hz hB
      simp only [ite_eq_right (not_not.mpr hB),ite_eq_right hz,ite_eq_right he,add_zero]
    · rw [ite_eq_left hB]
      have hb:=nielsenRawCornerClassWeight_bounds hD hNE hFG hfin w hwD hwN J hc hv q
      by_cases hz:weight q=0
      · have he:¬elliptic q:=fun he=>by
          have hh:=(nielsenRawEllipticClass_iff_weight hD hNE hFG hfin w hwD hwN J hc hv q hB).mp he
          rw [hz] at hh
          exact lt_irrefl 0 hh.1
        simp only [hz,sub_zero,ite_true,ite_eq_right he,add_zero]
      · have hp:0<weight q:=lt_of_le_of_ne hb.1 (Ne.symm hz)
        by_cases he:elliptic q
        · simp only [ite_eq_right hz,ite_eq_left he,zero_add]
        · have hn:¬weight q<1:=fun hl=>he
            ((nielsenRawEllipticClass_iff_weight hD hNE hFG hfin w hwD hwN J hc hv q hB).mpr ⟨hp,hl⟩)
          have hw:weight q=1:=le_antisymm hb.2 (le_of_not_gt hn)
          simp only [hw,ite_eq_right he,sub_self,one_ne_zero,ite_false,add_zero]
  have hzero:(∑q:V,if weight q=0 then (1:ℝ) else 0)=
      (nielsenRawIdealClassCount hD hNE hFG hfin w hwD hwN J hc hv:ℝ):=by
    rw [←Finset.sum_filter]
    simp only [nielsenRawIdealClassCount,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hE:(∑q:V,if elliptic q then 1-weight q else 0)=
      ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum:=by
    let E:=nielsenRawEllipticClassesEquiv hD hNE hFG hfin w hwD hwN J hc hv
    calc
      _=∑q:{q:V // elliptic q},(1-weight q.val):=by
        simpa only [Finset.sum_filter] using
          (Finset.sum_subtype (p:=fun q:V=>elliptic q)
            (Finset.univ.filter (fun q:V=>elliptic q)) (by simp) (fun q=>1-weight q))
      _=∑c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic,
          (1-1/(fuchsianEllipticClassOrder P.asFuchsianDisc c:ℝ)):=by
        rw [←Equiv.sum_comp E]
        apply Finset.sum_congr rfl
        intro q _hq
        rw [nielsenRawEllipticClass_weight]
        rfl
      _=_:=by
        rw [fuchsianEllipticOrderList,List.map_ofFn,List.sum_ofFn]
        exact (Equiv.sum_comp (Fintype.equivFin
          (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic)).symm
          (fun c=>1-1/(fuchsianEllipticClassOrder P.asFuchsianDisc c:ℝ))).symm
  calc
    _=∑q:V,if q∉RB then 1-weight q else 0:=by
      simpa only [Finset.sum_filter] using
        (Finset.sum_subtype (p:=fun q:V=>q∉RB)
          (Finset.univ.filter (fun q:V=>q∉RB)) (by simp) (fun q=>1-weight q)).symm
    _=∑q:V,((if weight q=0 then 1 else 0)+(if elliptic q then 1-weight q else 0)):=
      Finset.sum_congr rfl (fun q _=>hpoint q)
    _=_:=by rw [Finset.sum_add_distrib,hzero,hE]


/-- The genuine core area uses the entire original elliptic order list; only geometric cap genus, boundary count and cusp identification remain to be transported. -/
theorem nielsenCappedWord_genus_actualElliptic_area :
    let _nielsenCappedActualEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    ∃g,Surfaces.HasTopologicalGenus
      ((nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).PolygonalRealization
        (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
        (2*(g:ℝ)-2+Fintype.card (NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv)+
          nielsenRawIdealClassCount hD hNE hFG hfin w hwD hwN J hc hv+
          ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum) := by
  let _nielsenCappedActualEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD hfin
  obtain ⟨g,hg,ha⟩:=nielsenNonBoundaryRawCorners_genus_area hD hNE hFG hfin w hwD hwN J hc hv
  refine ⟨g,hg,?_⟩
  rw [nielsenNonBoundary_deficits_actual_elliptic hD hNE hFG hfin w hwD hwN J hc hv] at ha
  linear_combination ha

end NielsenActualEllipticDeficits






local instance nielsenInteriorSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex :=
  borel Mobius.ExtendedComplex
local instance nielsenInteriorSphereBorelSpace : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- The actual relative interior of an unpaired Nielsen side lies in the original open polygon. -/
theorem NielsenUnpairedSide.native_openSegment_mem_domain
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {hNE : DiscreteGroups.IsNonElementary H} (w : P.domain.carrier) (hwD : w ∈ D)
    (hwN : w ∈ fuchsianNielsenCore P hNE) (s : NielsenUnpairedSide P hNE D)
    {a b : 𝔻} (hab : a ≠ b)
    (he : nielsenUnpairedNativeCarrier P D s.val = Hyperbolic.closedDiscHSegment a b)
    {z : 𝔻} (hz : z ∈ Hyperbolic.openDiscHSegment a b) : P.finiteCoordinate.symm z ∈ D := by
  classical
  have hzH := (Hyperbolic.mem_openHSegment_iff (Hyperbolic.discToHalfPlane_injective.ne hab)).mp hz
  have hzC : z ∈ Hyperbolic.closedDiscHSegment a b := hzH.1
  have hzK : Hyperbolic.kleinCoordinate z ∈ openSegment ℝ (Hyperbolic.kleinCoordinate a) (Hyperbolic.kleinCoordinate b) := by
    apply mem_openSegment_of_ne_left_right
    · intro heq
      exact hzH.2.1 (congrArg Hyperbolic.discToHalfPlane (Hyperbolic.kleinCoordinate_injective heq).symm)
    · intro heq
      exact hzH.2.2 (congrArg Hyperbolic.discToHalfPlane (Hyperbolic.kleinCoordinate_injective heq).symm)
    · rw [← Hyperbolic.klein_image_closedDiscHSegment]
      exact mem_image_of_mem Hyperbolic.kleinCoordinate hzC
  have haC : a ∈ nielsenUnpairedNativeCarrier P D s.val := by
    apply Hyperbolic.kleinCoordinate_injective.mem_set_image.mp
    rw [he, Hyperbolic.klein_image_closedDiscHSegment]
    exact left_mem_segment ℝ _ _
  have hbC : b ∈ nielsenUnpairedNativeCarrier P D s.val := by
    apply Hyperbolic.kleinCoordinate_injective.mem_set_image.mp
    rw [he, Hyperbolic.klein_image_closedDiscHSegment]
    exact right_mem_segment ℝ _ _
  have hzNative : z ∈ nielsenUnpairedNativeCarrier P D s.val := he ▸ hzC
  have hclosure (u : 𝔻) (hu : u ∈ nielsenUnpairedNativeCarrier P D s.val) :
      P.finiteCoordinate.symm u ∈ closure D := by
    obtain ⟨x,hx,hxu⟩ := hu.2
    simpa only [← hxu, P.finiteCoordinate.symm_apply_apply] using hx
  by_contra hzD
  have hzFront : P.finiteCoordinate.symm z ∈ frontier D := by
    rw [hD.locallyFinite.fundamental.isOpen.frontier_eq]
    exact ⟨hclosure z hzNative, hzD⟩
  obtain ⟨S,hS,hzS⟩ := hD.boundary_mem_side hzFront
  obtain ⟨n,t,hn,_hstrict,hweak,hside⟩ := hD.side_global_support hS
  have hzEq : inner ℝ n (Hyperbolic.kleinCoordinate z) = t := by
    simpa only [UnitDiscFuchsianGroup.kleinCoordinate,
      P.finiteCoordinate.apply_symm_apply] using hside _ hzS
  have haWeak : inner ℝ n (Hyperbolic.kleinCoordinate a) ≤ t := by
    simpa only [UnitDiscFuchsianGroup.kleinCoordinate,
      P.finiteCoordinate.apply_symm_apply] using hweak _ (hclosure a haC)
  have hbWeak : inner ℝ n (Hyperbolic.kleinCoordinate b) ≤ t := by
    simpa only [UnitDiscFuchsianGroup.kleinCoordinate,
      P.finiteCoordinate.apply_symm_apply] using hweak _ (hclosure b hbC)
  obtain ⟨haEq,hbEq⟩ := linear_form_endpoints_eq_of_openSegment haWeak hbWeak hzK hzEq
  obtain ⟨m,k,hm,hline⟩ := s.val.klein_image_carrier
  have haLine : inner ℝ m (Hyperbolic.kleinCoordinate a) = k :=
    (hline ▸ mem_image_of_mem Hyperbolic.kleinCoordinate haC.1).1
  have hbLine : inner ℝ m (Hyperbolic.kleinCoordinate b) = k :=
    (hline ▸ mem_image_of_mem Hyperbolic.kleinCoordinate hbC.1).1
  have hSLine (x : P.domain.carrier) (hx : x ∈ S) : P.finiteCoordinate x ∈ s.val.carrier := by
    apply Hyperbolic.kleinCoordinate_injective.mem_set_image.mp
    rw [hline]
    constructor
    · exact (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points hn hm
        (Hyperbolic.kleinCoordinate_injective.ne hab) haEq hbEq haLine hbLine).mp (hside x hx)
    · rw [← Hyperbolic.range_kleinCoordinate]
      exact mem_range_self _
  obtain ⟨x,hx,y,hy,hxy⟩ := hS.2.2
  exact hxy (nielsen_boundary_original_side_subsingleton hD hNE w hwD hwN
    ⟨S,hS⟩ s.val s.property.1 ⟨hx,hSLine x hx⟩ ⟨hy,hSLine y hy⟩)




/-- Every positive subsegment of an actual unpaired clip has its open part in the original domain. -/
theorem NielsenUnpairedSide.native_openSubsegment_mem_domain
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    {hNE:DiscreteGroups.IsNonElementary H}
    (hFG:H.FG)
    (w:P.domain.carrier)
    (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) (s:NielsenUnpairedSide P hNE D)
    {a b:𝔻} (hab:a≠b) (hsub:Hyperbolic.closedDiscHSegment a b⊆nielsenUnpairedNativeCarrier P D s.val)
    {z:𝔻}
    (hz:z∈Hyperbolic.openDiscHSegment a b) : P.finiteCoordinate.symm z∈D := by
  obtain ⟨p,q,hpq,he⟩:=s.native_eq_segment hFG hD
  have hzprops:=(Hyperbolic.mem_openHSegment_iff (Hyperbolic.discToHalfPlane_injective.ne hab)).mp hz
  have hzne:z≠a ∧ z≠b:=⟨fun h=>hzprops.2.1 (congrArg Hyperbolic.discToHalfPlane h),
    fun h=>hzprops.2.2 (congrArg Hyperbolic.discToHalfPlane h)⟩
  have hzC:z∈Hyperbolic.closedDiscHSegment a b:=hzprops.1
  have hsubC:Hyperbolic.closedModelDiscHSegment (Hyperbolic.discToClosedModel a) (Hyperbolic.discToClosedModel b)⊆
      Hyperbolic.closedModelDiscHSegment (Hyperbolic.discToClosedModel p) (Hyperbolic.discToClosedModel q):=by
    rw [Hyperbolic.closedModelDiscHSegment_interior,Hyperbolic.closedModelDiscHSegment_interior]
    exact image_mono (he ▸ hsub)
  have hzM:Hyperbolic.discToClosedModel z∈Hyperbolic.closedModelDiscHSegment (Hyperbolic.discToClosedModel a) (Hyperbolic.discToClosedModel b):=by
    rw [Hyperbolic.closedModelDiscHSegment_interior]
    exact mem_image_of_mem _ hzC
  have hzpq:z≠p ∧ z≠q:=by
    constructor <;> intro h
    all_goals
      have hends:Hyperbolic.discToClosedModel z=Hyperbolic.discToClosedModel p∨Hyperbolic.discToClosedModel z=Hyperbolic.discToClosedModel q:=by
        first | exact Or.inl (congrArg Hyperbolic.discToClosedModel h) | exact Or.inr (congrArg
          Hyperbolic.discToClosedModel h)
      have hsmall:=original_closed_subsegment_endpoint _ _ _ _ _
        (Hyperbolic.isEmbedding_discToClosedModel.injective.ne hpq) hsubC hzM hends
      rcases hsmall with hsmall|hsmall
      · exact hzne.1 (Hyperbolic.isEmbedding_discToClosedModel.injective hsmall)
      · exact hzne.2 (Hyperbolic.isEmbedding_discToClosedModel.injective hsmall)
  apply s.native_openSegment_mem_domain hD w hwD hwN hpq he
  apply (Hyperbolic.mem_openHSegment_iff (Hyperbolic.discToHalfPlane_injective.ne hpq)).mpr
  have hzFull:z∈Hyperbolic.closedDiscHSegment p q:=by rw [←he];exact hsub hzC
  exact ⟨hzFull,fun h=>hzpq.1 (Hyperbolic.discToHalfPlane_injective h),
    fun h=>hzpq.2 (Hyperbolic.discToHalfPlane_injective h)⟩

section NielsenBoundaryProjectedEdges
open LeanEval.Topology.ClassificationOfSurfaces.Moise
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv
local notation "tag" => nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv
local notation "point" => nielsenCyclicBoundaryNativePoint hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCyclicBoundaryUnpairedSide (b:B) : NielsenUnpairedSide P hNE D :=
  Classical.choose ((nielsenCyclicPairIndex_fixed_iff hD hNE hFG hfin w hwD hwN J hc hv b.val).mp b.property)
local notation "side" => nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryUnpairedSide_spec (b:B) : tag b.val=Sum.inr (side b) :=
  Classical.choose_spec ((nielsenCyclicPairIndex_fixed_iff hD hNE hFG hfin w hwD hwN J hc hv b.val).mp b.property)

theorem nielsenCyclicBoundaryEdge_finite (b:B) (p:𝕔𝔻) (hp:p∈edge b.val) :
    ∃x:P.domain.carrier,Hyperbolic.discToClosedModel (P.finiteCoordinate x)=p := by
  have hs:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv b.val hp
  rw [nielsenCyclicBoundaryUnpairedSide_spec] at hs
  change p∈(side b).carrier at hs
  obtain ⟨z,_hz,hzp⟩:=hs
  exact ⟨P.finiteCoordinate.symm z,by simpa only [Homeomorph.apply_symm_apply] using hzp⟩

def nielsenCyclicBoundaryNativeRightPoint (b:B) : P.domain.carrier :=
  Classical.choose (nielsenCyclicBoundaryEdge_finite hD hNE hFG hfin w hwD hwN J hc hv b
    (vertex (b.val+1)) (Polygon.closedModelDiscHSegment_right_mem _ _))
local notation "rightPoint" => nielsenCyclicBoundaryNativeRightPoint hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryNativeRightPoint_spec (b:B) :
    Hyperbolic.discToClosedModel (P.finiteCoordinate (rightPoint b))=vertex (b.val+1) :=
  Classical.choose_spec (nielsenCyclicBoundaryEdge_finite hD hNE hFG hfin w hwD hwN J hc hv b
    (vertex (b.val+1)) (Polygon.closedModelDiscHSegment_right_mem _ _))

theorem nielsenCyclicBoundaryNativeEndpoints_ne (b:B) : point b≠rightPoint b := by
  intro he
  have hh:vertex b.val=vertex (b.val+1):=
    (nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b).1.symm.trans
      ((congrArg (fun x:P.domain.carrier=>Hyperbolic.discToClosedModel (P.finiteCoordinate x)) he).trans
        (nielsenCyclicBoundaryNativeRightPoint_spec hD hNE hFG hfin w hwD hwN J hc hv b))
  have hplane:=congrArg Polygon.discPolygonKleinPlane hh
  rw [nielsenCyclicVertex_plane,nielsenCyclicVertex_plane] at hplane
  exact J.adjacent_ne b.val hplane

def nielsenCyclicBoundaryNativeEdge (b:B) : Set P.domain.carrier :=
  P.finiteCoordinate.symm '' Hyperbolic.closedDiscHSegment (P.finiteCoordinate (point b)) (P.finiteCoordinate
    (rightPoint b))
local notation "nativeEdge" => nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv

theorem mem_nielsenCyclicBoundaryNativeEdge (b:B) (x:P.domain.carrier) :
    x∈nativeEdge b ↔ Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈edge b.val := by
  change x∈P.finiteCoordinate.symm '' _↔_∈Hyperbolic.closedModelDiscHSegment _ _
  rw [←(nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b).1,
    ←nielsenCyclicBoundaryNativeRightPoint_spec hD hNE hFG hfin w hwD hwN J hc hv b,
    Hyperbolic.closedModelDiscHSegment_interior,Hyperbolic.isEmbedding_discToClosedModel.injective.mem_set_image]
  constructor
  · rintro ⟨z,hz,rfl⟩
    simpa only [Homeomorph.apply_symm_apply] using hz
  · intro hx
    exact ⟨P.finiteCoordinate x,hx,P.finiteCoordinate.symm_apply_apply x⟩

theorem nielsenCyclicBoundaryNativeEdge_isCompact (b:B) : IsCompact (nativeEdge b) :=
  (Hyperbolic.isCompact_closedDiscHSegment (P.finiteCoordinate.injective.ne
    (nielsenCyclicBoundaryNativeEndpoints_ne hD hNE hFG hfin w hwD hwN J hc hv
      b))).image P.finiteCoordinate.symm.continuous

/-- Each true unpaired cyclic edge has its relative interior in the original open fundamental polygon. -/
theorem nielsenCyclicBoundaryNativeEdge_open_mem_domain (b:B) (x:P.domain.carrier)
    (hx:x∈nativeEdge b) (hL:x≠point b) (hR:x≠rightPoint b) : x∈D := by
  have hsub:Hyperbolic.closedDiscHSegment (P.finiteCoordinate (point b)) (P.finiteCoordinate (rightPoint b))⊆
      nielsenUnpairedNativeCarrier P D (side b).val:=by
    intro z hz
    have hzE:Hyperbolic.discToClosedModel z∈edge b.val:=by
      change _∈Hyperbolic.closedModelDiscHSegment _ _
      rw [←(nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b).1,
        ←nielsenCyclicBoundaryNativeRightPoint_spec hD hNE hFG hfin w hwD hwN J hc hv b,
        Hyperbolic.closedModelDiscHSegment_interior]
      exact mem_image_of_mem _ hz
    have hs:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv b.val hzE
    rw [nielsenCyclicBoundaryUnpairedSide_spec] at hs
    change Hyperbolic.discToClosedModel z∈Hyperbolic.discToClosedModel '' _ at hs
    exact Hyperbolic.isEmbedding_discToClosedModel.injective.mem_set_image.mp hs
  have hzC:P.finiteCoordinate x∈Hyperbolic.closedDiscHSegment (P.finiteCoordinate (point b))
      (P.finiteCoordinate (rightPoint b)):=by
    obtain ⟨z,hz,hzx⟩:=hx
    simpa only [←hzx,Homeomorph.apply_symm_apply] using hz
  have hzO:P.finiteCoordinate x∈Hyperbolic.openDiscHSegment (P.finiteCoordinate (point b))
      (P.finiteCoordinate (rightPoint b)):=by
    apply (Hyperbolic.mem_openHSegment_iff (Hyperbolic.discToHalfPlane_injective.ne
      (P.finiteCoordinate.injective.ne (nielsenCyclicBoundaryNativeEndpoints_ne hD hNE hFG hfin w hwD hwN J hc hv
        b)))).mpr
    exact ⟨hzC,fun he=>hL (P.finiteCoordinate.injective (Hyperbolic.discToHalfPlane_injective he)),
      fun he=>hR (P.finiteCoordinate.injective (Hyperbolic.discToHalfPlane_injective he))⟩
  simpa only [Homeomorph.symm_apply_apply] using (side b).native_openSubsegment_mem_domain
    hD hFG w hwD hwN (P.finiteCoordinate.injective.ne
      (nielsenCyclicBoundaryNativeEndpoints_ne hD hNE hFG hfin w hwD hwN J hc hv b)) hsub hzO


local instance nielsenProjectedEdgeSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenProjectedEdgeSphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

theorem nielsenCyclicBoundaryNativeEdge_subset_closure (b:B) : nativeEdge b⊆closure D := by
  intro x hx
  have hxE:=(mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b x).mp hx
  have hs:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv b.val hxE
  rw [nielsenCyclicBoundaryUnpairedSide_spec] at hs
  change Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈Hyperbolic.discToClosedModel '' _ at hs
  have hz:=Hyperbolic.isEmbedding_discToClosedModel.injective.mem_set_image.mp hs
  exact P.finiteCoordinate.injective.mem_set_image.mp hz.2

/-- A genuine free-edge interior point cannot acquire another cyclic-edge representative under the original whole-group projection. -/
theorem nielsenCyclicBoundaryNativeEdge_projection_interior
    (b c:B) (x y:P.domain.carrier) (hx:x∈nativeEdge b) (hy:y∈nativeEdge c)
    (hL:x≠point b) (hR:x≠rightPoint b)
    (hπ:Surfaces.mobiusDomainProjection P.domain x=Surfaces.mobiusDomainProjection P.domain y) : b=c ∧ x=y := by
  have hxD:=nielsenCyclicBoundaryNativeEdge_open_mem_domain hD hNE hFG hfin w hwD hwN J hc hv b x hx hL hR
  have horb:=Quotient.exact hπ
  change x∈MulAction.orbit H y at horb
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
  have hg1:g=1:=by
    by_contra hn
    have hxF:=hD.locallyFinite.fundamental.closed_tile_intersection_subset_frontier hn
      ⟨nielsenCyclicBoundaryNativeEdge_subset_closure hD hNE hFG hfin w hwD hwN J hc hv b hx,
        y,nielsenCyclicBoundaryNativeEdge_subset_closure hD hNE hFG hfin w hwD hwN J hc hv c hy,hg⟩
    exact ((hD.locallyFinite.fundamental.isOpen).frontier_eq ▸ hxF).2 hxD
  have hxy:x=y:=by simpa only [hg1,one_smul] using hg.symm
  refine ⟨?_,hxy⟩
  by_contra hbc
  have hi:b.val≠c.val:=fun h=>hbc (Subtype.ext h)
  have hxEdge:Polygon.discPolygonKleinPlane (Hyperbolic.discToClosedModel (P.finiteCoordinate x))∈J.edgeSegment b.val:=by
    rw [←nielsenCyclicEdge_plane hD hNE hFG J hv b.val]
    exact mem_image_of_mem _ ((mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b x).mp hx)
  have hyEdge:Polygon.discPolygonKleinPlane (Hyperbolic.discToClosedModel (P.finiteCoordinate x))∈J.edgeSegment c.val:=by
    rw [←nielsenCyclicEdge_plane hD hNE hFG J hv c.val,hxy]
    exact mem_image_of_mem _ ((mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv c y).mp hy)
  have hends:=J.edgeSegment_inter_subset_endpoints hi ⟨hxEdge,hyEdge⟩
  rcases hends with he|he
  · apply hL
    apply P.finiteCoordinate.injective
    apply Hyperbolic.isEmbedding_discToClosedModel.injective
    apply Polygon.discPolygonKleinPlane_injective
    exact he.trans (nielsenCyclicVertex_plane hD hNE hFG J hv b.val).symm |>.trans
      (congrArg Polygon.discPolygonKleinPlane
        (nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b).1.symm)
  · apply hR
    apply P.finiteCoordinate.injective
    apply Hyperbolic.isEmbedding_discToClosedModel.injective
    apply Polygon.discPolygonKleinPlane_injective
    exact he.trans (nielsenCyclicVertex_plane hD hNE hFG J hv (b.val+1)).symm |>.trans
      (congrArg Polygon.discPolygonKleinPlane
        (nielsenCyclicBoundaryNativeRightPoint_spec hD hNE hFG hfin w hwD hwN J hc hv b).symm)

/-- The right endpoint projects to exactly the next actual boundary-cycle vertex. -/
theorem nielsenCyclicBoundaryNativeRightPoint_projection (b:B) :
    Surfaces.mobiusDomainProjection P.domain (rightPoint b)=
      Surfaces.mobiusDomainProjection P.domain (point (nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv b)) := by
  obtain ⟨g,hg⟩:=nielsenCyclicBoundaryNext_endpoint_sphereOrbit hD hNE hFG hfin w hwD hwN J hc hv b
  have hright:=nielsenCyclicBoundaryNativeRightPoint_spec hD hNE hFG hfin w hwD hwN J hc hv b
  have hnext:=(nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv
    (nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv b)).1
  change Hyperbolic.discToClosedModel (P.finiteCoordinate (point
    (nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv b)))=
    vertex (nielsenCyclicBoundaryNext hD hNE hFG hfin w hwD hwN J hc hv b).val at hnext
  rw [←hright,←hnext] at hg
  change g.val.val (((P.finiteCoordinate (rightPoint b):𝔻):ℂ):Mobius.ExtendedComplex)=
    (((P.finiteCoordinate (point (nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
      b)):𝔻):ℂ):Mobius.ExtendedComplex) at hg
  rw [P.finiteCoordinate_extended,P.finiteCoordinate_extended] at hg
  have hpoint:g•rightPoint b=point (nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv b):=Subtype.ext hg
  rw [←hpoint,Surfaces.mobiusDomainProjection_smul]

def nielsenCyclicProjectedBoundaryEdge
    (b:B) : Set (Surfaces.MobiusDomainQuotient P.domain) :=
  Surfaces.mobiusDomainProjection P.domain '' nativeEdge b

theorem nielsenCyclicProjectedBoundaryEdge_isCompact (b:B) :
    IsCompact (nielsenCyclicProjectedBoundaryEdge hD hNE hFG hfin w hwD hwN J hc hv b) :=
  (nielsenCyclicBoundaryNativeEdge_isCompact hD hNE hFG hfin w hwD hwN J hc hv b).image
    (Surfaces.mobiusDomainProjection_continuous P.domain)

end NielsenBoundaryProjectedEdges



section NielsenProjectedBoundaryCycles
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "point" => nielsenCyclicBoundaryNativePoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "rightPoint" => nielsenCyclicBoundaryNativeRightPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "nativeEdge" => nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv
local notation "projectEdge" => nielsenCyclicProjectedBoundaryEdge hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv

theorem nielsenCyclicProjectedBoundaryEdges_inter_sameCycle (b c:B)
    (p:Surfaces.MobiusDomainQuotient P.domain)
    (hp:p∈projectEdge b∩projectEdge c) :
    Equiv.Perm.SameCycle (ρ) b c := by
  obtain ⟨x,hx,hxp⟩:=hp.1
  obtain ⟨y,hy,hyp⟩:=hp.2
  have hπ:=hxp.trans hyp.symm
  by_cases hxend:x=point b∨x=rightPoint b
  · by_cases hyend:y=point c∨y=rightPoint c
    · have endpoint (a:B) (z:P.domain.carrier) (hz:z=point a∨z=rightPoint a):
          ∃d:B,Equiv.Perm.SameCycle (ρ) a d ∧
            Surfaces.mobiusDomainProjection P.domain z=Surfaces.mobiusDomainProjection P.domain (point d):=by
        rcases hz with rfl|rfl
        · exact ⟨a,Equiv.Perm.SameCycle.refl _ _,rfl⟩
        · exact ⟨(ρ) a,(Equiv.Perm.SameCycle.refl (ρ) a).apply_right,
            nielsenCyclicBoundaryNativeRightPoint_projection hD hNE hFG hfin w hwD hwN J hc hv a⟩
      obtain ⟨d,hbd,hxd⟩:=endpoint b x hxend
      obtain ⟨e,hce,hye⟩:=endpoint c y hyend
      have hde:d=e:=nielsenCyclicBoundaryVertexProjection_injective hD hNE hFG hfin w hwD hwN J hc hv
        (hxd.symm.trans (hπ.trans hye))
      exact hbd.trans (hde ▸ hce.symm)
    · have hyL:y≠point c:=fun he=>hyend (Or.inl he)
      have hyR:y≠rightPoint c:=fun he=>hyend (Or.inr he)
      have hcb:=(nielsenCyclicBoundaryNativeEdge_projection_interior hD hNE hFG hfin w hwD hwN J hc hv c b y x hy hx hyL
        hyR hπ.symm).1
      exact hcb ▸ Equiv.Perm.SameCycle.refl (ρ) c
  · have hxL:x≠point b:=fun he=>hxend (Or.inl he)
    have hxR:x≠rightPoint b:=fun he=>hxend (Or.inr he)
    have hbc:=(nielsenCyclicBoundaryNativeEdge_projection_interior hD hNE hFG hfin w hwD hwN J hc hv b c x y hx hy hxL
      hxR hπ).1
    exact hbc ▸ Equiv.Perm.SameCycle.refl (ρ) b

/-- Literal projected boundary pieces grouped by their actual first-return cycle. -/
def nielsenProjectedBoundaryCycle
    (c:C) : Set (Surfaces.MobiusDomainQuotient P.domain) :=
  ⋃b:{b:B // (Quotient.mk (Equiv.Perm.SameCycle.setoid (ρ)) b:C)=c},projectEdge b.val
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenProjectedBoundaryCycle_isCompact (c:C) : IsCompact (cycleCarrier c) :=
  isCompact_iUnion (fun b=>nielsenCyclicProjectedBoundaryEdge_isCompact hD hNE hFG hfin w hwD hwN J hc hv b.val)

theorem nielsenProjectedBoundaryCycle_pairwise_disjoint : Pairwise
    (fun c d:C=>Disjoint (cycleCarrier c)
    (cycleCarrier d)) := by
  intro c d hcd
  apply disjoint_left.mpr
  intro p hpc hpd
  obtain ⟨b,hb⟩:=mem_iUnion.mp hpc
  obtain ⟨e,he⟩:=mem_iUnion.mp hpd
  have hbe:=nielsenCyclicProjectedBoundaryEdges_inter_sameCycle hD hNE hFG hfin w hwD hwN J hc hv b.val e.val p ⟨hb,he⟩
  exact hcd (b.property.symm.trans ((Quotient.sound hbe).trans e.property))

theorem nielsenProjectedBoundaryCycle_nonempty (c:C) : (cycleCarrier c).Nonempty := by
  obtain ⟨b,rfl⟩:=Quotient.exists_rep c
  refine ⟨Surfaces.mobiusDomainProjection P.domain (point b),mem_iUnion.mpr ⟨⟨b,rfl⟩,?_⟩⟩
  refine ⟨point b,?_,rfl⟩
  apply (mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b (point b)).mpr
  rw [(nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b).1]
  exact Polygon.closedModelDiscHSegment_left_mem _ _

/-- The finitely many literal projected boundary cycles cover exactly the true core frontier in the original quotient. -/
theorem nielsenProjectedBoundaryCycles_cover :
    (⋃c:C,cycleCarrier c)=Surfaces.mobiusDomainProjection P.domain '' frontier (fuchsianNielsenCore P hNE) := by
  apply subset_antisymm
  · intro p hp
    obtain ⟨c,hcP⟩:=mem_iUnion.mp hp
    obtain ⟨b,hbP⟩:=mem_iUnion.mp hcP
    obtain ⟨x,hx,rfl⟩:=hbP
    have hxE:=(mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b.val x).mp hx
    have hs:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv b.val.val hxE
    rw [nielsenCyclicBoundaryUnpairedSide_spec] at hs
    change Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈Hyperbolic.discToClosedModel '' _ at hs
    have hz:=Hyperbolic.isEmbedding_discToClosedModel.injective.mem_set_image.mp hs
    obtain ⟨u,hu,hux⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE
      (nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv b.val).val
      (nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv b.val).property.1 hz.1
    have he:u=x:=P.finiteCoordinate.injective hux
    exact ⟨x,he ▸ hu,rfl⟩
  · rintro p ⟨x,hx,rfl⟩
    obtain ⟨g,s,hgs⟩:=nielsenCore_frontier_positive_unpaired_representative hD hNE x hx
    obtain ⟨i,hi,hxi⟩:=nielsenBoundarySide_point_mem_tagged_cyclic_edge hD hNE hFG hfin w hwD hwN J hc hv
      (Sum.inr s) (Hyperbolic.discToClosedModel (P.finiteCoordinate (g•x))) ⟨P.finiteCoordinate (g•x),hgs,rfl⟩
    let b:B:=⟨i,nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv i s hi⟩
    refine mem_iUnion.mpr ⟨Quotient.mk _ b,mem_iUnion.mpr ⟨⟨b,rfl⟩,?_⟩⟩
    refine ⟨g•x,(mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b (g•x)).mpr hxi,?_⟩
    exact Surfaces.mobiusDomainProjection_smul P.domain g x

end NielsenProjectedBoundaryCycles



/-- Original orbit projection is unchanged on the actual translate of any physical subset. -/
theorem nielsenProjection_image_smul
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (g:H) (S:Set P.domain.carrier) :
    Surfaces.mobiusDomainProjection P.domain '' (g•S)=Surfaces.mobiusDomainProjection P.domain '' S := by
  ext p
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,hxp⟩
    exact ⟨x,hx,(Surfaces.mobiusDomainProjection_smul P.domain g x).symm.trans hxp⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨g•x,⟨x,hx,rfl⟩,Surfaces.mobiusDomainProjection_smul P.domain g x⟩

/-- Two projected genuine complete boundary geodesics meeting at one original orbit are equal as literal quotient subsets. -/
theorem nielsenBoundary_line_projections_eq_of_inter
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L M:Hyperbolic.DiscLine) (hL:L∈nielsenBoundaryDiscLineFamily P hNE)
    (hM:M∈nielsenBoundaryDiscLineFamily P hNE)
    (p:Surfaces.MobiusDomainQuotient P.domain)
    (hp:p∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier))
    (hq:p∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' M.carrier)) :
    Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier)=
      Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' M.carrier) := by
  obtain ⟨x,hx,hxp⟩:=hp
  obtain ⟨y,hy,hyp⟩:=hq
  have horb:=Quotient.exact (hxp.trans hyp.symm)
  change x∈MulAction.orbit H y at horb
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
  obtain ⟨K,hK,hgK⟩:=nielsenBoundary_original_line_image P hNE M hM g
  have hxK:x∈P.finiteCoordinate.symm '' K.carrier:=hgK ▸ mem_smul_set.mpr ⟨y,hy,hg⟩
  have hcoord (A:Hyperbolic.DiscLine) (hA:x∈P.finiteCoordinate.symm '' A.carrier):P.finiteCoordinate x∈A.carrier:=by
    obtain ⟨z,hz,rfl⟩:=hA
    simpa only [Homeomorph.apply_symm_apply] using hz
  have hKL:K=L:=by
    by_contra hn
    exact disjoint_left.mp (nielsenBoundaryDiscLineFamily_pairwise_disjoint P hNE hK hL hn)
      (hcoord K hxK) (hcoord L hx)
  rw [←hKL,←hgK,nielsenProjection_image_smul]

section NielsenBoundaryLineProjection
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "point" => nielsenCyclicBoundaryNativePoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "rightPoint" => nielsenCyclicBoundaryNativeRightPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "nativeEdge" => nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv
local notation "projectEdge" => nielsenCyclicProjectedBoundaryEdge hD hNE hFG hfin w hwD hwN J hc hv
local notation "side" => nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv

def nielsenBoundaryCompleteLineProjection
    (b:B) : Set (Surfaces.MobiusDomainQuotient P.domain) :=
  Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' (side b).val.carrier)
local notation "lineImage" => nielsenBoundaryCompleteLineProjection hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryNativeEdge_subset_fullLine (b:B) :
    nativeEdge b⊆P.finiteCoordinate.symm '' (side b).val.carrier := by
  intro x hx
  have hxE:=(mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b x).mp hx
  have hs:=nielsenCyclicSideTag_spec hD hNE hFG hfin w hwD hwN J hc hv b.val hxE
  rw [nielsenCyclicBoundaryUnpairedSide_spec] at hs
  change Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈Hyperbolic.discToClosedModel '' _ at hs
  have hz:=Hyperbolic.isEmbedding_discToClosedModel.injective.mem_set_image.mp hs
  exact ⟨P.finiteCoordinate x,hz.1,P.finiteCoordinate.symm_apply_apply x⟩

theorem nielsenProjectedBoundaryEdge_subset_lineProjection (b:B) : projectEdge b⊆lineImage b :=
  image_mono (nielsenCyclicBoundaryNativeEdge_subset_fullLine hD hNE hFG hfin w hwD hwN J hc hv b)

theorem nielsenBoundaryCompleteLineProjection_isPreconnected (b:B) : IsPreconnected (lineImage b) := by
  exact (((side b).val.hConvex.isPreconnected.image _ P.finiteCoordinate.symm.continuous.continuousOn).image _
    (Surfaces.mobiusDomainProjection_continuous P.domain).continuousOn)

theorem nielsenBoundaryCompleteLineProjection_subset_frontier (b:B) :
    lineImage b⊆Surfaces.mobiusDomainProjection P.domain '' frontier (fuchsianNielsenCore P hNE) := by
  apply image_mono
  rintro x ⟨z,hz,rfl⟩
  obtain ⟨y,hy,hyz⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE (side b).val (side b).property.1 hz
  rw [←hyz,P.finiteCoordinate.symm_apply_apply]
  exact hy

theorem nielsenBoundaryCompleteLineProjection_next (b:B) : lineImage b=lineImage ((ρ) b) := by
  have hR:rightPoint b∈nativeEdge b:=by
    apply (mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b _).mpr
    rw [nielsenCyclicBoundaryNativeRightPoint_spec]
    exact Polygon.closedModelDiscHSegment_right_mem _ _
  have hL:point ((ρ) b)∈nativeEdge ((ρ) b):=by
    apply (mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv ((ρ) b) _).mpr
    rw [(nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv ((ρ) b)).1]
    exact Polygon.closedModelDiscHSegment_left_mem _ _
  apply nielsenBoundary_line_projections_eq_of_inter P hNE (side b).val (side ((ρ) b)).val
    (side b).property.1 (side ((ρ) b)).property.1
    (Surfaces.mobiusDomainProjection P.domain (rightPoint b))
  · exact ⟨rightPoint b,nielsenCyclicBoundaryNativeEdge_subset_fullLine hD hNE hFG hfin w hwD hwN J hc hv b hR,rfl⟩
  · exact ⟨point ((ρ) b),nielsenCyclicBoundaryNativeEdge_subset_fullLine hD hNE hFG hfin w hwD hwN J hc hv ((ρ) b) hL,
      (nielsenCyclicBoundaryNativeRightPoint_projection hD hNE hFG hfin w hwD hwN J hc hv b).symm⟩

theorem nielsenBoundaryCompleteLineProjection_sameCycle (b c:B)
    (hbc:Equiv.Perm.SameCycle (ρ) b c) : lineImage b=lineImage c := by
  obtain ⟨n,_hn,rfl⟩:=hbc.exists_pow_eq'
  clear hbc _hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact ih.trans (nielsenBoundaryCompleteLineProjection_next hD hNE hFG hfin w hwD hwN J hc hv _)

/-- Each cap-cycle carrier lies in exactly its actual whole complete boundary-line projection. -/
theorem nielsenProjectedBoundaryCycle_subset_completeLine (b:B) :
    cycleCarrier (Quotient.mk _ b)⊆lineImage b := by
  intro p hp
  obtain ⟨c,hpc⟩:=mem_iUnion.mp hp
  have hbc:Equiv.Perm.SameCycle (ρ) b c.val:=Quotient.exact c.property.symm
  rw [nielsenBoundaryCompleteLineProjection_sameCycle hD hNE hFG hfin w hwD hwN J hc hv b c.val hbc]
  exact nielsenProjectedBoundaryEdge_subset_lineProjection hD hNE hFG hfin w hwD hwN J hc hv c.val hpc

/-- A complete actual boundary-line projection cannot split across the finitely many disjoint compact true boundary cycles. -/
theorem nielsenBoundaryCompleteLineProjection_subset_cycle (b:B) :
    lineImage b⊆cycleCarrier (Quotient.mk _ b) := by
  let :T2Space (Surfaces.MobiusDomainQuotient P.domain):=Surfaces.mobiusDomainQuotient_t2 P.domain P.discontinuous
  let c:C:=Quotient.mk _ b
  let T:Set (Surfaces.MobiusDomainQuotient P.domain):=⋃d:{d:C // d≠c},cycleCarrier d.val
  have hcompact (d : C) : IsCompact (cycleCarrier d) :=
    nielsenProjectedBoundaryCycle_isCompact
      hD hNE hFG hfin w hwD hwN J hc hv d
  have hS : IsClosed (cycleCarrier c) := (hcompact c).isClosed
  have hT : IsClosed T :=
    isClosed_iUnion_of_finite (fun d => (hcompact d.val).isClosed)
  have hd:Disjoint (cycleCarrier c) T:=by
    apply disjoint_left.mpr
    intro p hp hpt
    obtain ⟨d,hpd⟩:=mem_iUnion.mp hpt
    exact disjoint_left.mp (nielsenProjectedBoundaryCycle_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv
      d.property.symm) hp hpd
  have hcover:lineImage b⊆cycleCarrier c∪T:=by
    intro p hp
    have hpf:=nielsenBoundaryCompleteLineProjection_subset_frontier hD hNE hFG hfin w hwD hwN J hc hv b hp
    rw [←nielsenProjectedBoundaryCycles_cover hD hNE hFG hfin w hwD hwN J hc hv] at hpf
    obtain ⟨d,hpd⟩:=mem_iUnion.mp hpf
    by_cases he:d=c
    · exact Or.inl (he ▸ hpd)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨d,he⟩,hpd⟩)
  have hmeet:(lineImage b∩cycleCarrier c).Nonempty:=by
    obtain ⟨p,hp⟩:=nielsenProjectedBoundaryCycle_nonempty hD hNE hFG hfin w hwD hwN J hc hv c
    exact ⟨p,nielsenProjectedBoundaryCycle_subset_completeLine hD hNE hFG hfin w hwD hwN J hc hv b hp,hp⟩
  intro p hp
  by_contra hpn
  have hpt:p∈T:=(hcover hp).resolve_left hpn
  obtain ⟨z,_hz,hzS,hzT⟩:=isPreconnected_closed_iff.mp
    (nielsenBoundaryCompleteLineProjection_isPreconnected hD hNE hFG hfin w hwD hwN J hc hv b)
      _ _ hS hT hcover hmeet ⟨p,hp,hpt⟩
  exact disjoint_left.mp hd hzS hzT

/-- The actual whole boundary geodesic quotient equals its exact first-return cap-cycle carrier. -/
theorem nielsenProjectedBoundaryCycle_eq_completeLine (b:B) :
    cycleCarrier (Quotient.mk _ b)=lineImage b :=
  subset_antisymm
    (nielsenProjectedBoundaryCycle_subset_completeLine hD hNE hFG hfin w hwD hwN J hc hv b)
    (nielsenBoundaryCompleteLineProjection_subset_cycle hD hNE hFG hfin w hwD hwN J hc hv b)

end NielsenBoundaryLineProjection



section NielsenBoundaryCycleCircles
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "side" => nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv
local notation "lineImage" => nielsenBoundaryCompleteLineProjection hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv

/-- Each actual first-return cycle is a genuine circle in the original quotient, via the complete geometric boundary axis. -/
theorem nielsenProjectedBoundaryCycle_circle (b:B) :
    Nonempty (↥(cycleCarrier (Quotient.mk _ b))≃ₜCircle) := by
  obtain ⟨g,hg,M,hM,_hmax,C,hC,_hπ⟩:=finitelyGenerated_nielsen_boundary_line_embedded_circle
    P hNE hFG (side b).val (side b).property.1
  let F:Circle→Surfaces.MobiusDomainQuotient P.domain:=
    sphereSetOrbitMap P.asFuchsianDisc.domain M.carrier M.carrier_subset_domain ∘ C.symm
  have hF:Topology.IsEmbedding F:=hC
  have hR:range F=lineImage b:=by
    apply subset_antisymm
    · rintro p ⟨t,rfl⟩
      obtain ⟨a,ha⟩:=Quotient.exists_rep (C.symm t)
      have haM:a.val∈(Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) ''
          (P.finiteCoordinate.symm '' (side b).val.carrier):=by
        rw [←hM]
        exact a.property
      obtain ⟨x,hx,hxa⟩:=haM
      refine ⟨x,hx,?_⟩
      change Surfaces.mobiusDomainProjection P.domain x=sphereSetOrbitMap _ _ _ (C.symm t)
      rw [←ha]
      change Surfaces.mobiusDomainProjection P.domain x=Surfaces.mobiusDomainProjection P.domain ⟨a.val,_⟩
      congr 1
      exact Subtype.ext hxa
    · rintro p ⟨x,hx,rfl⟩
      let a:M.carrier:=⟨x.val,by rw [hM];exact mem_image_of_mem _ hx⟩
      refine ⟨C (Quotient.mk _ a),?_⟩
      change sphereSetOrbitMap _ _ _ (C.symm (C (Quotient.mk _ a)))=_
      rw [C.symm_apply_apply]
      rfl
  let E:Circle≃ₜ↥(lineImage b):=hF.toHomeomorph.trans (Homeomorph.setCongr hR)
  let G:=Homeomorph.setCongr (nielsenProjectedBoundaryCycle_eq_completeLine hD hNE hFG hfin w hwD hwN J hc hv b)
  exact ⟨G.trans E.symm⟩

end NielsenBoundaryCycleCircles



/-- Every original boundary-hyperbolic axis is one of the actual complete core frontier geodesics. -/
theorem nielsenBoundaryHyperbolic_axis_mem_family
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (f:H) (hf:IsBoundaryHyperbolic P.asFuchsianDisc f)
    (M:FuchsianAxisModel P.asFuchsianDisc f.val) :
    ∃L:Hyperbolic.DiscLine,L∈nielsenBoundaryDiscLineFamily P hNE ∧
      M.carrier=(Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier) := by
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  have hq:=P.asFuchsianDisc.nielsenArcNormalizer_image hNE
  have hinf:=P.asFuchsianDisc.nielsenArcNormalizer_limit hNE
  have hp:(q*f.val*q⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet:=by
    rw [←hq,Mobius.stableAxis_conjugate_image,q.val.injective.image_injective.eq_iff]
    exact P.image_eq f
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL _ hp
  have hAH:Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A):=by
    rw [hA]
    exact Mobius.mobiusHyperbolic_conjugation_forward _ q hf.hyperbolic
  have hAn:=hAH.1.1
  have ht:=(Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAH
  obtain ⟨G,hGF,hGA⟩:=boundaryHyperbolic_normalized_gap P.asFuchsianDisc hNE q hq hinf f hf A hA hAn ht
  obtain ⟨L,hGL⟩:=nielsenGap_original_native_line P hNE G
  refine ⟨L,⟨G,hGF,hGL⟩,?_⟩
  have hEll:P.finiteCoordinate.symm '' L.carrier=(nielsenHalfPlaneChart P hNE).symm '' G.line.carrier:=by
    rw [←hGL,image_image]
    simp only [Homeomorph.symm_apply_apply,Set.image_id']
  have hPhys:(Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier)=
      nielsenModelSet q G.line.carrier:=by
    rw [hEll]
    exact nielsen_gap_chart_line_sphere_image P q hq G
  have hqL:q.val '' ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier))=
      Hyperbolic.extendedHalfPlanePoint '' G.line.carrier:=by
    rw [hPhys,nielsenModelSet]
    simpa only [inv_inv] using nielsen_mobius_inverse_image q⁻¹ (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)
  apply q.val.injective.image_injective
  rw [boundary_axis_carrier_image_in_chart M q hq A hA hAn ht,←hGA,hqL]

/-- Conjugating a true full set stabilizer by an original member gives exactly the full stabilizer of the actual translated set. -/
theorem nielsen_mobiusSetStabilizer_conjugation
    {H:Subgroup Mobius.complexMobiusGroup}
    (g:H)
    (S:Set Mobius.ExtendedComplex) :
    DiscreteGroups.Action.Actions.subgroupConjugate g.val (Surfaces.mobiusSetStabilizer H S)=
      Surfaces.mobiusSetStabilizer H (g.val.val '' S) := by
  ext f
  constructor
  · intro hf
    obtain ⟨a,ha,rfl⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff g.val (Surfaces.mobiusSetStabilizer H S)
      f).mp hf
    refine ⟨H.mul_mem (H.mul_mem g.property ha.1) (H.inv_mem g.property),?_⟩
    change (g.val*a*g.val⁻¹).val '' (g.val.val '' S)=g.val.val '' S
    rw [Surfaces.cusp_conjugate_image]
    exact congrArg (Set.image g.val.val) (show a.val '' S=S from ha.2)
  · intro hf
    let a:=g.val⁻¹*f*g.val
    have haH:a∈H:=H.mul_mem (H.mul_mem (H.inv_mem g.property) hf.1) g.property
    have hconj:g.val*a*g.val⁻¹=f:=by dsimp only [a];group
    have haS:a.val '' S=S:=by
      apply g.val.val.injective.image_injective
      have h:=Surfaces.cusp_conjugate_image g.val a S
      have hfset:f.val '' (g.val.val '' S)=g.val.val '' S:=hf.2
      rw [hconj,hfset] at h
      exact h.symm
    exact (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff g.val (Surfaces.mobiusSetStabilizer H S) f).mpr
      ⟨a,⟨haH,haS⟩,hconj⟩

/-- Any original maximal cyclic subgroup containing this boundary hyperbolic is the full actual axis stabilizer. -/
theorem nielsen_maximalBoundaryCyclic_eq_axisStabilizer
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (K:Subgroup Mobius.complexMobiusGroup) (hK:IsMaximalCyclicIn H K)
    (f:H) (hfK:f.val∈K) (hf:IsBoundaryHyperbolic P.asFuchsianDisc f)
    (M:FuchsianAxisModel P.asFuchsianDisc f.val) : K=Surfaces.mobiusSetStabilizer H M.carrier := by
  obtain ⟨p,hp⟩:=Mobius.mobius_nonidentity_has_boundary_fixed f.val hf.hyperbolic.1.1
  exact (maximalCyclic_eq_boundaryStabilizer_of_fixed P.asFuchsianDisc K hK f.val hfK
    hf.hyperbolic.1.1 p hp).trans
      (boundaryHyperbolic_axis_stabilizer_eq_endpoint_stabilizer hNE hf M p hp).symm

/-- Intersecting projected complete boundary lines have an actual original whole-line transporter. -/
theorem nielsenBoundary_lines_transport_of_projection_inter
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L M:Hyperbolic.DiscLine) (hL:L∈nielsenBoundaryDiscLineFamily P hNE)
    (hM:M∈nielsenBoundaryDiscLineFamily P hNE)
    (p:Surfaces.MobiusDomainQuotient P.domain)
    (hp:p∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier))
    (hq:p∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' M.carrier)) :
    ∃g:H,g•(P.finiteCoordinate.symm '' M.carrier)=P.finiteCoordinate.symm '' L.carrier := by
  obtain ⟨x,hx,hxp⟩:=hp
  obtain ⟨y,hy,hyp⟩:=hq
  have horb:=Quotient.exact (hxp.trans hyp.symm)
  change x∈MulAction.orbit H y at horb
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
  obtain ⟨K,hK,hgK⟩:=nielsenBoundary_original_line_image P hNE M hM g
  have hxK:x∈P.finiteCoordinate.symm '' K.carrier:=hgK ▸ mem_smul_set.mpr ⟨y,hy,hg⟩
  have hcoord (A:Hyperbolic.DiscLine) (hA:x∈P.finiteCoordinate.symm '' A.carrier):P.finiteCoordinate x∈A.carrier:=by
    obtain ⟨z,hz,rfl⟩:=hA
    simpa only [Homeomorph.apply_symm_apply] using hz
  have hKL:K=L:=by
    by_contra hn
    exact disjoint_left.mp (nielsenBoundaryDiscLineFamily_pairwise_disjoint P hNE hK hL hn)
      (hcoord K hxK) (hcoord L hx)
  exact ⟨g,hKL ▸ hgK⟩



/-- A genuine hyperbolic preserving one complete actual core boundary geodesic has exactly that axis. -/
theorem nielsenBoundary_hyperbolic_invariant_line_axis
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (f:H)
    (hf:Mobius.MobiusHyperbolic f.val)
    (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (L:Hyperbolic.DiscLine) (hL:L∈nielsenBoundaryDiscLineFamily P hNE)
    (hfix:f.val.val '' ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) ''
      (P.finiteCoordinate.symm '' L.carrier))=
        (Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier)) :
    M.carrier=(Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier) := by
  let q:=P.asFuchsianDisc.nielsenArcNormalizer hNE
  have hq:=P.asFuchsianDisc.nielsenArcNormalizer_image hNE
  have hp:(q*f.val*q⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet:=by
    rw [←hq,Mobius.stableAxis_conjugate_image,q.val.injective.image_injective.eq_iff]
    exact P.image_eq f
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL _ hp
  have hAH:Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A):=by
    rw [hA]
    exact Mobius.mobiusHyperbolic_conjugation_forward _ q hf
  have hAn:=hAH.1.1
  have ht:=(Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAH
  obtain ⟨G,_hGF,hGL⟩:=hL
  let S:=(Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier)
  have hEll:P.finiteCoordinate.symm '' L.carrier=(nielsenHalfPlaneChart P hNE).symm '' G.line.carrier:=by
    rw [←hGL,image_image]
    simp only [Homeomorph.symm_apply_apply,Set.image_id']
  have hPhys:S=nielsenModelSet q G.line.carrier:=by
    change (Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier)=_
    rw [hEll]
    exact nielsen_gap_chart_line_sphere_image P q hq G
  have hqS:q.val '' S=Hyperbolic.extendedHalfPlanePoint '' G.line.carrier:=by
    rw [hPhys,nielsenModelSet]
    simpa only [inv_inv] using nielsen_mobius_inverse_image q⁻¹ (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)
  have hReal:(Hyperbolic.realSLMobius A).val '' (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier)=
      Hyperbolic.extendedHalfPlanePoint '' G.line.carrier:=by
    rw [hA,←hqS,Mobius.stableAxis_conjugate_image,hfix]
  have hNative:(fun z:ℍ=>A•z) '' G.line.carrier=G.line.carrier:=by
    apply Mobius.halfPlaneBoundaryPoint_injective.image_injective
    calc
      _=(Hyperbolic.realSLMobius A).val '' (Hyperbolic.extendedHalfPlanePoint '' G.line.carrier):=by
        rw [image_image,image_image]
        congr 1
        funext z
        exact (Hyperbolic.realSLMobius_action A z).symm
      _=Hyperbolic.extendedHalfPlanePoint '' G.line.carrier:=hReal
  have hAxis:=Hyperbolic.hHyperbolicAxis_unique_invariant A hAn ht G.line hNative
  apply q.val.injective.image_injective
  rw [boundary_axis_carrier_image_in_chart M q hq A hA hAn ht,←hAxis]
  exact hqS.symm



/-- The physical image of a genuine original set translate uses the same actual Mobius action. -/
theorem nielsen_physical_smul_image
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (g:H)
    (S:Set P.domain.carrier) :
    (Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (g•S)=
      g.val.val '' ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' S) := by
  change (Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' ((fun x:P.domain.carrier=>g•x) '' S)=_
  rw [image_image,image_image]
  rfl

/-- The complete stabilizer of an actual core boundary geodesic is a genuine maximal boundary cyclic subgroup of the whole original group. -/
def nielsenBoundaryLineMaximalCyclic
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) :
    fuchsianMaximalBoundaryHyperbolicCyclicSubgroups P.asFuchsianDisc := by
  let S:=(Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier)
  refine ⟨Surfaces.mobiusSetStabilizer H S,?_⟩
  obtain ⟨f,hf,M,hM⟩:=finitelyGenerated_nielsen_boundary_line_boundaryHyperbolic P hNE hFG L hL
  have hmax:=boundaryHyperbolic_axis_stabilizer_maximalCyclic hNE hf M
  rw [hM] at hmax
  refine ⟨hmax,f,?_ ,hf⟩
  change f.val∈Surfaces.mobiusSetStabilizer H
    ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier))
  rw [←hM]
  exact ⟨f.property,M.carrier_invariant⟩

theorem nielsenBoundaryLineMaximalCyclic_val
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) :
    (nielsenBoundaryLineMaximalCyclic P hNE hFG L hL).val=
      Surfaces.mobiusSetStabilizer H ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm
        '' L.carrier)) := rfl

def nielsenBoundaryLineCyclicClass
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) :
    FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc :=
  Quotient.mk _ (nielsenBoundaryLineMaximalCyclic P hNE hFG L hL)

/-- Meeting projected true boundary geodesics have exactly the same original boundary-cyclic class. -/
theorem nielsenBoundaryLineCyclicClass_eq_of_projection_inter
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (L M:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE)
    (hM:M∈nielsenBoundaryDiscLineFamily P hNE)
    (p:Surfaces.MobiusDomainQuotient P.domain)
    (hp:p∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier))
    (hq:p∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' M.carrier)) :
    nielsenBoundaryLineCyclicClass P hNE hFG L hL=nielsenBoundaryLineCyclicClass P hNE hFG M hM := by
  let :=mobiusSubgroupConjugationAction H
  obtain ⟨g,hg⟩:=nielsenBoundary_lines_transport_of_projection_inter P hNE L M hL hM p hp hq
  have hSphere:g.val.val '' ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm ''
    M.carrier))=
      (Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier):=by
    rw [←nielsen_physical_smul_image,hg]
  apply Quotient.sound
  change (nielsenBoundaryLineMaximalCyclic P hNE hFG L hL).val∈
    MulAction.orbit H (nielsenBoundaryLineMaximalCyclic P hNE hFG M hM).val
  rw [nielsenBoundaryLineMaximalCyclic_val,nielsenBoundaryLineMaximalCyclic_val]
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g,?_⟩
  change DiscreteGroups.Action.Actions.subgroupConjugate g.val (Surfaces.mobiusSetStabilizer H _) = _
  rw [nielsen_mobiusSetStabilizer_conjugation,hSphere]

/-- Actual conjugate maximal boundary-cyclic labels determine exactly the same literal whole-axis projection. -/
theorem nielsenBoundaryLine_projection_eq_of_class_eq
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (L M:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE)
    (hM:M∈nielsenBoundaryDiscLineFamily P hNE)
    (hclass:nielsenBoundaryLineCyclicClass P hNE hFG L hL=nielsenBoundaryLineCyclicClass P hNE hFG M hM) :
    Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier)=
      Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' M.carrier) := by
  let :=mobiusSubgroupConjugationAction H
  have horb:=Quotient.exact hclass
  change (nielsenBoundaryLineMaximalCyclic P hNE hFG L hL).val∈
    MulAction.orbit H (nielsenBoundaryLineMaximalCyclic P hNE hFG M hM).val at horb
  rw [nielsenBoundaryLineMaximalCyclic_val,nielsenBoundaryLineMaximalCyclic_val] at horb
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
  change DiscreteGroups.Action.Actions.subgroupConjugate g.val (Surfaces.mobiusSetStabilizer H _) = _ at hg
  obtain ⟨T,hT,hgT⟩:=nielsenBoundary_original_line_image P hNE M hM g
  have hSphere:g.val.val '' ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm ''
    M.carrier))=
      (Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' T.carrier):=by
    rw [←nielsen_physical_smul_image,hgT]
  rw [nielsen_mobiusSetStabilizer_conjugation,hSphere] at hg
  obtain ⟨f,hf,A,hA⟩:=finitelyGenerated_nielsen_boundary_line_boundaryHyperbolic P hNE hFG L hL
  have hfK:f.val∈Surfaces.mobiusSetStabilizer H
      ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier)):=by
    rw [←hA]
    exact ⟨f.property,A.carrier_invariant⟩
  have hfT:=hg.symm ▸ hfK
  have hAT:=nielsenBoundary_hyperbolic_invariant_line_axis P hNE f hf.hyperbolic A T hT
    (show f.val.val '' ((Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm ''
      T.carrier))=
      (Subtype.val:P.domain.carrier→Mobius.ExtendedComplex) '' (P.finiteCoordinate.symm '' T.carrier) from hfT.2)
  have hTL:P.finiteCoordinate.symm '' T.carrier=P.finiteCoordinate.symm '' L.carrier:=
    Subtype.val_injective.image_injective (hAT.symm.trans hA)
  calc
    _=Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' T.carrier):=congrArg (Set.image
      _) hTL.symm
    _=Surfaces.mobiusDomainProjection P.domain '' (g•(P.finiteCoordinate.symm '' M.carrier)):=by rw [hgT]
    _=_:=nielsenProjection_image_smul P g _



section NielsenBoundaryCycleClasses
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "side" => nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "lineImage" => nielsenBoundaryCompleteLineProjection hD hNE hFG hfin w hwD hwN J hc hv

def nielsenBoundaryCycleIndexClass (b:B) :
    FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc :=
  nielsenBoundaryLineCyclicClass P hNE hFG (side b).val (side b).property.1
local notation "indexClass" => nielsenBoundaryCycleIndexClass hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenBoundaryCycleIndexClass_sameCycle (b c:B)
    (hbc:Equiv.Perm.SameCycle (ρ) b c) : indexClass b=indexClass c := by
  obtain ⟨p,hp⟩:=nielsenProjectedBoundaryCycle_nonempty hD hNE hFG hfin w hwD hwN J hc hv (Quotient.mk _ b)
  have hpL:=nielsenProjectedBoundaryCycle_subset_completeLine hD hNE hFG hfin w hwD hwN J hc hv b hp
  have hpM:=hpL
  rw [nielsenBoundaryCompleteLineProjection_sameCycle hD hNE hFG hfin w hwD hwN J hc hv b c hbc] at hpM
  exact nielsenBoundaryLineCyclicClass_eq_of_projection_inter P hNE hFG
    (side b).val (side c).val (side b).property.1 (side c).property.1 p hpL hpM

/-- The label of an actual first-return boundary cycle is its whole original maximal boundary-cyclic conjugacy class. -/
def nielsenBoundaryCycleClassMap : C→FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc :=
  Quotient.lift (indexClass) (nielsenBoundaryCycleIndexClass_sameCycle hD hNE hFG hfin w hwD hwN J hc hv)
local notation "classMap" => nielsenBoundaryCycleClassMap hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenBoundaryCycleClassMap_mk (b:B) : classMap (Quotient.mk _ b)=indexClass b := rfl

theorem nielsenBoundaryCycleClassMap_injective : Function.Injective (classMap) := by
  intro c d hcd
  obtain ⟨b,rfl⟩:=Quotient.exists_rep c
  obtain ⟨e,rfl⟩:=Quotient.exists_rep d
  have he:lineImage b=lineImage e:=nielsenBoundaryLine_projection_eq_of_class_eq P hNE hFG
    (side b).val (side e).val (side b).property.1 (side e).property.1 hcd
  have hcar:cycleCarrier (Quotient.mk _ b)=cycleCarrier (Quotient.mk _ e):=by
    rw [nielsenProjectedBoundaryCycle_eq_completeLine,nielsenProjectedBoundaryCycle_eq_completeLine]
    exact he
  by_contra hne
  obtain ⟨p,hp⟩:=nielsenProjectedBoundaryCycle_nonempty hD hNE hFG hfin w hwD hwN J hc hv (Quotient.mk _ b)
  exact disjoint_left.mp (nielsenProjectedBoundaryCycle_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv hne)
    hp (hcar ▸ hp)

theorem nielsenBoundaryCycleClassMap_surjective : Function.Surjective (classMap) := by
  intro q
  induction q using Quotient.inductionOn with
  | h K =>
    obtain ⟨f,hfK,hf⟩:=K.property.2
    obtain ⟨M⟩:=P.asFuchsianDisc.axisModel_exists f.val f.property hf.hyperbolic
    obtain ⟨L,hL,hM⟩:=nielsenBoundaryHyperbolic_axis_mem_family P hNE f hf M
    have hKL:K.val=(nielsenBoundaryLineMaximalCyclic P hNE hFG L hL).val:=by
      rw [nielsenBoundaryLineMaximalCyclic_val,←hM]
      exact nielsen_maximalBoundaryCyclic_eq_axisStabilizer P hNE K.val K.property.1 f hfK hf M
    have hclass:Quotient.mk (fuchsianBoundaryHyperbolicCyclicConjugacySetoid P.asFuchsianDisc) K=
        nielsenBoundaryLineCyclicClass P hNE hFG L hL:=by
      exact congrArg (Quotient.mk _) (Subtype.ext hKL)
    have hnonempty:(P.finiteCoordinate.symm '' L.carrier).Nonempty:=by
      by_contra hn
      have he:(P.finiteCoordinate.symm '' L.carrier)=∅:=not_nonempty_iff_eq_empty.mp hn
      exact nielsenBoundary_original_line_not_compact P L (he ▸ isCompact_empty)
    obtain ⟨x,hx⟩:=hnonempty
    have hxN:x∈frontier (fuchsianNielsenCore P hNE):=by
      obtain ⟨z,hz,rfl⟩:=hx
      obtain ⟨y,hy,hyz⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hz
      rw [←hyz,P.finiteCoordinate.symm_apply_apply]
      exact hy
    have hp:Surfaces.mobiusDomainProjection P.domain x∈⋃c:C,cycleCarrier c:=by
      rw [nielsenProjectedBoundaryCycles_cover]
      exact ⟨x,hxN,rfl⟩
    obtain ⟨c,hpc⟩:=mem_iUnion.mp hp
    obtain ⟨b,rfl⟩:=Quotient.exists_rep c
    have hpb:=nielsenProjectedBoundaryCycle_subset_completeLine hD hNE hFG hfin w hwD hwN J hc hv b hpc
    refine ⟨Quotient.mk _ b,?_⟩
    exact (nielsenBoundaryLineCyclicClass_eq_of_projection_inter P hNE hFG
      (side b).val L (side b).property.1 hL (Surfaces.mobiusDomainProjection P.domain
        x) hpb ⟨x,hx,rfl⟩).trans hclass.symm

/-- Actual cap cycles count every original maximal boundary-hyperbolic cyclic conjugacy class exactly once. -/
def nielsenBoundaryCycleClassesEquiv : C≃FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc :=
  Equiv.ofBijective (classMap)
    ⟨nielsenBoundaryCycleClassMap_injective hD hNE hFG hfin w hwD hwN J hc hv,
      nielsenBoundaryCycleClassMap_surjective hD hNE hFG hfin w hwD hwN J hc hv⟩

theorem nielsenBoundaryCycleClassCount_eq :
    Nat.card C=Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) :=
  Nat.card_congr (nielsenBoundaryCycleClassesEquiv hD hNE hFG hfin w hwD hwN J hc hv)

end NielsenBoundaryCycleClasses

section NielsenActualBoundaryArea
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)

/-- The true original boundary-cyclic class count and full original elliptic order list occur in the actual Nielsen area identity. The remaining transports concern only the cap-word genus and ideal zero classes. -/
theorem nielsenCappedWord_genus_actualBoundaryElliptic_area :
    let _nielsenCappedBoundaryEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    ∃g,Surfaces.HasTopologicalGenus
      ((nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).PolygonalRealization
        (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
        (2*(g:ℝ)-2+Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc)+
          nielsenRawIdealClassCount hD hNE hFG hfin w hwD hwN J hc hv+
          ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum) := by
  let _nielsenCappedBoundaryEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD hfin
  obtain ⟨g,hg,ha⟩:=nielsenCappedWord_genus_actualElliptic_area hD hNE hFG hfin w hwD hwN J hc hv
  refine ⟨g,hg,?_⟩
  have ht:Fintype.card (NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv)=
      Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc):=by
    rw [←Nat.card_eq_fintype_card]
    exact nielsenBoundaryCycleClassCount_eq hD hNE hFG hfin w hwD hwN J hc hv
  rwa [ht] at ha

end NielsenActualBoundaryArea

end NielsenBoundaryCycleCensus

end LowDimensionalTopology.Geometry.Fuchsian
