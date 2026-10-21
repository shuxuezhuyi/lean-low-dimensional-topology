module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Support.StrictPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonConvexAngles
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Polygon.Development.Data
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareReflectionVertices
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The literal original finite geodesic polygon vertex in the native half-plane model. -/
def finitePolygonVertex {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i))

/-- Its actual compactified disc coordinate is precisely the given original polygon vertex. -/
theorem finitePolygonVertex_coordinate {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite i))=Q.vertices i := by
  rw [finitePolygonVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  exact Subtype.ext rfl

/-- The actual original cyclic geodesic side, transported without changing its points. -/
def finitePolygonSide {n : ℕ} (Q : DiscPolygon n) (i : Fin n) : Set ℍ :=
  (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) ⁻¹' discPolygonEdge Q.vertices i

theorem finitePolygonSide_left_mem {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    finitePolygonVertex Q hfinite i∈finitePolygonSide Q i := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite i))∈discPolygonEdge Q.vertices i
  rw [finitePolygonVertex_coordinate]
  exact closedModelDiscHSegment_left_mem _ _

theorem finitePolygonSide_right_mem {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    finitePolygonVertex Q hfinite (finRotate n i)∈finitePolygonSide Q i := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite (finRotate n i)))∈discPolygonEdge Q.vertices i
  rw [finitePolygonVertex_coordinate]
  exact closedModelDiscHSegment_right_mem _ _

/-- The source-defined actual Jordan polygon, with its genuine original inside and sides,
as the original abstract Poincare polygon data. No group or fundamental-domain property is assumed. -/
def finiteDiscPoincarePolygon {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : PoincarePolygon ℍ where
  interior := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior
  interior_nonempty := by
    obtain ⟨z,hz⟩ := Q.interior_isConnected.nonempty
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z,?_⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)∈Q.interior
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  sides := range (finitePolygonSide Q)
  sides_nonempty := by
    have hn : 0<n := by have:=Q.three_le;omega
    exact ⟨finitePolygonSide Q ⟨0,hn⟩,mem_range_self _⟩
  side_nonempty := by
    rintro s ⟨i,rfl⟩
    exact ⟨finitePolygonVertex Q hfinite i,finitePolygonSide_left_mem Q hfinite i⟩
  disjoint := by
    apply Set.disjoint_left.mpr
    intro z hzI hzB
    obtain ⟨s,⟨i,rfl⟩,hs⟩ := mem_sUnion.mp hzB
    have hboundary : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)∈Q.complexBoundary := by
      refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),?_,rfl⟩
      exact mem_iUnion.mpr ⟨i,hs⟩
    exact hzI.1 hboundary

/-- The actual original finite vertices remain distinct in native half-plane coordinates. -/
theorem finitePolygonVertex_injective {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : Function.Injective (finitePolygonVertex Q hfinite) := by
  intro i j hij
  apply Q.vertices_injective
  calc Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite i)) :=
        (finitePolygonVertex_coordinate Q hfinite i).symm
       _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite j)) :=
        congrArg (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) hij
       _=Q.vertices j := finitePolygonVertex_coordinate Q hfinite j

/-- Distinct actual cyclic polygon sides are distinct literal native sets. -/
theorem finitePolygonSide_injective {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : Function.Injective (finitePolygonSide Q) := by
  intro i j hij
  by_contra hne
  have hl := finitePolygonSide_left_mem Q hfinite i
  have hr := finitePolygonSide_right_mem Q hfinite i
  rw [hij] at hl hr
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite i))∈discPolygonEdge Q.vertices j at hl
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite (finRotate n i)))∈discPolygonEdge Q.vertices j at hr
  rw [finitePolygonVertex_coordinate] at hl hr
  have hle := (Q.simple_edges i j hne ⟨closedModelDiscHSegment_left_mem _ _,hl⟩).2
  have hre := (Q.simple_edges i j hne ⟨closedModelDiscHSegment_right_mem _ _,hr⟩).2
  simp only [mem_insert_iff,mem_singleton_iff] at hle hre
  have hleI : i=j ∨i=finRotate n j := hle.imp (fun h=>Q.vertices_injective h) (fun h=>Q.vertices_injective h)
  have hreI : finRotate n i=j ∨finRotate n i=finRotate n j := hre.imp (fun h=>Q.vertices_injective h) (fun
    h=>Q.vertices_injective h)
  rcases hleI with he | he
  · exact hne he
  · rcases hreI with he' | he'
    · apply polygonSupport_next_next_ne_self Q.three_le j
      exact (congrArg (finRotate n) he.symm).trans he'
    · exact hne ((finRotate n).injective he')

/-- Each original finite polygon side is genuinely closed in the native hyperbolic plane. -/
theorem finitePolygonSide_isClosed {n : ℕ} (Q : DiscPolygon n) (i : Fin n) :
    IsClosed (finitePolygonSide Q i) := by
  let : T2Space 𝕔𝔻 := Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  exact (closedModelDiscHSegment_isCompact (Q.vertices i) (Q.vertices (finRotate n i))).isClosed.preimage
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.continuous.comp
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous)

/-- The actual original union of sides is exactly the original native boundary. -/
theorem finiteDiscPoincarePolygon_boundary {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    (finiteDiscPoincarePolygon Q hfinite).boundary=
      (fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹' Q.complexBoundary := by
  ext z
  constructor
  · rintro ⟨s,⟨i,rfl⟩,hz⟩
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),mem_iUnion.mpr ⟨i,hz⟩,rfl⟩
  · rintro ⟨p,hp,he⟩
    have he' : p=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) := Subtype.ext he
    subst p
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    exact ⟨finitePolygonSide Q i,mem_range_self i,hi⟩

/-- The genuine original carrier is the closure of its actual open Jordan inside. -/
theorem finiteDiscPoincarePolygon_carrier {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    (finiteDiscPoincarePolygon Q hfinite).carrier=closure (finiteDiscPoincarePolygon Q hfinite).interior := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hfc : Continuous f := Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f := hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  calc
    _=(f ⁻¹' Q.complexInterior)∪(f ⁻¹' Q.complexBoundary) := by
      rw [PoincarePolygon.carrier,finiteDiscPoincarePolygon_boundary]
      rfl
    _=f ⁻¹' closure Q.complexInterior := by rw [Q.closure_complexInterior,preimage_union]
    _=closure (f ⁻¹' Q.complexInterior) := hfo.preimage_closure_eq_closure_preimage hfc _
    _=_ := rfl

/-- The actual original cyclic side index is equivalent to the literal Poincare side set. -/
def finitePolygonSideEquiv {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : Fin n ≃ (finiteDiscPoincarePolygon Q hfinite).Side :=
  Equiv.ofInjective (finitePolygonSide Q) (finitePolygonSide_injective Q hfinite)

/-- The support of the original native polygon side is its genuine geodesic. -/
def finitePolygonLine {n : ℕ} (Q : DiscPolygon n) (i : Fin
  n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine :=
  (Q.geodesicSide i).toHalfPlane

/-- A literal original side is contained in its true native geodesic support. -/
theorem finitePolygonSide_subset_line {n : ℕ} (Q : DiscPolygon n) (i : Fin n) :
    finitePolygonSide Q i⊆(finitePolygonLine Q i).carrier := by
  intro z hz
  let L:=Q.geodesicSide i
  have hEnds := Q.geodesicSide_endpoints i
  have hne : Q.vertices i≠Q.vertices (finRotate n i) := Q.vertices_injective.ne (Q.next_ne_self i).symm
  have hzArc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈L.closedArcHull (Q.vertices i) (Q.vertices (finRotate n i)) := by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_eq_arcHull L _ _ hne hEnds.1 hEnds.2]
    exact hz
  have hzL : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈L.closedCarrier :=
    hzArc L.closedCarrier L.closedCarrier_isPreconnected (Subset.refl _) hEnds.1 hEnds.2
  have hCarrier := (L.closedCarrier_mem_interior_iff (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    z)).mp hzL
  have hPlane := (L.mem_carrier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)).mp hCarrier
  change z∈L.toHalfPlane.carrier
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hPlane

/-- Reflection in the genuine original geodesic fixes the entire literal original side. -/
theorem finitePolygonSide_reflection_fixed {n : ℕ} (Q : DiscPolygon n) (i : Fin n)
    (z : ℍ) (hz : z∈finitePolygonSide Q i) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (finitePolygonLine Q i) z=z :=
  ((finitePolygonLine Q i).reflection_fixed_iff z).mpr (finitePolygonSide_subset_line Q i hz)

/-- The actual polygon reflection sends its original side exactly onto itself. -/
theorem finitePolygonSide_reflection_image {n : ℕ} (Q : DiscPolygon n) (i : Fin n) :
    (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (finitePolygonLine Q
      i) z) '' finitePolygonSide Q i=
      finitePolygonSide Q i := by
  apply subset_antisymm
  · rintro z ⟨p,hp,rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (finitePolygonLine Q
      i) p∈finitePolygonSide Q i
    rwa [finitePolygonSide_reflection_fixed Q i p hp]
  · intro z hz
    exact ⟨z,hz,finitePolygonSide_reflection_fixed Q i z hz⟩

/-- Each original side reflection is an involution in the actual native isometry group. -/
theorem nativeLineReflection_inv (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L)⁻¹ := by
  apply IsometryEquiv.ext
  intro z
  rfl

/-- The literal original reflection side pairing of the original finite Jordan polygon. -/
def finiteDiscPoincarePairing {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    PoincareSidePairing (ℍ ≃ᵢ ℍ) (finiteDiscPoincarePolygon Q hfinite) where
  paired := Equiv.refl _
  involutive := fun _=>rfl
  element s := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (finitePolygonLine Q
    ((finitePolygonSideEquiv Q hfinite).symm s))
  element_paired s := nativeLineReflection_inv _
  side_image s := by
    let i := (finitePolygonSideEquiv Q hfinite).symm s
    have hs : finitePolygonSide Q i=s.val :=
      congrArg Subtype.val ((finitePolygonSideEquiv Q hfinite).apply_symm_apply s)
    change (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
      (finitePolygonLine Q i) z) '' s.val=s.val
    rw [←hs]
    exact finitePolygonSide_reflection_image Q i

/-- The true generator corresponding to a literal original side is its actual geodesic reflection. -/
theorem finiteDiscPoincarePairing_element {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    (finiteDiscPoincarePairing Q hfinite).element (finitePolygonSideEquiv Q hfinite i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (finitePolygonLine Q i) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (finitePolygonLine Q
    ((finitePolygonSideEquiv Q hfinite).symm (finitePolygonSideEquiv Q hfinite i)))=_
  rw [(finitePolygonSideEquiv Q hfinite).symm_apply_apply]

/-- The original Poincare generated group is exactly the original polygon's actual reflection group. -/
theorem finiteDiscPoincarePairing_generated {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    (finiteDiscPoincarePairing Q hfinite).Generated=
      Subgroup.closure (range (fun i : Fin n=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (finitePolygonLine Q i))) := by
  change Subgroup.closure (range (finiteDiscPoincarePairing Q hfinite).element)=_
  congr 1
  ext g
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(finitePolygonSideEquiv Q hfinite).symm s,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨finitePolygonSideEquiv Q hfinite i,finiteDiscPoincarePairing_element Q hfinite i⟩

/-- Finite original endpoints force every point of their literal original side to be finite. -/
theorem finitePolygonEdge_finite {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) (p : 𝕔𝔻)
    (hp : p∈discPolygonEdge Q.vertices i) : ‖(p : ℂ)‖<1 := by
  let a:=Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)
  let b:=Complex.UnitDisc.mk (Q.vertices (finRotate n i) : ℂ) (hfinite (finRotate n i))
  have ha : Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a := Subtype.ext rfl
  have hb : Q.vertices (finRotate n
    i)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel b := Subtype.ext rfl
  change p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment _ _ at hp
  rw [ha,hb,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_interior] at hp
  obtain ⟨z,_hz,hzp⟩ := hp
  rw [←hzp]
  exact z.norm_lt_one

/-- With finite original vertices the entire actual compactified polygon lies in the finite model. -/
theorem finitePolygonCarrier_finite {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (p : 𝕔𝔻) (hp : p∈Q.closedCarrier) : ‖(p : ℂ)‖<1 := by
  have hpc : (p : ℂ)∈closure Q.complexInterior := by
    rw [←Q.closedCarrier_complex_image]
    exact ⟨p,hp,rfl⟩
  rw [Q.closure_complexInterior] at hpc
  rcases hpc with hI | ⟨q,hq,he⟩
  · have hh := Q.complexInterior_subset_disc hI
    change dist (p : ℂ) 0<1 at hh
    simpa only [dist_zero_right] using hh
  · have hqp : q=p := Subtype.ext he
    subst q
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    exact finitePolygonEdge_finite Q hfinite i p hi

/-- The actual native closed carrier is exactly the finite part of the original compactified carrier. -/
theorem finiteDiscPoincarePolygon_carrier_iff {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (z : ℍ) :
    z∈(finiteDiscPoincarePolygon Q hfinite).carrier ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈Q.closedCarrier := by
  rw [finiteDiscPoincarePolygon_carrier]
  change z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹' Q.interior) ↔
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' Q.interior)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.preimage_closure]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈closure Q.interior ↔_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.closure_eq_preimage_closure_image
    Q.interior]
  rfl

/-- The genuine native finite polygon carrier is compact; compactness is not an input. -/
theorem finiteDiscPoincarePolygon_isCompact {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : IsCompact (finiteDiscPoincarePolygon Q hfinite).carrier := by
  let f : ↥Q.closedCarrier→ℍ:=fun p=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    (Complex.UnitDisc.mk (p.val : ℂ) (finitePolygonCarrier_finite Q hfinite p.val p.property))
  have hf : Continuous f := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.continuous.comp
    apply Complex.UnitDisc.isEmbedding_coe.isInducing.continuous_iff.mpr
    exact Complex.UnitClosedDisc.continuous_coe.comp continuous_subtype_val
  have hcoord (p : ↥Q.closedCarrier) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f p))=p.val := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane _))=p.val
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact Subtype.ext rfl
  have he : range f=(finiteDiscPoincarePolygon Q hfinite).carrier := by
    ext z
    constructor
    · rintro ⟨p,rfl⟩
      rw [finiteDiscPoincarePolygon_carrier_iff,hcoord]
      exact p.property
    · intro hz
      have hp := (finiteDiscPoincarePolygon_carrier_iff Q hfinite z).mp hz
      let p : ↥Q.closedCarrier:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),hp⟩
      refine ⟨p,?_⟩
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
      apply Complex.UnitDisc.coe_injective
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane _) :
        ℂ)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
      rfl
  let : CompactSpace ↥Q.closedCarrier := isCompact_iff_compactSpace.mp Q.closedCarrier_isCompact
  rw [←he]
  exact isCompact_range hf

/-- Each original finite vertex belongs precisely to its two original cyclic incident sides. -/
theorem finitePolygonVertex_side_iff {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i j : Fin n) :
    finitePolygonVertex Q hfinite i∈finitePolygonSide Q j ↔j=(finRotate n).symm i ∨j=i := by
  constructor
  · intro hj
    by_cases hji : j=i
    · exact Or.inr hji
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite i))∈discPolygonEdge Q.vertices j at hj
      rw [finitePolygonVertex_coordinate] at hj
      have he := (Q.simple_edges i j (Ne.symm hji) ⟨closedModelDiscHSegment_left_mem _ _,hj⟩).2
      simp only [mem_insert_iff,mem_singleton_iff] at he
      rcases he with he | he
      · exact (hji (Q.vertices_injective he).symm).elim
      · left
        apply (finRotate n).injective
        rw [(finRotate n).apply_symm_apply]
        exact (Q.vertices_injective he).symm
  · rintro (rfl | rfl)
    · have hp := finitePolygonSide_right_mem Q hfinite ((finRotate n).symm i)
      rwa [(finRotate n).apply_symm_apply] at hp
    · exact finitePolygonSide_left_mem Q hfinite _

/-- The literal original finite vertex as a point of the actual Poincare carrier. -/
def finitePolygonPoincareVertex {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) : (finiteDiscPoincarePolygon Q hfinite).Point :=
  ⟨finitePolygonVertex Q hfinite i,
    (finiteDiscPoincarePolygon Q hfinite).side_subset_carrier (finitePolygonSideEquiv Q hfinite i)
      (finitePolygonSide_left_mem Q hfinite i)⟩

/-- There are genuinely only finitely many literal original sides. -/
theorem finiteDiscPoincarePolygon_finiteSides {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : Finite (finiteDiscPoincarePolygon Q hfinite).Side :=
  Finite.of_equiv (Fin n) (finitePolygonSideEquiv Q hfinite)

/-- Closedness of each actual side is proved from its original geodesic segment. -/
theorem finiteDiscPoincarePolygon_closedSides {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    ∀s : (finiteDiscPoincarePolygon Q hfinite).Side,IsClosed s.val := by
  intro s
  obtain ⟨i,rfl⟩ := (finitePolygonSideEquiv Q hfinite).surjective s
  exact finitePolygonSide_isClosed Q i

/-- Actual closed-side local finiteness follows from the true finite side set. -/
theorem finiteDiscPoincarePolygon_locallyFiniteSides {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    LocallyFinite (fun s : (finiteDiscPoincarePolygon Q hfinite).Side=>s.val) := by
  let : Finite (finiteDiscPoincarePolygon Q hfinite).Side := finiteDiscPoincarePolygon_finiteSides Q hfinite
  exact locallyFinite_of_finite _

/-- The actual backward incident forward ray at the original native finite vertex. -/
def finitePolygonPrevRay {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin
      n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (finitePolygonVertex Q hfinite i) :=
  (Q.cornerRayPrev i (Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)) (Subtype.ext rfl)).toHalfPlane

/-- The actual forward incident ray at the original native finite vertex. -/
def finitePolygonNextRay {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin
      n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (finitePolygonVertex Q hfinite i) :=
  (Q.cornerRayNext i (Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)) (Subtype.ext rfl)).toHalfPlane

theorem finitePolygonPrevRay_support {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    (finitePolygonPrevRay Q hfinite i).supportLine=finitePolygonLine Q ((finRotate n).symm i) := by
  have he := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane (Q.cornerRayPrev_support_geodesicSide i
    (Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)) (Subtype.ext rfl))
  simpa only [finitePolygonPrevRay,finitePolygonLine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.supportLine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane] using he

theorem finitePolygonNextRay_support {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    (finitePolygonNextRay Q hfinite i).supportLine=finitePolygonLine Q i := by
  have he := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane (Q.cornerRayNext_support_geodesicSide i
    (Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)) (Subtype.ext rfl))
  simpa only [finitePolygonNextRay,finitePolygonLine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.supportLine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane] using he

/-- A genuine nonstraight original angle has distinct actual native incident supports. -/
theorem finitePolygon_vertex_rays_proper {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) (ha : Q.angle i≠Real.pi) :
    (finitePolygonPrevRay Q hfinite i).supportLine≠(finitePolygonNextRay Q hfinite i).supportLine := by
  exact ((Q.cornerRayPrev i (Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)) (Subtype.ext
    rfl)).different_supports_iff
    (Q.cornerRayNext i (Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)) (Subtype.ext rfl))).mp
      (Q.finite_corner_proper_of_angle_ne_pi i _ (Subtype.ext rfl) ha)

/-- The actual native incident-ray angle is exactly the original geometric polygon interior angle. -/
theorem finitePolygon_vertex_angle {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) (ha : Q.angle i≠Real.pi) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (finitePolygonPrevRay Q hfinite i) (finitePolygonNextRay Q hfinite i)=Q.angle i := by
  let z:=Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)
  have hz : Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := Subtype.ext rfl
  have hne := Q.finite_corner_proper_of_angle_ne_pi i z hz ha
  have hm := Q.hasMinorInterior_of_isConvex_proper hQ i z hz hne
  have he := (Q.angle_of_minor i z hz hm).symm
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane] at he
  simpa only [finitePolygonPrevRay,finitePolygonNextRay,z] using he

/-- The actual original convex polygon carrier has precisely its genuine closed two-ray angle germ. -/
theorem finitePolygon_vertex_closed_angle_germ {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) (ha : Q.angle i≠Real.pi) :
    ∃r : ℝ,0<r ∧ ∀p : ℍ,dist p (finitePolygonVertex Q hfinite i)<r →
      (p∈(finiteDiscPoincarePolygon Q hfinite).carrier ↔
        p∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (finitePolygonPrevRay Q hfinite i) (finitePolygonNextRay Q hfinite i))) := by
  let z:=Complex.UnitDisc.mk (Q.vertices i : ℂ) (hfinite i)
  have hz : Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := Subtype.ext rfl
  have hne := Q.finite_corner_proper_of_angle_ne_pi i z hz ha
  have hm := Q.hasMinorInterior_of_isConvex_proper hQ i z hz hne
  have hF : Tendsto _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (𝓝 (finitePolygonVertex Q hfinite i)) (𝓝 z) := by
    have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_halfPlaneToDisc.tendsto (finitePolygonVertex
      Q hfinite i)
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hfinite
      i)=z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane z
    rwa [he] at hh
  have hOpen : ∀ᶠp in 𝓝 (finitePolygonVertex Q hfinite i),
      p∈(finiteDiscPoincarePolygon Q hfinite).interior ↔
      p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (finitePolygonPrevRay Q hfinite i) (finitePolygonNextRay Q hfinite i) := by
    filter_upwards [hF.eventually hm] with p hp
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc p∈Q.interior ↔_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior] at hp
    exact hp.trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.mem_set_image
  obtain ⟨r,hr,hG⟩ := Metric.eventually_nhds_iff_ball.mp (_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hOpen)
  refine ⟨r,hr,?_⟩
  intro p hp
  rw [finiteDiscPoincarePolygon_carrier]
  exact hG p hp

/-- The genuine original Jordan inside is open in the native hyperbolic plane. -/
theorem finiteDiscPoincarePolygon_interior_isOpen {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : IsOpen (finiteDiscPoincarePolygon Q hfinite).interior :=
  Q.interior_isOpen.preimage _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_halfPlaneToDisc

/-- The actual original open polygon is connected, independently of any generated group. -/
theorem finiteDiscPoincarePolygon_interior_isConnected {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : IsConnected (finiteDiscPoincarePolygon Q hfinite).interior := by
  change IsConnected (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹' Q.interior)
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isConnected_preimage.mpr Q.interior_isConnected

theorem finiteDiscPoincarePolygon_countableSides {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : (finiteDiscPoincarePolygon Q hfinite).sides.Countable :=
  (Set.finite_range _).countable

/-- Each literal original polygon side is contained in an actual native h-line. -/
theorem finiteDiscPoincarePolygon_geodesicSides {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    ∀s∈(finiteDiscPoincarePolygon Q hfinite).sides,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s⊆L.carrier := by
  rintro s ⟨i,rfl⟩
  exact ⟨finitePolygonLine Q i,finitePolygonSide_subset_line Q i⟩

/-- Every actual original side-pairing generator is precisely its pointwise-fixing original reflection. -/
theorem finiteDiscPoincarePairing_reflection_sides {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    ∀s : (finiteDiscPoincarePolygon Q
      hfinite).Side,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,
      s.val⊆L.carrier ∧ (finiteDiscPoincarePairing Q hfinite).element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L := by
  intro s
  obtain ⟨i,rfl⟩ := (finitePolygonSideEquiv Q hfinite).surjective s
  exact ⟨finitePolygonLine Q i,finitePolygonSide_subset_line Q i,finiteDiscPoincarePairing_element Q hfinite i⟩

/-- The literal original native vertex set is discrete because it is genuinely finite. -/
theorem finitePolygonVertices_isDiscrete {n : ℕ} (Q : DiscPolygon n)
    (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) : IsDiscrete (range (finitePolygonVertex Q hfinite)) :=
  (Set.finite_range _).isDiscrete

/-- Actual centered support data identify the entire genuine closed Jordan body in Klein coordinates. -/
theorem centeredPolygon_closedCarrier_klein_image {n : ℕ} (A : CenteredDiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' A.toDiscPolygon.closedCarrier=A.kleinRegion := by
  calc
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' (((↑) : 𝕔𝔻→ℂ) '' A.toDiscPolygon.closedCarrier) := by
      rw [image_image]
      simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed]
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' closure A.toDiscPolygon.complexInterior := by
      rw [A.toDiscPolygon.closedCarrier_complex_image]
    _=closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph ''
      A.toDiscPolygon.complexInterior) :=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_closure _
    _=A.kleinRegion := by rw [A.complexInterior_image,A.closure_strictKleinRegion]

/-- Every original side of a strictly convex original polygon is the whole genuine closed
polygon intersection with its own actual native supporting line. -/
theorem finitePolygonSide_eq_carrier_inter_line {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    finitePolygonSide Q i=(finiteDiscPoincarePolygon Q hfinite).carrier∩(finitePolygonLine Q i).carrier := by
  let A:=(Q.strictSupportData hQ ha).toCenteredData
  have hAQ : A.toDiscPolygon=Q := Q.strictSupportData_toDiscPolygon hQ ha
  have hAL : A.supportLine i=Q.geodesicSide i := Q.strictSupportData_supportLine hQ ha i
  have hBody : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.closedCarrier=A.kleinRegion := by
    rw [←hAQ]
    exact centeredPolygon_closedCarrier_klein_image A
  have hLine (z : ℍ) : z∈(finitePolygonLine Q i).carrier ↔
      inner ℝ (A.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)))=A.offsets i := by
    rw [←A.supportLine_equation]
    rw [hAL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_mem_interior_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    rfl
  ext z
  constructor
  · intro hz
    have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinFace i := by
      rw [←A.edge_image_eq_face]
      exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),hz,rfl⟩
    have hP : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈Q.closedCarrier := by
      have hh:=hK.1
      rw [←hBody] at hh
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp hh
    exact ⟨(finiteDiscPoincarePolygon_carrier_iff Q hfinite z).mpr hP,finitePolygonSide_subset_line Q i hz⟩
  · rintro ⟨hP,hL⟩
    have hcP := (finiteDiscPoincarePolygon_carrier_iff Q hfinite z).mp hP
    have hBodyP : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinRegion := by
      rw [←hBody]
      exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),hcP,rfl⟩
    have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinFace i :=
      ⟨hBodyP,(hLine z).mp hL⟩
    rw [←A.edge_image_eq_face] at hK
    have hz := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp hK
    exact hz

/-- Every actual reciprocal-angle vertex of the original finite polygon satisfies the full
local Poincare condition, from its original geometric angle and literal side reflections. -/
theorem finitePolygon_integral_vertex_local_condition {m : ℕ} (Q : DiscPolygon m) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hfinite : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (i : Fin m) (n : ℕ) (hn : 2≤n) (hangle : Q.angle i=Real.pi/(n:ℝ)) :
    ((finiteDiscPoincarePairing Q hfinite).project ⁻¹'
      {(finiteDiscPoincarePairing Q hfinite).project (1,finitePolygonPoincareVertex Q hfinite i)}).Finite ∧
    ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r ≤ r₀ →
      (finiteDiscPoincarePairing Q hfinite).LocalTessellation (1,finitePolygonPoincareVertex Q hfinite i) r := by
  let P:=finiteDiscPoincarePolygon Q hfinite
  let S:=finiteDiscPoincarePairing Q hfinite
  let x:=finitePolygonPoincareVertex Q hfinite i
  let s:=finitePolygonSideEquiv Q hfinite ((finRotate m).symm i)
  let t:=finitePolygonSideEquiv Q hfinite i
  let R:=finitePolygonPrevRay Q hfinite i
  let U:=finitePolygonNextRay Q hfinite i
  have hxs : x.val∈s.val := (finitePolygonVertex_side_iff Q hfinite i _).mpr (Or.inl rfl)
  have hxt : x.val∈t.val := finitePolygonSide_left_mem Q hfinite i
  have hAll : ∀u : P.Side,x.val∈u.val → u=s ∨u=t := by
    intro u hu
    obtain ⟨j,rfl⟩ := (finitePolygonSideEquiv Q hfinite).surjective u
    rcases (finitePolygonVertex_side_iff Q hfinite i j).mp hu with hj | hj
    · exact Or.inl (congrArg (finitePolygonSideEquiv Q hfinite) hj)
    · exact Or.inr (congrArg (finitePolygonSideEquiv Q hfinite) hj)
  have hR : S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine := by
    rw [finitePolygonPrevRay_support]
    exact finiteDiscPoincarePairing_element Q hfinite _
  have hU : S.element t=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry U.supportLine := by
    rw [finitePolygonNextRay_support]
    exact finiteDiscPoincarePairing_element Q hfinite _
  have hs : s.val=P.carrier∩R.supportLine.carrier := by
    rw [finitePolygonPrevRay_support]
    exact finitePolygonSide_eq_carrier_inter_line Q hQ ha hfinite _
  have ht : t.val=P.carrier∩U.supportLine.carrier := by
    rw [finitePolygonNextRay_support]
    exact finitePolygonSide_eq_carrier_inter_line Q hQ ha hfinite _
  have hθ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R U=Real.pi/(n:ℝ) :=
    (finitePolygon_vertex_angle Q hQ hfinite i (ha i).ne).trans hangle
  exact ⟨S.native_integral_reflection_vertex_fiber_finite
      (finiteDiscPoincarePairing_reflection_sides Q hfinite) x s t hxs hxt hAll R U hR hU n hn hθ,
    S.native_integral_reflection_vertex_local_radius
      (finiteDiscPoincarePairing_reflection_sides Q hfinite)
      (finiteDiscPoincarePolygon_locallyFiniteSides Q hfinite) (finiteDiscPoincarePolygon_closedSides Q hfinite)
      x s t R U hAll hR hU hs ht (finitePolygon_vertex_rays_proper Q hfinite i (ha i).ne)
      (finitePolygon_vertex_closed_angle_germ Q hQ hfinite i (ha i).ne) n hn hθ⟩

end LowDimensionalTopology.Geometry.Polygon
