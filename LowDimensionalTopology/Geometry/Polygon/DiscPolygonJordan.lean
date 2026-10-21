/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Support.SupportedDiscPolygons
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.Moise.PolygonalJordan
/-! # Genuine Jordan regions of actual native geodesic polygons

The actual cyclic native edges are transported through the ambient Klein
homeomorphism to honest Euclidean polygonal circles. The licensed LeanPool
polygonal Jordan theorem then supplies the actual two complementary regions.
Their source-defined inside/outside components, complete boundary frontiers,
compactified closure and connectedness are proved without convexity or extra
separation hypotheses. General corner-germ classification and polygon area remain
separate unfinished results.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Actual compactified native points in the genuine Euclidean plane used by the polygonal Jordan theorem. -/
def discPolygonKleinPlane (p : 𝕔𝔻) : LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)

theorem discPolygonKleinPlane_injective : Function.Injective discPolygonKleinPlane :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm.injective.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective

/-- Each genuine native geodesic edge becomes its actual straight segment in the Euclidean plane. -/
theorem discPolygonKleinPlane_image_edge {n : ℕ} (v : Fin n → 𝕔𝔻) (i : Fin n) :
    discPolygonKleinPlane '' discPolygonEdge v i =
      segment ℝ (discPolygonKleinPlane (v i)) (discPolygonKleinPlane (v (finRotate n i))) := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm
  calc
    _ = e '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' discPolygonEdge v i) := by rw [Set.image_image]; rfl
    _ = e '' segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v (finRotate n i))) := by
      rw [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    _ = _ := image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _


/-- The left endpoint lies on its genuine compactified geodesic segment. -/
theorem closedModelDiscHSegment_left_mem (p q : 𝕔𝔻) : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  exact left_mem_segment ℝ _ _

/-- The right endpoint lies on its genuine compactified geodesic segment. -/
theorem closedModelDiscHSegment_right_mem (p q : 𝕔𝔻) : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  exact right_mem_segment ℝ _ _

/-- Consecutive native edges meet exactly in their common vertex. -/
theorem DiscPolygon.edge_inter_next {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    discPolygonEdge P.vertices i ∩ discPolygonEdge P.vertices (finRotate n i) =
      {P.vertices (finRotate n i)} := by
  apply subset_antisymm
  · intro p hp
    have h := P.simple_edges i (finRotate n i) (P.next_ne_self i).symm hp
    rcases h.1 with hi | hi
    · rcases h.2 with hj | hj
      · exact ((P.next_ne_self i) (P.vertices_injective (hi.symm.trans hj)).symm).elim
      · exact ((polygonSupport_next_next_ne_self P.three_le i) (P.vertices_injective (hi.symm.trans hj)).symm).elim
    · exact hi
  · rintro p rfl
    constructor
    · exact closedModelDiscHSegment_right_mem _ _
    · exact closedModelDiscHSegment_left_mem _ _

/-- Nonadjacent actual native edges are disjoint. -/
theorem DiscPolygon.edge_inter_eq_empty_of_nonadjacent {n : ℕ} (P : DiscPolygon n)
    (i j : Fin n) (hij : i ≠ j) (hiprev : i ≠ finRotate n j) (hjinext : j ≠ finRotate n i) :
    discPolygonEdge P.vertices i ∩ discPolygonEdge P.vertices j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := P.simple_edges i j hij hp
  rcases h.1 with hi | hi <;> rcases h.2 with hj | hj
  · exact hij (P.vertices_injective (hi.symm.trans hj))
  · exact hiprev (P.vertices_injective (hi.symm.trans hj))
  · exact hjinext (P.vertices_injective (hj.symm.trans hi))
  · exact hij ((finRotate n).injective (P.vertices_injective (hi.symm.trans hj)))

/-- The actual cyclic index equivalence; its nonzero modulus follows from the genuine polygon. -/
def DiscPolygon.jordanIndexEquiv {n : ℕ} (P : DiscPolygon n) : Fin n ≃ ZMod n := by
  let polygonJordanIndexNonzero : NeZero n := ⟨by have := P.three_le; omega⟩
  exact (ZMod.finEquiv n).toEquiv

theorem DiscPolygon.jordanIndexEquiv_add_one {n : ℕ} (P : DiscPolygon n) (j : ZMod n) :
    P.jordanIndexEquiv.symm (j+1) = finRotate n (P.jordanIndexEquiv.symm j) := by
  let polygonJordanIndexNonzero : NeZero n := ⟨by have := P.three_le; omega⟩
  change (ZMod.finEquiv n).symm (j+1) = finRotate n ((ZMod.finEquiv n).symm j)
  simp only [map_add,map_one,finRotate_apply]

theorem DiscPolygon.jordanIndexEquiv_add_two {n : ℕ} (P : DiscPolygon n) (j : ZMod n) :
    P.jordanIndexEquiv.symm (j+2) = finRotate n (finRotate n (P.jordanIndexEquiv.symm j)) := by
  rw [show j+2 = (j+1)+1 by ring,P.jordanIndexEquiv_add_one,P.jordanIndexEquiv_add_one]

/-- Every actual Jordan geodesic polygon is an honest straight-edged polygonal circle in actual Klein coordinates. -/
def DiscPolygon.toPolygonalCircle {n : ℕ} (P : DiscPolygon n) :
    LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle where
  n := n
  three_le := P.three_le
  vertex j := discPolygonKleinPlane (P.vertices (P.jordanIndexEquiv.symm j))
  adjacent_ne := by
    intro j he
    rw [P.jordanIndexEquiv_add_one j] at he
    exact P.next_ne_self _ (P.vertices_injective (discPolygonKleinPlane_injective he)).symm
  consecutive_inter := by
    intro j
    rw [P.jordanIndexEquiv_add_one,P.jordanIndexEquiv_add_two,
      ← discPolygonKleinPlane_image_edge,← discPolygonKleinPlane_image_edge,
      ← Set.image_inter discPolygonKleinPlane_injective,P.edge_inter_next,Set.image_singleton]
  nonadjacent_disjoint := by
    intro j k hjk hjprev hkprev
    rw [P.jordanIndexEquiv_add_one,P.jordanIndexEquiv_add_one,
      ← discPolygonKleinPlane_image_edge,← discPolygonKleinPlane_image_edge,
      ← Set.image_inter discPolygonKleinPlane_injective]
    rw [P.edge_inter_eq_empty_of_nonadjacent]
    · exact Set.image_empty _
    · exact fun he => hjk (P.jordanIndexEquiv.symm.injective he)
    · intro he
      rw [← P.jordanIndexEquiv_add_one k] at he
      exact hjprev (P.jordanIndexEquiv.symm.injective he)
    · intro he
      rw [← P.jordanIndexEquiv_add_one j] at he
      exact hkprev (P.jordanIndexEquiv.symm.injective he)


/-- The polygonal-circle carrier is exactly the image of the entire actual native boundary. -/
theorem DiscPolygon.toPolygonalCircle_carrier {n : ℕ} (P : DiscPolygon n) :
    P.toPolygonalCircle.carrier = discPolygonKleinPlane '' P.boundary := by
  change (⋃ j : ZMod n,segment ℝ (discPolygonKleinPlane (P.vertices (P.jordanIndexEquiv.symm j)))
    (discPolygonKleinPlane (P.vertices (P.jordanIndexEquiv.symm (j+1))))) = _
  ext w
  constructor
  · intro hw
    obtain ⟨j,hj⟩ := mem_iUnion.mp hw
    change w ∈ segment ℝ (discPolygonKleinPlane (P.vertices (P.jordanIndexEquiv.symm j)))
      (discPolygonKleinPlane (P.vertices (P.jordanIndexEquiv.symm (j+1)))) at hj
    rw [P.jordanIndexEquiv_add_one,← discPolygonKleinPlane_image_edge] at hj
    obtain ⟨p,hp,rfl⟩ := hj
    exact ⟨p,mem_iUnion.mpr ⟨P.jordanIndexEquiv.symm j,hp⟩,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    apply mem_iUnion.mpr
    refine ⟨P.jordanIndexEquiv i,?_⟩
    rw [P.jordanIndexEquiv_add_one,Equiv.symm_apply_apply,← discPolygonKleinPlane_image_edge]
    exact mem_image_of_mem _ hi

/-- A genuine ambient-plane homeomorphism taking native geodesic polygon edges to straight edges. -/
def discPolygonKleinPlaneHomeomorph : ℂ ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.trans
    LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm.toHomeomorph

theorem discPolygonKleinPlaneHomeomorph_closed (p : 𝕔𝔻) :
    discPolygonKleinPlaneHomeomorph (p : ℂ) = discPolygonKleinPlane p := by
  change LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph (p : ℂ)) = _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed]
  rfl

theorem DiscPolygon.kleinPlaneHomeomorph_image_boundary {n : ℕ} (P : DiscPolygon n) :
    discPolygonKleinPlaneHomeomorph '' P.complexBoundary = P.toPolygonalCircle.carrier := by
  rw [P.toPolygonalCircle_carrier]
  change discPolygonKleinPlaneHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) '' P.boundary) = _
  rw [Set.image_image]
  simp only [discPolygonKleinPlaneHomeomorph_closed]

/-- Every actual native polygon has genuine open inside/outside regions with all separation conclusions. -/
theorem DiscPolygon.exists_jordan_regions {n : ℕ} (P : DiscPolygon n) :
    ∃ I O : Set ℂ,IsOpen I ∧ IsOpen O ∧ Disjoint I O ∧ I ∪ O = P.complexBoundaryᶜ ∧
      IsConnected I ∧ IsConnected O ∧ Bornology.IsBounded I ∧ ¬ Bornology.IsBounded O ∧
      frontier I = P.complexBoundary ∧ frontier O = P.complexBoundary := by
  obtain ⟨I,O,hI,hO,hd,hu,hIc,hOc,hIb,_,hIf,hOf⟩ := P.toPolygonalCircle.polygonal_jordan
  let h := discPolygonKleinPlaneHomeomorph
  have hb : h.symm '' P.toPolygonalCircle.carrier = P.complexBoundary := by
    rw [← P.kleinPlaneHomeomorph_image_boundary]
    simp only [Set.image_image]
    change (fun x => h.symm (h x)) '' P.complexBoundary = _
    simp only [h.symm_apply_apply,Set.image_id']
  have hdis : Disjoint (h.symm '' I) (h.symm '' O) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have he : x = y := h.symm.injective (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp hd hx (he ▸ hy)
  have hunion : h.symm '' I ∪ h.symm '' O = P.complexBoundaryᶜ := by
    rw [← Set.image_union,hu,h.symm.image_compl,hb]
  have hbound : Bornology.IsBounded (h.symm '' I) := by
    have hk : IsCompact (closure (h.symm '' I)) := by
      rw [← h.symm.image_closure]
      exact hIb.isCompact_closure.image h.symm.continuous
    exact hk.isBounded.subset subset_closure
  refine ⟨h.symm '' I,h.symm '' O,h.symm.isOpenMap I hI,h.symm.isOpenMap O hO,hdis,hunion,
    hIc.image h.symm h.symm.continuous.continuousOn,hOc.image h.symm h.symm.continuous.continuousOn,hbound,?_,?_,?_⟩
  · intro hbad
    have huniv : (h.symm '' I ∪ h.symm '' O) ∪ P.complexBoundary = univ := by
      rw [hunion,compl_union_self]
    apply NormedSpace.unbounded_univ ℝ ℂ
    rw [← huniv]
    exact (hbound.union hbad).union P.complexBoundary_isCompact.isBounded
  · rw [← h.symm.image_frontier,hIf,hb]
  · rw [← h.symm.image_frontier,hOf,hb]

/-- Any genuine Jordan separation identifies the source's actual exterior component. -/
theorem DiscPolygon.outside_eq_of_jordan_regions {n : ℕ} (P : DiscPolygon n) {I O : Set ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : I ∪ O = P.complexBoundaryᶜ)
    (hOc : IsConnected O) (hOb : ¬ Bornology.IsBounded O) : P.complexOutside = O := by
  have hOsub : O ⊆ P.complexBoundaryᶜ := by rw [← hu]; exact subset_union_right
  have hOutsub : P.complexOutside ⊆ I ∪ O := by rw [hu]; exact connectedComponentIn_subset _ _
  obtain ⟨w,hwO,hwNotInside⟩ : ∃ w ∈ O,w ∉ P.complexInterior := by
    by_contra hn
    push Not at hn
    exact hOb (P.complexInterior_isBounded.subset hn)
  have hwOut : w ∈ P.complexOutside := by
    by_contra hn
    exact hwNotInside ⟨hOsub hwO,hn⟩
  apply subset_antisymm
  · exact isPreconnected_connectedComponentIn.subset_right_of_subset_union hI hO hd hOutsub ⟨w,hwOut,hwO⟩
  · have hsub := hOc.isPreconnected.subset_connectedComponentIn hwO hOsub
    have he : connectedComponentIn P.complexBoundaryᶜ w = P.complexOutside := (connectedComponentIn_eq hwOut).symm
    rwa [he] at hsub

/-- The bounded source inside is exactly the bounded region of a genuine Jordan separation. -/
theorem DiscPolygon.interior_eq_of_jordan_regions {n : ℕ} (P : DiscPolygon n) {I O : Set ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : I ∪ O = P.complexBoundaryᶜ)
    (hOc : IsConnected O) (hOb : ¬ Bornology.IsBounded O) : P.complexInterior = I := by
  have he := P.outside_eq_of_jordan_regions hI hO hd hu hOc hOb
  apply subset_antisymm
  · intro z hz
    have hm : z ∈ I ∪ O := hu ▸ hz.1
    exact hm.resolve_right (by simpa only [← he] using hz.2)
  · intro z hz
    exact ⟨hu ▸ Or.inl hz,by rw [he]; exact Set.disjoint_left.mp hd hz⟩

/-- The actual bounded inside of every genuine native polygon is nonempty and connected. -/
theorem DiscPolygon.complexInterior_isConnected {n : ℕ} (P : DiscPolygon n) : IsConnected P.complexInterior := by
  obtain ⟨I,O,hI,hO,hd,hu,hIc,hOc,_,hOb,_,_⟩ := P.exists_jordan_regions
  rw [P.interior_eq_of_jordan_regions hI hO hd hu hOc hOb]
  exact hIc

/-- The actual unbounded exterior of every genuine native polygon is connected. -/
theorem DiscPolygon.complexOutside_isConnected {n : ℕ} (P : DiscPolygon n) : IsConnected P.complexOutside := by
  obtain ⟨I,O,hI,hO,hd,hu,_,hOc,_,hOb,_,_⟩ := P.exists_jordan_regions
  rw [P.outside_eq_of_jordan_regions hI hO hd hu hOc hOb]
  exact hOc

/-- The entire actual cyclic boundary is precisely the frontier of the actual inside. -/
theorem DiscPolygon.frontier_complexInterior {n : ℕ} (P : DiscPolygon n) :
    frontier P.complexInterior = P.complexBoundary := by
  obtain ⟨I,O,hI,hO,hd,hu,_,hOc,_,hOb,hIf,_⟩ := P.exists_jordan_regions
  rw [P.interior_eq_of_jordan_regions hI hO hd hu hOc hOb]
  exact hIf

/-- The entire actual cyclic boundary is also precisely the frontier of the unbounded exterior. -/
theorem DiscPolygon.frontier_complexOutside {n : ℕ} (P : DiscPolygon n) :
    frontier P.complexOutside = P.complexBoundary := by
  obtain ⟨I,O,hI,hO,hd,hu,_,hOc,_,hOb,_,hOf⟩ := P.exists_jordan_regions
  rw [P.outside_eq_of_jordan_regions hI hO hd hu hOc hOb]
  exact hOf


/-- The genuine native inside of any actual polygon is connected and nonempty. -/
theorem DiscPolygon.interior_isConnected {n : ℕ} (P : DiscPolygon n) : IsConnected P.interior := by
  have hne : P.interior.Nonempty := by
    have h := P.complexInterior_isConnected.nonempty
    rw [← P.interior_complex_image,Set.image_nonempty] at h
    exact h
  refine ⟨hne,Complex.UnitDisc.isEmbedding_coe.isInducing.isPreconnected_image.mp ?_⟩
  rw [P.interior_complex_image]
  exact P.complexInterior_isConnected.isPreconnected

/-- The full cyclic boundary and the genuine open inside form precisely the actual ambient closure. -/
theorem DiscPolygon.closure_complexInterior {n : ℕ} (P : DiscPolygon n) :
    closure P.complexInterior = P.complexInterior ∪ P.complexBoundary := by
  rw [closure_eq_self_union_frontier,P.frontier_complexInterior]

/-- The actual compactified polygon, including every finite and ideal boundary point. -/
def DiscPolygon.closedCarrier {n : ℕ} (P : DiscPolygon n) : Set 𝕔𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure P.interior

/-- The compactified closure really has exactly the ambient polygon closure as its complex image. -/
theorem DiscPolygon.closedCarrier_complex_image {n : ℕ} (P : DiscPolygon n) :
    ((↑) : 𝕔𝔻 → ℂ) '' P.closedCarrier = closure P.complexInterior := by
  let polygonJordanClosedDiscCompact : CompactSpace 𝕔𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscCompactSpace
  have he : Topology.IsClosedEmbedding ((↑) : 𝕔𝔻 → ℂ) :=
    Complex.UnitClosedDisc.continuous_coe.isClosedEmbedding Complex.UnitClosedDisc.isEmbedding_coe.injective
  rw [DiscPolygon.closedCarrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,←
    he.closure_image_eq,image_image]
  change closure (((↑) : 𝔻 → ℂ) '' P.interior) = _
  rw [P.interior_complex_image]

/-- The actual compactified polygon is closed. -/
theorem DiscPolygon.closedCarrier_isClosed {n : ℕ} (P : DiscPolygon n) : IsClosed P.closedCarrier :=
  isClosed_closure

/-- The actual compactified polygon is preconnected without assuming convexity. -/
theorem DiscPolygon.closedCarrier_isPreconnected {n : ℕ} (P : DiscPolygon n) : IsPreconnected P.closedCarrier := by
  apply Complex.UnitClosedDisc.isEmbedding_coe.isInducing.isPreconnected_image.mp
  rw [P.closedCarrier_complex_image]
  exact P.complexInterior_isConnected.isPreconnected.closure

/-- Every actual cyclic finite or ideal boundary point belongs to the true compactified polygon closure. -/
theorem DiscPolygon.boundary_subset_closedCarrier {n : ℕ} (P : DiscPolygon n) : P.boundary ⊆ P.closedCarrier := by
  intro p hp
  apply Complex.UnitClosedDisc.isEmbedding_coe.injective.mem_set_image.mp
  rw [P.closedCarrier_complex_image]
  have hm : (p : ℂ) ∈ P.complexBoundary := mem_image_of_mem _ hp
  rw [← P.frontier_complexInterior] at hm
  exact frontier_subset_closure hm

/-- The actual compactified polygon is compact, including possible ideal vertices. -/
theorem DiscPolygon.closedCarrier_isCompact {n : ℕ} (P : DiscPolygon n) : IsCompact P.closedCarrier := by
  apply Complex.UnitClosedDisc.isEmbedding_coe.isCompact_iff.mpr
  rw [P.closedCarrier_complex_image]
  exact P.complexInterior_isBounded.isCompact_closure


/-- The actual unbounded exterior is exactly the complement of the actual closed polygon. -/
theorem DiscPolygon.complexOutside_eq_compl_closure_inside {n : ℕ} (P : DiscPolygon n) :
    P.complexOutside = (closure P.complexInterior)ᶜ := by
  rw [P.closure_complexInterior]
  ext z
  constructor
  · intro hz hbad
    rcases hbad with hi | hb
    · exact hi.2 hz
    · exact connectedComponentIn_subset P.complexBoundaryᶜ (2 : ℂ) hz hb
  · intro hz
    by_contra hout
    apply hz
    exact Or.inl ⟨fun hb => hz (Or.inr hb),hout⟩

/-- The unbounded exterior closure consists of its true region and the whole cyclic boundary. -/
theorem DiscPolygon.closure_complexOutside {n : ℕ} (P : DiscPolygon n) :
    closure P.complexOutside = P.complexOutside ∪ P.complexBoundary := by
  rw [closure_eq_self_union_frontier,P.frontier_complexOutside]

/-- The actual bounded inside is exactly the complement of the closed exterior. -/
theorem DiscPolygon.complexInterior_eq_compl_closure_outside {n : ℕ} (P : DiscPolygon n) :
    P.complexInterior = (closure P.complexOutside)ᶜ := by
  rw [P.closure_complexOutside]
  ext z
  change (z ∈ P.complexBoundaryᶜ ∧ z ∉ P.complexOutside) ↔ _
  simp only [mem_compl_iff,mem_union,not_or]
  exact and_comm

/-- No extra slits or missing boundary neighborhoods occur in the actual Jordan inside. -/
theorem DiscPolygon.interior_closure_complexInterior {n : ℕ} (P : DiscPolygon n) :
    _root_.interior (closure P.complexInterior) = P.complexInterior := by
  have he : closure P.complexInterior = P.complexOutsideᶜ := by
    rw [P.complexOutside_eq_compl_closure_inside,compl_compl]
  rw [he,interior_compl,← P.complexInterior_eq_compl_closure_outside]

/-- The genuine exterior has the same regular-open property. -/
theorem DiscPolygon.interior_closure_complexOutside {n : ℕ} (P : DiscPolygon n) :
    _root_.interior (closure P.complexOutside) = P.complexOutside := by
  have he : closure P.complexOutside = P.complexInteriorᶜ := by
    rw [P.complexInterior_eq_compl_closure_outside,compl_compl]
  rw [he,interior_compl,← P.complexOutside_eq_compl_closure_inside]

end
end LowDimensionalTopology.Geometry.Polygon
