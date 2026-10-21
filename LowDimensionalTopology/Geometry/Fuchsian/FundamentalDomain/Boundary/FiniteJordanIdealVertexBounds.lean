module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.DiscPolygonConjugation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.IdealPolygonVertexGeometry
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonCornerRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.UnitDiscCrossing
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.ProperSectorAngularMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.IdealVertexDistance
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ZeroStabilizerRotations
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.EllipticSidePairing
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanCornerSectors

/-!
# Ideal joining-line bounds for finite Jordan polygons

The argument separates boundary accessibility, normalization of the angle at the
origin, least stabilizer rotations, and alternation on the boundary circle.
These geometric ingredients bound the distance from an elliptic point to the
line joining two ideal boundary points of the finite Jordan domain.

The final numerical estimate and lens exclusion require stabilizer order at least
three. The distinct order-two case is treated by an explicit counterexample.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology Metric Schoenflies
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The genuine native region in the real Klein plane used by the crosscut API. -/
def kleinPlaneTrace (S : Set Complex.UnitDisc) : Set Plane :=
  Complex.orthonormalBasisOneI.repr '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S)

theorem kleinPlaneTrace_isOpen {S : Set Complex.UnitDisc} (hS : IsOpen S) :
    IsOpen (kleinPlaneTrace S) :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenMap _
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap S hS)

theorem kleinPlaneTrace_isPreconnected {S : Set Complex.UnitDisc} (hS : IsPreconnected S) :
    IsPreconnected (kleinPlaneTrace S) :=
  (hS.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_kleinCoordinate.continuous.continuousOn).image
    Complex.orthonormalBasisOneI.repr Complex.orthonormalBasisOneI.repr.continuous.continuousOn

theorem kleinPlaneTrace_subset_ball (S : Set Complex.UnitDisc) :
    kleinPlaneTrace S ⊆ ball (0 : Plane) 1 := by
  rintro z ⟨u,⟨w,_hw,rfl⟩,rfl⟩
  rw [mem_ball_zero_iff,Complex.orthonormalBasisOneI.repr.norm_map]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein w).norm_lt_one

/-- Actual compactified closure points remain actual closure points of the
concrete real trace, with no accessibility assumption. -/
theorem closedCarrier_mem_closure_kleinPlaneTrace {S : Set Complex.UnitDisc}
    {p : Complex.UnitClosedDisc} (hp : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S) :
    Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) ∈ closure (kleinPlaneTrace S) := by
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) := by
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S = closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.closure_image_eq,image_image]
      rfl
    rw [←he]
    exact mem_image_of_mem _ hp
  exact image_closure_subset_closure_image Complex.orthonormalBasisOneI.repr.continuous
    (mem_image_of_mem _ hK)

/-- A closed-model native isometry has its genuine finite homeomorphism. -/
def finiteIsometryHomeomorph (e :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry) : Complex.UnitDisc ≃ₜ Complex.UnitDisc where
  toEquiv := e.finiteEquiv
  continuous_toFun := by
    let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    have h : Isometry e.finiteMap := Isometry.of_dist_eq (fun z w => by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance]
      exact e.distance_eq z w)
    exact h.continuous
  continuous_invFun := by
    let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    have h : Isometry e.symm.finiteMap := Isometry.of_dist_eq (fun z w => by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance]
      exact e.symm.distance_eq z w)
    exact h.continuous

/-- A locally convex closure of a regular open region provides an actual straight
access segment; no convexity of the entire region is required. -/
theorem exists_straight_access_of_local_convex_closure {A V : Set ℂ} {p : ℂ}
    (hA : IsOpen A) (hreg : interior (closure A) = A) (hp : p ∈ closure A)
    (hV : IsOpen V) (hpV : p ∈ V) (hc : Convex ℝ (closure A ∩ V)) :
    ∃ q ∈ A, openSegment ℝ p q ⊆ A := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hV p hpV
  let C := closure A ∩ ball p r
  have hC : Convex ℝ C := by
    have he : C = (closure A ∩ V) ∩ ball p r := by
      ext z
      simp only [C,mem_inter_iff]
      exact ⟨fun hz => ⟨⟨hz.1,hball hz.2⟩,hz.2⟩,fun hz => ⟨hz.1.1,hz.2⟩⟩
    rw [he]
    exact hc.inter (convex_ball p r)
  obtain ⟨q,hqball,hqA⟩ := mem_closure_iff_nhds.mp hp _
    (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hqi : q ∈ interior C :=
    (hA.inter isOpen_ball).subset_interior_iff.mpr
      (inter_subset_inter_left _ subset_closure) ⟨hqA,hqball⟩
  have hpC : p ∈ closure C := subset_closure ⟨hp,mem_ball_self hr⟩
  refine ⟨q,hqA,?_⟩
  have hseg := hC.openSegment_interior_closure_subset_interior hqi hpC
  rw [openSegment_symm] at hseg
  exact hseg.trans (by rw [←hreg];exact interior_mono inter_subset_left)

/-- Actual native ideal vertices of arbitrary finite Jordan geodesic polygons
have straight access from the actual Klein inside. -/
theorem ideal_vertex_straight_access {n : ℕ} (P : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (i : Fin
  n)
    (hi : ‖(P.vertices i : ℂ)‖ = 1) :
    ∃ q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior,
      openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)) q ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior := by
  obtain ⟨U,hU,hpU,hconv⟩ := P.closedCarrier_locallyConvex_at_ideal_vertex i hi
  obtain ⟨V,hV,heV⟩ :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.isInducing.isOpen_iff.mp hU
  have hconvV : Convex ℝ (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) ∩ V) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex,←heV,image_inter_preimage,
      P.closedKlein_image_closedCarrier] at hconv
    exact hconv
  have hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) := by
    rw [←P.closedKlein_image_closedCarrier]
    exact mem_image_of_mem _ (P.boundary_subset_closedCarrier
      (mem_iUnion.mpr ⟨i,_root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _⟩))
  have hreg : interior (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior := by
    rw [P.klein_image_interior,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_closure,
      ←_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_interior,P.interior_closure_complexInterior]
  exact exists_straight_access_of_local_convex_closure P.klein_jordan_regions.1 hreg hp
    hV (by rwa [←heV] at hpU) hconvV

/-- The actual ideal vertex is polygonally accessible in the real plane used by
the existing Jordan crosscut theorem. -/
theorem ideal_vertex_polyAccessible {n : ℕ} (P : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (i : Fin
  n)
    (hi : ‖(P.vertices i : ℂ)‖ = 1) :
    PolyAccessible (Complex.orthonormalBasisOneI.repr ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior))
      (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i))) := by
  obtain ⟨q,hq,hseg⟩ := ideal_vertex_straight_access P i hi
  apply PolyAccessible.of_openSegment (mem_image_of_mem _ hq)
  have he : Complex.orthonormalBasisOneI.repr ''
      openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)) q =
      openSegment ℝ (Complex.orthonormalBasisOneI.repr
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)))
        (Complex.orthonormalBasisOneI.repr q) :=
    image_openSegment ℝ Complex.orthonormalBasisOneI.repr.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  rw [←he]
  exact image_mono hseg

/-- Every ideal point of the genuine compactified finite polygon is one of its
original finitely many vertices. -/
theorem ideal_closedCarrier_exists_vertex {n : ℕ} (P : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (p : Complex.UnitClosedDisc) (hp : p ∈ P.closedCarrier) (hpn : ‖(p : ℂ)‖ = 1) :
    ∃ i : Fin n, P.vertices i = p := by
  have hpcl := mem_image_of_mem ((↑) : Complex.UnitClosedDisc → ℂ) hp
  rw [P.closedCarrier_complex_image,P.closure_complexInterior] at hpcl
  have hpB : p ∈ P.boundary := by
    rcases hpcl with hpI | hpB
    · have hh := P.complexInterior_subset_disc hpI
      simp only [mem_ball,dist_zero_right,hpn,lt_self_iff_false] at hh
    · obtain ⟨q,hq,he⟩ := hpB
      exact Complex.UnitClosedDisc.coe_injective he ▸ hq
  obtain ⟨i,hi⟩ := mem_iUnion.mp hpB
  by_cases hl : p = P.vertices i
  · exact ⟨i,hl.symm⟩
  by_cases hr : p = P.vertices (finRotate n i)
  · exact ⟨finRotate n i,hr.symm⟩
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ openSegment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))) := by
    apply mem_openSegment_of_ne_left_right
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Ne.symm
        hl)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Ne.symm hr))
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact mem_image_of_mem _ hi
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i) ∈ closedBall (0 :
    ℂ) 1 :=
    mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein _).norm_le_one
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n
    i)) ∈ closedBall (0 : ℂ) 1 :=
    mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein _).norm_le_one
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    i) ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (P.vertices_injective.ne
      (P.next_ne_self i).symm)
  have hh := (strictConvex_closedBall ℝ (0 : ℂ) 1).openSegment_subset ha hb hne hm
  rw [interior_closedBall (0 : ℂ) one_ne_zero] at hh
  have hpk := (_root_.LowDimensionalTopology.Geometry.Polygon.norm_closedKleinCoordinate_eq_one_iff p).mpr hpn
  simp only [mem_ball,dist_zero_right,hpk,lt_self_iff_false] at hh

/-- Accessibility of arbitrary actual ideal closure points is derived from the
finite Jordan polygon itself. -/
theorem ideal_closedCarrier_polyAccessible {n : ℕ} (P : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (p : Complex.UnitClosedDisc) (hp : p ∈ P.closedCarrier) (hpn : ‖(p : ℂ)‖ = 1) :
    PolyAccessible (Complex.orthonormalBasisOneI.repr ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior))
      (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)) := by
  obtain ⟨i,rfl⟩ := ideal_closedCarrier_exists_vertex P p hp hpn
  exact ideal_vertex_polyAccessible P i hpn

/-- A true native isometry carries a straight Klein access segment to a
straight Klein access segment in its actual image region. -/
theorem straight_access_isometry_image {S : Set Complex.UnitDisc}
    (e : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry) (p : Complex.UnitClosedDisc) (hp : ‖(p :
      ℂ)‖ = 1)
    (w : Complex.UnitDisc)
    (hseg : openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) ⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) :
    openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap
      p)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (e.finiteMap w)) ⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (e.finiteMap '' S) := by
  have hpw : p ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w := by
    intro he
    have hh := w.norm_lt_one
    change ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w : Complex.UnitClosedDisc) :
      ℂ)‖ < 1 at hh
    rw [←he,hp] at hh
    exact (lt_irrefl (1 : ℝ)) hh
  have hnew : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap p) ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (e.finiteMap w) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap p) ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (e.finiteMap w))
    rw [←e.finite_commutes]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (e.closedMap.injective.ne
      hpw)
  intro z hz
  have hzleft : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap p) ≠ z := by
    intro he
    rw [←he] at hz
    exact hnew (left_mem_openSegment_iff.mp hz)
  have hzright : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (e.finiteMap w) ≠ z := by
    intro he
    rw [←he] at hz
    exact hnew (right_mem_openSegment_iff.mp hz)
  have hzseg := openSegment_subset_segment ℝ _ _ hz
  have hzrange : z ∈ range _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedKleinCoordinate]
    exact (convex_closedBall (0 : ℂ) 1).segment_subset
      (mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
        _).norm_le_one)
      (mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein
        _).norm_lt_one.le) hzseg
  obtain ⟨x,hx⟩ := hzrange
  have hxseg : x ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (e.closedMap p) (e.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w)) := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,e.finite_commutes]
    exact hx ▸ hzseg
  rw [←e.image_closedModelDiscHSegment] at hxseg
  obtain ⟨t,ht,het⟩ := hxseg
  have htp : p ≠ t := by
    intro he
    subst t
    exact hzleft ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate het).trans hx)
  have htw : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ≠ t := by
    intro he
    subst t
    apply hzright
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (e.finiteMap w)) = z
    rw [←e.finite_commutes]
    exact (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate het).trans hx
  have hKt : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate t ∈ openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) := by
    apply mem_openSegment_of_ne_left_right
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne
        htp) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne htw)
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact mem_image_of_mem _ ht
  obtain ⟨u,hu,hKu⟩ := hseg hKt
  have hut : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel u = t := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective hKu
  refine ⟨e.finiteMap u,⟨u,hu,rfl⟩,?_⟩
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (e.finiteMap u)) = z
  rw [←e.finite_commutes,hut]
  exact (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate het).trans hx

/-- The endpoint-access condition after actual elliptic normalization follows
from the original finite Jordan polygon and the actual native isometry. -/
theorem ideal_closedCarrier_isometry_polyAccessible {n : ℕ} (P :
  _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (e : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry) (p : Complex.UnitClosedDisc)
    (hp : p ∈ P.closedCarrier) (hpn : ‖(p : ℂ)‖ = 1) :
    PolyAccessible
      (Complex.orthonormalBasisOneI.repr '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
        (e.finiteMap '' P.interior)))
      (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap p))) := by
  obtain ⟨i,rfl⟩ := ideal_closedCarrier_exists_vertex P p hp hpn
  obtain ⟨q,hq,hseg⟩ := ideal_vertex_straight_access P i hpn
  obtain ⟨w,hw,rfl⟩ := hq
  have hnew := straight_access_isometry_image e (P.vertices i) hpn w hseg
  apply PolyAccessible.of_openSegment
    (mem_image_of_mem _ (mem_image_of_mem _ (mem_image_of_mem e.finiteMap hw)))
  have he : Complex.orthonormalBasisOneI.repr ''
      openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap (P.vertices
        i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (e.finiteMap w)) =
      openSegment ℝ (Complex.orthonormalBasisOneI.repr
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap (P.vertices i))))
        (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
          (e.finiteMap w))) :=
    image_openSegment ℝ Complex.orthonormalBasisOneI.repr.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  rw [←he]
  exact image_mono hnew

/-- Alternating ideal endpoints force intersection of the actual open traces
when the first trace's two endpoints are accessible. -/
theorem alternating_accessible_ball_traces_intersect {A B C D : Set Plane} {a b c d : Plane}
    (hAo : IsOpen A) (hA : IsPreconnected A) (hAball : A ⊆ ball 0 1)
    (ha : PolyAccessible A a) (hb : PolyAccessible A b)
    (hcut : IsCutPair (sphere (0 : Plane) 1) a b C D)
    (hB : IsPreconnected B) (hBball : B ⊆ ball 0 1)
    (hc : c ∈ closure B) (hd : d ∈ closure B)
    (hcC : c ∈ C) (hcD : c ∉ D) (hdD : d ∈ D) (hdC : d ∉ C) :
    (A ∩ B).Nonempty := by
  obtain ⟨P,hpoly,harc,hP⟩ := exists_simple_arc_of_polyAccessible hAo hA hcut.fst.ne ha hb
  have haS := hcut.fst_subset hcut.fst.left_mem
  have hbS := hcut.fst_subset hcut.fst.right_mem
  have hcross : IsCrosscut (sphere (0 : Plane) 1) P a b :=
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing.unitSphere_isJordanCurve,harc,hpoly,haS,hbS,
      fun z hz => by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing.inside_unitSphere]; exact hAball (hP hz)⟩
  obtain ⟨z,hzB,hzP⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing.crosscut_intersection hcross hcut hB
    (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing.inside_unitSphere];exact hBball) hc hd hcC hcD hdD hdC
  have hzend : z ∉ ({a,b} : Set Plane) := by
    rintro (rfl | rfl)
    · exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp haS).ge)
        (mem_ball_zero_iff.mp (hBball hzB))
    · exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hbS).ge)
        (mem_ball_zero_iff.mp (hBball hzB))
  exact ⟨z,hP ⟨hzP,hzend⟩,hzB⟩

/-- The original finite Jordan polygon supplies every access and connectedness
condition after native normalization; only the actual alternating endpoints of
the second trace enter this intersection conclusion. -/
theorem finite_polygon_isometry_alternating_intersection {n : ℕ} (P :
  _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (e : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry) (p q : Complex.UnitClosedDisc)
    (hp : p ∈ P.closedCarrier) (hq : q ∈ P.closedCarrier)
    (hpn : ‖(p : ℂ)‖ = 1) (hqn : ‖(q : ℂ)‖ = 1)
    {B C D : Set Plane} {c d : Plane}
    (hcut : IsCutPair (sphere (0 : Plane) 1)
      (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (e.closedMap p)))
      (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (e.closedMap q))) C D)
    (hB : IsPreconnected B) (hBball : B ⊆ ball 0 1)
    (hc : c ∈ closure B) (hd : d ∈ closure B)
    (hcC : c ∈ C) (hcD : c ∉ D) (hdD : d ∈ D) (hdC : d ∉ C) :
    (kleinPlaneTrace (e.finiteMap '' P.interior) ∩ B).Nonempty := by
  have ho : IsOpen (e.finiteMap '' P.interior) :=
    (finiteIsometryHomeomorph e).isOpenMap P.interior P.interior_isOpen
  have hconn : IsPreconnected (e.finiteMap '' P.interior) :=
    P.interior_isConnected.isPreconnected.image e.finiteMap
      (finiteIsometryHomeomorph e).continuous.continuousOn
  exact alternating_accessible_ball_traces_intersect (kleinPlaneTrace_isOpen ho)
    (kleinPlaneTrace_isPreconnected hconn) (kleinPlaneTrace_subset_ball _)
    (ideal_closedCarrier_isometry_polyAccessible P e p hp hpn)
    (ideal_closedCarrier_isometry_polyAccessible P e q hq hqn)
    hcut hB hBball hc hd hcC hcD hdD hdC

end LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set InnerProductGeometry
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian.JordanIdealOriginAngle
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- A concrete finite radial point in the genuine native disc. -/
def idealHalfPoint (p : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) : Complex.UnitDisc :=
  Complex.UnitDisc.mk ((1/2 : ℝ) • (p : ℂ)) (by
    rw [norm_smul,Real.norm_eq_abs,hp]
    norm_num)

theorem idealHalfPoint_norm (p : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) :
    ‖(idealHalfPoint p hp : ℂ)‖ = 1/2 := by
  change ‖(1/2 : ℝ) • (p : ℂ)‖ = _
  rw [norm_smul,Real.norm_eq_abs,hp]
  norm_num

theorem idealHalfPoint_ne_zero (p : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) :
    idealHalfPoint p hp ≠ 0 := by
  intro he
  have hn := idealHalfPoint_norm p hp
  rw [he] at hn
  norm_num at hn

theorem idealHalfPoint_mem_closed_segment (p : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (idealHalfPoint p hp) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) p := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  have hzero : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : Complex.UnitDisc)) = 0 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula 0 = 0
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hpK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p = (p :
    ℂ) := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm_one hp
  have hhalf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (idealHalfPoint p hp)) =
      (4/5 : ℝ) • (p : ℂ) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (idealHalfPoint p hp : ℂ) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,idealHalfPoint_norm]
    change ((2 / (1+(1/2 : ℝ)^2) : ℝ) : ℂ) * ((1/2 : ℝ) • (p : ℂ)) = _
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [hzero,hpK,hhalf,segment_eq_image']
  refine ⟨4/5,by norm_num,?_⟩
  simp

/-- The actual angle of a finite-origin triangle with ideal neighbours equals
the ordinary angular separation of its actual ideal endpoints. -/
theorem closedTriangle_alpha_at_origin (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : Complex.UnitDisc))
    (hb : ‖(T.b : ℂ)‖ = 1) (hc : ‖(T.c : ℂ)‖ = 1) :
    T.alpha = angle (T.b : ℂ) (T.c : ℂ) := by
  let R := T.cornerRayABAtA 0 ha
  let S := T.cornerRayACAtA 0 ha
  let hbase := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero
  let RR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt UpperHalfPlane.I := hbase ▸ R.toHalfPlane
  let SS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt UpperHalfPlane.I := hbase ▸ S.toHalfPlane
  have hR : R.toHalfPlane.val = RR.val := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.val_transport hbase
    R.toHalfPlane).symm
  have hS : S.toHalfPlane.val = SS.val := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.val_transport hbase
    S.toHalfPlane).symm
  have hbside : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (idealHalfPoint T.b hb) ∈ T.sideC := by
    change _ ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment T.a T.b
    rw [ha]
    exact idealHalfPoint_mem_closed_segment T.b hb
  have hcside : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (idealHalfPoint T.c hc) ∈ T.sideB := by
    change _ ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment T.c T.a
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm,ha]
    exact idealHalfPoint_mem_closed_segment T.c hc
  have hbR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (idealHalfPoint T.b hb) ∈ RR.val := by
    rw [←hR]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (T.cornerAtA_sideC_finite_subset 0 ha hbside)
  have hcS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (idealHalfPoint T.c hc) ∈ SS.val := by
    rw [←hS]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (T.cornerAtA_sideB_finite_subset 0 ha hcside)
  have hbI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (idealHalfPoint T.b hb) ≠ UpperHalfPlane.I := by
    intro he
    apply idealHalfPoint_ne_zero T.b hb
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective
    rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
  have hcI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (idealHalfPoint T.c hc) ≠ UpperHalfPlane.I := by
    intro he
    apply idealHalfPoint_ne_zero T.c hc
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective
    rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
  rw [T.alpha_of_finite 0 ha,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R.toHalfPlane S.toHalfPlane = _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_congr_base hbase R.toHalfPlane
    S.toHalfPlane RR SS hR hS,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_I_cayley RR SS hbR hbI hcS hcI,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  change angle ((1/2 : ℝ) • (T.b : ℂ)) ((1/2 : ℝ) • (T.c : ℂ)) = _
  rw [angle_smul_left_of_pos _ _ (by norm_num : (0 : ℝ) < 1/2),
    angle_smul_right_of_pos _ _ (by norm_num : (0 : ℝ) < 1/2)]

end LowDimensionalTopology.Geometry.Fuchsian.JordanIdealOriginAngle
/- Released under Apache 2.0 license as described in the file LICENSE. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian.JordanIdealMinimalRotation
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- After fixing the actual disc center, the original finite cyclic subgroup
contains the literal positive rotation through its exact minimal period. -/
theorem normalized_cyclic_positive_rotation {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H) (f : H)
    (hfix : f.val.val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((0 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (n : ℕ) (hn : 0 < n) (horder : orderOf f.val = n) :
    ∃ k : ℤ, f.val ^ k = _root_.LowDimensionalTopology.Geometry.Fuchsian.finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) := by
  let K := Subgroup.zpowers f.val
  let _minimalRotationCyclicFinite : Finite K :=
    (orderOf_pos_iff.mp (horder.symm ▸ hn)).finite_zpowers
  have hKH : K ≤ H := Subgroup.zpowers_le.mpr f.property
  have hp : ∀ g ∈ K, g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    intro g hg
    exact P.image_eq ⟨g,hKH hg⟩
  have h0 : ∀ g ∈ K, g.val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro g hg
    obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact _root_.LowDimensionalTopology.Geometry.Fuchsian.primitive_mobius_zpow_fixed hfix k
  have hK : K = _root_.LowDimensionalTopology.Geometry.Fuchsian.finiteMobiusRotationGroup n := by
    have he := _root_.LowDimensionalTopology.Geometry.Fuchsian.finiteZeroDiscGroup_eq_rotation K hp h0
    simpa only [K,Nat.card_zpowers,horder] using he
  have hmem : _root_.LowDimensionalTopology.Geometry.Fuchsian.finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) ∈ K := by
    rw [hK]
    exact Subgroup.mem_zpowers _
  exact Subgroup.mem_zpowers_iff.mp hmem

/-- The positive rotation obtained from the original cyclic subgroup has its
literal original action on every finite sphere point, including ideal endpoints. -/
theorem normalized_cyclic_positive_rotation_action {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H) (f : H)
    (hfix : f.val.val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((0 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (n : ℕ) (hn : 0 < n) (horder : orderOf f.val = n) :
    ∃ k : ℤ, f.val ^ k ∈ H ∧ orderOf (f.val ^ k) = n ∧
      ∀ z : ℂ, (f.val ^ k).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
        (((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n : Circle) : ℂ) * z : ℂ) := by
  obtain ⟨k,hk⟩ := normalized_cyclic_positive_rotation P f hfix n hn horder
  refine ⟨k,H.zpow_mem f.property k,?_,?_⟩
  · rw [hk]
    exact _root_.LowDimensionalTopology.Geometry.Fuchsian.finiteMobiusRotation_order n hn.ne'
  · intro z
    rw [hk]
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n))).val
      (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
    rfl

end LowDimensionalTopology.Geometry.Fuchsian.JordanIdealMinimalRotation
/- Released under Apache 2.0 license as described in the file LICENSE. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Schoenflies
open scoped Topology
namespace LowDimensionalTopology.Geometry.Fuchsian.JordanIdealCircleAlternation
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- A literal angular point of the round ideal circle in the crossing plane. -/
def circlePoint (t : ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr (Circle.exp t : ℂ)

def circleArc (a b : ℝ) : Set Plane := circlePoint '' Icc a b

theorem circlePoint_continuous : Continuous circlePoint :=
  Complex.orthonormalBasisOneI.repr.continuous.comp
    (continuous_subtype_val.comp Circle.exp.continuous)

theorem circlePoint_period (a : ℝ) : circlePoint (a+2*Real.pi) = circlePoint a :=
  congrArg (fun u : Circle => Complex.orthonormalBasisOneI.repr (u : ℂ))
    (Circle.periodic_exp a)

theorem circlePoint_injOn_period (a : ℝ) :
    Set.InjOn circlePoint (Ico a (a+2*Real.pi)) := by
  intro s hs t ht he
  apply Circle.exp_injOn_Ico (a:=a) (b:=a+2*Real.pi) (by linarith) hs ht
  apply Circle.coe_injective
  exact Complex.orthonormalBasisOneI.repr.injective he

/-- Every genuine closed proper angular interval is an actual Jordan arc. -/
theorem circleArc_isArcBetween (a b : ℝ) (hab : a < b) (hba : b < a+2*Real.pi) :
    IsArcBetween (circleArc a b) (circlePoint a) (circlePoint b) := by
  let f : ℝ → Plane := fun t => circlePoint (a+(b-a)*t)
  have hparam (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      a+(b-a)*t ∈ Icc a b := by
    constructor <;> nlinarith [ht.1,ht.2]
  refine ⟨f,?_,?_,?_,?_,?_⟩
  · exact (circlePoint_continuous.comp
      (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  · intro s hs t ht he
    have hs' := hparam s hs
    have ht' := hparam t ht
    have he' := circlePoint_injOn_period a
      ⟨hs'.1,hs'.2.trans_lt hba⟩ ⟨ht'.1,ht'.2.trans_lt hba⟩ he
    nlinarith
  · ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨a+(b-a)*t,hparam t ht,rfl⟩
    · rintro ⟨s,hs,rfl⟩
      refine ⟨(s-a)/(b-a),?_,?_⟩
      · exact ⟨div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hab).le,
          (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hs.2])⟩
      · change circlePoint (a+(b-a)*((s-a)/(b-a))) = circlePoint s
        congr 1
        field_simp [(sub_pos.mpr hab).ne']
        ring
  · simp only [f,mul_zero,add_zero]
  · simp only [f,mul_one]
    congr 1
    ring

/-- The two literal complementary angular arcs form the actual cut pair of
the entire round circle used by the existing crosscut theorem. -/
theorem circleArc_cutPair (a b : ℝ) (hab : a < b) (hba : b < a+2*Real.pi) :
    IsCutPair (sphere (0:Plane) 1) (circlePoint a) (circlePoint b)
      (circleArc a b) (circleArc b (a+2*Real.pi)) := by
  have hperiod := circlePoint_period a
  have hI : Icc a b ∪ Icc b (a+2*Real.pi) = Icc a (a+2*Real.pi) := by
    ext t
    constructor
    · rintro (ht|ht)
      · exact ⟨ht.1,ht.2.trans hba.le⟩
      · exact ⟨hab.le.trans ht.1,ht.2⟩
    · intro ht
      by_cases htb : t ≤ b
      · exact Or.inl ⟨ht.1,htb⟩
      · exact Or.inr ⟨(le_of_not_ge htb),ht.2⟩
  have hwhole : circlePoint '' Icc a (a+2*Real.pi) = sphere (0:Plane) 1 := by
    ext z
    constructor
    · rintro ⟨t,_ht,rfl⟩
      rw [mem_sphere_zero_iff_norm]
      exact (Complex.orthonormalBasisOneI.repr.norm_map _).trans (Circle.norm_coe _)
    · intro hz
      let u : Circle := ⟨Complex.orthonormalBasisOneI.repr.symm z,
        mem_sphere_zero_iff_norm.mpr (by
          rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
          exact mem_sphere_zero_iff_norm.mp hz)⟩
      have hfull : Circle.exp '' Icc a (a+2*Real.pi) = univ := by
        rw [Circle.periodic_exp.image_Icc (by positivity),Circle.exp_surjective.range_eq]
      obtain ⟨t,ht,he⟩ := hfull.symm ▸ mem_univ u
      refine ⟨t,ht,?_⟩
      change Complex.orthonormalBasisOneI.repr (Circle.exp t : ℂ) = z
      rw [he]
      exact Complex.orthonormalBasisOneI.repr.apply_symm_apply z
  refine ⟨circleArc_isArcBetween a b hab hba,?_,?_,?_⟩
  · have h := (circleArc_isArcBetween b (a+2*Real.pi) hba (by linarith)).reverse
    simpa only [hperiod] using h
  · rw [circleArc,circleArc,←image_union,hI,hwhole]
  · ext z
    constructor
    · rintro ⟨⟨s,hs,rfl⟩,⟨t,ht,he⟩⟩
      by_cases htc : t = a+2*Real.pi
      · rw [htc,hperiod] at he
        have hsa := circlePoint_injOn_period a
          ⟨hs.1,hs.2.trans_lt hba⟩ ⟨le_rfl,by linarith [Real.pi_pos]⟩ he.symm
        exact Or.inl (congrArg circlePoint hsa)
      · have htlt : t < a+2*Real.pi := lt_of_le_of_ne ht.2 htc
        have hst := circlePoint_injOn_period a
          ⟨hs.1,hs.2.trans_lt hba⟩ ⟨hab.le.trans ht.1,htlt⟩ he.symm
        have hsb : s = b := by linarith [hs.2,ht.1]
        exact Or.inr (congrArg circlePoint hsb)
    · rintro (rfl|rfl)
      · exact ⟨⟨a,⟨le_rfl,hab.le⟩,rfl⟩,
          ⟨a+2*Real.pi,⟨hba.le,le_rfl⟩,hperiod⟩⟩
      · exact ⟨⟨b,⟨hab.le,le_rfl⟩,rfl⟩,
          ⟨b,⟨le_rfl,hba.le⟩,rfl⟩⟩

/-- A positive rotation smaller than a genuine short endpoint angle sends
the two endpoints into opposite open arcs of their actual circle cut pair. -/
theorem short_angle_rotation_alternates (a b τ : ℝ)
    (hτ : 0 < τ) (hgap : τ < b-a) (hshort : b-a ≤ Real.pi) :
    IsCutPair (sphere (0:Plane) 1) (circlePoint a) (circlePoint b)
        (circleArc a b) (circleArc b (a+2*Real.pi)) ∧
      circlePoint (a+τ) ∈ circleArc a b ∧
      circlePoint (a+τ) ∉ circleArc b (a+2*Real.pi) ∧
      circlePoint (b+τ) ∈ circleArc b (a+2*Real.pi) ∧
      circlePoint (b+τ) ∉ circleArc a b := by
  have hab : a < b := by linarith
  have hba : b < a+2*Real.pi := by linarith [Real.pi_pos]
  have hbt : b+τ < a+2*Real.pi := by linarith [Real.pi_pos]
  have hcut := circleArc_cutPair a b hab hba
  have hpA : circlePoint (a+τ) ∈ circleArc a b :=
    ⟨a+τ,⟨by linarith,by linarith⟩,rfl⟩
  have hqB : circlePoint (b+τ) ∈ circleArc b (a+2*Real.pi) :=
    ⟨b+τ,⟨by linarith,hbt.le⟩,rfl⟩
  have hnonend (s : ℝ) (hs : s ∈ Ioo a (a+2*Real.pi)) (hsb : s ≠ b) :
      circlePoint s ≠ circlePoint a ∧ circlePoint s ≠ circlePoint b := by
    constructor
    · intro he
      have hsa := circlePoint_injOn_period a ⟨hs.1.le,hs.2⟩
        ⟨le_rfl,by linarith [Real.pi_pos]⟩ he
      exact hs.1.ne' hsa
    · intro he
      exact hsb (circlePoint_injOn_period a ⟨hs.1.le,hs.2⟩ ⟨hab.le,hba⟩ he)
  have hpne := hnonend (a+τ) ⟨by linarith,by linarith⟩ (by linarith)
  have hqne := hnonend (b+τ) ⟨by linarith,hbt⟩ (by linarith)
  refine ⟨hcut,hpA,?_,hqB,?_⟩
  · intro hpB
    have hend : circlePoint (a+τ) ∈ ({circlePoint a,circlePoint b} : Set Plane) := by
      rw [←hcut.inter_eq]
      exact ⟨hpA,hpB⟩
    exact hend.elim hpne.1 hpne.2
  · intro hqA
    have hend : circlePoint (b+τ) ∈ ({circlePoint a,circlePoint b} : Set Plane) := by
      rw [←hcut.inter_eq]
      exact ⟨hqA,hqB⟩
    exact hend.elim hqne.1 hqne.2

/-- The short angular lift measures the genuine Euclidean angle of the two
actual ideal directions, including the antipodal endpoint case. -/
theorem circle_short_lift_angle (a b : ℝ) (hab : a ≤ b) (hshort : b-a ≤ Real.pi) :
    InnerProductGeometry.angle (Circle.exp a : ℂ) (Circle.exp b : ℂ) = b-a := by
  have h := _root_.LowDimensionalTopology.Geometry.Euclidean.circle_exp_endpoint_angle ((a+b)/2) (r:=(b-a)/2)
    (by linarith) (by linarith)
  have ha : (a+b)/2-(b-a)/2 = a := by ring
  have hb : (a+b)/2+(b-a)/2 = b := by ring
  simpa only [ha,hb,show 2*((b-a)/2) = b-a by ring] using h

/-- Any distinct ideal directions have actual increasing lifts along one of
the two short oriented arcs, with exactly their geometric angle as length. -/
theorem circle_short_ordered_lifts (u v : Circle) (hne : u ≠ v) :
    ∃ a b : ℝ, a < b ∧ b-a ≤ Real.pi ∧
      InnerProductGeometry.angle (u : ℂ) (v : ℂ) = b-a ∧
      ((Circle.exp a = u ∧ Circle.exp b = v) ∨
       (Circle.exp a = v ∧ Circle.exp b = u)) := by
  obtain ⟨a,b,hab,hba,ha,hb⟩ := _root_.LowDimensionalTopology.Geometry.Polygon.circle_distinct_ordered_lifts u v hne
  by_cases hshort : b-a ≤ Real.pi
  · refine ⟨a,b,hab,hshort,?_,Or.inl ⟨ha,hb⟩⟩
    rw [←ha,←hb]
    exact circle_short_lift_angle a b hab.le hshort
  · have hcompl : a+2*Real.pi-b ≤ Real.pi := by linarith
    refine ⟨b,a+2*Real.pi,hba,hcompl,?_,Or.inr ⟨hb,?_⟩⟩
    · have h := circle_short_lift_angle b (a+2*Real.pi) hba.le hcompl
      rw [Circle.periodic_exp a,hb,ha,InnerProductGeometry.angle_comm] at h
      exact h
    · rw [Circle.periodic_exp a,ha]

/-- A rotation smaller than the actual short endpoint angle gives the precise
opposite-arc membership data needed by the existing Jordan crossing theorem. -/
theorem geometric_angle_rotation_alternates (u v : Circle) (τ : ℝ)
    (hτ : 0 < τ) (hangle : τ < InnerProductGeometry.angle (u : ℂ) (v : ℂ)) :
    ∃ A B : Set Plane,
      IsCutPair (sphere (0:Plane) 1)
        (Complex.orthonormalBasisOneI.repr (u : ℂ))
        (Complex.orthonormalBasisOneI.repr (v : ℂ)) A B ∧
      ((Complex.orthonormalBasisOneI.repr ((Circle.exp τ*u : Circle) : ℂ) ∈ A ∧
        Complex.orthonormalBasisOneI.repr ((Circle.exp τ*u : Circle) : ℂ) ∉ B ∧
        Complex.orthonormalBasisOneI.repr ((Circle.exp τ*v : Circle) : ℂ) ∈ B ∧
        Complex.orthonormalBasisOneI.repr ((Circle.exp τ*v : Circle) : ℂ) ∉ A) ∨
       (Complex.orthonormalBasisOneI.repr ((Circle.exp τ*v : Circle) : ℂ) ∈ A ∧
        Complex.orthonormalBasisOneI.repr ((Circle.exp τ*v : Circle) : ℂ) ∉ B ∧
        Complex.orthonormalBasisOneI.repr ((Circle.exp τ*u : Circle) : ℂ) ∈ B ∧
        Complex.orthonormalBasisOneI.repr ((Circle.exp τ*u : Circle) : ℂ) ∉ A)) := by
  have hne : u ≠ v := by
    intro he
    rw [he,InnerProductGeometry.angle_self (Circle.coe_ne_zero v)] at hangle
    linarith
  obtain ⟨a,b,hab,hshort,hα,hends⟩ := circle_short_ordered_lifts u v hne
  have hgap : τ < b-a := hα ▸ hangle
  obtain ⟨hcut,hpA,hpB,hqB,hqA⟩ := short_angle_rotation_alternates a b τ hτ hgap hshort
  have hrotate (t : ℝ) : circlePoint (t+τ) =
      Complex.orthonormalBasisOneI.repr ((Circle.exp τ*Circle.exp t : Circle) : ℂ) := by
    simp only [circlePoint,Circle.exp_add,mul_comm]
  rcases hends with ⟨ha,hb⟩|⟨ha,hb⟩
  · refine ⟨circleArc a b,circleArc b (a+2*Real.pi),?_,Or.inl ?_⟩
    · simpa only [circlePoint,ha,hb] using hcut
    · simpa only [hrotate,ha,hb] using And.intro hpA (And.intro hpB (And.intro hqB hqA))
  · have hcut' : IsCutPair (sphere (0:Plane) 1)
        (Complex.orthonormalBasisOneI.repr (u : ℂ))
        (Complex.orthonormalBasisOneI.repr (v : ℂ))
        (circleArc a b) (circleArc b (a+2*Real.pi)) := by
      have hcutUV : IsCutPair (sphere (0:Plane) 1)
          (Complex.orthonormalBasisOneI.repr (v : ℂ))
          (Complex.orthonormalBasisOneI.repr (u : ℂ))
          (circleArc a b) (circleArc b (a+2*Real.pi)) := by
        simpa only [circlePoint,ha,hb] using hcut
      refine ⟨hcutUV.fst.reverse,hcutUV.snd.reverse,hcutUV.union_eq,?_⟩
      simpa only [pair_comm] using hcutUV.inter_eq
    refine ⟨circleArc a b,circleArc b (a+2*Real.pi),hcut',Or.inr ?_⟩
    simpa only [hrotate,ha,hb] using And.intro hpA (And.intro hpB (And.intro hqB hqA))

end LowDimensionalTopology.Geometry.Fuchsian.JordanIdealCircleAlternation
namespace LowDimensionalTopology.Geometry.Fuchsian.JordanIdealVertexBounds
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess
  LowDimensionalTopology.Geometry.Fuchsian.JordanIdealMinimalRotation
  LowDimensionalTopology.Geometry.Fuchsian.JordanIdealCircleAlternation
  LowDimensionalTopology.Geometry.Fuchsian.JordanIdealOriginAngle
open Set Filter Topology Metric Schoenflies InnerProductGeometry
open scoped Complex.UnitDisc OnePoint Pointwise

local instance jordanIdealSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance jordanIdealSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Literal unit rotation in the real crossing plane. -/
def planeRotation (u : Circle) (x : Plane) : Plane :=
  Complex.orthonormalBasisOneI.repr ((u : ℂ) * Complex.orthonormalBasisOneI.repr.symm x)

theorem planeRotation_continuous (u : Circle) : Continuous (planeRotation u) :=
  Complex.orthonormalBasisOneI.repr.continuous.comp
    (continuous_const.mul Complex.orthonormalBasisOneI.repr.symm.continuous)

theorem planeRotation_norm (u : Circle) (x : Plane) : ‖planeRotation u x‖ = ‖x‖ := by
  rw [planeRotation,Complex.orthonormalBasisOneI.repr.norm_map,norm_mul,Circle.norm_coe,
    one_mul,Complex.orthonormalBasisOneI.repr.symm.norm_map]

theorem kleinFormula_circle_mul (u : Circle) (z : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula ((u : ℂ) * z) = (u : ℂ) * _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z := by
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,norm_mul,Circle.norm_coe,one_mul]
  ring

/-- Packing is transported from the original whole-group fundamental domain;
the rotation is an actual element of that same group. -/
theorem native_fundamental_trace_disjoint_rotation {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H) {D : Set P.domain.carrier}
    (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain P D) (g : H) (hg : g ≠ 1)
    (u : Circle) (hgu : g.val = _root_.LowDimensionalTopology.Geometry.Fuchsian.finiteMobiusRotationHom u) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace
      (P.finiteCoordinate '' D))
      (planeRotation u '' _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace (P.finiteCoordinate '' D)) := by
  let F : P.domain.carrier → Plane :=
    fun x => Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      (P.finiteCoordinate x))
  have hFinj : Function.Injective F :=
    Complex.orthonormalBasisOneI.repr.injective.comp
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_kleinCoordinate.injective.comp
        P.finiteCoordinate.injective)
  have hrot (x : P.domain.carrier) : F (g • x) = planeRotation u (F x) := by
    change Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      (P.finiteCoordinate (g • x) : ℂ)) = _
    rw [P.rotation_finite_action g u hgu x,kleinFormula_circle_mul]
    simp only [F,planeRotation,LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hleft : _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace (P.finiteCoordinate '' D) = F '' D := by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace,image_image,image_image]
  have hright : planeRotation u '' _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace (P.finiteCoordinate '' D) =
      F '' ((fun x : P.domain.carrier => g • x) '' D) := by
    rw [hleft,image_image,image_image]
    exact image_congr (fun x _ => (hrot x).symm)
  rw [hright,hleft,Set.disjoint_image_iff hFinj]
  exact (hD.disjoint_image hg).symm

/-- In the actual finite-Jordan class, ideal endpoint accessibility forces the
original order-n rotation bound even when the original polygon is nonconvex. -/
theorem normalized_finite_jordan_ideal_angle_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H) {D : Set P.domain.carrier}
    (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain P D) {m : ℕ} (Q :
      _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (e : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry)
    (hQD : P.finiteCoordinate '' D = e.finiteMap '' Q.interior)
    (f : H) (hf0 : f.val.val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((0 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (n : ℕ) (hn : 3 ≤ n) (horder : orderOf f.val = n)
    (p q : Complex.UnitClosedDisc) (hp : p ∈ Q.closedCarrier) (hq : q ∈ Q.closedCarrier)
    (hpn : ‖(p : ℂ)‖ = 1) (hqn : ‖(q : ℂ)‖ = 1) :
    angle (e.closedMap p : ℂ) (e.closedMap q : ℂ) ≤ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n := by
  by_contra! hwide
  let u : Circle := ⟨(e.closedMap p : ℂ),mem_sphere_zero_iff_norm.mpr ((e.ideal_iff p).mpr hpn)⟩
  let v : Circle := ⟨(e.closedMap q : ℂ),mem_sphere_zero_iff_norm.mpr ((e.ideal_iff q).mpr hqn)⟩
  let ζ := _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n
  obtain ⟨k,hk⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealMinimalRotation.normalized_cyclic_positive_rotation P f hf0 n (by omega) horder
  let g : H := ⟨f.val ^ k,H.zpow_mem f.property k⟩
  have hgn : g ≠ 1 := by
    intro he
    have hval : f.val ^ k = 1 := congrArg Subtype.val he
    have hord := _root_.LowDimensionalTopology.Geometry.Fuchsian.finiteMobiusRotation_order n (by omega)
    rw [←hk,hval,orderOf_one] at hord
    omega
  let A := _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace (e.finiteMap ''
    Q.interior)
  let B := planeRotation ζ '' A
  have hdis : Disjoint A B := by
    change Disjoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace
      (e.finiteMap '' Q.interior))
      (planeRotation ζ '' _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace
        (e.finiteMap '' Q.interior))
    rw [←hQD]
    exact native_fundamental_trace_disjoint_rotation P hD g hgn ζ hk
  have hpclosed : e.closedMap p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (e.finiteMap '' Q.interior) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,←e.closedMap_image_finite,←e.closedMap.image_closure]
    exact mem_image_of_mem e.closedMap hp
  have hqclosed : e.closedMap q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (e.finiteMap '' Q.interior) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,←e.closedMap_image_finite,←e.closedMap.image_closure]
    exact mem_image_of_mem e.closedMap hq
  have hpu : Complex.orthonormalBasisOneI.repr (u : ℂ) ∈ closure A := by
    have hh := _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.closedCarrier_mem_closure_kleinPlaneTrace hpclosed
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap p) = (u : ℂ) :=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm_one ((e.ideal_iff p).mpr hpn)
    rwa [he] at hh
  have hqv : Complex.orthonormalBasisOneI.repr (v : ℂ) ∈ closure A := by
    have hh := _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.closedCarrier_mem_closure_kleinPlaneTrace hqclosed
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap q) = (v : ℂ) :=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm_one ((e.ideal_iff q).mpr hqn)
    rwa [he] at hh
  have hBu : Complex.orthonormalBasisOneI.repr ((ζ*u : Circle) : ℂ) ∈ closure B := by
    change Complex.orthonormalBasisOneI.repr ((ζ*u : Circle) : ℂ) ∈ closure (planeRotation ζ '' A)
    have hh := image_closure_subset_closure_image (planeRotation_continuous ζ)
      (mem_image_of_mem (planeRotation ζ) hpu)
    simpa only [planeRotation,LinearIsometryEquiv.symm_apply_apply,Circle.coe_mul] using hh
  have hBv : Complex.orthonormalBasisOneI.repr ((ζ*v : Circle) : ℂ) ∈ closure B := by
    change Complex.orthonormalBasisOneI.repr ((ζ*v : Circle) : ℂ) ∈ closure (planeRotation ζ '' A)
    have hh := image_closure_subset_closure_image (planeRotation_continuous ζ)
      (mem_image_of_mem (planeRotation ζ) hqv)
    simpa only [planeRotation,LinearIsometryEquiv.symm_apply_apply,Circle.coe_mul] using hh
  have hB : IsPreconnected B := by
    have hh := Q.interior_isConnected.isPreconnected.image e.finiteMap
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.finiteIsometryHomeomorph
        e).continuous.continuousOn
    exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace_isPreconnected
      hh).image _ (planeRotation_continuous ζ).continuousOn
  have hBball : B ⊆ ball (0 : Plane) 1 := by
    rintro z ⟨x,hx,rfl⟩
    rw [mem_ball_zero_iff,planeRotation_norm]
    exact mem_ball_zero_iff.mp (_root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.kleinPlaneTrace_subset_ball _ hx)
  obtain ⟨C,E,hcut,hcases⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealCircleAlternation.geometric_angle_rotation_alternates u v (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n)
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_pos n (by omega)) hwide
  have hpK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap p) = (u : ℂ) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm_one ((e.ideal_iff p).mpr hpn)
  have hqK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap q) = (v : ℂ) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm_one ((e.ideal_iff q).mpr hqn)
  have hcut' : IsCutPair (Metric.sphere (0 : Plane) 1)
      (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (e.closedMap p)))
      (Complex.orthonormalBasisOneI.repr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (e.closedMap q))) C E := by
    rwa [hpK,hqK]
  have hmeet : (A ∩ B).Nonempty := by
    rcases hcases with hs | hs
    · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.finite_polygon_isometry_alternating_intersection Q e p q hp hq hpn hqn hcut'
        hB hBball hBu hBv hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealBoundaryAccess.finite_polygon_isometry_alternating_intersection Q e p q hp hq hpn hqn hcut'
        hB hBball hBv hBu hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  obtain ⟨z,hzA,hzB⟩ := hmeet
  exact Set.disjoint_left.mp hdis hzA hzB

/-- Distinct actual ideal endpoints with short angle below pi determine a
genuine nondegenerate triangle with the physical origin. -/
def idealTriangleAtOrigin (p q : Complex.UnitClosedDisc)
    (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1) (hpq : p ≠ q)
    (hangle : angle (p : ℂ) (q : ℂ) <
      Real.pi) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0
  b := p
  c := q
  noncollinear := by
    rintro ⟨L,hzero,hpL,hqL⟩
    obtain ⟨v,t,hv,hL⟩ := L.closedKlein_affine_equation
    have h0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : Complex.UnitDisc)) = 0 := by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula 0 = 0
      simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
    have hpK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p = (p :
      ℂ) := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm_one hp
    have hqK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q = (q :
      ℂ) := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm_one hq
    have ht : t = 0 := by
      have hh := (hL _).mp hzero
      simpa only [h0,inner_zero_right] using hh.symm
    have hcol : Collinear ℝ ({(p : ℂ),0,(q : ℂ)} : Set ℂ) := by
      apply _root_.LowDimensionalTopology.Geometry.Polygon.polygonComplex_hyperplane_collinear v 0 hv (by simp)
      intro z hz
      rcases hz with rfl | rfl | rfl
      · simpa only [hpK,ht,inner_zero_right] using (hL p).mp hpL
      · rfl
      · simpa only [hqK,ht,inner_zero_right] using (hL q).mp hqL
    rcases EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp hcol with
      hp0 | hq0 | ha0 | hapi
    · have hh := hp
      rw [hp0,norm_zero] at hh
      exact zero_ne_one hh
    · have hh := hq
      rw [hq0,norm_zero] at hh
      exact zero_ne_one hh
    · have he : (p : ℂ) = (q : ℂ) := eq_of_angle_eq_zero_of_norm_eq
        (by simpa only [EuclideanGeometry.angle, vsub_eq_sub,sub_zero] using ha0)
        (hp.trans hq.symm)
      exact hpq (Complex.UnitClosedDisc.coe_injective he)
    · have he : angle (p : ℂ) (q : ℂ) = Real.pi := by
        simpa only [EuclideanGeometry.angle,vsub_eq_sub,sub_zero] using hapi
      exact (ne_of_lt hangle) he

/-- The existing ideal-triangle metric identity applies after actual native
normalization; triangle containment is never assumed here. -/
theorem ideal_joining_distance_of_normalized_angle_bound
    (e : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry) (v : Complex.UnitDisc) (hv : e.finiteMap
      v = 0)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hpL : p ∈ L.closedCarrier) (hqL : q
      ∈ L.closedCarrier)
    (n : ℕ) (hn : 3 ≤ n)
    (hangle : angle (e.closedMap p : ℂ) (e.closedMap q : ℂ) ≤
      _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n) :
    1 / Real.sin (Real.pi / (n : ℝ)) ≤ Real.cosh (L.pointDist v) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hperiod : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n < Real.pi := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod]
    apply (div_lt_iff₀ hn0).mpr
    nlinarith [Real.pi_pos]
  let T0 := idealTriangleAtOrigin (e.closedMap p) (e.closedMap q)
    ((e.ideal_iff p).mpr hp) ((e.ideal_iff q).mpr hq) (e.closedMap.injective.ne hpq)
    (hangle.trans_lt hperiod)
  let T := T0.mapClosedIsometry e.symm
  have ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel v := by
    change e.closedMap.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      0) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel v
    apply e.closedMap.injective
    rw [e.closedMap.apply_symm_apply,e.finite_commutes,hv]
  have hb : T.b = p := e.closedMap.symm_apply_apply p
  have hc : T.c = q := e.closedMap.symm_apply_apply q
  have hTangle : T.alpha ≤ 2 * Real.pi / (n : ℝ) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.mapClosedIsometry_alpha]
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.JordanIdealOriginAngle.closedTriangle_alpha_at_origin T0 rfl
      ((e.ideal_iff p).mpr hp) ((e.ideal_iff q).mpr hq)]
    exact hangle
  have hline : T.sideLineA = L :=
    T.sideLineA.eq_of_two_closed_points L (by rwa [hb,hc])
      T.b_mem_sideLineA T.c_mem_sideLineA (by rwa [hb]) (by rwa [hc])
  have hbound := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedTriangle_cosh_pointDist_ge_csc_order T v ha
    (by rwa [hb]) (by rwa [hc]) n (by omega) hTangle
  rwa [hline] at hbound

/-- The geometric estimate for the original finite Jordan geodesic polygon, with the original Fuchsian action, true elliptic element and genuine ideal closure points. No convexity or triangle containment is imposed. -/
theorem finite_jordan_ideal_joining_line_cosh_pointDist_ge_csc_element_order
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H)
    {D : Set P.domain.carrier} (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain P D)
    {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m) (hQD : P.finiteCoordinate '' D =
      Q.interior)
    (v : P.domain.carrier) (f : H) (hfv : f • v = v)
    (n : ℕ) (hn : 2 ≤ n) (horder : orderOf f.val = n)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q)
    (hpD : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hqD : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hpL : p ∈ L.closedCarrier) (hqL : q ∈
      L.closedCarrier) :
    1 / Real.sin (Real.pi / (n : ℝ)) ≤ Real.cosh (L.pointDist (P.finiteCoordinate v)) := by
  by_cases hn2 : n = 2
  · rw [hn2]
    norm_num only [Nat.cast_ofNat,Real.sin_pi_div_two,div_one]
    exact Real.one_le_cosh _
  have hn3 : 3 ≤ n := by omega
  obtain ⟨r,hr,hrv⟩ := P.point_normalizer_exists v
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate r H
  let P' := P.conjugateData r hr
  let Φ := P.conjugateCoordinate r hr
  let E := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence r H
  let F : Complex.UnitDisc ≃ₜ Complex.UnitDisc :=
    (P.finiteCoordinate.symm.trans Φ).trans P'.finiteCoordinate
  have hFiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric; Isometry F := P.conjugateCoordinate_isometry r hr
  have hFdist (z w : Complex.UnitDisc) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F z) (F w) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z w := by
    let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using hFiso.dist_eq z w
  let e := _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry F hFdist
  have hFv : e.finiteMap (P.finiteCoordinate v) = 0 := by
    change F (P.finiteCoordinate v) = 0
    simp only [F,Homeomorph.trans_apply,P.finiteCoordinate.symm_apply_apply]
    apply P'.finiteCoordinate.symm.injective
    rw [P'.finiteCoordinate.symm_apply_apply]
    apply Subtype.ext
    exact hrv.trans (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe 0).symm
  have hback (g : K) (x : P'.domain.carrier) : Φ.symm (g • x) = E.symm g • Φ.symm x := by
    apply Φ.injective
    rw [Φ.apply_symm_apply,P.conjugateCoordinate_equivariant r hr,E.apply_symm_apply,
      Φ.apply_symm_apply]
  have hD' : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain P' (Φ '' D) := by
    have hh := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage E.symm Φ.symm hback hD
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain K P'.domain.carrier (MeasureTheory.Measure.map Φ P.area)
      (Φ.symm ⁻¹' D) at hh
    have hset : Φ.symm ⁻¹' D = Φ '' D := (Φ.toEquiv.image_eq_preimage_symm D).symm
    rwa [P.conjugateCoordinate_area_map r hr,hset] at hh
  have hQD' : P'.finiteCoordinate '' (Φ '' D) = e.finiteMap '' Q.interior := by
    rw [←hQD,image_image,image_image]
    apply image_congr
    intro x _hx
    change P'.finiteCoordinate (Φ x) = F (P.finiteCoordinate x)
    simp only [F,Homeomorph.trans_apply,P.finiteCoordinate.symm_apply_apply]
  have hf0 : (E f).val.val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    have hh := P.conjugateCoordinate_equivariant r hr f v
    rw [hfv] at hh
    have hh' := congrArg Subtype.val hh.symm
    change (E f).val.val (Φ v).val = (Φ v).val at hh'
    rwa [hrv] at hh'
  have horder' : orderOf (E f).val = n := by
    calc
      orderOf (E f).val = orderOf (E f) := Subgroup.orderOf_coe _
      _ = orderOf f := orderOf_injective E.toMonoidHom E.injective f
      _ = orderOf f.val := (Subgroup.orderOf_coe f).symm
      _ = n := horder
  have hpQ : p ∈ Q.closedCarrier := by
    change p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure Q.interior
    rwa [←hQD]
  have hqQ : q ∈ Q.closedCarrier := by
    change q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure Q.interior
    rwa [←hQD]
  have hangle := normalized_finite_jordan_ideal_angle_bound P' hD' Q e hQD' (E f) hf0
    n hn3 horder' p q hpQ hqQ hp hq
  exact ideal_joining_distance_of_normalized_angle_bound e (P.finiteCoordinate v) hFv
    p q hp hq hpq L hpL hqL n hn3 hangle

/-- The same original-scope estimate uses the entire genuine point stabilizer
order; a primitive generator is derived from the actual finite cyclic group. -/
theorem finite_jordan_ideal_joining_line_cosh_pointDist_ge_csc_point_order
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H)
    {D : Set P.domain.carrier} (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain P D)
    {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m) (hQD : P.finiteCoordinate '' D =
      Q.interior)
    (v : P.domain.carrier) (hn : 2 ≤ _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianPointOrder P v)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q)
    (hpD : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hqD : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hpL : p ∈ L.closedCarrier) (hqL : q ∈
      L.closedCarrier) :
    1 / Real.sin (Real.pi / (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianPointOrder P v : ℝ)) ≤
      Real.cosh (L.pointDist (P.finiteCoordinate v)) := by
  let _jordanIdealStabilizerFinite : Finite (MulAction.stabilizer H v) := P.stabilizer_finite v
  let _jordanIdealStabilizerCyclic : IsCyclic (MulAction.stabilizer H v) := P.stabilizer_isCyclic v
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic (MulAction.stabilizer H v))
  have horder : orderOf g.val.val = _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianPointOrder P v := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hg]
    rfl
  exact finite_jordan_ideal_joining_line_cosh_pointDist_ge_csc_element_order P hD Q hQD v g.val
    (MulAction.mem_stabilizer_iff.mp g.property) (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianPointOrder P
      v) hn horder
    p q hp hq hpq hpD hqD L hpL hqL

/-- The necessary order-at-least-three restriction yields the universal scalar
bound in the complete original finite Jordan scope. -/
theorem finite_jordan_ideal_joining_line_cosh_pointDist_ge_two_div_sqrt_three
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H)
    {D : Set P.domain.carrier} (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain P D)
    {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m) (hQD : P.finiteCoordinate '' D =
      Q.interior)
    (v : P.domain.carrier) (hn : 3 ≤ _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianPointOrder P v)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q)
    (hpD : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hqD : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hpL : p ∈ L.closedCarrier) (hqL : q ∈
      L.closedCarrier) :
    2 / Real.sqrt 3 ≤ Real.cosh (L.pointDist (P.finiteCoordinate v)) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.csc_pi_div_nat_ge_two_div_sqrt_three _ hn).trans
    (finite_jordan_ideal_joining_line_cosh_pointDist_ge_csc_point_order P hD Q hQD v (by omega)
      p q hp hq hpq hpD hqD L hpL hqL)

/-- The positive distance width corresponding to the actual pi/6 hypercycles. -/
def idealJoiningLensWidth : ℝ := Real.artanh (1/2)

theorem idealJoiningLensWidth_pos : 0 < idealJoiningLensWidth :=
  Real.artanh_pos (by norm_num)

theorem idealJoiningLensWidth_angle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hypercyclicWidthAngle idealJoiningLensWidth = Real.pi/6 := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hypercyclicWidthAngle,idealJoiningLensWidth,Real.tanh_artanh (by norm_num)]
  rw [←Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

theorem idealJoiningLensWidth_cosh : Real.cosh idealJoiningLensWidth = 2/Real.sqrt 3 := by
  rw [idealJoiningLensWidth,Real.cosh_artanh (by norm_num)]
  have he : Real.sqrt (1-(1/2 : ℝ)^2) = Real.sqrt 3 / 2 := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt 3 / 2)).mp
    rw [Real.sq_sqrt (by norm_num)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [he]
  field_simp

/-- The actual lens is the genuine point-to-line distance sublevel bounded by
the hypercycles whose source inclination angle is pi/6. -/
def idealJoiningLens (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) : Set Complex.UnitDisc := L.distanceSublevel idealJoiningLensWidth

theorem idealJoiningLens_hypercyclic (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHypercyclicRegion (idealJoiningLens L) :=
  L.distanceSublevel_hypercyclic idealJoiningLensWidth idealJoiningLensWidth_pos

/-- The corrected source lens exclusion follows in the full finite Jordan
scope for every genuine point stabilizer of order at least three. -/
theorem finite_jordan_ideal_joining_lens_exclusion
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H)
    {D : Set P.domain.carrier} (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianFundamentalDomain P D)
    {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m) (hQD : P.finiteCoordinate '' D =
      Q.interior)
    (v : P.domain.carrier) (hn : 3 ≤ _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianPointOrder P v)
    (p q : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (hpq : p ≠ q)
    (hpD : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hqD : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hpL : p ∈ L.closedCarrier) (hqL : q ∈
      L.closedCarrier) :
    P.finiteCoordinate v ∉ idealJoiningLens L := by
  intro hmem
  have hbound := finite_jordan_ideal_joining_line_cosh_pointDist_ge_two_div_sqrt_three P hD Q hQD v hn
    p q hp hq hpq hpD hqD L hpL hqL
  have hless : Real.cosh (L.pointDist (P.finiteCoordinate v)) < Real.cosh idealJoiningLensWidth := by
    apply Real.cosh_lt_cosh.mpr
    rw [abs_of_nonneg (L.pointDist_nonneg _),abs_of_pos idealJoiningLensWidth_pos]
    exact hmem
  rw [idealJoiningLensWidth_cosh] at hless
  exact (not_lt_of_ge hbound) hless

end LowDimensionalTopology.Geometry.Fuchsian.JordanIdealVertexBounds
