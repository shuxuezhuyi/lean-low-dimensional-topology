/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleIsometries
public import Mathlib.Topology.Connected.LocallyConnected
/-! # Actual finite and ideal Jordan geodesic polygons

The cyclic edges and boundary use the genuine closed native geodesic segments.
The inside is defined through the actual complement components. This module proves
basic topology and exact triangle compatibility; general polygon area, corner-angle
classification and convexity criteria are separate unfinished results.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
open Set MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Each edge is the actual closed finite-or-ideal native geodesic arc. -/
def discPolygonEdge {n : ℕ} (v : Fin n → 𝕔𝔻) (i : Fin n) : Set 𝕔𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (v i) (v (finRotate n i))

/-- The whole actual cyclic geodesic trace. -/
def discPolygonBoundary {n : ℕ} (v : Fin n → 𝕔𝔻) : Set 𝕔𝔻 := ⋃ i,discPolygonEdge v i

/-- Genuine Jordan geodesic polygons with finite or ideal vertices. The edge-intersection
condition records the simple cyclic traversal; straight angles remain permitted. -/
structure DiscPolygon (n : ℕ) where
  three_le : 3 ≤ n
  vertices : Fin n → 𝕔𝔻
  vertices_injective : Function.Injective vertices
  simple_edges : ∀ i j : Fin n,i ≠ j →
    discPolygonEdge vertices i ∩ discPolygonEdge vertices j ⊆
      {vertices i,vertices (finRotate n i)} ∩ {vertices j,vertices (finRotate n j)}
  jordanBoundary : Nonempty (↥(discPolygonBoundary vertices) ≃ₜ Metric.sphere (0 : ℝ × ℝ) 1)

def DiscPolygon.boundary {n : ℕ} (P : DiscPolygon n) : Set 𝕔𝔻 := discPolygonBoundary P.vertices

def DiscPolygon.complexBoundary {n : ℕ} (P : DiscPolygon n) : Set ℂ :=
  ((↑) : 𝕔𝔻 → ℂ) '' P.boundary

/-- The exterior is the actual component containing the fixed point 2 outside the entire closed model. -/
def DiscPolygon.complexOutside {n : ℕ} (P : DiscPolygon n) : Set ℂ :=
  connectedComponentIn P.complexBoundaryᶜ (2 : ℂ)

/-- The true bounded-side region of the Jordan trace; no triangulation data enter this definition. -/
def DiscPolygon.complexInterior {n : ℕ} (P : DiscPolygon n) : Set ℂ :=
  P.complexBoundaryᶜ \ P.complexOutside

def DiscPolygon.interior {n : ℕ} (P : DiscPolygon n) : Set 𝔻 :=
  ((↑) : 𝔻 → ℂ) ⁻¹' P.complexInterior

/-- Polygon area is the existing actual hyperbolic density area. -/
def DiscPolygon.area {n : ℕ} (P : DiscPolygon
  n) : ENNReal := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea P.interior

/-- Convexity is the existing genuine geodesic-segment convexity of the actual region. -/
def DiscPolygon.IsConvex {n : ℕ} (P : DiscPolygon
  n) : Prop := _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex P.interior

theorem closedModelDiscHSegment_isCompact (p q : 𝕔𝔻) : IsCompact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.isCompact_iff.mpr
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  rw [segment_eq_image]
  exact isCompact_Icc.image (((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul
    continuous_const))

theorem DiscPolygon.boundary_isCompact {n : ℕ} (P : DiscPolygon n) : IsCompact P.boundary :=
  isCompact_iUnion (fun i => closedModelDiscHSegment_isCompact (P.vertices i) (P.vertices (finRotate n i)))

theorem DiscPolygon.complexBoundary_isCompact {n : ℕ} (P : DiscPolygon n) : IsCompact P.complexBoundary :=
  P.boundary_isCompact.image Complex.UnitClosedDisc.isEmbedding_coe.continuous

theorem DiscPolygon.complexBoundary_isClosed {n : ℕ} (P : DiscPolygon n) : IsClosed P.complexBoundary :=
  P.complexBoundary_isCompact.isClosed

theorem DiscPolygon.outside_point_not_mem_boundary {n : ℕ} (P : DiscPolygon n) :
    (2 : ℂ) ∉ P.complexBoundary := by
  rintro ⟨p,_,hp⟩
  have hn := p.norm_le_one
  rw [hp] at hn
  norm_num at hn

theorem DiscPolygon.complexOutside_isOpen {n : ℕ} (P : DiscPolygon n) : IsOpen P.complexOutside :=
  P.complexBoundary_isClosed.isOpen_compl.connectedComponentIn

/-- The inside is exactly the union of all actual complement components other than the exterior. -/
theorem DiscPolygon.complexInterior_eq_components {n : ℕ} (P : DiscPolygon n) :
    P.complexInterior = ⋃ z ∈ P.complexInterior,connectedComponentIn P.complexBoundaryᶜ z := by
  apply subset_antisymm
  · intro z hz
    exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨hz,mem_connectedComponentIn hz.1⟩⟩
  · intro w hw
    obtain ⟨z,hw⟩ := mem_iUnion.mp hw
    obtain ⟨hz,hw⟩ := mem_iUnion.mp hw
    refine ⟨connectedComponentIn_subset _ _ hw,?_⟩
    intro hout
    have he := (connectedComponentIn_eq hw).trans (connectedComponentIn_eq hout).symm
    have hzout : z ∈ P.complexOutside := by
      change z ∈ connectedComponentIn P.complexBoundaryᶜ (2 : ℂ)
      rw [← he]
      exact mem_connectedComponentIn hz.1
    exact hz.2 hzout

theorem DiscPolygon.complexInterior_isOpen {n : ℕ} (P : DiscPolygon n) : IsOpen P.complexInterior := by
  rw [P.complexInterior_eq_components]
  exact isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => P.complexBoundary_isClosed.isOpen_compl.connectedComponentIn))

theorem DiscPolygon.interior_isOpen {n : ℕ} (P : DiscPolygon n) : IsOpen P.interior :=
  P.complexInterior_isOpen.preimage Complex.UnitDisc.continuous_coe

theorem DiscPolygon.interior_measurable {n : ℕ} (P : DiscPolygon n) : MeasurableSet P.interior :=
  P.interior_isOpen.measurableSet

/-- Every point beyond the unit circle belongs to the actual exterior component. -/
theorem DiscPolygon.outer_region_subset_outside {n : ℕ} (P : DiscPolygon n) :
    {z : ℂ | 1 < ‖z‖} ⊆ P.complexOutside := by
  have hsub : {z : ℂ | 1 < ‖z‖} ⊆ P.complexBoundaryᶜ := by
    intro z hz
    rintro ⟨p,_,rfl⟩
    exact (not_lt_of_ge p.norm_le_one) hz
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_outer_region_isPreconnected (by norm_num : (0 : ℝ) ≤ 1)).subset_connectedComponentIn
  · norm_num
  · exact hsub

/-- The true inside cannot extend outside the closed disc. -/
theorem DiscPolygon.complexInterior_subset_closedBall {n : ℕ} (P : DiscPolygon n) :
    P.complexInterior ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro z hz
  change dist z 0 ≤ 1
  rw [dist_zero_right]
  by_contra! hn
  exact hz.2 (P.outer_region_subset_outside hn)

/-- Since it is open, the inside lies in the genuine finite disc even when the boundary has ideal vertices. -/
theorem DiscPolygon.complexInterior_subset_disc {n : ℕ} (P : DiscPolygon n) :
    P.complexInterior ⊆ Metric.ball (0 : ℂ) 1 := by
  have hsub := interior_mono P.complexInterior_subset_closedBall
  rw [P.complexInterior_isOpen.interior_eq,interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hsub
  exact hsub

theorem DiscPolygon.complexInterior_isBounded {n : ℕ} (P : DiscPolygon n) :
    Bornology.IsBounded P.complexInterior :=
  (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset P.complexInterior_subset_closedBall

/-- The actual finite native region has exactly the intended complex inside image. -/
theorem DiscPolygon.interior_complex_image {n : ℕ} (P : DiscPolygon n) :
    ((↑) : 𝔻 → ℂ) '' P.interior = P.complexInterior := by
  apply image_preimage_eq_of_subset
  intro z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using P.complexInterior_subset_disc hz
  exact ⟨Complex.UnitDisc.mk z hn,rfl⟩

/-- The compactified boundary really is a Jordan trace in the original complex plane. -/
theorem DiscPolygon.exists_jordan_curve {n : ℕ} (P : DiscPolygon n) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ,Continuous γ ∧ Function.Injective γ ∧
      range γ = P.complexBoundary := by
  obtain ⟨h⟩ := P.jordanBoundary
  let γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ := fun q => ((h.symm q).val : ℂ)
  refine ⟨γ,Complex.UnitClosedDisc.isEmbedding_coe.continuous.comp (continuous_subtype_val.comp
    h.symm.continuous),?_,?_⟩
  · intro p q he
    apply h.symm.injective
    exact Subtype.ext (Complex.UnitClosedDisc.coe_injective he)
  · ext z
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨(h.symm q).val,(h.symm q).property,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      refine ⟨h ⟨p,hp⟩,?_⟩
      change ((h.symm (h ⟨p,hp⟩)).val : ℂ) = (p : ℂ)
      rw [h.symm_apply_apply]

/-- A cyclic successor cannot fix a vertex index of a genuine polygon. -/
theorem DiscPolygon.next_ne_self {n : ℕ} (P : DiscPolygon n) (i : Fin n) : finRotate n i ≠ i := by
  have hn := P.three_le
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hi : i = Fin.last k
  · subst i
    rw [finRotate_last]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero,Fin.val_last] at hv
    have := P.three_le
    omega
  · have hv : ((finRotate (k+1)) i).val = i.val + 1 := coe_finRotate_of_ne_last hi
    intro he
    exact Nat.succ_ne_self i.val (hv.symm.trans (congrArg Fin.val he))

theorem DiscPolygon.prev_ne_self {n : ℕ} (P : DiscPolygon n) (i : Fin n) : (finRotate n).symm i ≠ i := by
  intro he
  have hx := congrArg (finRotate n) he
  rw [Equiv.apply_symm_apply] at hx
  exact P.next_ne_self i hx.symm

/-- The genuine ray from a finite point towards a distinct finite or ideal closed vertex. -/
def discRayTowardClosed (z : 𝔻) (q : 𝕔𝔻) (hzq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ q) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z := by
  classical
  by_cases hq : ‖(q : ℂ)‖ < 1
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint q hq) (by
      intro he
      apply hzq
      rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec])
  · have hqE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary :=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary _).mpr (le_antisymm
        q.norm_le_one (le_of_not_gt hq))
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay z
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended
      q),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q,hqE,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHLineRay_discHRay z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q) hqE⟩

theorem discRayTowardClosed_finite (z w : 𝔻) (hzw : z ≠ w)
    (hzq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w) :
    discRayTowardClosed z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w) hzq = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough z w hzw := by
  have hw : ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w : 𝕔𝔻) : ℂ)‖ < 1 := w.norm_lt_one
  rw [discRayTowardClosed,dite_eq_left hw]
  rfl

theorem discRayTowardClosed_idealEndpoint (z : 𝔻) (q : 𝕔𝔻)
    (hzq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ q) (hq : ‖(q : ℂ)‖ = 1) :
    (discRayTowardClosed z q hzq).idealEndpoint = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q := by
  have hqE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary _).mpr hq
  apply (discRayTowardClosed z q hzq).idealEndpoint_eq_of_canonical_subset _ hqE
  have hqn : ¬ ‖(q : ℂ)‖ < 1 := by rw [hq]; exact lt_irrefl (1 : ℝ)
  rw [discRayTowardClosed,dite_eq_right hqn]

theorem discRayTowardClosed_endpoint_mem (z : 𝔻) (q : 𝕔𝔻)
    (hzq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ q) : q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (discRayTowardClosed z q hzq).val := by
  by_cases hq : ‖(q : ℂ)‖ < 1
  · have hz : z ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint q hq := by
      intro he
      apply hzq
      rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec]
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint q hq) = q := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec q hq
    have hr : discRayTowardClosed z q hzq = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint q hq) hz := by
      rw [discRayTowardClosed,dite_eq_left hq]
    rw [hr]
    have hm := subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough_mem _ _ hz))
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,he] using hm
  · exact (discRayTowardClosed z q hzq).ideal_mem_closedClosure q
      (discRayTowardClosed_idealEndpoint z q hzq (le_antisymm q.norm_le_one (le_of_not_gt hq)))

/-- The next actual side direction at a finite polygon vertex. -/
def DiscPolygon.cornerRayNext {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      z) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z :=
  discRayTowardClosed z (P.vertices (finRotate n i)) (by
    rw [← hz]
    exact fun he => P.next_ne_self i (P.vertices_injective he).symm)

/-- The preceding actual side direction at a finite polygon vertex. -/
def DiscPolygon.cornerRayPrev {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      z) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z :=
  discRayTowardClosed z (P.vertices ((finRotate n).symm i)) (by
    rw [← hz]
    exact fun he => P.prev_ne_self i (P.vertices_injective he).symm)

/-- Actual native side lengths, with infinite length at an ideal endpoint. -/
def DiscPolygon.sideLength {n : ℕ} (P : DiscPolygon n) (i : Fin n) : ENNReal :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices i) (P.vertices (finRotate n i))

/-- The actual cyclic vertices of a closed triangle. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : Fin 3 → 𝕔𝔻 := ![T.a,T.b,T.c]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices_injective (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    Function.Injective T.polygonVertices := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,T.a_ne_b,T.b_ne_c,T.c_ne_a,Ne.symm T.a_ne_b,Ne.symm T.b_ne_c,Ne.symm T.c_ne_a]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonEdge_zero (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    discPolygonEdge T.polygonVertices 0 = T.sideC := by
  norm_num [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideC]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonEdge_one (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    discPolygonEdge T.polygonVertices 1 = T.sideA := by
  norm_num [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideA]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonEdge_two (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    discPolygonEdge T.polygonVertices 2 = T.sideB := by
  norm_num [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideB]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonBoundary (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    discPolygonBoundary T.polygonVertices = T.sideA ∪ T.sideB ∪ T.sideC := by
  ext p
  simp only [discPolygonBoundary,mem_iUnion]
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inr (T.polygonEdge_zero ▸ hi)
    · exact Or.inl (Or.inl (T.polygonEdge_one ▸ hi))
    · exact Or.inl (Or.inr (T.polygonEdge_two ▸ hi))
  · rintro ((h | h) | h)
    · exact ⟨1,T.polygonEdge_one.symm ▸ h⟩
    · exact ⟨2,T.polygonEdge_two.symm ▸ h⟩
    · exact ⟨0,T.polygonEdge_zero.symm ▸ h⟩

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideA_inter_sideB (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : T.sideA ∩ T.sideB = {T.c} := by
  ext p
  rw [mem_inter_iff,T.mem_sideA_iff_coordinate,T.mem_sideB_iff_coordinate,mem_singleton_iff]
  constructor
  · rintro ⟨hA,hB⟩
    apply T.coordinateHomeomorph.injective.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
    change T.coordinate p = T.coordinate T.c
    rw [T.coordinate_c]
    ext <;> dsimp <;> linarith
  · rintro rfl
    rw [T.coordinate_c]
    norm_num

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideB_inter_sideC (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : T.sideB ∩ T.sideC = {T.a} := by
  ext p
  rw [mem_inter_iff,T.mem_sideB_iff_coordinate,T.mem_sideC_iff_coordinate,mem_singleton_iff]
  constructor
  · rintro ⟨hB,hC⟩
    apply T.coordinateHomeomorph.injective.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
    change T.coordinate p = T.coordinate T.a
    rw [T.coordinate_a]
    ext <;> dsimp <;> linarith
  · rintro rfl
    rw [T.coordinate_a]
    norm_num

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.sideC_inter_sideA (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : T.sideC ∩ T.sideA = {T.b} := by
  ext p
  rw [mem_inter_iff,T.mem_sideC_iff_coordinate,T.mem_sideA_iff_coordinate,mem_singleton_iff]
  constructor
  · rintro ⟨hC,hA⟩
    apply T.coordinateHomeomorph.injective.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
    change T.coordinate p = T.coordinate T.b
    rw [T.coordinate_b]
    ext <;> dsimp <;> linarith
  · rintro rfl
    rw [T.coordinate_b]
    norm_num

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices_simple_edges (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    ∀ i j : Fin 3,i ≠ j →
      discPolygonEdge T.polygonVertices i ∩ discPolygonEdge T.polygonVertices j ⊆
        {T.polygonVertices i,T.polygonVertices (finRotate 3 i)} ∩
          {T.polygonVertices j,T.polygonVertices (finRotate 3 j)} := by
  intro i j hij p hp
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change p ∈ T.sideC ∩ T.sideA at hp
    rw [T.sideC_inter_sideA] at hp
    have he := mem_singleton_iff.mp hp
    subst p
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply]
  · change p ∈ T.sideC ∩ T.sideB at hp
    rw [inter_comm,T.sideB_inter_sideC] at hp
    have he := mem_singleton_iff.mp hp
    subst p
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply]
  · change p ∈ T.sideA ∩ T.sideC at hp
    rw [inter_comm,T.sideC_inter_sideA] at hp
    have he := mem_singleton_iff.mp hp
    subst p
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply]
  · exact (hij rfl).elim
  · change p ∈ T.sideA ∩ T.sideB at hp
    rw [T.sideA_inter_sideB] at hp
    have he := mem_singleton_iff.mp hp
    subst p
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply]
  · change p ∈ T.sideB ∩ T.sideC at hp
    rw [T.sideB_inter_sideC] at hp
    have he := mem_singleton_iff.mp hp
    subst p
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply]
  · change p ∈ T.sideB ∩ T.sideA at hp
    rw [inter_comm,T.sideA_inter_sideB] at hp
    have he := mem_singleton_iff.mp hp
    subst p
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.polygonVertices,finRotate_apply]
  · exact (hij rfl).elim

/-- Every genuine finite-or-ideal triangle is a genuine Jordan geodesic polygon. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : DiscPolygon 3 where
  three_le := le_rfl
  vertices := T.polygonVertices
  vertices_injective := T.polygonVertices_injective
  simple_edges := T.polygonVertices_simple_edges
  jordanBoundary := by
    rw [T.polygonBoundary]
    exact T.closedSides_circle_homeomorph

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_complexBoundary (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.toDiscPolygon.complexBoundary = frontier T.complexInterior := by
  change ((↑) : 𝕔𝔻 → ℂ) '' discPolygonBoundary T.polygonVertices = _
  rw [T.polygonBoundary,T.complexInterior_frontier]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_complexOutside (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.toDiscPolygon.complexOutside = (closure T.complexInterior)ᶜ := by
  change connectedComponentIn T.toDiscPolygon.complexBoundaryᶜ (2 : ℂ) = _
  rw [T.toDiscPolygon_complexBoundary]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.connectedComponentIn_compl_frontier_of_mem_exterior T.complexInterior_isOpen
    T.complexExterior_isPreconnected
  intro h
  rw [T.complexInterior_closure] at h
  have hn := T.complexClosedCarrier_subset_closedBall h
  norm_num at hn

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_complexInterior (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.toDiscPolygon.complexInterior = T.complexInterior := by
  change T.toDiscPolygon.complexBoundaryᶜ \ T.toDiscPolygon.complexOutside = _
  rw [T.toDiscPolygon_complexBoundary,T.toDiscPolygon_complexOutside,frontier,
    T.complexInterior_isOpen.interior_eq]
  ext z
  simp only [mem_sdiff,mem_compl_iff,not_and,not_not]
  constructor
  · rintro ⟨h,hc⟩
    exact h hc
  · intro hz
    exact ⟨fun _ => hz,subset_closure hz⟩

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_interior (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.toDiscPolygon.interior = T.interior := by
  change ((↑) : 𝔻 → ℂ) ⁻¹' T.toDiscPolygon.complexInterior = _
  rw [T.toDiscPolygon_complexInterior]
  rfl

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_area (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.toDiscPolygon.area = ENNReal.ofReal (Real.pi-T.alpha-T.beta-T.gamma) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea T.toDiscPolygon.interior = _
  rw [T.toDiscPolygon_interior,T.area_eq_angle_defect]

end
end LowDimensionalTopology.Geometry.Polygon
