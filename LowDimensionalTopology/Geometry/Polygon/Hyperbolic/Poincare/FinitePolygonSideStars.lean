module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.FinitePolygonPoincareData
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePairedSideStars
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Two actual points on a native supporting line identify either of its genuine signed
closed half-planes with the corresponding nonzero original Klein affine inequality. -/
theorem native_halfPlane_signed_support (N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) {m : ℂ} {t
  : ℝ}
    (hm : m≠0) {a b : ℍ} (hab : a≠b) (ha : a∈N.carrier) (hb : b∈N.carrier)
    (hma : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate a)=t)
    (hmb : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate b)=t) :
    ∃σ : ℝ,σ≠0 ∧ ∀z : ℍ,
      (0≤σ*N.normalTimeAt z ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤t) := by
  have hn : N.incenterNormal≠0 := by
    intro h
    have hunit:=N.incenterNormal_lorentz_unit
    rw [h,norm_zero,zero_pow (by decide : 2≠0)] at hunit
    nlinarith [sq_nonneg N.incenterOffset]
  have habK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate a≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate b :=
    fun h=>hab (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.injective h)
  have hna : inner ℝ N.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate a)=N.incenterOffset := by
    have h:=(N.incenter_affine_eq_zero_iff a).mpr ha
    exact sub_eq_zero.mp h
  have hnb : inner ℝ N.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate b)=N.incenterOffset := by
    have h:=(N.incenter_affine_eq_zero_iff b).mpr hb
    exact sub_eq_zero.mp h
  obtain ⟨u,hu⟩ : ∃u : ℂ,inner ℝ m u-t≠0 := by
    by_cases ht : t=0
    · refine ⟨m,?_⟩
      simpa only [ht,sub_zero,real_inner_self_eq_norm_sq] using
        (sq_pos_of_pos (norm_pos_iff.mpr hm)).ne'
    · refine ⟨0,?_⟩
      simpa using ht
  have hnu : inner ℝ N.incenterNormal u-N.incenterOffset≠0 := by
    intro h
    have he:=_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points (x:=u) hn hm habK hna hnb hma hmb
    exact hu (sub_eq_zero.mpr (he.mp (sub_eq_zero.mp h)))
  let σ:=(inner ℝ N.incenterNormal u-N.incenterOffset)/(inner ℝ m u-t)
  have hσ : σ≠0 := div_ne_zero hnu hu
  refine ⟨σ,hσ,?_⟩
  intro z
  have hc:=_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_difference_cross (x:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) (u:=u)
    hn hm habK hna hnb hma hmb
  have hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine N.incenterNormal N.incenterOffset z=
      σ*(inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)-t) := by
    dsimp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,σ]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hu).mpr
    nlinarith only [hc]
  have hcoef : 0<_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*σ^2 :=
    mul_pos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos z) (sq_pos_of_ne_zero hσ)
  rw [N.normalTimeAt_eq_affine,hp]
  have he : σ*(-_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*(σ*(inner ℝ m
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)-t)))=
      -(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight z*σ^2)*(inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)-t) := by ring
  rw [he]
  constructor <;> intro h <;> nlinarith

/-- The actual original strict convex polygon determines its original supporting affine data. -/
def finitePolygonSupports {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) : CenteredDiscPolygonSupportData n :=
  (Q.strictSupportData hQ ha).toCenteredData

/-- The literal closed polygon is precisely the intersection of its actual original support cuts. -/
theorem finitePolygon_carrier_support_iff {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (z : ℍ) :
    z∈(finiteDiscPoincarePolygon Q hf).carrier ↔
      ∀i,inner ℝ ((finitePolygonSupports Q hQ ha).normals
        i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤
        (finitePolygonSupports Q hQ ha).offsets i := by
  let A:=finitePolygonSupports Q hQ ha
  have hAQ : A.toDiscPolygon=Q := Q.strictSupportData_toDiscPolygon hQ ha
  have hBody : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.closedCarrier=A.kleinRegion := by
    rw [←hAQ]
    exact centeredPolygon_closedCarrier_klein_image A
  rw [finiteDiscPoincarePolygon_carrier_iff]
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈Q.closedCarrier ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinRegion := by
    rw [←hBody]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.symm
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
  rfl

/-- An actual original supporting h-line has exactly the original affine zero equation. -/
theorem finitePolygon_line_support_iff {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (i : Fin n) (z : ℍ) :
    z∈(finitePolygonLine Q i).carrier ↔
      inner ℝ ((finitePolygonSupports Q hQ ha).normals
        i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)=
        (finitePolygonSupports Q hQ ha).offsets i := by
  let A:=finitePolygonSupports Q hQ ha
  have hAL : A.supportLine i=Q.geodesicSide i := Q.strictSupportData_supportLine hQ ha i
  have he:=A.supportLine_equation i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))
  rw [hAL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_mem_interior_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at he
  exact he

/-- Two distinct actual sides can meet only at an actual original endpoint. -/
theorem finitePolygon_common_sides_vertex {n : ℕ} (Q : DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) {i j : Fin n} (hne : i≠j) {z : ℍ}
    (hi : z∈finitePolygonSide Q i) (hj : z∈finitePolygonSide Q j) :
    z∈range (finitePolygonVertex Q hf) := by
  have he:=(Q.simple_edges i j hne ⟨hi,hj⟩).1
  simp only [mem_insert_iff,mem_singleton_iff] at he
  rcases he with he | he
  · refine ⟨i,?_⟩
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
    apply Subtype.ext
    exact congrArg (fun p : 𝕔𝔻=>(p : ℂ)) ((finitePolygonVertex_coordinate Q hf i).trans he.symm)
  · refine ⟨finRotate n i,?_⟩
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
    apply Subtype.ext
    exact congrArg (fun p : 𝕔𝔻=>(p : ℂ)) ((finitePolygonVertex_coordinate Q hf (finRotate n i)).trans he.symm)

/-- A nonvertex point of an actual original side has every other original support cut strict. -/
theorem finitePolygon_other_support_strict {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    {i : Fin n} {z : ℍ} (hi : z∈finitePolygonSide Q i)
    (hv : z∉range (finitePolygonVertex Q hf)) {j : Fin n} (hj : j≠i) :
    inner ℝ ((finitePolygonSupports Q hQ ha).normals
      j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<
      (finitePolygonSupports Q hQ ha).offsets j := by
  have hP : z∈(finiteDiscPoincarePolygon Q hf).carrier :=
    (finiteDiscPoincarePolygon Q hf).side_subset_carrier (finitePolygonSideEquiv Q hf i) hi
  have hw := (finitePolygon_carrier_support_iff Q hQ ha hf z).mp hP j
  apply lt_of_le_of_ne hw
  intro he
  have hL := (finitePolygon_line_support_iff Q hQ ha j z).mpr he
  have hjs : z∈finitePolygonSide Q j := by
    rw [finitePolygonSide_eq_carrier_inter_line Q hQ ha hf j]
    exact ⟨hP,hL⟩
  exact hv (finitePolygon_common_sides_vertex Q hf hj.symm hi hjs)

/-- Near a genuine nonvertex side point, all other original support inequalities disappear;
the original closed polygon is exactly the one actual supporting closed half-plane. -/
theorem finitePolygon_nonvertex_support_germ {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    {i : Fin n} {z : ℍ} (hi : z∈finitePolygonSide Q i)
    (hv : z∉range (finitePolygonVertex Q hf)) :
    ∃r : ℝ,0<r ∧ ∀w : ℍ,dist w z<r →
      (w∈(finiteDiscPoincarePolygon Q hf).carrier ↔
        inner ℝ ((finitePolygonSupports Q hQ ha).normals
          i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤
          (finitePolygonSupports Q hQ ha).offsets i) := by
  let A:=finitePolygonSupports Q hQ ha
  let U : Set ℍ:=⋂j,⋂(_ : j≠i),{w : ℍ|inner ℝ (A.normals j)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)<A.offsets j}
  have hU : IsOpen U := isOpen_iInter_of_finite (fun j=>isOpen_iInter_of_finite (fun _=>
    isOpen_lt (continuous_const.inner _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous) continuous_const))
  have hzU : z∈U := by
    apply mem_iInter.mpr
    intro j
    apply mem_iInter.mpr
    intro hj
    exact finitePolygon_other_support_strict Q hQ ha hf hi hv hj
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  refine ⟨r,hr,?_⟩
  intro w hw
  rw [finitePolygon_carrier_support_iff Q hQ ha hf w]
  constructor
  · exact fun h=>h i
  · intro h j
    by_cases hj : j=i
    · simpa only [hj] using h
    · exact (mem_iInter₂.mp (hBall hw) j hj).le

/-- The original affine supporting cut is a true signed Lorentz half-plane of its own reflection. -/
theorem finitePolygon_side_signed_support {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    ∃σ : ℝ,σ≠0 ∧ ∀z : ℍ,
      (0≤σ*(finitePolygonLine Q i).normalTimeAt z ↔
        inner ℝ ((finitePolygonSupports Q hQ ha).normals
          i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤
          (finitePolygonSupports Q hQ ha).offsets i) := by
  let A:=finitePolygonSupports Q hQ ha
  have hm : A.normals i≠0 := by
    intro h
    have hn:=A.normal_norm i
    rw [h,norm_zero] at hn
    norm_num at hn
  have hne : finitePolygonVertex Q hf i≠finitePolygonVertex Q hf (finRotate n i) :=
    (finitePolygonVertex_injective Q hf).ne (centeredPolygonSupport_next_ne_self Q.three_le i).symm
  have hl:=finitePolygonSide_subset_line Q i (finitePolygonSide_left_mem Q hf i)
  have hr:=finitePolygonSide_subset_line Q i (finitePolygonSide_right_mem Q hf i)
  exact native_halfPlane_signed_support (finitePolygonLine Q i) hm hne hl hr
    ((finitePolygon_line_support_iff Q hQ ha i _).mp hl)
    ((finitePolygon_line_support_iff Q hQ ha i _).mp hr)

/-- Reflection in a genuine nonvertex original side gives the actual two-half-ball gluing
neighborhood, derived solely from the original polygon's strict support geometry. -/
theorem finitePolygon_nonvertex_paired_side {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (x : (finiteDiscPoincarePolygon Q hf).Point) (i : Fin n)
    (hi : x.val∈finitePolygonSide Q i) (hv : x.val∉range (finitePolygonVertex Q hf)) :
    ∃r : ℝ,(finiteDiscPoincarePairing Q hf).PairedSideNeighborhood x (finitePolygonSideEquiv Q hf i) r := by
  let P:=finiteDiscPoincarePolygon Q hf
  let S:=finiteDiscPoincarePairing Q hf
  let s:=finitePolygonSideEquiv Q hf i
  let N:=finitePolygonLine Q i
  obtain ⟨r₀,hr₀,hG⟩:=finitePolygon_nonvertex_support_germ Q hQ ha hf hi hv
  obtain ⟨r₁,hr₁,hNear⟩:=PoincareSidePairing.exists_ball_incident_sides
    (finiteDiscPoincarePolygon_locallyFiniteSides Q hf) (finiteDiscPoincarePolygon_closedSides Q hf) x
  obtain ⟨σ,hσ,hCut⟩:=finitePolygon_side_signed_support Q hQ ha hf i
  let r:=min r₀ r₁
  have hr : 0<r:=lt_min hr₀ hr₁
  refine ⟨r,S.pairedSideNeighborhood_of_halfPlaneReflection N hr hσ hi
    (finitePolygonSide_subset_line Q i) (by rfl) ?_ ?_ ?_ ?_⟩
  · intro z
    change S.element s z=N.reflection z
    rw [finiteDiscPoincarePairing_element]
    rfl
  · intro t y hy hdy
    have hxt:=hNear y (lt_of_lt_of_le hdy (min_le_right _ _)) t hy
    obtain ⟨j,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective t
    by_cases hji : j=i
    · exact congrArg (finitePolygonSideEquiv Q hf) hji
    · exact (hv (finitePolygon_common_sides_vertex Q hf (fun h=>hji h.symm) hi hxt)).elim
  · intro z hz
    exact (hG z (lt_of_lt_of_le hz (min_le_left _ _))).trans (hCut z).symm
  · intro z hz hZero
    have hL:=(N.normalTimeAt_eq_zero_iff z).mp hZero
    have hweak:=(finitePolygon_line_support_iff Q hQ ha i z).mp hL
    have hP:=(hG z (lt_of_lt_of_le hz (min_le_left _ _))).mpr hweak.le
    change z∈finitePolygonSide Q i
    rw [finitePolygonSide_eq_carrier_inter_line Q hQ ha hf i]
    exact ⟨hP,hL⟩

/-- Every point of the original finite reflection polygon satisfies the original complete
local Poincare condition, using its actual reciprocal angles and its genuine original sides. -/
theorem finitePolygon_integral_local_tessellation {m : ℕ} (Q : DiscPolygon m) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (n : Fin m→ℕ) (hn : ∀i,2≤n i) (hangle : ∀i,Q.angle i=Real.pi/(n i:ℝ)) :
    (finiteDiscPoincarePairing Q hf).FiniteFiberLocalTessellationCondition := by
  let P:=finiteDiscPoincarePolygon Q hf
  let S:=finiteDiscPoincarePairing Q hf
  let : IsIsometricSMul S.Generated ℍ :=
    (S.native_metric_assumptions (finiteDiscPoincarePolygon_interior_isOpen Q hf)
      (finiteDiscPoincarePolygon_interior_isConnected Q hf)).generatedIsometricSMul S
  have hcases (x : P.Point) : x.val∈P.interior ∨
      (∃i,x=finitePolygonPoincareVertex Q hf i) ∨
      ∃s : P.Side,∃r : ℝ,S.PairedSideNeighborhood x s r := by
    by_cases hxI : x.val∈P.interior
    · exact Or.inl hxI
    right
    by_cases hxV : x.val∈range (finitePolygonVertex Q hf)
    · obtain ⟨i,hi⟩:=hxV
      exact Or.inl ⟨i,Subtype.ext hi.symm⟩
    · right
      have hxB : x.val∈P.boundary := x.prop.resolve_left hxI
      obtain ⟨s,⟨i,rfl⟩,hxs⟩:=mem_sUnion.mp hxB
      obtain ⟨r,hr⟩:=finitePolygon_nonvertex_paired_side Q hQ ha hf x i hxs hxV
      exact ⟨finitePolygonSideEquiv Q hf i,r,hr⟩
  constructor
  · intro x
    rcases hcases x with hx | ⟨i,rfl⟩ | ⟨s,r,hr⟩
    · rw [S.project_fiber_eq_singleton_of_interior (1,x) hx]
      exact finite_singleton _
    · exact (finitePolygon_integral_vertex_local_condition Q hQ ha hf i (n i) (hn i) (hangle i)).1
    · exact hr.finite_class S
  · intro x
    rcases hcases x with hx | ⟨i,rfl⟩ | ⟨s,r,hr⟩
    · exact S.interior_local_radius (finiteDiscPoincarePolygon_interior_isOpen Q hf) x hx
    · exact (finitePolygon_integral_vertex_local_condition Q hQ ha hf i (n i) (hn i) (hangle i)).2
    · exact hr.local_radius S

/-- The genuine original reciprocal-angle finite polygon is a fundamental domain for its
actual original reflection group, which is discrete in the existing native isometry topology. -/
theorem finitePolygon_integral_poincare {m : ℕ} (Q : DiscPolygon m) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (n : Fin m→ℕ) (hn : ∀i,2≤n i) (hangle : ∀i,Q.angle i=Real.pi/(n i:ℝ)) :
    DiscreteTopology (↥(Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))
      ℍ MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior) := by
  have hh:=(finiteDiscPoincarePairing Q hf).native_poincare_of_compact
    (finitePolygon_integral_local_tessellation Q hQ ha hf n hn hangle)
    (finiteDiscPoincarePolygon_interior_isOpen Q hf)
    (finiteDiscPoincarePolygon_interior_isConnected Q hf)
    (finiteDiscPoincarePolygon_carrier Q hf)
    (finiteDiscPoincarePolygon_isCompact Q hf)
    (finiteDiscPoincarePolygon_countableSides Q hf)
    (finiteDiscPoincarePolygon_geodesicSides Q hf)
  change DiscreteTopology (↥(finiteDiscPoincarePairing Q hf).Generated) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (finiteDiscPoincarePairing Q
      hf).Generated
      ℍ MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior) at hh
  rwa [finiteDiscPoincarePairing_generated Q hf] at hh

/-- For original proper reciprocal-angle vertices, convexity, finiteness of every vertex
and compactness are conclusions from the actual angle data, rather than additional hypotheses. -/
theorem finitePolygon_reflection_poincare {m : ℕ} (Q : DiscPolygon m)
    (n : Fin m→ℕ) (hn : ∀i,2≤n i) (hangle : ∀i,Q.angle i=Real.pi/(n i:ℝ)) :
    DiscreteTopology (↥(Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))
      ℍ MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior) := by
  have ha : ∀i,Q.angle i<Real.pi := by
    intro i
    rw [hangle i]
    exact div_lt_self Real.pi_pos (by exact_mod_cast (by have:=hn i;omega : 1<n i))
  have hf : ∀i,‖(Q.vertices i : ℂ)‖<1 := by
    intro i
    apply Q.vertex_finite_of_angle_pos i
    rw [hangle i]
    apply div_pos Real.pi_pos
    exact_mod_cast (by have:=hn i;omega : 0<n i)
  have hQ : Q.IsConvex := Q.isConvex_iff_angles_le_pi.mpr (fun i=>(ha i).le)
  exact finitePolygon_integral_poincare Q hQ ha hf n hn hangle

end LowDimensionalTopology.Geometry.Polygon
