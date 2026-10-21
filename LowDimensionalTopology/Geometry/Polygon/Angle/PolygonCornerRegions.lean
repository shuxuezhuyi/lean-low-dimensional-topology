/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonStraightAngles
public import LowDimensionalTopology.Geometry.Polygon.FinitePolygonConvexity
/-! # Actual ideal corner regions of genuine native polygons -/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

-- BEGIN IDEAL CORNER REGIONS BLOCK

/-- A two-sided corner whose outside reaches the negative quadrant has precisely the positive-quadrant inside. -/
theorem polygonCorner_positive_region_of_negative_outside {I O U : Set (ℝ × ℝ)}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hU : IsOpen U)
    (hUc : Convex ℝ U) (h0U : (0 : ℝ × ℝ) ∈ U) (h0I : (0 : ℝ × ℝ) ∈ closure I)
    (hu : ∀ y ∈ U, (y ∈ I ∨ y ∈ O) ↔
      ((0 < y.1 ∧ 0 < y.2) ∨ y.1 < 0 ∨ y.2 < 0))
    (hneg : ∃ w ∈ U, w.1 < 0 ∧ w.2 < 0 ∧ w ∈ O) :
    ∀ y ∈ U, y ∈ I ↔ 0 < y.1 ∧ 0 < y.2 := by
  let A : Set (ℝ × ℝ) := U ∩ {y | 0 < y.1 ∧ 0 < y.2}
  let C : Set (ℝ × ℝ) := U ∩ {y | y.1 < 0 ∨ y.2 < 0}
  obtain ⟨w,hw,hw1,hw2,hwO⟩ := hneg
  have hAc : IsPreconnected A :=
    (hUc.inter ((convex_Ioi (0 : ℝ)).prod (convex_Ioi (0 : ℝ)))).isPreconnected
  have hCc : IsPreconnected C := by
    have h1 : Convex ℝ (U ∩ {y : ℝ × ℝ | y.1 < 0}) :=
      hUc.inter ((convex_Iio (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ))
    have h2 : Convex ℝ (U ∩ {y : ℝ × ℝ | y.2 < 0}) :=
      hUc.inter ((convex_Iio (0 : ℝ)).linear_preimage (LinearMap.snd ℝ ℝ ℝ))
    have he : C = (U ∩ {y : ℝ × ℝ | y.1 < 0}) ∪ (U ∩ {y : ℝ × ℝ | y.2 < 0}) := by
      ext y
      change (y ∈ U ∧ (y.1 < 0 ∨ y.2 < 0)) ↔ _
      simp only [mem_union,mem_inter_iff,mem_ofPred_eq]
      tauto
    rw [he]
    exact h1.isPreconnected.union w ⟨hw,hw1⟩ ⟨hw,hw2⟩ h2.isPreconnected
  have hAsub : A ⊆ I ∪ O := by
    intro y hy
    exact (hu y hy.1).mpr (Or.inl hy.2)
  have hCsub : C ⊆ I ∪ O := by
    intro y hy
    exact (hu y hy.1).mpr (Or.inr hy.2)
  have hCO : C ⊆ O := hCc.subset_right_of_subset_union hI hO hd hCsub
    ⟨w,⟨hw,Or.inl hw1⟩,hwO⟩
  have hAI : A ⊆ I := by
    rcases hAc.subset_or_subset hI hO hd hAsub with h | h
    · exact h
    · obtain ⟨y,hyU,hyI⟩ := mem_closure_iff.mp h0I U hU h0U
      rcases (hu y hyU).mp (Or.inl hyI) with hpos | hneg
      · exact (Set.disjoint_left.mp hd hyI (h ⟨hyU,hpos⟩)).elim
      · exact (Set.disjoint_left.mp hd hyI (hCO ⟨hyU,hneg⟩)).elim
  intro y hy
  constructor
  · intro hyI
    rcases (hu y hy).mp (Or.inl hyI) with hpos | hneg
    · exact hpos
    · exact (Set.disjoint_left.mp hd hyI (hCO ⟨hy,hneg⟩)).elim
  · intro hypos
    exact hAI ⟨hy,hypos⟩

/-- The two actual positive coordinate rays meeting at a corner. -/
def polygonCornerAxes : Set (ℝ × ℝ) :=
  {y | (y.1 = 0 ∧ 0 ≤ y.2) ∨ (0 ≤ y.1 ∧ y.2 = 0)}

theorem polygonCorner_segment_horizontal (y : ℝ × ℝ) :
    y ∈ segment ℝ (0 : ℝ × ℝ) (1,0) ↔ y.1 ∈ Icc (0 : ℝ) 1 ∧ y.2 = 0 := by
  have ht (t : ℝ) : AffineMap.lineMap (0 : ℝ × ℝ) (1,0) t = (t,0) := by
    ext <;> simp [AffineMap.lineMap_apply]
  rw [segment_eq_image_lineMap]
  simp_rw [mem_image,ht]
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨ht,rfl⟩
  · rintro ⟨hy,he⟩
    exact ⟨y.1,hy,Prod.ext rfl he.symm⟩

theorem polygonCorner_segment_vertical (y : ℝ × ℝ) :
    y ∈ segment ℝ (0 : ℝ × ℝ) (0,1) ↔ y.1 = 0 ∧ y.2 ∈ Icc (0 : ℝ) 1 := by
  have ht (t : ℝ) : AffineMap.lineMap (0 : ℝ × ℝ) (0,1) t = (0,t) := by
    ext <;> simp [AffineMap.lineMap_apply]
  rw [segment_eq_image_lineMap]
  simp_rw [mem_image,ht]
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨rfl,ht⟩
  · rintro ⟨he,hy⟩
    exact ⟨y.2,hy,Prod.ext he.symm rfl⟩

/-- Two true unit incident segments have exactly the two positive-axis boundary germ. -/
theorem polygonCornerAxes_segment_germ :
    ∀ᶠ y in 𝓝 (0 : ℝ × ℝ),
      y ∈ segment ℝ (0 : ℝ × ℝ) (1,0) ∪ segment ℝ (0 : ℝ × ℝ) (0,1) ↔
        y ∈ polygonCornerAxes := by
  have h1 : ∀ᶠ y in 𝓝 (0 : ℝ × ℝ), y.1 < 1 :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds (by norm_num)
  have h2 : ∀ᶠ y in 𝓝 (0 : ℝ × ℝ), y.2 < 1 :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds (by norm_num)
  filter_upwards [h1,h2] with y hy1 hy2
  rw [mem_union,polygonCorner_segment_horizontal,polygonCorner_segment_vertical]
  change ((0 ≤ y.1 ∧ y.1 ≤ 1) ∧ y.2 = 0) ∨ (y.1 = 0 ∧ (0 ≤ y.2 ∧ y.2 ≤ 1)) ↔ _
  change _ ↔ (y.1 = 0 ∧ 0 ≤ y.2) ∨ (0 ≤ y.1 ∧ y.2 = 0)
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨h.1.1,h.2⟩
    · exact Or.inl ⟨h.1,h.2.1⟩
  · rintro (h | h)
    · exact Or.inr ⟨h.1,h.2,hy2.le⟩
    · exact Or.inl ⟨⟨h.1,hy1.le⟩,h.2⟩

/-- The true corner-axis complement is precisely its minor positive quadrant and major outside. -/
theorem polygonCornerAxes_compl (y : ℝ × ℝ) :
    y ∉ polygonCornerAxes ↔ (0 < y.1 ∧ 0 < y.2) ∨ y.1 < 0 ∨ y.2 < 0 := by
  constructor
  · intro hy
    by_cases h1 : y.1 < 0
    · exact Or.inr (Or.inl h1)
    by_cases h2 : y.2 < 0
    · exact Or.inr (Or.inr h2)
    have hn1 : 0 ≤ y.1 := le_of_not_gt h1
    have hn2 : 0 ≤ y.2 := le_of_not_gt h2
    have he1 : y.1 ≠ 0 := fun h => hy (Or.inl ⟨h,hn2⟩)
    have he2 : y.2 ≠ 0 := fun h => hy (Or.inr ⟨hn1,h⟩)
    exact Or.inl ⟨lt_of_le_of_ne hn1 he1.symm,lt_of_le_of_ne hn2 he2.symm⟩
  · rintro (h | h | h) haxis
    · rcases haxis with ha | ha
      · linarith [h.1,ha.1]
      · linarith [h.2,ha.2]
    · rcases haxis with ha | ha
      · linarith [ha.1]
      · linarith [ha.1]
    · rcases haxis with ha | ha
      · linarith [ha.2]
      · linarith [ha.2]

/-- Genuine incident edges give the actual positive-axis boundary germ in any true corner coordinates. -/
theorem polygonalCircle_positive_axes_germ
    (J : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle) (i : ZMod J.n)
    (F : LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane ≃ᵃ[ℝ] ℝ × ℝ)
    (h0 : F (J.vertex i) = 0) (hb : F (J.vertex (i-1)) = (1,0))
    (hc : F (J.vertex (i+1)) = (0,1)) :
    ∀ᶠ y in 𝓝 (0 : ℝ × ℝ), y ∈ F '' J.carrier ↔ y ∈ polygonCornerAxes := by
  let h : LeanEval.Topology.ClassificationOfSurfaces.Moise.Plane ≃ₜ ℝ × ℝ :=
    { toEquiv := F.toEquiv
      continuous_toFun := F.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := F.symm.toAffineMap.continuous_of_finiteDimensional }
  have hseg (j : ZMod J.n) : F '' J.edgeSegment j =
      segment ℝ (F (J.vertex j)) (F (J.vertex (j+1))) :=
    image_segment ℝ F.toAffineMap _ _
  have hfull : F '' (J.edgeSegment i ∪ J.edgeSegment (i-1)) =
      segment ℝ (0 : ℝ × ℝ) (1,0) ∪ segment ℝ (0 : ℝ × ℝ) (0,1) := by
    rw [image_union,hseg,hseg,sub_add_cancel,h0,hb,hc,segment_symm ℝ (1,0) 0,union_comm]
  obtain ⟨r,hr,_,_,hsep⟩ := J.exists_featureRadius
  have hsep' : ∀ k j : ZMod J.n, k ≠ j → k ≠ j+1 →
      ∀ y ∈ J.edgeSegment j, r < dist (J.vertex k) y := by
    intro k j hkj hkjn y hy
    have hh := hsep k j hkj hkjn y hy
    linarith
  have hball := J.ball_inter_carrier_eq_incident_edges hsep' i
  have hnear : ∀ᶠ y in 𝓝 (F (J.vertex i)), F.symm y ∈ Metric.ball (J.vertex i) r := by
    have hh : Metric.ball (J.vertex i) r ∈ 𝓝 (h.symm (h (J.vertex i))) := by
      simpa only [h.symm_apply_apply] using (Metric.ball_mem_nhds (J.vertex i) hr)
    exact (h.symm.continuous.tendsto _).eventually hh
  rw [h0] at hnear
  filter_upwards [hnear,polygonCornerAxes_segment_germ] with y hy hyl
  rw [← hyl,← hfull]
  constructor
  · rintro ⟨v,hv,rfl⟩
    rw [F.symm_apply_apply] at hy
    have hv' : v ∈ Metric.ball (J.vertex i) r ∩ J.carrier := ⟨hy,hv⟩
    rw [hball] at hv'
    exact ⟨v,hv'.2,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    rcases hv with hv | hv
    · exact ⟨v,mem_iUnion.mpr ⟨i,hv⟩,rfl⟩
    · exact ⟨v,mem_iUnion.mpr ⟨i-1,hv⟩,rfl⟩

/-- The two actual edges at an ideal vertex are never collinear in the closed Klein disc. -/
theorem DiscPolygon.klein_neighbors_not_collinear_of_ideal {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (hi : ‖(P.vertices i : ℂ)‖ = 1) :
    ¬ Collinear ℝ ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices ((finRotate
      n).symm i)),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))} : Set ℂ) := by
  intro hc
  have hm := P.klein_vertex_between_of_collinear i hc
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices ((finRotate n).symm i)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    exact mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
      _).norm_le_one
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    exact mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
      _).norm_le_one
  have hpn : (finRotate n).symm i ≠ finRotate n i := by
    intro h
    have hh := congrArg (finRotate n) h
    rw [Equiv.apply_symm_apply] at hh
    exact polygonSupport_next_next_ne_self P.three_le i hh.symm
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices ((finRotate n).symm
    i)) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (P.vertices_injective.ne hpn)
  have hh := (strictConvex_closedBall ℝ (0 : ℂ) 1).openSegment_subset hb hn hne hm
  rw [interior_closedBall (0 : ℂ) one_ne_zero] at hh
  have he := (norm_closedKleinCoordinate_eq_one_iff (P.vertices i)).mpr hi
  simp only [Metric.mem_ball,dist_zero_right,he,lt_self_iff_false] at hh

/-- The genuine ideal corner and its two actual neighbors form a true native finite-or-ideal triangle. -/
def DiscPolygon.idealCornerTriangle {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (hi : ‖(P.vertices i : ℂ)‖ = 1) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := P.vertices i
  b := P.vertices ((finRotate n).symm i)
  c := P.vertices (finRotate n i)
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    obtain ⟨m,t,hm,he⟩ := L.closedKlein_affine_equation
    apply P.klein_neighbors_not_collinear_of_ideal i hi
    apply polygonComplex_hyperplane_collinear m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)) hm (by simp)
    intro q hq
    have hself := (he _).mp ha
    rcases hq with hq | hq | hq
    · rw [hq,(he _).mp hb,hself]
    · rw [hq]
    · rw [hq,(he _).mp hc,hself]

/-- The existing genuine triangle coordinates as an actual real-affine equivalence. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.coordinateAffineEquiv (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : ℂ ≃ᵃ[ℝ] ℝ × ℝ :=
  (AffineEquiv.vaddConst ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.a)).symm.trans T.coordinateLinear.toAffineEquiv

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.coordinateAffineEquiv_apply (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (x : ℂ) :
    T.coordinateAffineEquiv x = T.coordinateHomeomorph x := rfl

/-- An actual adjacent-vertex triangle gives the genuine local two-positive-axis polygon boundary. -/
theorem DiscPolygon.corner_coordinate_boundary_germ {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha : T.a = P.vertices i)
    (hb : T.b = P.vertices ((finRotate n).symm i)) (hc : T.c = P.vertices (finRotate n i)) :
    ∀ᶠ y in 𝓝 (0 : ℝ × ℝ),
      y ∈ T.ambientCoordinateHomeomorph '' P.complexBoundary ↔ y ∈ polygonCornerAxes := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  let F := e.toLinearEquiv.toAffineEquiv.trans T.coordinateAffineEquiv
  have hF (j : ZMod n) : F (P.toPolygonalCircle.vertex j) =
      T.coordinate (P.vertices (P.jordanIndexEquiv.symm j)) := by
    change T.coordinateAffineEquiv (e (e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (P.vertices (P.jordanIndexEquiv.symm j))))) = _
    rw [e.apply_symm_apply,T.coordinateAffineEquiv_apply]
    rfl
  have h0 : F (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i)) = 0 := by
    rw [hF,Equiv.symm_apply_apply,← ha,T.coordinate_a]
    rfl
  have hb' : F (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n))) = (1,0) := by
    rw [hF,P.jordanIndexEquiv_sub_one,Equiv.symm_apply_apply,← hb,T.coordinate_b]
  have hc' : F (P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n))) = (0,1) := by
    rw [hF,P.jordanIndexEquiv_add_one,Equiv.symm_apply_apply,← hc,T.coordinate_c]
  have hB : F '' P.toPolygonalCircle.carrier = T.ambientCoordinateHomeomorph '' P.complexBoundary := by
    rw [← P.kleinPlaneHomeomorph_image_boundary,image_image]
    apply image_congr
    intro z _
    change T.coordinateAffineEquiv (e (e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph
      z))) =
      T.coordinateHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph z)
    rw [e.apply_symm_apply,T.coordinateAffineEquiv_apply]
  have h := polygonalCircle_positive_axes_germ P.toPolygonalCircle (P.jordanIndexEquiv i) F h0 hb' hc'
  rwa [hB] at h

/-- A different point in the true closed unit disc has strictly smaller pairing with a unit point. -/
theorem polygon_unit_inner_lt {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ ≤ 1) (hne : a ≠ b) :
    inner ℝ a b < 1 := by
  have hsq := norm_sub_sq_real a b
  have hpos : 0 < ‖a-b‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  rw [ha] at hsq
  nlinarith [norm_nonneg b]

/-- The genuine affine corner-coordinate inverse has its actual basis reconstruction everywhere. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.coordinate_inverse_reconstruction (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (q : ℝ × ℝ) :
    T.coordinateHomeomorph.symm q = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a +
      q.1 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b -
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) +
      q.2 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c - _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) := by
  let x := T.coordinateHomeomorph.symm q
  have he := T.kleinBasis.sum_repr (x-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)
  rw [Fin.sum_univ_two,T.kleinBasis_zero,T.kleinBasis_one] at he
  change (T.coordinateHomeomorph x).1 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) +
    (T.coordinateHomeomorph x).2 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) =
      x-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a at he
  have hq : T.coordinateHomeomorph x = q := T.coordinateHomeomorph.apply_symm_apply q
  rw [hq] at he
  calc
    _ = q.1 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      T.b-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) +
      q.2 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.c-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        T.a) + _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a :=
        sub_eq_iff_eq_add.mp he.symm
    _ = _ := by abel

/-- At a genuine ideal triangle corner every negative diagonal coordinate lies outside the true closed Klein disc. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.ideal_negative_coordinate_norm (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (ha : ‖(T.a : ℂ)‖ = 1) {t : ℝ} (ht : 0 < t) :
    1 < ‖T.coordinateHomeomorph.symm (-t,-t)‖ := by
  have hA : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a‖ = 1 := (norm_closedKleinCoordinate_eq_one_iff T.a).mpr ha
  have hB : inner ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.b) < 1 := polygon_unit_inner_lt hA (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
    T.b).norm_le_one
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne T.a_ne_b)
  have hC : inner ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.c) < 1 := polygon_unit_inner_lt hA (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein
    T.c).norm_le_one
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne T.c_ne_a.symm)
  have hx : 1 < inner ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) (T.coordinateHomeomorph.symm (-t,-t)) := by
    rw [T.coordinate_inverse_reconstruction]
    simp only [inner_add_right,inner_smul_right,inner_sub_right,real_inner_self_eq_norm_sq,hA,one_pow]
    nlinarith only [mul_pos ht (sub_pos.mpr hB),mul_pos ht (sub_pos.mpr hC)]
  have hmax := real_inner_le_norm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    T.a) (T.coordinateHomeomorph.symm (-t,-t))
  rw [hA,one_mul] at hmax
  exact hx.trans_le hmax

/-- A genuine ambient homeomorphism transports all actual two-sided Jordan region data. -/
theorem polygon_jordan_regions_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {I O B : Set X} (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O)
    (hu : I ∪ O = Bᶜ) (hfI : frontier I = B) (hfO : frontier O = B) :
    IsOpen (h '' I) ∧ IsOpen (h '' O) ∧ Disjoint (h '' I) (h '' O) ∧
      (h '' I) ∪ (h '' O) = (h '' B)ᶜ ∧ frontier (h '' I) = h '' B ∧ frontier (h '' O) = h '' B := by
  refine ⟨h.isOpenMap _ hI,h.isOpenMap _ hO,?_,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    exact Set.disjoint_left.mp hd hx (h.injective he ▸ hy)
  · rw [← image_union,hu,h.image_compl]
  · rw [← h.image_frontier,hfI]
  · rw [← h.image_frontier,hfO]

/-- Genuine native corner coordinates transport the actual polygon's two complementary regions. -/
theorem DiscPolygon.corner_coordinate_jordan_regions {n : ℕ} (P : DiscPolygon n) (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    IsOpen (T.ambientCoordinateHomeomorph '' P.complexInterior) ∧
    IsOpen (T.ambientCoordinateHomeomorph '' P.complexOutside) ∧
    Disjoint (T.ambientCoordinateHomeomorph '' P.complexInterior) (T.ambientCoordinateHomeomorph '' P.complexOutside) ∧
    (T.ambientCoordinateHomeomorph '' P.complexInterior) ∪ (T.ambientCoordinateHomeomorph '' P.complexOutside) =
      (T.ambientCoordinateHomeomorph '' P.complexBoundary)ᶜ ∧
    frontier (T.ambientCoordinateHomeomorph '' P.complexInterior) = T.ambientCoordinateHomeomorph '' P.complexBoundary ∧
    frontier (T.ambientCoordinateHomeomorph '' P.complexOutside) = T.ambientCoordinateHomeomorph '' P.complexBoundary := by
  have hd : Disjoint P.complexInterior P.complexOutside := by
    exact Set.disjoint_left.mpr (fun _ hx ho => hx.2 ho)
  have hu : P.complexInterior ∪ P.complexOutside = P.complexBoundaryᶜ := by
    ext z
    change (z ∈ P.complexBoundaryᶜ ∧ z ∉ P.complexOutside) ∨ z ∈ P.complexOutside ↔ _
    constructor
    · rintro (hz | hz)
      · exact hz.1
      · exact connectedComponentIn_subset _ _ hz
    · intro hz
      by_cases ho : z ∈ P.complexOutside
      · exact Or.inr ho
      · exact Or.inl ⟨hz,ho⟩
  exact polygon_jordan_regions_image T.ambientCoordinateHomeomorph P.complexInterior_isOpen
    P.complexOutside_isOpen hd hu P.frontier_complexInterior P.frontier_complexOutside

/-- Every negative diagonal near a genuine ideal corner belongs to the actual polygon exterior. -/
theorem DiscPolygon.ideal_negative_coordinate_mem_outside {n : ℕ} (P : DiscPolygon n)
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha : ‖(T.a : ℂ)‖ = 1) {t : ℝ} (ht : 0 <
      t) :
    (-t,-t) ∈ T.ambientCoordinateHomeomorph '' P.complexOutside := by
  let x := T.coordinateHomeomorph.symm (-t,-t)
  have hn : 1 < ‖x‖ := T.ideal_negative_coordinate_norm ha ht
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph x = x := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinFormula x = x
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinFormula,ite_eq_right (not_le_of_gt hn)]
  refine ⟨x,P.outer_region_subset_outside hn,?_⟩
  change T.coordinateHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph x) = (-t,-t)
  rw [hK]
  exact T.coordinateHomeomorph.apply_symm_apply _

/-- The genuine compactified closed polygon is locally convex at every actual ideal vertex. -/
theorem DiscPolygon.closedCarrier_locallyConvex_at_ideal_vertex {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (hi : ‖(P.vertices i : ℂ)‖ = 1) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ P.vertices i ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) := by
  let T := P.idealCornerTriangle i hi
  have hTa : ‖(T.a : ℂ)‖ = 1 := hi
  have hB := P.corner_coordinate_boundary_germ i T rfl rfl rfl
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp hB
  obtain ⟨hI,hO,hd,hu,hfI,_⟩ := P.corner_coordinate_jordan_regions T
  have h0B : (0 : ℝ × ℝ) ∈ T.ambientCoordinateHomeomorph '' P.complexBoundary := by
    refine ⟨(P.vertices i : ℂ),mem_image_of_mem _ (mem_iUnion.mpr ⟨i,closedModelDiscHSegment_left_mem _ _⟩),?_⟩
    rw [T.ambientCoordinateHomeomorph_closed]
    exact T.coordinate_a
  have h0I : (0 : ℝ × ℝ) ∈ closure (T.ambientCoordinateHomeomorph '' P.complexInterior) :=
    frontier_subset_closure (hfI.symm ▸ h0B)
  have hpartition : ∀ y ∈ Metric.ball (0 : ℝ × ℝ) r,
      (y ∈ T.ambientCoordinateHomeomorph '' P.complexInterior ∨
        y ∈ T.ambientCoordinateHomeomorph '' P.complexOutside) ↔
      ((0 < y.1 ∧ 0 < y.2) ∨ y.1 < 0 ∨ y.2 < 0) := by
    intro y hy
    change y ∈ (T.ambientCoordinateHomeomorph '' P.complexInterior) ∪
      (T.ambientCoordinateHomeomorph '' P.complexOutside) ↔ _
    rw [hu,mem_compl_iff]
    have hh : y ∈ T.ambientCoordinateHomeomorph '' P.complexBoundary ↔ y ∈ polygonCornerAxes := hre hy
    rw [hh,polygonCornerAxes_compl]
  have hneg : ∃ w ∈ Metric.ball (0 : ℝ × ℝ) r,
      w.1 < 0 ∧ w.2 < 0 ∧ w ∈ T.ambientCoordinateHomeomorph '' P.complexOutside := by
    refine ⟨(-(r/2),-(r/2)),?_,by linarith,by linarith,?_⟩
    · change max |(-(r/2))-0| |(-(r/2))-0| < r
      rw [sub_zero,abs_neg,abs_of_pos (by positivity : 0 < r/2),max_self]
      linarith
    · exact P.ideal_negative_coordinate_mem_outside T hTa (by linarith : 0 < r/2)
  have hinside := polygonCorner_positive_region_of_negative_outside hI hO hd Metric.isOpen_ball
    (convex_ball (0 : ℝ × ℝ) r) (Metric.mem_ball_self hr) h0I hpartition hneg
  have hIm : T.ambientCoordinateHomeomorph '' P.complexInterior =
      T.coordinateHomeomorph '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) := by
    rw [P.klein_image_interior,image_image]
    rfl
  have h0 : T.coordinateHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    i)) = 0 := T.coordinate_a
  have hg : ∀ᶠ y in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    i)), y ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior ↔
      0 < (T.coordinateHomeomorph y).1 ∧ 0 < (T.coordinateHomeomorph y).2 := by
    have hn : Metric.ball (0 : ℝ × ℝ) r ∈ 𝓝 (T.coordinateHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i))) := by
      rw [h0]
      exact Metric.ball_mem_nhds _ hr
    filter_upwards [(T.coordinateHomeomorph.continuous.tendsto _).eventually hn] with y hy
    have hh := hinside (T.coordinateHomeomorph y) hy
    rw [hIm,T.coordinateHomeomorph.injective.mem_set_image] at hh
    exact hh
  have hc : Convex ℝ {y : ℂ | 0 < (T.coordinateHomeomorph y).1 ∧ 0 < (T.coordinateHomeomorph y).2} :=
    ((convex_Ioi (0 : ℝ)).prod (convex_Ioi (0 : ℝ))).affine_preimage T.coordinateAffineEquiv.toAffineMap
  obtain ⟨U,hU,hpU,hconv⟩ := complex_convex_closure_germ hc hg
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ⁻¹' U,hU.preimage
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous,hpU,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex,image_inter_preimage,P.closedKlein_image_closedCarrier]
  exact hconv

/-- Every actual finite-or-ideal Jordan polygon with all genuine interior angles at most pi is convex. -/
theorem DiscPolygon.isConvex_of_angles_le_pi {n : ℕ} (P : DiscPolygon n)
    (ha : ∀ i : Fin n, P.angle i ≤ Real.pi) : P.IsConvex := by
  apply P.isConvex_of_vertices_locallyConvex
  intro i
  by_cases hi : ‖(P.vertices i : ℂ)‖ < 1
  · let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) hi
    exact P.closedCarrier_locallyConvex_at_finite_vertex i z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ _).symm (ha i)
  · exact P.closedCarrier_locallyConvex_at_ideal_vertex i (le_antisymm (P.vertices i).norm_le_one (le_of_not_gt hi))

end
end LowDimensionalTopology.Geometry.Polygon
