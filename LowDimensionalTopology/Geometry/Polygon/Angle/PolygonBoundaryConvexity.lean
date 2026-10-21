/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.DiscPolygonLocalConvexity
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonAngles
/-! # Genuine local convexity at finite polygon corners and side interiors

The actual angle convention selects the genuine minor interior germ precisely
when the interior angle is at most pi at a nonstraight finite corner. This
implies local convexity of the actual compactified closed polygon there.
Straight finite corners and relative-interior side points are also covered via
the genuine local affine-line boundary and both actual complementary regions.
Ideal corners and the complete angle criterion remain separate obligations.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Equal local set germs have equal closure germs on a smaller genuine convex neighborhood. -/
theorem complex_convex_closure_germ {S T : Set ℂ} {x : ℂ}
    (hT : Convex ℝ T) (he : ∀ᶠ y in 𝓝 x, y ∈ S ↔ y ∈ T) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ Convex ℝ (closure S ∩ U) := by
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp he
  have heq : S ∩ Metric.ball x r = T ∩ Metric.ball x r := by
    ext y
    constructor
    · intro hy
      exact ⟨(hre hy.2).mp hy.1,hy.2⟩
    · intro hy
      exact ⟨(hre hy.2).mpr hy.1,hy.2⟩
  have hclosure : closure S ∩ Metric.ball x r = closure T ∩ Metric.ball x r := by
    apply subset_antisymm
    · intro y hy
      refine ⟨?_,hy.2⟩
      have h := Metric.isOpen_ball.closure_inter hy
      rw [heq] at h
      exact closure_mono inter_subset_left h
    · intro y hy
      refine ⟨?_,hy.2⟩
      have h := Metric.isOpen_ball.closure_inter hy
      rw [← heq] at h
      exact closure_mono inter_subset_left h
  refine ⟨Metric.ball x r,Metric.isOpen_ball,Metric.mem_ball_self hr,?_⟩
  rw [hclosure]
  exact hT.closure.inter (convex_ball x r)

/-- At a genuine finite nonstraight corner, angle at most pi exactly selects the actual minor germ. -/
theorem DiscPolygon.angle_le_pi_iff_hasMinor_of_proper {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine) :
    P.angle i ≤ Real.pi ↔ P.HasMinorInteriorAt i z hz := by
  have hlt : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz) < Real.pi := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_lt_pi _ _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.different_supports_iff _ _).mp hne)
  rw [P.angle_of_finite i z hz]
  by_cases hm : P.HasMinorInteriorAt i z hz
  · simp only [hm,ite_true,iff_true]
    exact hlt.le
  · simp only [hm,ite_false,iff_false]
    linarith

/-- A true minor finite corner makes the actual compactified polygon locally convex there. -/
theorem DiscPolygon.closedCarrier_locallyConvex_of_minor {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine)
    (hm : P.HasMinorInteriorAt i z hz) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ P.vertices i ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) := by
  let T := _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (P.cornerRayPrev i z
    hz) (P.cornerRayNext i z hz)
  have hT : Convex ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' T) :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior_hConvex _ _ hne)
  obtain ⟨V,hVe,hVo,hzV⟩ := mem_nhds_iff.mp hm
  have hK : ∀ᶠ y in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z),
      y ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior ↔ y ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' T := by
    have hU : IsOpen (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
      V) := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap V hVo
    filter_upwards [hU.mem_nhds (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      hzV)] with y hy
    obtain ⟨w,hw,rfl⟩ := hy
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.mem_set_image,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.mem_set_image]
    exact hVe hw
  obtain ⟨U,hU,hzU,hconv⟩ := complex_convex_closure_germ hT hK
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ⁻¹' U,hU.preimage
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous,?_,?_⟩
  · rw [hz]
    exact hzU
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex,image_inter_preimage,P.closedKlein_image_closedCarrier]
    exact hconv

/-- The actual angle bound implies genuine local convexity at every nonstraight finite corner. -/
theorem DiscPolygon.closedCarrier_locallyConvex_of_angle_le_pi_proper {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine)
    (ha : P.angle i ≤ Real.pi) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ P.vertices i ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) :=
  P.closedCarrier_locallyConvex_of_minor i z hz hne
    ((P.angle_le_pi_iff_hasMinor_of_proper i z hz hne).mp ha)


/-- A genuine two-sided Jordan boundary which is locally a line has a locally convex closed inside. -/
theorem complex_jordan_linear_boundary_locallyConvex {I O B : Set ℂ} {x : ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : I ∪ O = Bᶜ)
    (hxI : x ∈ frontier I) (hxO : x ∈ frontier O) (f : ℂ →ᵃ[ℝ] ℝ)
    (he : ∀ᶠ y in 𝓝 x, y ∈ B ↔ f y = 0) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ Convex ℝ (closure I ∩ U) := by
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp he
  let A : Set ℂ := Metric.ball x r ∩ {y | 0 < f y}
  let C : Set ℂ := Metric.ball x r ∩ {y | f y < 0}
  have hAc : IsPreconnected A :=
    ((convex_ball x r).inter ((convex_Ioi (0 : ℝ)).affine_preimage f)).isPreconnected
  have hCc : IsPreconnected C :=
    ((convex_ball x r).inter ((convex_Iio (0 : ℝ)).affine_preimage f)).isPreconnected
  have hmem (y : ℂ) (hy : y ∈ Metric.ball x r) :
      (y ∈ I ∨ y ∈ O) ↔ f y ≠ 0 := by
    change y ∈ I ∪ O ↔ _
    have hh : y ∈ B ↔ f y = 0 := hre hy
    rw [hu,mem_compl_iff,hh]
  have hAsub : A ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_gt hy.2)
  have hCsub : C ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_lt hy.2)
  have hexI : ∃ y ∈ Metric.ball x r, y ∈ I := by
    exact mem_closure_iff.mp (frontier_subset_closure hxI) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hexO : ∃ y ∈ Metric.ball x r, y ∈ O := by
    exact mem_closure_iff.mp (frontier_subset_closure hxO) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hnotBothI : ¬ (A ⊆ I ∧ C ⊆ I) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyo⟩ := hexO
    have hn := (hmem y hy).mp (Or.inr hyo)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd (hc ⟨hy,hneg⟩) hyo
    · exact Set.disjoint_left.mp hd (ha ⟨hy,hpos⟩) hyo
  have hnotBothO : ¬ (A ⊆ O ∧ C ⊆ O) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyi⟩ := hexI
    have hn := (hmem y hy).mp (Or.inl hyi)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd hyi (hc ⟨hy,hneg⟩)
    · exact Set.disjoint_left.mp hd hyi (ha ⟨hy,hpos⟩)
  rcases hAc.subset_or_subset hI hO hd hAsub with ha | ha
  · have hc : C ⊆ O := (hCc.subset_or_subset hI hO hd hCsub).resolve_left
      (fun hi => hnotBothI ⟨ha,hi⟩)
    apply complex_convex_closure_germ ((convex_Ioi (0 : ℝ)).affine_preimage f)
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    change y ∈ I ↔ 0 < f y
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact (Set.disjoint_left.mp hd hi (hc ⟨hy,hneg⟩)).elim
      · exact hpos
    · intro hypos
      exact ha ⟨hy,hypos⟩
  · have hc : C ⊆ I := (hCc.subset_or_subset hI hO hd hCsub).resolve_right
      (fun ho => hnotBothO ⟨ha,ho⟩)
    apply complex_convex_closure_germ ((convex_Iio (0 : ℝ)).affine_preimage f)
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    change y ∈ I ↔ f y < 0
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact hneg
      · exact (Set.disjoint_left.mp hd hi (ha ⟨hy,hpos⟩)).elim
    · intro hyneg
      exact hc ⟨hy,hyneg⟩

/-- Actual real-affine line coordinate normal to the genuine line through two complex points. -/
def polygonComplexLineEquation (a b : ℂ) : ℂ →ᵃ[ℝ] ℝ :=
  (Complex.imLm.comp ((b-a)⁻¹ • (LinearMap.id : ℂ →ₗ[ℝ] ℂ))).toAffineMap.comp
    (AffineEquiv.constVAdd ℝ ℂ (-a)).toAffineMap

theorem polygonComplexLineEquation_apply (a b z : ℂ) :
    polygonComplexLineEquation a b z = ((z-a)/(b-a)).im := by
  change ((b-a)⁻¹*(-a+z)).im = _
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- True affine coordinates identify an actual complex segment, including its endpoints. -/
theorem polygonComplex_mem_segment_iff {a b z : ℂ} (hab : a ≠ b) :
    z ∈ segment ℝ a b ↔ ((z-a)/(b-a)).im = 0 ∧ ((z-a)/(b-a)).re ∈ Icc (0 : ℝ) 1 := by
  have hv : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    have he : ((AffineMap.lineMap a b t)-a)/(b-a) = (t : ℂ) := by
      rw [AffineMap.lineMap_apply,Complex.real_smul]
      change (((t : ℂ)*(b-a)+a)-a)/(b-a) = (t : ℂ)
      field_simp [hv]
      ring
    rw [he]
    exact ⟨Complex.ofReal_im t,by simpa using ht⟩
  · rintro ⟨h0,ht⟩
    let t := ((z-a)/(b-a)).re
    have he : (t : ℂ) = (z-a)/(b-a) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using h0.symm
    rw [segment_eq_image_lineMap]
    refine ⟨t,ht,?_⟩
    rw [AffineMap.lineMap_apply,Complex.real_smul]
    change (t : ℂ)*(b-a)+a = z
    rw [he]
    field_simp [hv]
    ring

/-- Strict parameter coordinates identify the actual relative-interior segment. -/
theorem polygonComplex_mem_openSegment_iff {a b z : ℂ} (hab : a ≠ b) :
    z ∈ openSegment ℝ a b ↔ ((z-a)/(b-a)).im = 0 ∧ ((z-a)/(b-a)).re ∈ Ioo (0 : ℝ) 1 := by
  have hv : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  constructor
  · intro hz
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    have he : ((AffineMap.lineMap a b t)-a)/(b-a) = (t : ℂ) := by
      rw [AffineMap.lineMap_apply,Complex.real_smul]
      change (((t : ℂ)*(b-a)+a)-a)/(b-a) = (t : ℂ)
      field_simp [hv]
      ring
    rw [he]
    exact ⟨Complex.ofReal_im t,by simpa using ht⟩
  · rintro ⟨h0,ht⟩
    let t := ((z-a)/(b-a)).re
    have he : (t : ℂ) = (z-a)/(b-a) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using h0.symm
    rw [openSegment_eq_image_lineMap]
    refine ⟨t,ht,?_⟩
    rw [AffineMap.lineMap_apply,Complex.real_smul]
    change (t : ℂ)*(b-a)+a = z
    rw [he]
    field_simp [hv]
    ring

/-- Near a point in a segment's genuine relative interior, that segment is exactly its full supporting line. -/
theorem polygonComplex_segment_line_germ {a b x : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) :
    ∀ᶠ y in 𝓝 x, y ∈ segment ℝ a b ↔ polygonComplexLineEquation a b y = 0 := by
  have hx' := ((polygonComplex_mem_openSegment_iff hab).mp hx).2
  have hc : Continuous (fun y : ℂ => ((y-a)/(b-a)).re) := by fun_prop
  filter_upwards [(isOpen_Ioo.preimage hc).mem_nhds hx'] with y hy
  rw [polygonComplex_mem_segment_iff hab,polygonComplexLineEquation_apply]
  exact and_iff_left ⟨hy.1.le,hy.2.le⟩

/-- Every actual PL edge is its full supporting affine line locally at its relative-interior points. -/
theorem polygonalCircle_complex_carrier_line_germ
    (J : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle) (i : ZMod J.n)
    {x : ℂ} (hx : x ∈ openSegment ℝ
      (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv (J.vertex i))
      (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv (J.vertex (i+1)))) :
    ∀ᶠ y in 𝓝 x,
      y ∈ LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv '' J.carrier ↔
        polygonComplexLineEquation
          (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv (J.vertex i))
          (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv (J.vertex (i+1))) y = 0 := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  have hseg : e '' J.edgeSegment i = segment ℝ (e (J.vertex i)) (e (J.vertex (i+1))) :=
    image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  have hopen : e '' openSegment ℝ (J.vertex i) (J.vertex (i+1)) =
      openSegment ℝ (e (J.vertex i)) (e (J.vertex (i+1))) :=
    image_openSegment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  obtain ⟨u,hu,rfl⟩ := hopen ▸ hx
  obtain ⟨r,hr,hball⟩ := J.exists_ball_inter_carrier_subset_edgeSegment hu
  have hnear : ∀ᶠ y in 𝓝 (e u), e.symm y ∈ Metric.ball u r := by
    have hh : Metric.ball u r ∈ 𝓝 (e.symm (e u)) := by
      simpa only [e.symm_apply_apply] using (Metric.ball_mem_nhds u hr)
    exact (e.symm.continuous.tendsto (e u)).eventually hh
  have hline := polygonComplex_segment_line_germ
    (e.injective.ne (J.adjacent_ne i)) (by rw [← hopen]; exact mem_image_of_mem e hu)
  filter_upwards [hnear,hline] with y hy hyl
  rw [← hyl,← hseg]
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨v,hball ⟨?_,hv⟩,rfl⟩
    change e.symm (e v) ∈ Metric.ball u r at hy
    simpa only [e.symm_apply_apply] using hy
  · rintro ⟨v,hv,rfl⟩
    exact ⟨v,mem_iUnion.mpr ⟨i,hv⟩,rfl⟩

/-- The actual entire native boundary commutes with the genuine ambient Klein homeomorphism. -/
theorem DiscPolygon.ambientKlein_image_boundary {n : ℕ} (P : DiscPolygon n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' P.complexBoundary = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary := by
  rw [DiscPolygon.complexBoundary,image_image]
  apply image_congr
  intro p _
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed p

/-- The actual complementary regions in Klein coordinates have the same true whole frontier. -/
theorem DiscPolygon.klein_jordan_regions {n : ℕ} (P : DiscPolygon n) :
    IsOpen (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) ∧
    IsOpen (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' P.complexOutside) ∧
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
      P.interior) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' P.complexOutside) ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
      P.interior) ∪ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' P.complexOutside) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary)ᶜ ∧
    frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
      P.interior) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary ∧
    frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' P.complexOutside) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary := by
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
  rw [P.klein_image_interior]
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.isOpenMap _ P.complexInterior_isOpen,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.isOpenMap _ P.complexOutside_isOpen,?_,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    exact hu.2 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.injective he ▸ hv)
  · rw [← image_union,hu,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_compl,P.ambientKlein_image_boundary]
  · rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_frontier,P.frontier_complexInterior,P.ambientKlein_image_boundary]
  · rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_frontier,P.frontier_complexOutside,P.ambientKlein_image_boundary]

/-- Any true local affine-line boundary of a native polygon makes its actual closed polygon locally convex. -/
theorem DiscPolygon.closedCarrier_locallyConvex_of_line_germ {n : ℕ} (P : DiscPolygon n)
    (p : 𝕔𝔻) (hp : p ∈ P.boundary) (f : ℂ →ᵃ[ℝ] ℝ)
    (he : ∀ᶠ y in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p),
      y ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary ↔ f y = 0) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ p ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) := by
  obtain ⟨hI,hO,hd,hu,hfI,hfO⟩ := P.klein_jordan_regions
  have hpI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) := by
    rw [hfI]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hp
  have hpO : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' P.complexOutside) := by
    rw [hfO]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hp
  obtain ⟨U,hU,hpU,hconv⟩ := complex_jordan_linear_boundary_locallyConvex hI hO hd hu hpI hpO f he
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ⁻¹' U,hU.preimage
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous,hpU,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex,image_inter_preimage,P.closedKlein_image_closedCarrier]
  exact hconv

/-- The actual Klein boundary has its genuine edge-line germ at each relative-interior edge point. -/
theorem DiscPolygon.klein_boundary_line_germ_edge {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) {x : ℂ}
    (hx : x ∈ openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)))) :
    ∀ᶠ y in 𝓝 x, y ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary ↔
      polygonComplexLineEquation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        i))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))) y = 0 := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  let J := P.toPolygonalCircle
  let j := P.jordanIndexEquiv i
  have hj : e (J.vertex j) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i) := by
    change e (e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i))))) = _
    rw [Equiv.symm_apply_apply,e.apply_symm_apply]
  have hjn : e (J.vertex (j+(1 : ZMod n))) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)) := by
    change e (e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      (P.jordanIndexEquiv.symm (j+(1 : ZMod n)))))) = _
    rw [P.jordanIndexEquiv_add_one,show P.jordanIndexEquiv.symm j = i from P.jordanIndexEquiv.symm_apply_apply i,
      e.apply_symm_apply]
  have hb : e '' J.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary := by
    rw [P.toPolygonalCircle_carrier,image_image]
    apply image_congr
    intro q _
    exact e.apply_symm_apply _
  have hx' : x ∈ openSegment ℝ (e (J.vertex j)) (e (J.vertex (j+(1 : ZMod n)))) := by rwa [hj,hjn]
  have h := polygonalCircle_complex_carrier_line_germ J j hx'
  change ∀ᶠ y in 𝓝 x, y ∈ e '' J.carrier ↔
    polygonComplexLineEquation (e (J.vertex j)) (e (J.vertex (j+(1 : ZMod n)))) y = 0 at h
  rw [← hb]
  simpa only [hj,hjn] using h

/-- The genuine closed polygon is locally convex at every actual relative-interior point of a side. -/
theorem DiscPolygon.closedCarrier_locallyConvex_at_edge_interior {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (p : 𝕔𝔻)
    (hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ openSegment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)))) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ p ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) := by
  have hpseg : p ∈ discPolygonEdge P.vertices i := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
    rw [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact openSegment_subset_segment ℝ _ _ hp
  exact P.closedCarrier_locallyConvex_of_line_germ p (mem_iUnion.mpr ⟨i,hpseg⟩)
    (polygonComplexLineEquation _ _) (P.klein_boundary_line_germ_edge i hp)

/-- Splitting an actual segment at one of its own points recovers precisely the whole segment. -/
theorem polygon_segment_split {a b c : ℂ} (hb : b ∈ segment ℝ a c) :
    segment ℝ a b ∪ segment ℝ b c = segment ℝ a c := by
  apply subset_antisymm
  · exact union_subset
      ((convex_segment a c).segment_subset (left_mem_segment ℝ a c) hb)
      ((convex_segment a c).segment_subset hb (right_mem_segment ℝ a c))
  · apply (openSegment_subset_iff_segment_subset
      (show a ∈ segment ℝ a b ∪ segment ℝ b c from Or.inl (left_mem_segment ℝ a b))
      (show c ∈ segment ℝ a b ∪ segment ℝ b c from Or.inr (right_mem_segment ℝ b c))).mp
    have hb' : b ∈ Set.range (AffineMap.lineMap a c : ℝ → ℂ) := by
      rw [segment_eq_image_lineMap] at hb
      exact image_subset_range _ _ hb
    intro z hz
    rcases openSegment_subset_union a c hb' hz with he | he
    · subst z
      exact Or.inl (right_mem_segment ℝ a b)
    · rcases he with he | he
      · exact Or.inl (openSegment_subset_segment ℝ a b he)
      · exact Or.inr (openSegment_subset_segment ℝ b c he)

/-- A collinear genuine polygon vertex lies strictly between its two neighbors; backtracking is excluded. -/
theorem polygonalCircle_collinear_vertex_between
    (J : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle) (i : ZMod J.n)
    (hc : Collinear ℝ ({J.vertex (i-1),J.vertex i,J.vertex (i+1)} : Set _)) :
    J.vertex i ∈ openSegment ℝ (J.vertex (i-1)) (J.vertex (i+1)) := by
  have hprev : J.vertex (i-1) ≠ J.vertex i := by
    simpa only [sub_add_cancel] using J.adjacent_ne (i-1)
  have hnext : J.vertex (i+1) ≠ J.vertex i := (J.adjacent_ne i).symm
  have hinter : segment ℝ (J.vertex (i-1)) (J.vertex i) ∩
      segment ℝ (J.vertex i) (J.vertex (i+1)) = {J.vertex i} := by
    simpa only [sub_add_cancel,show i-1+2 = i+1 by ring] using J.consecutive_inter (i-1)
  apply mem_openSegment_of_ne_left_right hprev hnext
  rcases hc.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact h.mem_segment
  · have hm : J.vertex (i+1) ∈ segment ℝ (J.vertex (i-1)) (J.vertex i) := by
      rw [segment_symm]
      exact h.mem_segment
    have he := hinter ▸ (show J.vertex (i+1) ∈ segment ℝ (J.vertex (i-1)) (J.vertex i) ∩
        segment ℝ (J.vertex i) (J.vertex (i+1)) from ⟨hm,right_mem_segment ℝ _ _⟩)
    exact (hnext he).elim
  · have hm : J.vertex (i-1) ∈ segment ℝ (J.vertex i) (J.vertex (i+1)) := by
      rw [segment_symm]
      exact h.mem_segment
    have he := hinter ▸ (show J.vertex (i-1) ∈ segment ℝ (J.vertex (i-1)) (J.vertex i) ∩
        segment ℝ (J.vertex i) (J.vertex (i+1)) from ⟨left_mem_segment ℝ _ _,hm⟩)
    exact (hprev he).elim

/-- The genuine PL boundary has the full line germ at a collinear straight vertex. -/
theorem polygonalCircle_complex_carrier_straight_germ
    (J : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle) (i : ZMod J.n)
    (hc : Collinear ℝ ({J.vertex (i-1),J.vertex i,J.vertex (i+1)} : Set _)) :
    ∀ᶠ y in 𝓝 (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv (J.vertex i)),
      y ∈ LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv '' J.carrier ↔
        polygonComplexLineEquation
          (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv (J.vertex (i-1)))
          (LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv (J.vertex (i+1))) y = 0 := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  have hmid := polygonalCircle_collinear_vertex_between J i hc
  have hopen : e '' openSegment ℝ (J.vertex (i-1)) (J.vertex (i+1)) =
      openSegment ℝ (e (J.vertex (i-1))) (e (J.vertex (i+1))) :=
    image_openSegment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
  have hmid' : e (J.vertex i) ∈ openSegment ℝ (e (J.vertex (i-1))) (e (J.vertex (i+1))) := by
    rw [← hopen]
    exact mem_image_of_mem e hmid
  have hbc : e (J.vertex (i-1)) ≠ e (J.vertex (i+1)) := by
    intro he
    rw [← he,openSegment_same] at hmid'
    apply J.adjacent_ne (i-1)
    have h := e.injective hmid'
    simpa only [sub_add_cancel] using h.symm
  have hfull : e '' (J.edgeSegment i ∪ J.edgeSegment (i-1)) =
      segment ℝ (e (J.vertex (i-1))) (e (J.vertex (i+1))) := by
    have hseg (j : ZMod J.n) : e '' J.edgeSegment j =
        segment ℝ (e (J.vertex j)) (e (J.vertex (j+1))) :=
      image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _
    rw [image_union,hseg,hseg,sub_add_cancel,union_comm]
    exact polygon_segment_split (openSegment_subset_segment ℝ _ _ hmid')
  obtain ⟨r,hr,_,_,hsep⟩ := J.exists_featureRadius
  have hsep' : ∀ k j : ZMod J.n, k ≠ j → k ≠ j+1 →
      ∀ y ∈ J.edgeSegment j, r < dist (J.vertex k) y := by
    intro k j hkj hkjn y hy
    have h := hsep k j hkj hkjn y hy
    linarith
  have hball := J.ball_inter_carrier_eq_incident_edges hsep' i
  have hnear : ∀ᶠ y in 𝓝 (e (J.vertex i)), e.symm y ∈ Metric.ball (J.vertex i) r := by
    have hh : Metric.ball (J.vertex i) r ∈ 𝓝 (e.symm (e (J.vertex i))) := by
      simpa only [e.symm_apply_apply] using (Metric.ball_mem_nhds (J.vertex i) hr)
    exact (e.symm.continuous.tendsto _).eventually hh
  have hline := polygonComplex_segment_line_germ hbc hmid'
  filter_upwards [hnear,hline] with y hy hyl
  rw [← hyl,← hfull]
  constructor
  · rintro ⟨v,hv,rfl⟩
    change e.symm (e v) ∈ Metric.ball (J.vertex i) r at hy
    rw [e.symm_apply_apply] at hy
    have hv' : v ∈ Metric.ball (J.vertex i) r ∩ J.carrier := ⟨hy,hv⟩
    rw [hball] at hv'
    exact ⟨v,hv'.2,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    rcases hv with hv | hv
    · exact ⟨v,mem_iUnion.mpr ⟨i,hv⟩,rfl⟩
    · exact ⟨v,mem_iUnion.mpr ⟨i-1,hv⟩,rfl⟩

/-- Real-affine maps carry genuine collinear sets to collinear sets. -/
theorem polygon_collinear_affine_image {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E →ᵃ[ℝ] F) {S : Set E} (hS : Collinear ℝ S) :
    Collinear ℝ (f '' S) := by
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h,image_empty]
    exact collinear_empty ℝ F
  · obtain ⟨a,ha⟩ := h
    obtain ⟨v,hv⟩ := (collinear_iff_of_mem ha).mp hS
    apply (collinear_iff_of_mem (mem_image_of_mem f ha)).mpr
    refine ⟨f.linear v,?_⟩
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨r,hr⟩ := hv x hx
    refine ⟨r,?_⟩
    rw [hr,f.map_vadd,map_smul]

/-- An actual affine hyperplane in the real complex plane is a genuine collinear set. -/
theorem polygonComplex_hyperplane_collinear {S : Set ℂ} (n a : ℂ) (hn : n ≠ 0)
    (ha : a ∈ S) (hS : ∀ z ∈ S, inner ℝ n z = inner ℝ n a) : Collinear ℝ S := by
  apply (collinear_iff_of_mem ha).mpr
  refine ⟨Complex.I*n,?_⟩
  intro z hz
  have hi : inner ℝ n (z-a) = 0 := by rw [inner_sub_right,hS z hz,sub_self]
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] at hi
  have hv : Complex.I*n ≠ 0 := mul_ne_zero Complex.I_ne_zero hn
  have hq : ((z-a)/(Complex.I*n)).im = 0 := by
    rw [Complex.div_im]
    have hnum : (z-a).im*(Complex.I*n).re-(z-a).re*(Complex.I*n).im = 0 := by
      simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,zero_sub]
      linarith only [hi]
    rw [← sub_div,hnum,zero_div]
  refine ⟨((z-a)/(Complex.I*n)).re,?_⟩
  have he : ((((z-a)/(Complex.I*n)).re : ℝ) : ℂ) = (z-a)/(Complex.I*n) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hq.symm
  change z = (((z-a)/(Complex.I*n)).re : ℂ)*(Complex.I*n)+a
  rw [he,div_mul_cancel₀ _ hv,sub_add_cancel]

/-- The true adjacent finite rays on the same support put all three actual Klein vertices on one line. -/
theorem DiscPolygon.klein_neighbors_collinear_of_same_support {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine) :
    Collinear ℝ ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices ((finRotate
      n).symm i)),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))} : Set ℂ) := by
  let R := P.cornerRayPrev i z hz
  let S := P.cornerRayNext i z hz
  let L := R.supportLine
  have hprev : P.vertices ((finRotate n).symm i) ∈ L.closedCarrier := by
    have h := discRayTowardClosed_endpoint_mem z (P.vertices ((finRotate n).symm i))
      (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ P.vertices ((finRotate n).symm i) from by
        rw [← hz]; exact fun he => P.prev_ne_self i (P.vertices_injective he).symm)
    exact closure_mono (image_mono R.subset_support) h
  have hself : P.vertices i ∈ L.closedCarrier := by
    rw [hz]
    exact subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (R.subset_support R.start_mem))
  have hnext : P.vertices (finRotate n i) ∈ L.closedCarrier := by
    have h := discRayTowardClosed_endpoint_mem z (P.vertices (finRotate n i))
      (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ P.vertices (finRotate n i) from by
        rw [← hz]; exact fun he => P.next_ne_self i (P.vertices_injective he).symm)
    have hh : P.vertices (finRotate n i) ∈ S.supportLine.closedCarrier :=
      closure_mono (image_mono S.subset_support) h
    change P.vertices (finRotate n i) ∈ R.supportLine.closedCarrier
    rwa [hL]
  obtain ⟨m,t,hm,he⟩ := L.closedKlein_affine_equation
  apply polygonComplex_hyperplane_collinear m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)) hm (by simp)
  intro q hq
  have hself' := (he _).mp hself
  rcases hq with hq | hq | hq
  · rw [hq,(he _).mp hprev,hself']
  · rw [hq]
  · rw [hq,(he _).mp hnext,hself']

theorem DiscPolygon.jordanIndexEquiv_sub_one {n : ℕ} (P : DiscPolygon n) (j : ZMod n) :
    P.jordanIndexEquiv.symm (j-1) = (finRotate n).symm (P.jordanIndexEquiv.symm j) := by
  apply (finRotate n).injective
  rw [Equiv.apply_symm_apply]
  have h := P.jordanIndexEquiv_add_one (j-1)
  rw [sub_add_cancel] at h
  exact h.symm

/-- The licensed PL boundary and the actual closed Klein boundary are identical sets. -/
theorem DiscPolygon.toPolygonalCircle_complex_carrier {n : ℕ} (P : DiscPolygon n) :
    LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv '' P.toPolygonalCircle.carrier =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary := by
  rw [P.toPolygonalCircle_carrier,image_image]
  apply image_congr
  intro q _
  exact LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.apply_symm_apply _

/-- The actual cyclic PL vertices are exactly the true native Klein vertices. -/
theorem DiscPolygon.toPolygonalCircle_complex_vertex {n : ℕ} (P : DiscPolygon n) (j : ZMod n) :
    LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
      (P.toPolygonalCircle.vertex
        j) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        (P.jordanIndexEquiv.symm j)) :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv.apply_symm_apply _

/-- A true same-support finite native corner has the genuine full straight-line boundary germ. -/
theorem DiscPolygon.klein_boundary_straight_germ {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine) :
    ∀ᶠ y in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)), y ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary ↔
      polygonComplexLineEquation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        ((finRotate n).symm i)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))) y = 0 := by
  let e := LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.planeComplexEquiv
  have hc := P.klein_neighbors_collinear_of_same_support i z hz hL
  have hc' := polygon_collinear_affine_image e.symm.toLinearEquiv.toAffineEquiv.toAffineMap hc
  simp only [image_insert_eq,image_singleton] at hc'
  have hindex := P.jordanIndexEquiv_sub_one (P.jordanIndexEquiv i)
  rw [Equiv.symm_apply_apply] at hindex
  have hindexn := P.jordanIndexEquiv_add_one (P.jordanIndexEquiv i)
  rw [Equiv.symm_apply_apply] at hindexn
  have hcJ : Collinear ℝ ({P.toPolygonalCircle.vertex (P.jordanIndexEquiv i-(1 : ZMod n)),
      P.toPolygonalCircle.vertex (P.jordanIndexEquiv i),
      P.toPolygonalCircle.vertex (P.jordanIndexEquiv i+(1 : ZMod n))} : Set _) := by
    change Collinear ℝ ({e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i-(1 : ZMod n))))),
      e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i)))),
      e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        (P.jordanIndexEquiv.symm (P.jordanIndexEquiv i+(1 : ZMod n)))))} : Set _)
    rw [hindex,Equiv.symm_apply_apply,hindexn]
    exact hc'
  have h := polygonalCircle_complex_carrier_straight_germ P.toPolygonalCircle (P.jordanIndexEquiv i) hcJ
  simpa only [P.toPolygonalCircle_complex_carrier,P.toPolygonalCircle_complex_vertex,hindex,hindexn,
    Equiv.symm_apply_apply] using h

/-- The actual closed polygon is locally convex at every genuine straight finite corner. -/
theorem DiscPolygon.closedCarrier_locallyConvex_of_same_support {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ P.vertices i ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) := by
  have hp : P.vertices i ∈ P.boundary := mem_iUnion.mpr ⟨i,closedModelDiscHSegment_left_mem _ _⟩
  exact P.closedCarrier_locallyConvex_of_line_germ _ hp (polygonComplexLineEquation _ _)
    (P.klein_boundary_straight_germ i z hz hL)

/-- Every actual finite vertex with angle at most pi makes the genuine closed polygon locally convex. -/
theorem DiscPolygon.closedCarrier_locallyConvex_at_finite_vertex {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (ha
      : P.angle i ≤ Real.pi) :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ P.vertices i ∈ U ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (P.closedCarrier ∩ U) := by
  by_cases hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine
  · exact P.closedCarrier_locallyConvex_of_same_support i z hz hL
  · exact P.closedCarrier_locallyConvex_of_angle_le_pi_proper i z hz hL ha

end
end LowDimensionalTopology.Geometry.Polygon
