/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonCornerRegions
public import LowDimensionalTopology.Geometry.Polygon.Support.SupportedPolygonAngles
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-! # The genuine native polygon convexity and interior-angle criterion -/

/-- A genuine proper finite corner and its two actual neighbors form a true triangle. -/
def DiscPolygon.properCornerTriangle {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z
      hz).supportLine) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := P.vertices i
  b := P.vertices ((finRotate n).symm i)
  c := P.vertices (finRotate n i)
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    let R := P.cornerRayPrev i z hz
    let S := P.cornerRayNext i z hz
    have hprev : P.vertices ((finRotate n).symm i) ∈ R.supportLine.closedCarrier := by
      have h := discRayTowardClosed_endpoint_mem z (P.vertices ((finRotate n).symm i))
        (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ P.vertices ((finRotate n).symm i) from by
          rw [← hz]; exact fun he => P.prev_ne_self i (P.vertices_injective he).symm)
      exact closure_mono (image_mono R.subset_support) h
    have hselfR : P.vertices i ∈ R.supportLine.closedCarrier := by
      rw [hz]
      exact subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (R.subset_support R.start_mem))
    have hselfS : P.vertices i ∈ S.supportLine.closedCarrier := by
      rw [hz]
      exact subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (S.subset_support S.start_mem))
    have hnext : P.vertices (finRotate n i) ∈ S.supportLine.closedCarrier := by
      have h := discRayTowardClosed_endpoint_mem z (P.vertices (finRotate n i))
        (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ P.vertices (finRotate n i) from by
          rw [← hz]; exact fun he => P.next_ne_self i (P.vertices_injective he).symm)
      exact closure_mono (image_mono S.subset_support) h
    have hpne : P.vertices i ≠ P.vertices ((finRotate n).symm i) :=
      P.vertices_injective.ne (Ne.symm (P.prev_ne_self i))
    have hnne : P.vertices i ≠ P.vertices (finRotate n i) :=
      P.vertices_injective.ne (Ne.symm (P.next_ne_self i))
    exact hne ((R.supportLine.eq_of_two_closed_points L hpne hselfR hprev ha hb).trans
      (S.supportLine.eq_of_two_closed_points L hnne hselfS hnext ha hc).symm)

/-- All three true adjacent vertex coordinates are actual boundary or closure points of the polygon. -/
theorem DiscPolygon.corner_coordinate_vertices_closure {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha : T.a = P.vertices i)
    (hb : T.b = P.vertices ((finRotate n).symm i)) (hc : T.c = P.vertices (finRotate n i)) :
    (0 : ℝ × ℝ) ∈ frontier (T.ambientCoordinateHomeomorph '' P.complexInterior) ∧
    (1,0) ∈ closure (T.ambientCoordinateHomeomorph '' P.complexInterior) ∧
    (0,1) ∈ closure (T.ambientCoordinateHomeomorph '' P.complexInterior) := by
  obtain ⟨_,_,_,_,hF,_⟩ := P.corner_coordinate_jordan_regions T
  have hj (j : Fin n) : T.ambientCoordinateHomeomorph (P.vertices j : ℂ) ∈
      frontier (T.ambientCoordinateHomeomorph '' P.complexInterior) := by
    rw [hF]
    exact mem_image_of_mem _ (mem_image_of_mem _ (mem_iUnion.mpr ⟨j,closedModelDiscHSegment_left_mem _ _⟩))
  have h0 := hj i
  have h1 := frontier_subset_closure (hj ((finRotate n).symm i))
  have h2 := frontier_subset_closure (hj (finRotate n i))
  rw [← ha,T.ambientCoordinateHomeomorph_closed,T.coordinate_a] at h0
  rw [← hb,T.ambientCoordinateHomeomorph_closed,T.coordinate_b] at h1
  rw [← hc,T.ambientCoordinateHomeomorph_closed,T.coordinate_c] at h2
  exact ⟨h0,h1,h2⟩

/-- Convexity excludes every negative-diagonal interior point at a true native corner. -/
theorem DiscPolygon.convex_corner_negative_not_inside {n : ℕ} (P : DiscPolygon n) (hP : P.IsConvex)
    (i : Fin n) (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha : T.a = P.vertices i)
    (hb : T.b = P.vertices ((finRotate n).symm i)) (hc : T.c = P.vertices (finRotate n i))
    {t : ℝ} (ht : 0 < t) : (-t,-t) ∉ T.ambientCoordinateHomeomorph '' P.complexInterior := by
  intro hw
  let I := T.ambientCoordinateHomeomorph '' P.complexInterior
  have hI : IsOpen I := T.ambientCoordinateHomeomorph.isOpenMap _ P.complexInterior_isOpen
  have hIc : Convex ℝ I := by
    have hh := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp
      hP).affine_image T.coordinateAffineEquiv.toAffineMap
    change Convex ℝ (T.coordinateHomeomorph '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
      P.interior)) at hh
    rw [P.klein_image_interior,image_image] at hh
    exact hh
  obtain ⟨h0,h1,h2⟩ := P.corner_coordinate_vertices_closure i T ha hb hc
  have hd : ((1/2,1/2) : ℝ × ℝ) ∈ closure I := by
    have hh := hIc.closure h1 h2 (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    convert hh using 1
    ext <;> norm_num
  have hw' : (-t,-t) ∈ _root_.interior I := by rwa [hI.interior_eq]
  have hden : 0 < 1+2*t := by linarith
  have hsum : 1/(1+2*t)+(2*t)/(1+2*t) = 1 := by field_simp [ne_of_gt hden]
  have hh := hIc.combo_interior_closure_mem_interior hw' hd
    (a := 1/(1+2*t)) (b := (2*t)/(1+2*t)) (by positivity) (by positivity) hsum
  have he : (1/(1+2*t)) • ((-t,-t) : ℝ × ℝ) + (2*t/(1+2*t)) • ((1/2,1/2) : ℝ × ℝ) = 0 := by
    apply Prod.ext
    all_goals change (1/(1+2*t))*(-t)+(2*t/(1+2*t))*(1/2) = 0
    all_goals ring
  rw [he] at hh
  exact h0.2 hh

/-- Convexity selects the true positive coordinate sector of every genuine nonstraight corner. -/
theorem DiscPolygon.convex_corner_coordinate_region {n : ℕ} (P : DiscPolygon n) (hP : P.IsConvex)
    (i : Fin n) (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha : T.a = P.vertices i)
    (hb : T.b = P.vertices ((finRotate n).symm i)) (hc : T.c = P.vertices (finRotate n i)) :
    ∀ᶠ y in 𝓝 (0 : ℝ × ℝ),
      y ∈ T.ambientCoordinateHomeomorph '' P.complexInterior ↔ 0 < y.1 ∧ 0 < y.2 := by
  have hB := P.corner_coordinate_boundary_germ i T ha hb hc
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp hB
  obtain ⟨hI,hO,hd,hu,_,_⟩ := P.corner_coordinate_jordan_regions T
  have h0I := (P.corner_coordinate_vertices_closure i T ha hb hc).1
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
    have hm : ((-(r/2),-(r/2)) : ℝ × ℝ) ∈ Metric.ball 0 r := by
      change max |(-(r/2))-0| |(-(r/2))-0| < r
      rw [sub_zero,abs_neg,abs_of_pos (by positivity : 0 < r/2),max_self]
      linarith
    refine ⟨(-(r/2),-(r/2)),hm,by linarith,by linarith,?_⟩
    exact ((hpartition _ hm).mpr (Or.inr (Or.inl (by linarith)))).resolve_left
      (P.convex_corner_negative_not_inside hP i T ha hb hc (by linarith : 0 < r/2))
  have hh := polygonCorner_positive_region_of_negative_outside hI hO hd Metric.isOpen_ball
    (convex_ball (0 : ℝ × ℝ) r) (Metric.mem_ball_self hr) (frontier_subset_closure h0I) hpartition hneg
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) hr] with y hy
  exact hh y hy

/-- The actual interior of a convex native polygon has the adjacent true triangle germ. -/
theorem DiscPolygon.convex_corner_triangle_interior_germ {n : ℕ} (P : DiscPolygon n) (hP : P.IsConvex)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha : T.a = P.vertices i)
    (hb : T.b = P.vertices ((finRotate n).symm i)) (hc : T.c = P.vertices (finRotate n i)) :
    ∀ᶠ w in 𝓝 z,w ∈ P.interior ↔ w ∈ T.interior := by
  have hcoord : T.discCoordinate z = (0,0) := by
    change T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) = (0,0)
    rw [← hz,← ha]
    exact T.coordinate_a
  have hsum : ∀ᶠ w in 𝓝 z,(T.discCoordinate w).1+(T.discCoordinate w).2 < 1 := by
    apply (isOpen_lt (T.continuous_discCoordinate.fst.add T.continuous_discCoordinate.snd) continuous_const).mem_nhds
    change (T.discCoordinate z).1+(T.discCoordinate z).2 < 1
    rw [hcoord]
    norm_num
  have hh := P.convex_corner_coordinate_region hP i T ha hb hc
  have hg : ∀ᶠ w in 𝓝 z,
      T.discCoordinate w ∈ T.ambientCoordinateHomeomorph '' P.complexInterior ↔
        0 < (T.discCoordinate w).1 ∧ 0 < (T.discCoordinate w).2 := by
    have ht := T.continuous_discCoordinate.tendsto z
    rw [hcoord] at ht
    exact ht.eventually hh
  filter_upwards [hg,hsum] with w hw hs
  rw [T.mem_interior_iff_discCoordinate]
  rw [← T.ambientCoordinateHomeomorph_disc w,T.ambientCoordinateHomeomorph.injective.mem_set_image] at hw
  change (w : ℂ) ∈ P.complexInterior ↔ _
  rw [T.ambientCoordinateHomeomorph_disc] at hw
  exact hw.trans (by simp only [hs,and_true])

/-- A convex polygon always selects the genuine minor angle at every proper finite corner. -/
theorem DiscPolygon.hasMinorInterior_of_isConvex_proper {n : ℕ} (P : DiscPolygon n) (hP : P.IsConvex)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine) :
    P.HasMinorInteriorAt i z hz := by
  let T := P.properCornerTriangle i z hz hne
  have hTa : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := hz
  have hp : P.cornerRayPrev i z hz = T.cornerRayABAtA z hTa := by
    change discRayTowardClosed z T.b _ = _
    exact T.rayToward_b z hTa _
  have hn : P.cornerRayNext i z hz = T.cornerRayACAtA z hTa := by
    change discRayTowardClosed z T.c _ = _
    exact T.rayToward_c z hTa _
  change ∀ᶠ w in 𝓝 z,w ∈ P.interior ↔ w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior
    (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz)
  rw [hp,hn]
  have hg := P.convex_corner_triangle_interior_germ hP i z hz T rfl rfl rfl
  let polygonConvexCornerMetric : MetricSpace 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := T.cornerAtA_locally_interior z hTa
  filter_upwards [hg,Metric.ball_mem_nhds z hr] with w hw hb
  have hh := congrArg (fun S : Set 𝔻 => w ∈ S) he
  have ht : w ∈ T.interior ↔ w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (T.cornerRayABAtA z hTa)
      (T.cornerRayACAtA z hTa) := by
    simpa only [mem_inter_iff,hb,true_and] using iff_of_eq hh
  exact hw.trans ht

/-- Every genuine finite, ideal or straight interior angle of a convex polygon is at most pi. -/
theorem DiscPolygon.angle_le_pi_of_isConvex {n : ℕ} (P : DiscPolygon n) (hP : P.IsConvex)
    (i : Fin n) : P.angle i ≤ Real.pi := by
  by_cases hi : ‖(P.vertices i : ℂ)‖ < 1
  · let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) hi
    have hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
    by_cases hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine
    · rw [P.angle_eq_pi_of_same_support i z hz hL]
    · exact (P.angle_le_pi_iff_hasMinor_of_proper i z hz hL).mpr
        (P.hasMinorInterior_of_isConvex_proper hP i z hz hL)
  · rw [P.angle_of_ideal i (le_antisymm (P.vertices i).norm_le_one (le_of_not_gt hi))]
    exact Real.pi_pos.le

/-- For arbitrary actual finite-or-ideal Jordan polygons, including straight corners. -/
theorem DiscPolygon.isConvex_iff_angles_le_pi {n : ℕ} (P : DiscPolygon n) :
    P.IsConvex ↔ ∀ i : Fin n,P.angle i ≤ Real.pi :=
  ⟨P.angle_le_pi_of_isConvex,P.isConvex_of_angles_le_pi⟩

end
end LowDimensionalTopology.Geometry.Polygon
