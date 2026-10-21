/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonConvexAngles
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The actual first forward side is exactly the nonnegative first coordinate axis. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.FiniteCorner.mem_rayAB_iff_coordinates {T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) (x : ℍ) :
    x ∈ C.rayAB.val ↔ 0 ≤ (T.halfPlaneCoordinate x).1 ∧ (T.halfPlaneCoordinate x).2 = 0 := by
  by_cases hx : x = z
  · subst x
    rw [T.halfPlaneCoordinate_at_a ha]
    exact iff_of_true C.rayAB.start_mem (by norm_num)
  have he : x ∈ C.rayAB.val ↔ T.halfPlaneCoordinate x ∈
      T.halfPlaneCoordinate '' (C.rayAB.val \ {z}) := by
    rw [T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image]
    simp only [Set.mem_sdiff,mem_singleton_iff,hx,not_false_eq_true,and_true]
  rw [he,C.imageAB]
  have hn : T.halfPlaneCoordinate x ≠ 0 := by
    intro hh
    exact hx (T.halfPlaneCoordinate_isOpenEmbedding.injective (hh.trans (T.halfPlaneCoordinate_at_a ha).symm))
  simp only [mem_inter_iff,mem_range_self,true_and,mem_ofPred]
  constructor
  · rintro ⟨hp,h0⟩
    exact ⟨hp.le,h0⟩
  · rintro ⟨hp,h0⟩
    refine ⟨lt_of_le_of_ne hp ?_,h0⟩
    intro he
    exact hn (Prod.ext he.symm h0)

/-- The actual second forward side is exactly the nonnegative second coordinate axis. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.FiniteCorner.mem_rayAC_iff_coordinates {T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) (x : ℍ) :
    x ∈ C.rayAC.val ↔ (T.halfPlaneCoordinate x).1 = 0 ∧ 0 ≤ (T.halfPlaneCoordinate x).2 := by
  by_cases hx : x = z
  · subst x
    rw [T.halfPlaneCoordinate_at_a ha]
    exact iff_of_true C.rayAC.start_mem (by norm_num)
  have he : x ∈ C.rayAC.val ↔ T.halfPlaneCoordinate x ∈
      T.halfPlaneCoordinate '' (C.rayAC.val \ {z}) := by
    rw [T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image]
    simp only [Set.mem_sdiff,mem_singleton_iff,hx,not_false_eq_true,and_true]
  rw [he,C.imageAC]
  have hn : T.halfPlaneCoordinate x ≠ 0 := by
    intro hh
    exact hx (T.halfPlaneCoordinate_isOpenEmbedding.injective (hh.trans (T.halfPlaneCoordinate_at_a ha).symm))
  simp only [mem_inter_iff,mem_range_self,true_and,mem_ofPred]
  constructor
  · rintro ⟨h0,hp⟩
    exact ⟨h0,hp.le⟩
  · rintro ⟨h0,hp⟩
    refine ⟨h0,lt_of_le_of_ne hp ?_⟩
    intro he
    exact hn (Prod.ext h0 he.symm)

/-- The actual major corner sector is exactly the union of the two negative coordinate half-planes. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.FiniteCorner.mem_exterior_iff_coordinates {T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) (x : ℍ) :
    x ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior C.rayAB C.rayAC ↔
      (T.halfPlaneCoordinate x).1 < 0 ∨ (T.halfPlaneCoordinate x).2 < 0 := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior,Set.mem_sdiff,mem_compl_iff,mem_union,
    C.mem_rayAB_iff_coordinates ha x,C.mem_rayAC_iff_coordinates ha x,C.mem_interior_iff x]
  rcases lt_trichotomy (T.halfPlaneCoordinate x).1 0 with h | h | h <;>
    rcases lt_trichotomy (T.halfPlaneCoordinate x).2 0 with k | k | k <;> grind

/-- True native minor-sector membership is exactly strict positivity of both genuine coordinates. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.mem_cornerInterior_iff_coordinates (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (w : 𝔻) :
    w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (T.cornerRayABAtA z
      ha) (T.cornerRayACAtA z ha) ↔
      0 < (T.discCoordinate w).1 ∧ 0 < (T.discCoordinate w).2 := by
  rw [T.cornerAtA_interior_cayley]
  have he : w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior
      (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior
        (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane w,(show Function.Injective
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc from
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective).mem_set_image]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  rw [he,(T.finiteHalfPlaneCornerAtDiscA z ha).mem_interior_iff]
  change 0 < (T.discCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w))).1 ∧
      0 < (T.discCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w))).2 ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]

/-- True native major-sector membership uses the actual exterior between the forward rays. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.mem_cornerExterior_iff_coordinates (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (w : 𝔻) :
    w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior (T.cornerRayABAtA z
      ha) (T.cornerRayACAtA z ha) ↔
      (T.discCoordinate w).1 < 0 ∨ (T.discCoordinate w).2 < 0 := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior,T.cornerRayABAtA_toHalfPlane,T.cornerRayACAtA_toHalfPlane]
  have he : w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior
      (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior
        (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane w,(show Function.Injective
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc from
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective).mem_set_image]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  rw [he,(T.finiteHalfPlaneCornerAtDiscA z ha).mem_exterior_iff_coordinates
    (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane])]
  change (T.discCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w))).1 < 0 ∨
      (T.discCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w))).2 < 0 ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]

/-- Every actual Jordan corner selects exactly one of the two genuine coordinate sectors. -/
theorem DiscPolygon.corner_coordinate_region_cases {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha : T.a = P.vertices i)
    (hb : T.b = P.vertices ((finRotate n).symm i)) (hc : T.c = P.vertices (finRotate n i)) :
    (∀ᶠ y in 𝓝 (0 : ℝ × ℝ),
      y ∈ T.ambientCoordinateHomeomorph '' P.complexInterior ↔ 0 < y.1 ∧ 0 < y.2) ∨
    (∀ᶠ y in 𝓝 (0 : ℝ × ℝ),
      y ∈ T.ambientCoordinateHomeomorph '' P.complexInterior ↔ y.1 < 0 ∨ y.2 < 0) := by
  have hB := P.corner_coordinate_boundary_germ i T ha hb hc
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp hB
  obtain ⟨hI,hO,hd,hu,hfI,hfO⟩ := P.corner_coordinate_jordan_regions T
  have h0B : (0 : ℝ × ℝ) ∈ T.ambientCoordinateHomeomorph '' P.complexBoundary := by
    have hh := (P.corner_coordinate_vertices_closure i T ha hb hc).1
    rwa [hfI] at hh
  have h0I : (0 : ℝ × ℝ) ∈ closure (T.ambientCoordinateHomeomorph '' P.complexInterior) :=
    frontier_subset_closure (hfI.symm ▸ h0B)
  have h0O : (0 : ℝ × ℝ) ∈ closure (T.ambientCoordinateHomeomorph '' P.complexOutside) :=
    frontier_subset_closure (hfO.symm ▸ h0B)
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
  have hw : ((-(r/2),-(r/2)) : ℝ × ℝ) ∈ Metric.ball 0 r := by
    change max |(-(r/2))-0| |(-(r/2))-0| < r
    rw [sub_zero,abs_neg,abs_of_pos (by positivity : 0 < r/2),max_self]
    linarith
  rcases (hpartition _ hw).mpr (Or.inr (Or.inl (by linarith))) with hwI | hwO
  · right
    have hswap : ∀ y ∈ Metric.ball (0 : ℝ × ℝ) r,
        (y ∈ T.ambientCoordinateHomeomorph '' P.complexOutside ∨
          y ∈ T.ambientCoordinateHomeomorph '' P.complexInterior) ↔
        ((0 < y.1 ∧ 0 < y.2) ∨ y.1 < 0 ∨ y.2 < 0) := by
      intro y hy
      rw [or_comm]
      exact hpartition y hy
    have hpos := polygonCorner_positive_region_of_negative_outside hO hI hd.symm Metric.isOpen_ball
      (convex_ball (0 : ℝ × ℝ) r) (Metric.mem_ball_self hr) h0O hswap
      ⟨(-(r/2),-(r/2)),hw,by linarith,by linarith,hwI⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) hr] with y hy
    constructor
    · intro hyI
      rcases (hpartition y hy).mp (Or.inl hyI) with hp | hn
      · exact (Set.disjoint_left.mp hd hyI ((hpos y hy).mpr hp)).elim
      · exact hn
    · intro hn
      have hnp : ¬ (0 < y.1 ∧ 0 < y.2) := by
        rintro ⟨h1,h2⟩
        rcases hn with hh | hh <;> linarith
      exact ((hpartition y hy).mpr (Or.inr hn)).resolve_right
        (fun hh => hnp ((hpos y hy).mp hh))
  · left
    have hh := polygonCorner_positive_region_of_negative_outside hI hO hd Metric.isOpen_ball
      (convex_ball (0 : ℝ × ℝ) r) (Metric.mem_ball_self hr) h0I hpartition
      ⟨(-(r/2),-(r/2)),hw,by linarith,by linarith,hwO⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) hr] with y hy
    exact hh y hy

/-- At every proper finite vertex the actual polygon interior has the genuine minor or major angle germ. -/
theorem DiscPolygon.corner_interior_germ_cases {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine) :
    P.HasMinorInteriorAt i z hz ∨
    (∀ᶠ w in 𝓝 z,w ∈ P.interior ↔
      w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz)) := by
  let T := P.properCornerTriangle i z hz hne
  have hTa : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := hz
  have hp : P.cornerRayPrev i z hz = T.cornerRayABAtA z hTa := by
    change discRayTowardClosed z T.b _ = _
    exact T.rayToward_b z hTa _
  have hn : P.cornerRayNext i z hz = T.cornerRayACAtA z hTa := by
    change discRayTowardClosed z T.c _ = _
    exact T.rayToward_c z hTa _
  have hcoord : T.discCoordinate z = 0 := by
    change T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) = 0
    rw [← hTa]
    exact T.coordinate_a
  have ht := T.continuous_discCoordinate.tendsto z
  rw [hcoord] at ht
  rcases P.corner_coordinate_region_cases i T rfl rfl rfl with hm | hM
  · left
    change ∀ᶠ w in 𝓝 z,w ∈ P.interior ↔ _
    filter_upwards [ht.eventually hm] with w hw
    rw [← T.ambientCoordinateHomeomorph_disc w,T.ambientCoordinateHomeomorph.injective.mem_set_image,
      T.ambientCoordinateHomeomorph_disc w] at hw
    rw [hp,hn,T.mem_cornerInterior_iff_coordinates]
    exact hw
  · right
    filter_upwards [ht.eventually hM] with w hw
    rw [← T.ambientCoordinateHomeomorph_disc w,T.ambientCoordinateHomeomorph.injective.mem_set_image,
      T.ambientCoordinateHomeomorph_disc w] at hw
    rw [hp,hn,T.mem_cornerExterior_iff_coordinates]
    exact hw

/-- The reflex branch of the numeric angle always measures the actual genuine major interior germ. -/
theorem DiscPolygon.majorInterior_of_not_minor {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine)
    (hm : ¬ P.HasMinorInteriorAt i z hz) :
    ∀ᶠ w in 𝓝 z,w ∈ P.interior ↔
      w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior (P.cornerRayPrev i z
        hz) (P.cornerRayNext i z hz) :=
  (P.corner_interior_germ_cases i z hz hne).resolve_left hm

/-- At a genuine proper finite corner the numeric angle measures the actual selected minor or major interior. -/
theorem DiscPolygon.angle_geometric_branches {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine) :
    (P.HasMinorInteriorAt i z hz ∧ P.angle i =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z
        hz) (P.cornerRayNext i z hz)) ∨
    ((∀ᶠ w in 𝓝 z,w ∈ P.interior ↔
        w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior (P.cornerRayPrev i z
          hz) (P.cornerRayNext i z hz)) ∧
      P.angle i = 2*Real.pi-_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz)) := by
  classical
  by_cases hm : P.HasMinorInteriorAt i z hz
  · exact Or.inl ⟨hm,P.angle_of_minor i z hz hm⟩
  · exact Or.inr ⟨P.majorInterior_of_not_minor i z hz hne hm,P.angle_of_not_minor i z hz hm⟩

/-- Finite vertices have genuine strictly positive angles smaller than a full turn, including straight corners. -/
theorem DiscPolygon.angle_mem_Ioo_of_finite {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    P.angle i ∈ Ioo (0 : ℝ) (2*Real.pi) := by
  by_cases hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine
  · rw [P.angle_eq_pi_of_same_support i z hz hL]
    constructor <;> linarith [Real.pi_pos]
  · have h0 : 0 < _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_pos _ _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.different_supports_iff _ _).mp hL)
    have hπ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz) < Real.pi := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_lt_pi _ _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.different_supports_iff _ _).mp hL)
    rw [P.angle_of_finite i z hz]
    split_ifs <;> constructor <;> linarith [Real.pi_pos]

/-- Zero angle characterizes exactly the genuine ideal vertices. -/
theorem DiscPolygon.angle_eq_zero_iff_ideal {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    P.angle i = 0 ↔ ‖(P.vertices i : ℂ)‖ = 1 := by
  constructor
  · intro h0
    by_contra hi
    have hfin : ‖(P.vertices i : ℂ)‖ < 1 := lt_of_le_of_ne (P.vertices i).norm_le_one hi
    have hp := (P.angle_mem_Ioo_of_finite i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
      (P.vertices i) hfin)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hfin).symm).1
    linarith
  · exact P.angle_of_ideal i

/-- At a proper corner the reflex angle occurs exactly when the actual interior is not the minor germ. -/
theorem DiscPolygon.pi_lt_angle_iff_not_minor_of_proper {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine) :
    Real.pi < P.angle i ↔ ¬ P.HasMinorInteriorAt i z hz := by
  exact not_le.symm.trans (not_congr (P.angle_le_pi_iff_hasMinor_of_proper i z hz hne))

end
end LowDimensionalTopology.Geometry.Polygon
