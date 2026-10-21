module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.PositiveConeAngularMeasure
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.TriangleMeshAngularMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleIsometries

/-! Genuine closed-sector angular measure and actual finite triangle corners.
The measure-based angle is identified with the independently defined forward-ray angle.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc NNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem hAngleCoordinate_nonnegative_span {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) (x : ℍ) :
    halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z ∈
      Submodule.span ℝ≥0 {R.kleinDirection, S.kleinDirection} ↔
      0 ≤ (hAngleCoordinate R S hne x).1 ∧ 0 ≤ (hAngleCoordinate R S hne x).2 := by
  let L := hAngleCoordinateLinear R S hne
  have hR : L R.kleinDirection = (1,0) := hAngleCoordinateLinear_first_direction R S hne
  have hS : L S.kleinDirection = (0,1) := hAngleCoordinateLinear_second_direction R S hne
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, he⟩
    have hMap : ((a : ℝ), (b : ℝ)) = hAngleCoordinate R S hne x := by
      change _ = L (halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z)
      rw [← he]
      change _ = L ((a : ℝ) • R.kleinDirection + (b : ℝ) • S.kleinDirection)
      rw [map_add, map_smul, map_smul, hR, hS]
      simp
    rw [← hMap]
    exact ⟨a.property, b.property⟩
  · rintro ⟨ha, hb⟩
    refine ⟨⟨(hAngleCoordinate R S hne x).1,ha⟩,
      ⟨(hAngleCoordinate R S hne x).2,hb⟩, ?_⟩
    apply L.injective
    change L ((hAngleCoordinate R S hne x).1 • R.kleinDirection +
      (hAngleCoordinate R S hne x).2 • S.kleinDirection) = hAngleCoordinate R S hne x
    rw [map_add, map_smul, map_smul, hR, hS]
    ext <;> simp

/-- The actual closed minor sector is the genuine nonnegative Klein cone. -/
theorem closure_properHAngleInterior_eq_nonnegative_span {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    closure (properHAngleInterior R S) =
      {x : ℍ | halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z ∈
        Submodule.span ℝ≥0 {R.kleinDirection, S.kleinDirection}} := by
  let F := hAngleCoordinate R S hne
  have hI : properHAngleInterior R S = F ⁻¹' positiveCoordinateQuadrant := by
    ext x
    constructor
    · intro hx
      have hh := mem_image_of_mem F hx
      rw [hAngleCoordinate_image_interior R S hne] at hh
      exact hh.2
    · intro hx
      apply (hAngleCoordinate_isOpenEmbedding R S hne).injective.mem_set_image.mp
      rw [hAngleCoordinate_image_interior R S hne]
      exact ⟨by rw [← hAngleCoordinate_range]; exact mem_range_self x, hx⟩
  have hQ : closure positiveCoordinateQuadrant =
      {y : ℝ × ℝ | 0 ≤ y.1 ∧ 0 ≤ y.2} := by
    change closure (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) = Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)
    rw [closure_prod_eq, closure_Ioi]
  rw [hI, ← (hAngleCoordinate_isOpenEmbedding R S hne).isOpenMap.preimage_closure_eq_closure_preimage
    (hAngleCoordinate_isOpenEmbedding R S hne).continuous, hQ]
  ext x
  exact (hAngleCoordinate_nonnegative_span R S hne x).symm

theorem halfPlaneKleinCoordinate_I_zero : halfPlaneKleinCoordinate UpperHalfPlane.I = 0 := by
  have hz : halfPlaneToDisc UpperHalfPlane.I = 0 := by
    simpa only [discToHalfPlane_zero] using halfPlaneToDisc_discToHalfPlane (0 : 𝔻)
  rw [halfPlaneKleinCoordinate, hz]
  change kleinFormula 0 = 0
  simp [kleinFormula]

theorem kleinCoordinate_positive_smul (z : 𝔻) :
    ∃ c : ℝ, 0 < c ∧ kleinCoordinate z = c • (z : ℂ) := by
  refine ⟨2 / (1 + ‖(z : ℂ)‖ ^ 2), by positivity, ?_⟩
  rfl

theorem cayley_closure_properHAngleInterior_I (R S : HRayAt UpperHalfPlane.I)
    (hne : R.supportLine ≠ S.supportLine) :
    halfPlaneToDisc '' closure (properHAngleInterior R S) =
      discPositiveCone R.kleinDirection S.kleinDirection := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [closure_properHAngleInterior_eq_nonnegative_span R S hne] at hx
    change halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate UpperHalfPlane.I ∈ Submodule.span ℝ≥0 {R.kleinDirection, S.kleinDirection} at hx
    rw [halfPlaneKleinCoordinate_I_zero, sub_zero] at hx
    obtain ⟨c, hc, he⟩ := kleinCoordinate_positive_smul (halfPlaneToDisc x)
    change kleinCoordinate (halfPlaneToDisc x) ∈ Submodule.span ℝ≥0 {R.kleinDirection, S.kleinDirection} at hx
    rw [he] at hx
    let d : ℝ≥0 := ⟨c, hc.le⟩
    have hd : d ≠ 0 := by
      intro h
      have h' := congrArg (fun d : ℝ≥0 => (d : ℝ)) h
      exact hc.ne' h'
    exact (Submodule.smul_mem_iff _ hd).mp hx
  · intro hw
    refine ⟨discToHalfPlane w, ?_, halfPlaneToDisc_discToHalfPlane w⟩
    rw [closure_properHAngleInterior_eq_nonnegative_span R S hne]
    change halfPlaneKleinCoordinate (discToHalfPlane w) -
      halfPlaneKleinCoordinate UpperHalfPlane.I ∈ Submodule.span ℝ≥0 {R.kleinDirection, S.kleinDirection}
    rw [halfPlaneKleinCoordinate_I_zero, sub_zero, halfPlaneKleinCoordinate,
      halfPlaneToDisc_discToHalfPlane]
    obtain ⟨c, hc, he⟩ := kleinCoordinate_positive_smul w
    rw [he]
    exact Submodule.smul_mem _ (⟨c,hc.le⟩ : ℝ≥0) hw

theorem hInteriorAngleMeasure_I_eq_klein_angle (R S : HRayAt UpperHalfPlane.I) :
    hInteriorAngleMeasure R S = angle R.kleinDirection S.kleinDirection := by
  rw [hInteriorAngleMeasure_I_cayley R S R.directionPoint_mem.1 R.directionPoint_mem.2
    S.directionPoint_mem.1 S.directionPoint_mem.2]
  obtain ⟨r, hr, hR⟩ := kleinCoordinate_positive_smul (halfPlaneToDisc R.directionPoint)
  obtain ⟨t, ht, hS⟩ := kleinCoordinate_positive_smul (halfPlaneToDisc S.directionPoint)
  simp only [HRayAt.kleinDirection, halfPlaneKleinCoordinate_I_zero, sub_zero]
  change angle (halfPlaneToDisc R.directionPoint : ℂ) (halfPlaneToDisc S.directionPoint : ℂ) =
    angle (kleinCoordinate (halfPlaneToDisc R.directionPoint))
      (kleinCoordinate (halfPlaneToDisc S.directionPoint))
  rw [hR, hS, angle_smul_left_of_pos _ _ hr, angle_smul_right_of_pos _ _ ht]

/-- The genuine closed minor ray sector has exactly the existing forward-tangent angle. -/
theorem discSubtendedAngle_cayley_closed_sector (R S : HRayAt UpperHalfPlane.I)
    (hne : R.supportLine ≠ S.supportLine) :
    discSubtendedAngle (halfPlaneToDisc '' closure (properHAngleInterior R S)) 0 =
      hInteriorAngleMeasure R S := by
  rw [cayley_closure_properHAngleInterior_I R S hne,
    discSubtendedAngle_positiveCone R.kleinDirection_ne_zero S.kleinDirection_ne_zero
      (by rw [← hInteriorAngleMeasure_I_eq_klein_angle]; exact hInteriorAngleMeasure_lt_pi R S hne),
    ← hInteriorAngleMeasure_I_eq_klein_angle]


/-- For genuine convex sets through the origin, the actual angular measure depends only on the germ. -/
theorem discSubtendedAngle_eq_of_convex_germ {A B : Set 𝔻}
    (hA : DiscHConvex A) (hB : DiscHConvex B) (h0A : (0 : 𝔻) ∈ A) (h0B : (0 : 𝔻) ∈ B)
    (h : ∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ A ↔ w ∈ B) :
    discSubtendedAngle A 0 = discSubtendedAngle B 0 := by
  let N : Set 𝔻 := {w | w ∈ A ↔ w ∈ B}
  have hN : N ∈ 𝓝 (0 : 𝔻) := h
  have heq : A ∩ N = B ∩ N := by
    ext w
    simp only [Set.mem_inter_iff, N, Set.mem_ofPred_eq]
    tauto
  have hD : discRadialDirections A = discRadialDirections B := by
    rw [← discRadialDirections_inter_nhds hA h0A hN, heq,
      discRadialDirections_inter_nhds hB h0B hN]
  rw [discSubtendedAngle, discSubtendedAngle, discSubtendedAngularFraction_zero,
    discSubtendedAngularFraction_zero, hD]

theorem HRayAt.val_transport {z w : ℍ} (h : z = w) (R : HRayAt z) :
    (h ▸ R).val = R.val := by
  cases h
  rfl

theorem HRayAt.supportLine_transport {z w : ℍ} (h : z = w) (R : HRayAt z) :
    (h ▸ R).supportLine = R.supportLine := by
  cases h
  rfl

theorem properHAngleInterior_congr_base {z w : ℍ} (h : z = w)
    (R S : HRayAt z) (R' S' : HRayAt w) (hR : R.val = R'.val) (hS : S.val = S'.val) :
    properHAngleInterior R S = properHAngleInterior R' S' := by
  cases h
  rw [Subtype.ext hR, Subtype.ext hS]

/-- At the actual native origin a genuine closed minor sector has its genuine ray-tangent angle. -/
theorem discSubtendedAngle_closed_properSector_zero (R S : DiscRayAt (0 : 𝔻))
    (hne : R.supportLine ≠ S.supportLine) :
    discSubtendedAngle (closure (properDiscAngleInterior R S)) 0 =
      discInteriorAngleMeasure R S := by
  let hbase := discToHalfPlane_zero
  let RR : HRayAt UpperHalfPlane.I := hbase ▸ R.toHalfPlane
  let SS : HRayAt UpperHalfPlane.I := hbase ▸ S.toHalfPlane
  have hR : R.toHalfPlane.val = RR.val := (HRayAt.val_transport hbase R.toHalfPlane).symm
  have hS : S.toHalfPlane.val = SS.val := (HRayAt.val_transport hbase S.toHalfPlane).symm
  have hRR : RR.supportLine = R.toHalfPlane.supportLine :=
    HRayAt.supportLine_transport hbase R.toHalfPlane
  have hSS : SS.supportLine = S.toHalfPlane.supportLine :=
    HRayAt.supportLine_transport hbase S.toHalfPlane
  have hneH : RR.supportLine ≠ SS.supportLine := by
    rw [hRR, hSS]
    exact (R.different_supports_iff S).mp hne
  have hproper := properHAngleInterior_congr_base hbase R.toHalfPlane S.toHalfPlane RR SS hR hS
  have hclosed : closure (properDiscAngleInterior R S) =
      halfPlaneToDisc '' closure (properHAngleInterior RR SS) := by
    change closure (halfPlaneToDisc '' properHAngleInterior R.toHalfPlane S.toHalfPlane) = _
    have he : halfPlaneToDisc '' closure (properHAngleInterior R.toHalfPlane S.toHalfPlane) =
        closure (halfPlaneToDisc '' properHAngleInterior R.toHalfPlane S.toHalfPlane) :=
      cayleyHomeomorph.image_closure _
    exact he.symm.trans (congrArg (fun U : Set ℍ => halfPlaneToDisc '' closure U) hproper)
  rw [hclosed, discSubtendedAngle_cayley_closed_sector RR SS hneH,
    discInteriorAngleMeasure_eq_halfPlane]
  exact (hInteriorAngleMeasure_congr_base hbase R.toHalfPlane S.toHalfPlane RR SS hR hS).symm

/-- The Haar-defined angle of an actual finite triangle corner at the origin is its original native angle. -/
theorem ClosedDiscTriangle.subtendedAngle_at_zero (T : ClosedDiscTriangle)
    (ha : T.a = discToClosedModel (0 : 𝔻)) :
    discSubtendedAngle T.finiteCarrier 0 = T.alpha := by
  let R := T.cornerRayABAtA 0 ha
  let S := T.cornerRayACAtA 0 ha
  have hne : R.supportLine ≠ S.supportLine := T.cornerAtA_proper 0 ha
  have hG : ∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ T.interior ↔ w ∈ properDiscAngleInterior R S := by
    let triangleCornerZeroMetricSpace : MetricSpace 𝔻 := discHyperbolicMetric
    obtain ⟨r, hr, he⟩ := T.cornerAtA_locally_interior 0 ha
    filter_upwards [Metric.ball_mem_nhds (0 : 𝔻) hr] with w hw
    constructor
    · intro ht
      have hh : w ∈ Metric.ball 0 r ∩ T.interior := ⟨hw, ht⟩
      rw [he] at hh
      exact hh.2
    · intro ht
      have hh : w ∈ Metric.ball 0 r ∩ properDiscAngleInterior R S := ⟨hw, ht⟩
      rw [← he] at hh
      exact hh.2
  have hC := Auxiliary.Topology.angular_closure_germ hG
  rw [← T.finiteCarrier_eq_closure] at hC
  have h0T : (0 : 𝔻) ∈ T.finiteCarrier := by
    change discToClosedModel 0 ∈ T.closedCarrier
    rw [← ha]
    exact subset_closedDiscHConvexHull {T.a,T.b,T.c} (by simp)
  have h0S : (0 : 𝔻) ∈ closure (properDiscAngleInterior R S) :=
    (mem_of_mem_nhds hC).mp h0T
  calc
    discSubtendedAngle T.finiteCarrier 0 =
        discSubtendedAngle (closure (properDiscAngleInterior R S)) 0 :=
      discSubtendedAngle_eq_of_convex_germ T.finiteCarrier_hConvex
        (properDiscAngleInterior_hConvex R S hne).closure h0T h0S hC
    _ = discInteriorAngleMeasure R S := discSubtendedAngle_closed_properSector_zero R S hne
    _ = T.alpha := (T.alpha_of_finite 0 ha).symm

/-- A genuine isometry carries the actual minor component to the actual minor component. -/
theorem properDiscAngleInterior_image_isometry {z w : 𝔻} (F : 𝔻 ≃ₜ 𝔻)
    (hF : let := discHyperbolicMetric; Isometry F)
    (R S : DiscRayAt z) (R' S' : DiscRayAt w)
    (hR : F '' R.val = R'.val) (hS : F '' S.val = S'.val)
    (hne : R.supportLine ≠ S.supportLine) (hne' : R'.supportLine ≠ S'.supportLine) :
    F '' properDiscAngleInterior R S = properDiscAngleInterior R' S' := by
  obtain ⟨x, hx⟩ := properDiscAngleInterior_nonempty R S hne
  have hxC : x ∈ (R.val ∪ S.val)ᶜ := by
    rw [properDiscAngle_interior_exterior_partition]
    exact Or.inl hx
  have hComp := F.image_connectedComponentIn hxC
  rw [connectedComponentIn_properDiscAngleInterior R S hne hx] at hComp
  have hdom : F '' (R.val ∪ S.val)ᶜ = (R'.val ∪ S'.val)ᶜ := by
    rw [image_compl_eq F.bijective, image_union, hR, hS]
  rw [hdom] at hComp
  have hxF : F x ∈ (R'.val ∪ S'.val)ᶜ := by
    rw [← hdom]
    exact mem_image_of_mem F hxC
  rcases properDiscAngle_component_classification R' S' hne' hxF with hminor | hmajor
  · exact hComp.trans hminor
  · have hconv := (properDiscAngleInterior_hConvex R S hne).isometry_image hF
    exact False.elim ((properDiscAngleExterior_not_hConvex R' S' hne')
      ((hComp.trans hmajor) ▸ hconv))


theorem ClosedDiscTriangle.interior_corner_germ (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    ∀ᶠ w in 𝓝 z, w ∈ T.interior ↔
      w ∈ properDiscAngleInterior (T.cornerRayABAtA z ha) (T.cornerRayACAtA z ha) := by
  let triangleCornerGermMetricSpace : MetricSpace 𝔻 := discHyperbolicMetric
  obtain ⟨r, hr, he⟩ := T.cornerAtA_locally_interior z ha
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  constructor
  · intro ht
    have hh : w ∈ Metric.ball z r ∩ T.interior := ⟨hw, ht⟩
    rw [he] at hh
    exact hh.2
  · intro ht
    have hh : w ∈ Metric.ball z r ∩
        properDiscAngleInterior (T.cornerRayABAtA z ha) (T.cornerRayACAtA z ha) := ⟨hw, ht⟩
    rw [← he] at hh
    exact hh.2

theorem ClosedDiscTriangle.cornerAB_carrier_congr_base (T : ClosedDiscTriangle)
    {z w : 𝔻} (h : z = w) (hz : T.a = discToClosedModel z)
    (hw : T.a = discToClosedModel w) :
    (T.cornerRayABAtA z hz).val = (T.cornerRayABAtA w hw).val := by
  cases h
  rfl

theorem ClosedDiscTriangle.cornerAC_carrier_congr_base (T : ClosedDiscTriangle)
    {z w : 𝔻} (h : z = w) (hz : T.a = discToClosedModel z)
    (hw : T.a = discToClosedModel w) :
    (T.cornerRayACAtA z hz).val = (T.cornerRayACAtA w hw).val := by
  cases h
  rfl

/-- Haar angle agrees with the genuine native angle at every actual finite triangle vertex. -/
theorem ClosedDiscTriangle.subtendedAngle_at_finite (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    discSubtendedAngle T.finiteCarrier z = T.alpha := by
  let F := discOriginNormalizer z
  have hF : let := discHyperbolicMetric; Isometry F := discOriginNormalizer_isometry z
  have hFz : F z = 0 := discOriginNormalizer_apply_self z
  have hd : ∀ u v, discPathDist (F u) (F v) = discPathDist u v := by
    let triangleNormalizationMetricSpace : MetricSpace 𝔻 := discHyperbolicMetric
    intro u v
    have he := hF.dist_eq u v
    simpa only [discHyperbolicMetric_distance] using he
  let e := _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry F hd
  let U := T.mapClosedIsometry e
  have hUa : U.a = discToClosedModel (F z) := by
    change e.closedMap T.a = _
    rw [ha, e.finite_commutes]
    rfl
  have hU0 : U.a = discToClosedModel 0 := hUa.trans (congrArg discToClosedModel hFz)
  let R := T.cornerRayABAtA z ha
  let S := T.cornerRayACAtA z ha
  let R' := U.cornerRayABAtA 0 hU0
  let S' := U.cornerRayACAtA 0 hU0
  have hR : F '' R.val = R'.val := by
    have hh := congrArg (fun Q : DiscRayAt (F z) => Q.val)
      (T.mapClosedIsometry_cornerAB e z ha)
    change (U.cornerRayABAtA (F z) hUa).val = F '' R.val at hh
    exact hh.symm.trans (U.cornerAB_carrier_congr_base hFz hUa hU0)
  have hS : F '' S.val = S'.val := by
    have hh := congrArg (fun Q : DiscRayAt (F z) => Q.val)
      (T.mapClosedIsometry_cornerAC e z ha)
    change (U.cornerRayACAtA (F z) hUa).val = F '' S.val at hh
    exact hh.symm.trans (U.cornerAC_carrier_congr_base hFz hUa hU0)
  have hne : R.supportLine ≠ S.supportLine := T.cornerAtA_proper z ha
  have hne' : R'.supportLine ≠ S'.supportLine := U.cornerAtA_proper 0 hU0
  have hI := properDiscAngleInterior_image_isometry F hF R S R' S' hR hS hne hne'
  have hClosure : F '' closure (properDiscAngleInterior R S) =
      closure (properDiscAngleInterior R' S') :=
    (F.image_closure _).trans (congrArg closure hI)
  have hgT := Auxiliary.Topology.angular_closure_germ (T.interior_corner_germ z ha)
  rw [← T.finiteCarrier_eq_closure] at hgT
  have hgF := Auxiliary.Topology.angular_homeomorph_germ F hgT
  rw [hFz, hClosure] at hgF
  have hgU := Auxiliary.Topology.angular_closure_germ (U.interior_corner_germ 0 hU0)
  rw [← U.finiteCarrier_eq_closure] at hgU
  have hg : ∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ F '' T.finiteCarrier ↔ w ∈ U.finiteCarrier := by
    filter_upwards [hgF, hgU] with w hwF hwU
    exact hwF.trans hwU.symm
  have hzT : z ∈ T.finiteCarrier := by
    change discToClosedModel z ∈ T.closedCarrier
    rw [← ha]
    exact subset_closedDiscHConvexHull {T.a,T.b,T.c} (by simp)
  have h0F : (0 : 𝔻) ∈ F '' T.finiteCarrier := ⟨z, hzT, hFz⟩
  have h0U : (0 : 𝔻) ∈ U.finiteCarrier := (mem_of_mem_nhds hg).mp h0F
  have hm := discSubtendedAngle_isometry F hF T.finiteCarrier z
  rw [hFz] at hm
  calc
    discSubtendedAngle T.finiteCarrier z = discSubtendedAngle (F '' T.finiteCarrier) 0 := hm.symm
    _ = discSubtendedAngle U.finiteCarrier 0 :=
      discSubtendedAngle_eq_of_convex_germ (T.finiteCarrier_hConvex.isometry_image hF)
        U.finiteCarrier_hConvex h0F h0U hg
    _ = U.alpha := U.subtendedAngle_at_zero hU0
    _ = T.alpha := T.mapClosedIsometry_alpha e

end
end LowDimensionalTopology.Geometry.Hyperbolic
