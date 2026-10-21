module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.ClosedTriangleIncenter
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaGeometry
@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem isometric_parameter_mem_closure_ball {X : Type*} [MetricSpace X] {γ : ℝ → X}
    (hγ : Isometry γ) (s t r : ℝ) (hr : r ≠ 0) (ht : dist (γ s) (γ t) ≤ r) :
    γ t ∈ closure (Metric.ball (γ s) r) := by
  have hreal : t ∈ closure (Metric.ball s r) := by
    rw [closure_ball s hr,Metric.mem_closedBall]
    simpa only [hγ.dist_eq,dist_comm] using ht
  have hc := mem_closure_image hγ.continuous.continuousAt hreal
  apply closure_mono (t := Metric.ball (γ s) r) ?_ hc
  rintro x ⟨u,hu,rfl⟩
  simpa only [Metric.mem_ball,hγ.dist_eq] using hu

theorem halfPlane_mem_closure_ball {q w : ℍ} {r : ℝ} (hr : 0 < r) (hw : dist q w ≤ r) :
    w ∈ closure (Metric.ball q r) := by
  by_cases hqw : q = w
  · subst w
    exact subset_closure (Metric.mem_ball_self hr)
  obtain ⟨L,hq,hwL⟩ := exists_halfPlaneLine_through q w hqw
  obtain ⟨γ,hγ,he⟩ := L.exists_isometric_param
  obtain ⟨s,hs⟩ := he.symm ▸ hq
  obtain ⟨t,ht⟩ := he.symm ▸ hwL
  rw [← hs,← ht] at hw ⊢
  exact isometric_parameter_mem_closure_ball hγ s t r hr.ne' hw

theorem disc_mem_closure_hyperbolic_ball (q w : 𝔻) (r : ℝ) (hr : 0 < r)
    (hw : discPathDist q w ≤ r) :
    let := discHyperbolicMetric
    w ∈ closure (Metric.ball q r) := by
  let := discHyperbolicMetric
  have hH : discToHalfPlane w ∈ closure (Metric.ball (discToHalfPlane q) r) :=
    halfPlane_mem_closure_ball hr (by rwa [← discPathDist_eq_halfPlane])
  have hc := mem_closure_image (continuous_halfPlaneToDisc.continuousAt) hH
  let e : ℍ ≃ᵢ 𝔻 := { cayleyEquiv with isometry_toFun := cayley_isometry }
  have he := e.image_ball (discToHalfPlane q) r
  change halfPlaneToDisc '' Metric.ball (discToHalfPlane q) r =
    Metric.ball (halfPlaneToDisc (discToHalfPlane q)) r at he
  rw [he,halfPlaneToDisc_discToHalfPlane,halfPlaneToDisc_discToHalfPlane] at hc
  exact hc

/-- A ball of radius at most the actual side distance stays in its genuine half-plane. -/
theorem HalfPlaneLine.ball_subset_openHalfPlane (L : HalfPlaneLine) (q : ℍ) (r : ℝ)
    (hr : 0 < r) (hrL : r ≤ L.pointDist q) : Metric.ball q r ⊆ openHHalfPlane L q := by
  apply (hConvex_metric_ball q r).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hr)
  intro z hz hzL
  have hd : dist q z < r := by simpa only [Metric.mem_ball,dist_comm] using hz
  have hL : L.pointDist q ≤ dist q z := Metric.infDist_le_dist_of_mem hzL
  linarith

/-- The common true distance to the three complete side geodesics. -/
def ClosedDiscTriangle.inradius (T : ClosedDiscTriangle) : ℝ := T.sideLineA.pointDist T.incenter

/-- The metric circle at the actual internal centre with the actual common side distance. -/
def ClosedDiscTriangle.incircle (T : ClosedDiscTriangle) : Set 𝔻 :=
  {z | discPathDist T.incenter z = T.inradius}

def ClosedDiscTriangle.inball (T : ClosedDiscTriangle) : Set 𝔻 :=
  {z | discPathDist T.incenter z < T.inradius}

theorem ClosedDiscTriangle.inradius_pos (T : ClosedDiscTriangle) : 0 < T.inradius := by
  let := discHyperbolicMetric
  have hp := T.incenter_interior_coordinates T.incenter_mem_interior
  have hnot : T.incenter ∉ T.sideLineA.carrier := by
    intro h
    have he := (T.sideLineA_iff_coordinate (discToClosedModel T.incenter)).mp
      ((T.sideLineA.closedCarrier_mem_interior_iff _).mpr h)
    change (T.discCoordinate T.incenter).1 + (T.discCoordinate T.incenter).2 = 1 at he
    linarith [hp.2.2]
  obtain ⟨p,⟨hpL,_⟩,_⟩ := T.sideLineA.exists_unique_nearest_point T.incenter
  change 0 < Metric.infDist T.incenter T.sideLineA.carrier
  exact (T.sideLineA.isClosed_carrier.notMem_iff_infDist_pos ⟨p,hpL⟩).mp hnot

theorem ClosedDiscTriangle.inradius_eq_sideDist (T : ClosedDiscTriangle) :
    T.inradius = T.sideLineA.pointDist T.incenter ∧
      T.inradius = T.sideLineB.pointDist T.incenter ∧ T.inradius = T.sideLineC.pointDist T.incenter :=
  ⟨rfl,T.incenter_equidistant.1,T.incenter_equidistant.1.trans T.incenter_equidistant.2⟩

theorem ClosedDiscTriangle.incircle_nonempty (T : ClosedDiscTriangle) : T.incircle.Nonempty := by
  obtain ⟨p,⟨_,hp⟩,_⟩ := T.sideLineA.exists_unique_nearest_point T.incenter
  exact ⟨p,hp.symm⟩

theorem DiscLine.nearest_point_perpendicular (L : DiscLine) (q p : 𝔻)
    (hp : p ∈ L.carrier) (hd : L.pointDist q = discPathDist q p) :
    ∃ N : DiscLine, q ∈ N.carrier ∧ L.OrthogonalAt N p := by
  obtain ⟨r,⟨hr,N,hqN,hrN⟩,_⟩ := L.exists_unique_orthogonal_foot q
  have hdr := L.pointDist_eq_dist_of_perpendicular N r q hrN hqN
  have he : r = p := (L.exists_unique_nearest_point q).unique ⟨hr,hdr⟩ ⟨hp,hd⟩
  subst r
  exact ⟨N,hqN,hrN⟩

/-- Distinct geodesics cannot have the same positive-distance nearest point from one point. -/
theorem DiscLine.eq_of_common_nearest_point (L M : DiscLine) (q p : 𝔻) (hqp : q ≠ p)
    (hpL : p ∈ L.carrier) (hpM : p ∈ M.carrier)
    (hdL : L.pointDist q = discPathDist q p) (hdM : M.pointDist q = discPathDist q p) : L = M := by
  obtain ⟨N,hqN,hLN⟩ := L.nearest_point_perpendicular q p hpL hdL
  obtain ⟨K,hqK,hMK⟩ := M.nearest_point_perpendicular q p hpM hdM
  have he : N = K := N.eq_of_two_points K hqp hqN hLN.2.1 hqK hMK.2.1
  subst K
  have hNL : N.OrthogonalAt L p := ⟨hLN.2.1,hLN.1,by rw [real_inner_comm]; exact hLN.2.2⟩
  have hNM : N.OrthogonalAt M p := ⟨hMK.2.1,hMK.1,by rw [real_inner_comm]; exact hMK.2.2⟩
  exact (N.existsUnique_perpendicular p).unique
    ⟨hpL,(N.orthogonalAt_iff L p hNL.1 hNL.2.1).mp hNL⟩
    ⟨hpM,(N.orthogonalAt_iff M p hNM.1 hNM.2.1).mp hNM⟩

/-- The actual open disc of the common side radius is wholly inside the genuine triangle. -/
theorem ClosedDiscTriangle.inball_subset_interior (T : ClosedDiscTriangle) : T.inball ⊆ T.interior := by
  have hcentre : discToHalfPlane T.incenter ∈ T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane T.incenter) ∈ T.interior
    rw [halfPlaneToDisc_discToHalfPlane]
    exact T.incenter_mem_interior
  have hA : T.inradius ≤ T.sideLineA.toHalfPlane.pointDist (discToHalfPlane T.incenter) := by
    rw [← T.sideLineA.pointDist_eq_halfPlane]
    exact le_rfl
  have hB : T.inradius ≤ T.sideLineB.toHalfPlane.pointDist (discToHalfPlane T.incenter) := by
    rw [← T.sideLineB.pointDist_eq_halfPlane,← T.inradius_eq_sideDist.2.1]
  have hC : T.inradius ≤ T.sideLineC.toHalfPlane.pointDist (discToHalfPlane T.incenter) := by
    rw [← T.sideLineC.pointDist_eq_halfPlane,← T.inradius_eq_sideDist.2.2]
  intro z hz
  have hzBall : discToHalfPlane z ∈ Metric.ball (discToHalfPlane T.incenter) T.inradius := by
    change dist (discToHalfPlane z) (discToHalfPlane T.incenter) < T.inradius
    rw [dist_comm,← discPathDist_eq_halfPlane]
    exact hz
  have hi : discToHalfPlane z ∈ T.halfPlaneInterior := by
    rw [T.halfPlaneInterior_eq_components _ hcentre]
    exact ⟨T.sideLineA.toHalfPlane.ball_subset_openHalfPlane _ _ T.inradius_pos hA hzBall,
      T.sideLineB.toHalfPlane.ball_subset_openHalfPlane _ _ T.inradius_pos hB hzBall,
      T.sideLineC.toHalfPlane.ball_subset_openHalfPlane _ _ T.inradius_pos hC hzBall⟩
  change halfPlaneToDisc (discToHalfPlane z) ∈ T.interior at hi
  rwa [halfPlaneToDisc_discToHalfPlane] at hi

/-- Every point of the true in-circle lies in the actual finite/ideal closed triangle. -/
theorem ClosedDiscTriangle.incircle_subset_closedCarrier (T : ClosedDiscTriangle) {z : 𝔻}
    (hz : z ∈ T.incircle) : discToClosedModel z ∈ T.closedCarrier := by
  have hcl : z ∈ closure T.inball := by
    have he := disc_mem_closure_hyperbolic_ball T.incenter z T.inradius T.inradius_pos (le_of_eq hz)
    let := discHyperbolicMetric
    change z ∈ closure (Metric.ball T.incenter T.inradius) at he
    have hball : Metric.ball T.incenter T.inradius = T.inball := by
      ext x
      change dist x T.incenter < T.inradius ↔ discPathDist T.incenter x < T.inradius
      rw [discHyperbolicMetric_distance,discPathDist_eq_halfPlane,discPathDist_eq_halfPlane,dist_comm]
    rwa [hball] at he
  have hi : z ∈ closure T.interior := closure_mono T.inball_subset_interior hcl
  have hc : Continuous discToClosedModel := by
    change Continuous (fun z : 𝔻 => Complex.UnitClosedDisc.mk (z : ℂ) z.norm_lt_one.le)
    exact Complex.UnitDisc.continuous_coe.subtype_mk _
  rw [T.closedCarrier_eq_closedModelClosure,discClosedModelClosure]
  exact mem_closure_image hc.continuousAt hi

theorem ClosedDiscTriangle.incircle_sideLines_distinct (T : ClosedDiscTriangle) :
    T.sideLineA ≠ T.sideLineB ∧ T.sideLineA ≠ T.sideLineC ∧ T.sideLineB ≠ T.sideLineC := by
  refine ⟨?_,?_,?_⟩
  · intro h
    exact T.a_not_mem_sideLineA (by rw [h]; exact T.a_mem_sideLineB)
  · intro h
    exact T.a_not_mem_sideLineA (by rw [h]; exact T.a_mem_sideLineC)
  · intro h
    exact T.b_not_mem_sideLineB (by rw [h]; exact T.b_mem_sideLineC)

theorem ClosedDiscTriangle.incircle_ne_common_vertex (T : ClosedDiscTriangle)
    (L M : DiscLine) (p : 𝕔𝔻) (hLp : p ∈ L.closedCarrier) (hMp : p ∈ M.closedCarrier)
    (hLM : L ≠ M) (hLR : L.pointDist T.incenter = T.inradius)
    (hMR : M.pointDist T.incenter = T.inradius) (z : 𝔻) (hz : z ∈ T.incircle) :
    discToClosedModel z ≠ p := by
  intro he
  have hzL : z ∈ L.carrier := (L.closedCarrier_mem_interior_iff z).mp (by rw [he]; exact hLp)
  have hzM : z ∈ M.carrier := (M.closedCarrier_mem_interior_iff z).mp (by rw [he]; exact hMp)
  have hqz : T.incenter ≠ z := by
    intro h
    change discPathDist T.incenter z = T.inradius at hz
    rw [← h,discPathDist_eq_halfPlane,dist_self] at hz
    linarith [T.inradius_pos]
  exact hLM (L.eq_of_common_nearest_point M T.incenter z hqz hzL hzM
    (hLR.trans hz.symm) (hMR.trans hz.symm))

theorem ClosedDiscTriangle.incircle_avoids_vertices (T : ClosedDiscTriangle) {z : 𝔻}
    (hz : z ∈ T.incircle) : discToClosedModel z ≠ T.a ∧ discToClosedModel z ≠ T.b ∧
      discToClosedModel z ≠ T.c := by
  refine ⟨?_,?_,?_⟩
  · exact T.incircle_ne_common_vertex T.sideLineB T.sideLineC T.a
      T.a_mem_sideLineB T.a_mem_sideLineC T.incircle_sideLines_distinct.2.2
      T.inradius_eq_sideDist.2.1.symm T.inradius_eq_sideDist.2.2.symm z hz
  · exact T.incircle_ne_common_vertex T.sideLineA T.sideLineC T.b
      T.b_mem_sideLineA T.b_mem_sideLineC T.incircle_sideLines_distinct.2.1
      T.inradius_eq_sideDist.1.symm T.inradius_eq_sideDist.2.2.symm z hz
  · exact T.incircle_ne_common_vertex T.sideLineA T.sideLineB T.c
      T.c_mem_sideLineA T.c_mem_sideLineB T.incircle_sideLines_distinct.1
      T.inradius_eq_sideDist.1.symm T.inradius_eq_sideDist.2.1.symm z hz

/-- Each side geodesic meets the actual circle at its unique genuine nearest point. -/
theorem ClosedDiscTriangle.exists_unique_incircle_contact (T : ClosedDiscTriangle)
    (L : DiscLine) (hLR : L.pointDist T.incenter = T.inradius) :
    ∃! p : 𝔻, p ∈ T.incircle ∧ p ∈ L.carrier := by
  obtain ⟨p,⟨hp,hd⟩,huniq⟩ := L.exists_unique_nearest_point T.incenter
  refine ⟨p,⟨hd.symm.trans hLR,hp⟩,?_⟩
  intro q hq
  exact huniq q ⟨hq.2,hLR.trans hq.1.symm⟩

theorem ClosedDiscTriangle.incircle_contact_perpendicular (T : ClosedDiscTriangle)
    (L : DiscLine) (hLR : L.pointDist T.incenter = T.inradius) {p : 𝔻}
    (hp : p ∈ T.incircle) (hpL : p ∈ L.carrier) :
    ∃ N : DiscLine, T.incenter ∈ N.carrier ∧ L.OrthogonalAt N p :=
  L.nearest_point_perpendicular T.incenter p hpL (hLR.trans hp.symm)

/-- Every contact lies on the actual open side, including when the side endpoints are ideal. -/
theorem ClosedDiscTriangle.incircle_contact_open_sides (T : ClosedDiscTriangle) {p : 𝔻}
    (hp : p ∈ T.incircle) :
    (p ∈ T.sideLineA.carrier → discToClosedModel p ∈ T.sideA \ {T.b,T.c}) ∧
    (p ∈ T.sideLineB.carrier → discToClosedModel p ∈ T.sideB \ {T.c,T.a}) ∧
    (p ∈ T.sideLineC.carrier → discToClosedModel p ∈ T.sideC \ {T.a,T.b}) := by
  have hc : T.coordinate (discToClosedModel p) ∈ standardClosedTriangle := by
    rw [← T.coordinate_image_closedCarrier]
    exact mem_image_of_mem T.coordinate (T.incircle_subset_closedCarrier hp)
  have hn := T.incircle_avoids_vertices hp
  refine ⟨?_,?_,?_⟩
  · intro hL
    have hs := (T.sideLineA_iff_coordinate _).mp ((T.sideLineA.closedCarrier_mem_interior_iff p).mpr hL)
    refine ⟨?_,?_⟩
    · change discToClosedModel p ∈ closedModelDiscHSegment T.b T.c
      rw [T.mem_closedSegment_iff_coordinate,T.coordinate_b,T.coordinate_c,standard_opposite_segment]
      exact ⟨hc.1,hc.2.1,hs⟩
    · simp only [mem_insert_iff,mem_singleton_iff,not_or]
      exact ⟨hn.2.1,hn.2.2⟩
  · intro hL
    have hs := (T.sideLineB_iff_coordinate _).mp ((T.sideLineB.closedCarrier_mem_interior_iff p).mpr hL)
    refine ⟨?_,?_⟩
    · rw [T.mem_sideB_iff_coordinate]
      exact ⟨hc.2.1,by linarith [hc.2.2],hs⟩
    · simp only [mem_insert_iff,mem_singleton_iff,not_or]
      exact ⟨hn.2.2,hn.1⟩
  · intro hL
    have hs := (T.sideLineC_iff_coordinate _).mp ((T.sideLineC.closedCarrier_mem_interior_iff p).mpr hL)
    refine ⟨?_,?_⟩
    · rw [T.mem_sideC_iff_coordinate]
      exact ⟨hc.1,by linarith [hc.2.2],hs⟩
    · simp only [mem_insert_iff,mem_singleton_iff,not_or]
      exact ⟨hn.1,hn.2.1⟩

/-- Geometric contact: the actual circle meets this actual side at exactly one point,
which lies away from its endpoints and has a genuine perpendicular radius geodesic. -/
def IsIncircleContactOnOpenSide (T : ClosedDiscTriangle) (L : DiscLine)
    (side endpoints : Set 𝕔𝔻) (p : 𝔻) : Prop :=
  p ∈ T.incircle ∧ p ∈ L.carrier ∧ discToClosedModel p ∈ side \ endpoints ∧
    (∀ q : 𝔻, q ∈ T.incircle ∧ q ∈ L.carrier → q = p) ∧
    ∃ N : DiscLine, T.incenter ∈ N.carrier ∧ L.OrthogonalAt N p

/-- The three genuine tangent points of the actual inscribed circle. -/
theorem ClosedDiscTriangle.inscribed_circle_contacts (T : ClosedDiscTriangle) :
    ∃ a b c : 𝔻,
      IsIncircleContactOnOpenSide T T.sideLineA T.sideA {T.b,T.c} a ∧
      IsIncircleContactOnOpenSide T T.sideLineB T.sideB {T.c,T.a} b ∧
      IsIncircleContactOnOpenSide T T.sideLineC T.sideC {T.a,T.b} c := by
  obtain ⟨a,ha,huniqA⟩ := T.exists_unique_incircle_contact T.sideLineA T.inradius_eq_sideDist.1.symm
  obtain ⟨b,hb,huniqB⟩ := T.exists_unique_incircle_contact T.sideLineB T.inradius_eq_sideDist.2.1.symm
  obtain ⟨c,hc,huniqC⟩ := T.exists_unique_incircle_contact T.sideLineC T.inradius_eq_sideDist.2.2.symm
  refine ⟨a,b,c,?_,?_,?_⟩
  · exact ⟨ha.1,ha.2,(T.incircle_contact_open_sides ha.1).1 ha.2,huniqA,
      T.incircle_contact_perpendicular T.sideLineA T.inradius_eq_sideDist.1.symm ha.1 ha.2⟩
  · exact ⟨hb.1,hb.2,(T.incircle_contact_open_sides hb.1).2.1 hb.2,huniqB,
      T.incircle_contact_perpendicular T.sideLineB T.inradius_eq_sideDist.2.1.symm hb.1 hb.2⟩
  · exact ⟨hc.1,hc.2,(T.incircle_contact_open_sides hc.1).2.2 hc.2,huniqC,
      T.incircle_contact_perpendicular T.sideLineC T.inradius_eq_sideDist.2.2.symm hc.1 hc.2⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
