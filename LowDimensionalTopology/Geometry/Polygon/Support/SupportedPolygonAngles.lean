/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Support.SupportedDiscPolygons
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicNormalCoordinates
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter InnerProductGeometry
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The previous index is distinct from the current one in a genuine polygon. -/
theorem polygonSupport_prev_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (finRotate n).symm i ≠ i := by
  intro he
  have hh := congrArg (finRotate n) he
  rw [Equiv.apply_symm_apply] at hh
  exact polygonSupport_next_ne_self hn i hh.symm

/-- The two neighboring indices at a genuine corner are distinct. -/
theorem polygonSupport_prev_ne_next {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (finRotate n).symm i ≠ finRotate n i := by
  intro he
  have hh := congrArg (finRotate n) he
  rw [Equiv.apply_symm_apply] at hh
  exact polygonSupport_next_next_ne_self hn i hh.symm

/-- The genuine triangle formed by an actual supported corner and its two neighbors. -/
def DiscPolygonSupportData.cornerTriangle {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := S.vertices i
  b := S.vertices ((finRotate n).symm i)
  c := S.vertices (finRotate n i)
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    have hac : S.vertices i ≠ S.vertices (finRotate n i) := by
      intro he
      exact polygonSupport_next_ne_self S.three_le i (S.vertices_injective he).symm
    have he : L = S.supportLine i := L.eq_of_two_closed_points (S.supportLine i) hac ha hc
      (S.incident_mem_support i).1 (S.incident_mem_support i).2
    rw [he] at hb
    have heq := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _
      _).mp hb
    have hlt := S.nonincident i ((finRotate n).symm i)
      (polygonSupport_prev_ne_self S.three_le i) (polygonSupport_prev_ne_next S.three_le i)
    exact hlt.ne heq

/-- The genuine outgoing corner side is exactly its supplied native support. -/
theorem DiscPolygonSupportData.cornerTriangle_sideB {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    (S.cornerTriangle i).sideLineB = S.supportLine i := by
  let T := S.cornerTriangle i
  exact T.sideLineB.eq_of_two_closed_points (S.supportLine i) T.c_ne_a T.c_mem_sideLineB T.a_mem_sideLineB
    (S.incident_mem_support i).2 (S.incident_mem_support i).1

/-- The genuine incoming corner side is exactly the previous supplied native support. -/
theorem DiscPolygonSupportData.cornerTriangle_sideC {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    (S.cornerTriangle i).sideLineC = S.supportLine ((finRotate n).symm i) := by
  let T := S.cornerTriangle i
  apply T.sideLineC.eq_of_two_closed_points _ T.a_ne_b T.a_mem_sideLineC T.b_mem_sideLineC
  · change S.vertices i ∈ (S.supportLine ((finRotate n).symm i)).closedCarrier
    simpa only [Equiv.apply_symm_apply] using (S.incident_mem_support ((finRotate n).symm i)).2
  · exact (S.incident_mem_support ((finRotate n).symm i)).1

/-- The outgoing strict support condition is exactly positivity of the actual first corner coordinate. -/
theorem DiscPolygonSupportData.cornerTriangle_outgoing_cut {n : ℕ} (S : DiscPolygonSupportData n)
    (i : Fin n) (p : 𝕔𝔻) :
    inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) < S.offsets i ↔
      0 < ((S.cornerTriangle i).coordinate p).1 := by
  let T := S.cornerTriangle i
  let x := (T.coordinate p).1
  let s := inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
    ((finRotate n).symm i)))
  have hs : s < S.offsets i := S.nonincident i ((finRotate n).symm i)
    (polygonSupport_prev_ne_self S.three_le i) (polygonSupport_prev_ne_next S.three_le i)
  have he := T.inner_klein_reconstruction (S.normals i) p
  change inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) =
    inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) +
      x*(s-inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
        i))) +
      (T.coordinate p).2*(inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (S.vertices (finRotate n i)))-
        inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
          i))) at he
  rw [(S.incident i).1,(S.incident i).2,sub_self,mul_zero,add_zero] at he
  rw [he]
  constructor
  · intro h
    by_contra hx
    have hprod := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hx) (sub_nonpos.mpr hs.le)
    linarith only [h,hprod]
  · intro hx
    have hprod := mul_neg_of_pos_of_neg hx (sub_neg.mpr hs)
    linarith only [hprod]

/-- The incoming strict support condition is exactly positivity of the actual second corner coordinate. -/
theorem DiscPolygonSupportData.cornerTriangle_incoming_cut {n : ℕ} (S : DiscPolygonSupportData n)
    (i : Fin n) (p : 𝕔𝔻) :
    inner ℝ (S.normals ((finRotate n).symm i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p) < S.offsets ((finRotate n).symm i) ↔
      0 < ((S.cornerTriangle i).coordinate p).2 := by
  let T := S.cornerTriangle i
  let j := (finRotate n).symm i
  let y := (T.coordinate p).2
  let s := inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
    (finRotate n i)))
  have hji : finRotate n j = i := (finRotate n).apply_symm_apply i
  have hs : s < S.offsets j := by
    apply S.nonincident j (finRotate n i)
    · exact (polygonSupport_prev_ne_next S.three_le i).symm
    · rw [hji]
      exact polygonSupport_next_ne_self S.three_le i
  have ha : inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) = S.offsets j := by
    simpa only [hji] using (S.incident j).2
  have he := T.inner_klein_reconstruction (S.normals j) p
  change inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) =
    inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) +
      (T.coordinate p).1*(inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (S.vertices j))-
        inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
          i))) +
      y*(s-inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
        i))) at he
  rw [ha,(S.incident j).1,sub_self,mul_zero,add_zero] at he
  rw [he]
  constructor
  · intro h
    by_contra hy
    have hprod := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hy) (sub_nonpos.mpr hs.le)
    linarith only [h,hprod]
  · intro hy
    have hprod := mul_neg_of_pos_of_neg hy (sub_neg.mpr hs)
    linarith only [hprod]

/-- The genuine polygon interior selects the actual positive corner cone. -/
theorem DiscPolygonSupportData.cornerTriangle_origin_coordinates {n : ℕ} (S : DiscPolygonSupportData n)
    (i : Fin n) :
    0 < ((S.cornerTriangle i).discCoordinate (0 : 𝔻)).1 ∧
      0 < ((S.cornerTriangle i).discCoordinate (0 : 𝔻)).2 := by
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : 𝔻)) = 0 := by
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  constructor
  · apply (S.cornerTriangle_outgoing_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 :
    𝔻))).mp
    rw [hz,inner_zero_right]
    exact (S.offset_mem i).1
  · apply (S.cornerTriangle_incoming_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 :
    𝔻))).mp
    rw [hz,inner_zero_right]
    exact (S.offset_mem ((finRotate n).symm i)).1


/-- Genuine native triangle coordinates vary continuously. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.continuous_discCoordinate (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : Continuous T.discCoordinate := by
  have he : T.discCoordinate = fun z : 𝔻 => T.ambientCoordinateHomeomorph (z : ℂ) :=
    funext (fun z => (T.ambientCoordinateHomeomorph_disc z).symm)
  rw [he]
  exact T.ambientCoordinateHomeomorph.continuous.comp Complex.UnitDisc.continuous_coe

/-- Actual native triangle interior membership in its genuine affine coordinates. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.mem_interior_iff_discCoordinate (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻) :
    z ∈ T.interior ↔ 0 < (T.discCoordinate z).1 ∧ 0 < (T.discCoordinate z).2 ∧
      (T.discCoordinate z).1+(T.discCoordinate z).2 < 1 := by
  have he : T.complexInterior = T.ambientCoordinateHomeomorph ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle := by
    rw [← T.ambient_image_interior,Set.preimage_image_eq _ T.ambientCoordinateHomeomorph.injective]
  change (z : ℂ) ∈ T.complexInterior ↔ _
  rw [he]
  change T.ambientCoordinateHomeomorph (z :
    ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle ↔ _
  rw [T.ambientCoordinateHomeomorph_disc]
  rfl

/-- Near a genuine supported corner the actual polygon interior equals the actual corner-triangle interior. -/
theorem DiscPolygonSupportData.cornerTriangle_interior_germ {n : ℕ} (S : DiscPolygonSupportData n)
    (i : Fin n) (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    ∀ᶠ w in 𝓝 z,w ∈ S.toDiscPolygon.interior ↔ w ∈ (S.cornerTriangle i).interior := by
  let T := S.cornerTriangle i
  have hcoord : T.discCoordinate z = (0,0) := by
    change T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) = (0,0)
    rw [← hz]
    exact T.coordinate_a
  have hsum : ∀ᶠ w in 𝓝 z,(T.discCoordinate w).1+(T.discCoordinate w).2 < 1 := by
    apply (isOpen_lt (T.continuous_discCoordinate.fst.add T.continuous_discCoordinate.snd) continuous_const).mem_nhds
    change (T.discCoordinate z).1+(T.discCoordinate z).2 < 1
    rw [hcoord]
    norm_num
  have hother : ∀ j : Fin n,∀ᶠ w in 𝓝 z,j ≠ i → j ≠ (finRotate n).symm i →
      inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) < S.offsets j := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
    by_cases hjprev : j = (finRotate n).symm i
    · exact Filter.Eventually.of_forall (fun _ _ h => (h hjprev).elim)
    have hzj : inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) < S.offsets j := by
      rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion z,← hz]
      apply S.nonincident j i (Ne.symm hji)
      intro he
      apply hjprev
      exact (finRotate n).injective (by rw [Equiv.apply_symm_apply]; exact he.symm)
    have ho : IsOpen {w : 𝔻 | inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      w) < S.offsets j} :=
      isOpen_lt (continuous_const.inner
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate) continuous_const
    have hmem : ∀ᶠ w in 𝓝 z,inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      w) < S.offsets j := ho.mem_nhds hzj
    exact hmem.mono (fun _ h _ _ => h)
  filter_upwards [hsum,Filter.eventually_all.mpr hother] with w hsumw hotherw
  rw [S.toDiscPolygon_interior,T.mem_interior_iff_discCoordinate]
  change (∀ j : Fin n,inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) <
    S.offsets j) ↔ _
  constructor
  · intro hw
    exact ⟨(S.cornerTriangle_outgoing_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w)).mp
      (hw i),
      (S.cornerTriangle_incoming_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w)).mp (hw
        ((finRotate n).symm i)),hsumw⟩
  · rintro ⟨hx,hy,_⟩ j
    by_cases hji : j = i
    · subst j
      exact (S.cornerTriangle_outgoing_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        w)).mpr hx
    by_cases hjprev : j = (finRotate n).symm i
    · subst j
      exact (S.cornerTriangle_incoming_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        w)).mpr hy
    exact hotherw j hji hjprev

/-- The genuine incoming native ray agrees with its corner-triangle ray. -/
theorem DiscPolygonSupportData.cornerRayPrev_eq {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n)
    (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    S.toDiscPolygon.cornerRayPrev i z hz = (S.cornerTriangle i).cornerRayABAtA z hz := by
  exact (S.cornerTriangle i).rayToward_b z hz _

/-- The genuine outgoing native ray agrees with its corner-triangle ray. -/
theorem DiscPolygonSupportData.cornerRayNext_eq {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n)
    (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    S.toDiscPolygon.cornerRayNext i z hz = (S.cornerTriangle i).cornerRayACAtA z hz := by
  exact (S.cornerTriangle i).rayToward_c z hz _

/-- Actual interior germs select the genuine minor branch at every finite supported corner. -/
theorem DiscPolygonSupportData.hasMinorInterior {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n)
    (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    S.toDiscPolygon.HasMinorInteriorAt i z hz := by
  let T := S.cornerTriangle i
  change ∀ᶠ w in 𝓝 z,w ∈ S.toDiscPolygon.interior ↔ w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior
    (S.toDiscPolygon.cornerRayPrev i z hz) (S.toDiscPolygon.cornerRayNext i z hz)
  rw [S.cornerRayPrev_eq i z hz,S.cornerRayNext_eq i z hz]
  let polygonSupportAngleNativeMetric : MetricSpace 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := T.cornerAtA_locally_interior z hz
  filter_upwards [S.cornerTriangle_interior_germ i z hz,Metric.ball_mem_nhds z hr] with w hw hball
  have hm := congrArg (fun U : Set 𝔻 => w ∈ U) he
  exact hw.trans (by simpa only [mem_inter_iff,hball,true_and] using iff_of_eq hm)

/-- The actual polygon interior angle is exactly the genuine corner-triangle angle, including ideal corners. -/
theorem DiscPolygonSupportData.angle_eq_cornerTriangle {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    S.toDiscPolygon.angle i = (S.cornerTriangle i).alpha := by
  let T := S.cornerTriangle i
  by_cases hi : ‖(S.vertices i : ℂ)‖ < 1
  · let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (S.vertices i) hi
    have hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
    rw [S.toDiscPolygon.angle_of_minor i z hz (S.hasMinorInterior i z hz),
      S.cornerRayPrev_eq i z hz,S.cornerRayNext_eq i z hz,T.alpha_of_finite z hz]
  · have hi' := le_antisymm (S.vertices i).norm_le_one (le_of_not_gt hi)
    rw [S.toDiscPolygon.angle_of_ideal i hi',T.alpha_of_ideal hi']

end
end LowDimensionalTopology.Geometry.Polygon
