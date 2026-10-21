/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Disk
/-! # Actual polygon interior germs and finite, ideal and reflex angle conventions.
The general local Jordan-corner classification remains a separate unfinished obligation. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
open Set Filter InnerProductGeometry
open scoped Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

local instance polygonAnglesPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual polygon interior has the germ of the smaller angle between its true adjacent rays. -/
def DiscPolygon.HasMinorInteriorAt {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) : Prop :=
  ∀ᶠ w in 𝓝 z,w ∈ P.interior ↔
    w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (P.cornerRayPrev i z
      hz) (P.cornerRayNext i z hz)

/-- The interior angle uses the genuine forward tangents and the actual local interior germ.
At an ideal vertex it is zero. Straight finite corners have angle pi in either branch. -/
def DiscPolygon.angle {n : ℕ} (P : DiscPolygon n) (i : Fin n) : ℝ := by
  classical
  exact if hi : ‖(P.vertices i : ℂ)‖ < 1 then
    let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) hi
    let hz := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec (P.vertices i) hi).symm
    let θ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z
      hz) (P.cornerRayNext i z hz)
    if P.HasMinorInteriorAt i z hz then θ else 2*Real.pi-θ
  else 0

theorem DiscPolygon.angle_of_finite {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    P.angle i = if P.HasMinorInteriorAt i z hz then
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z
        hz) (P.cornerRayNext i z hz)
    else 2*Real.pi-_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz) := by
  classical
  have hi : ‖(P.vertices i : ℂ)‖ < 1 := by rw [hz]; exact z.norm_lt_one
  rw [DiscPolygon.angle,dite_eq_left hi]
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) hi = z := by
    apply Complex.UnitDisc.coe_injective
    exact congrArg (fun p : 𝕔𝔻 => (p : ℂ)) hz
  subst z
  rfl

theorem DiscPolygon.angle_of_ideal {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (hi : ‖(P.vertices i : ℂ)‖ = 1) : P.angle i = 0 := by
  simp only [DiscPolygon.angle,hi,lt_self_iff_false,dite_eq_right,not_false_eq_true]

theorem DiscPolygon.angle_of_minor {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hminor :
      P.HasMinorInteriorAt i z hz) :
    P.angle i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz) := by
  rw [P.angle_of_finite i z hz,ite_eq_left hminor]

theorem DiscPolygon.angle_of_not_minor {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hminor :
      ¬P.HasMinorInteriorAt i z hz) :
    P.angle i = 2*Real.pi-_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz) := by
  rw [P.angle_of_finite i z hz,ite_eq_right hminor]

theorem DiscPolygon.angle_mem_Icc {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    P.angle i ∈ Icc (0 : ℝ) (2*Real.pi) := by
  by_cases hi : ‖(P.vertices i : ℂ)‖ < 1
  · let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) hi
    have hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
    rw [P.angle_of_finite i z hz]
    have h0 : 0 ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z
      hz) (P.cornerRayNext i z hz) := angle_nonneg _ _
    have hπ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z
      hz) (P.cornerRayNext i z hz) ≤ Real.pi := angle_le_pi _ _
    split_ifs <;> constructor <;> linarith [Real.pi_pos]
  · rw [P.angle_of_ideal i (le_antisymm (P.vertices i).norm_le_one (le_of_not_gt hi))]
    exact ⟨le_rfl,by positivity⟩

theorem DiscPolygon.angle_eq_pi_of_straight {n : ℕ} (P : DiscPolygon n) (i : Fin n) (z : 𝔻)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hstraight : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz)
      (P.cornerRayNext i z hz) = Real.pi) :
    P.angle i = Real.pi := by
  rw [P.angle_of_finite i z hz,hstraight]
  split_ifs <;> ring

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.rayToward_b (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hzb :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ T.b) :
    discRayTowardClosed z T.b hzb = T.cornerRayABAtA z ha := by
  by_cases hb : ‖(T.b : ℂ)‖ < 1
  · have hz : z ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint T.b hb := by
      intro he
      apply hzb
      rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec]
    have hr : discRayTowardClosed z T.b hzb = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint T.b hb) hz := by
      rw [discRayTowardClosed,dite_eq_left hb]
    rw [hr,T.cornerAB_eq_through_finite z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint T.b
      hb) ha
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec T.b hb).symm hz]
  · have hb' := le_antisymm T.b.norm_le_one (le_of_not_gt hb)
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.eq_of_idealEndpoint_eq
    rw [discRayTowardClosed_idealEndpoint z T.b hzb hb',T.cornerRayABAtA_idealEndpoint z ha hb']

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.rayToward_c (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hzc :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ T.c) :
    discRayTowardClosed z T.c hzc = T.cornerRayACAtA z ha := by
  by_cases hc : ‖(T.c : ℂ)‖ < 1
  · have hz : z ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint T.c hc := by
      intro he
      apply hzc
      rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec]
    have hr : discRayTowardClosed z T.c hzc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint T.c hc) hz := by
      rw [discRayTowardClosed,dite_eq_left hc]
    rw [hr,T.cornerAC_eq_through_finite z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint T.c
      hc) ha
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec T.c hc).symm hz]
  · have hc' := le_antisymm T.c.norm_le_one (le_of_not_gt hc)
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.eq_of_idealEndpoint_eq
    rw [discRayTowardClosed_idealEndpoint z T.c hzc hc',T.cornerRayACAtA_idealEndpoint z ha hc']

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_cornerNext_zero (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    T.toDiscPolygon.cornerRayNext 0 z ha = T.cornerRayABAtA z ha := by
  change discRayTowardClosed z T.b _ = _
  exact T.rayToward_b z ha _

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_cornerPrev_zero (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    T.toDiscPolygon.cornerRayPrev 0 z ha = T.cornerRayACAtA z ha := by
  change discRayTowardClosed z T.c _ = _
  exact T.rayToward_c z ha _

/-- The minor branch is selected by the actual triangle interior, with no angle hypothesis. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_hasMinorInterior_zero (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) : T.toDiscPolygon.HasMinorInteriorAt 0 z ha := by
  change ∀ᶠ w in 𝓝 z,w ∈ T.toDiscPolygon.interior ↔ w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior
    (T.toDiscPolygon.cornerRayPrev 0 z ha) (T.toDiscPolygon.cornerRayNext 0 z ha)
  rw [T.toDiscPolygon_interior,T.toDiscPolygon_cornerNext_zero z ha,T.toDiscPolygon_cornerPrev_zero z ha]
  have hcomm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (T.cornerRayACAtA z
    ha) (T.cornerRayABAtA z ha) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (T.cornerRayABAtA z ha) (T.cornerRayACAtA z ha) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior_eq_sides,_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior_eq_sides,inter_comm]
  rw [hcomm]
  let polygonAngleNativeMetric : MetricSpace 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := T.cornerAtA_locally_interior z ha
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  have hm := congrArg (fun S : Set 𝔻 => w ∈ S) he
  simpa only [mem_inter_iff,hw,true_and] using iff_of_eq hm

/-- The new polygon-angle convention exactly recovers the established true triangle corner angle. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_angle_zero (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    T.toDiscPolygon.angle 0 = T.alpha := by
  by_cases ha : ‖(T.a : ℂ)‖ < 1
  · let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint T.a ha
    have hz : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ ha).symm
    rw [T.toDiscPolygon.angle_of_minor 0 z hz (T.toDiscPolygon_hasMinorInterior_zero z hz),
      T.toDiscPolygon_cornerNext_zero z hz,T.toDiscPolygon_cornerPrev_zero z hz,T.alpha_of_finite z hz]
    exact angle_comm _ _
  · have ha' := le_antisymm T.a.norm_le_one (le_of_not_gt ha)
    rw [T.toDiscPolygon.angle_of_ideal 0 ha',T.alpha_of_ideal ha']

end
end LowDimensionalTopology.Geometry.Polygon
