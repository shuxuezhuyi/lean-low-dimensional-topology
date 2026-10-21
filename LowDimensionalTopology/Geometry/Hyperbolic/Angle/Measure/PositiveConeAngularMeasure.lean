module
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Metric InnerProductGeometry
open scoped Complex.UnitDisc Topology Classical NNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

local notation "𝔸" => AddCircle (2 * Real.pi)








/-- The actual native disc portion of the ordinary nonnegative planar cone. -/
def discPositiveCone (u v : ℂ) : Set 𝔻 :=
  {z | (z : ℂ) ∈ Submodule.span ℝ≥0 {u, v}}

theorem discRadialDirections_positiveCone (u v : ℂ) :
    discRadialDirections (discPositiveCone u v) =
      {x : Circle | (x : ℂ) ∈ Submodule.span ℝ≥0 {u, v}} := by
  ext x
  constructor
  · rintro ⟨r, hr⟩
    let c : ℝ≥0 := ⟨r.val, r.property.1.le⟩
    have hc : c ≠ 0 := by
      intro he
      have he' := congrArg (fun c : ℝ≥0 => (c : ℝ)) he
      change r.val = 0 at he'
      exact r.property.1.ne' he'
    change c • (x : ℂ) ∈ Submodule.span ℝ≥0 {u, v} at hr
    exact (Submodule.smul_mem_iff _ hc).mp hr
  · intro hx
    let r := discRadialTestRadius 0
    refine ⟨r, ?_⟩
    change (⟨r.val, r.property.1.le⟩ : ℝ≥0) • (x : ℂ) ∈ Submodule.span ℝ≥0 {u, v}
    exact Submodule.smul_mem _ _ hx

theorem discSubtendedAngle_positiveCone_endpoints (a : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hrπ : r < Real.pi / 2) :
    discSubtendedAngle (discPositiveCone (Circle.exp (a - r) : ℂ)
      (Circle.exp (a + r) : ℂ)) 0 =
        angle (Circle.exp (a - r) : ℂ) (Circle.exp (a + r) : ℂ) := by
  rw [discSubtendedAngle, discSubtendedAngularFraction_zero,
    discRadialDirections_positiveCone]
  have he : {x : Circle | (x : ℂ) ∈ Submodule.span ℝ≥0
      {(Circle.exp (a - r) : ℂ), (Circle.exp (a + r) : ℂ)}} =
      _root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc (a : 𝔸) r := by
    ext x
    exact _root_.LowDimensionalTopology.Geometry.Euclidean.circle_mem_positiveCone_endpoints a hr hrπ x
  rw [he]
  exact polygonDirectionMeasure_closedArc_eq_geometric_angle a hr hrπ.le

theorem discSubtendedAngle_positiveCone_circle (u v : Circle)
    (hangle : angle (u : ℂ) (v : ℂ) < Real.pi) :
    discSubtendedAngle (discPositiveCone (u : ℂ) (v : ℂ)) 0 = angle (u : ℂ) (v : ℂ) := by
  obtain ⟨a, r, hr, hrπ,
    hpair⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.circle_exists_short_arc_endpoints u v hangle
  rcases hpair with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · rw [hu, hv]
    exact discSubtendedAngle_positiveCone_endpoints a hr hrπ
  · have he : discPositiveCone (u : ℂ) (v : ℂ) = discPositiveCone (v : ℂ) (u : ℂ) := by
      simp only [discPositiveCone, Set.pair_comm]
    rw [he, angle_comm, hv, hu]
    exact discSubtendedAngle_positiveCone_endpoints a hr hrπ

theorem discPositiveCone_eq_nonnegative_combinations (u v : ℂ) :
    discPositiveCone u v =
      {z : 𝔻 | ∃ a : ℝ, 0 ≤ a ∧ ∃ b : ℝ, 0 ≤ b ∧ (z : ℂ) = a • u + b • v} := by
  ext z
  rw [discPositiveCone]
  change ((z : ℂ) ∈ Submodule.span ℝ≥0 {u,v}) ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, he⟩
    exact ⟨a, a.property, b, b.property, he.symm⟩
  · rintro ⟨a, ha, b, hb, he⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, he.symm⟩

/-- The genuine angular measure of an arbitrary proper nonnegative planar cone is its actual Euclidean angle. -/
theorem discSubtendedAngle_positiveCone {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hangle : angle u v < Real.pi) :
    discSubtendedAngle (discPositiveCone u v) 0 = angle u v := by
  let U := Circle.exp (Complex.arg u)
  let V := Circle.exp (Complex.arg v)
  have hU : ‖u‖ • (U : ℂ) = u := by
    simpa only [U, Complex.real_smul, Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I u
  have hV : ‖v‖ • (V : ℂ) = v := by
    simpa only [V, Complex.real_smul, Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I v
  have hθ : angle u v = angle (U : ℂ) (V : ℂ) := by
    rw [← hU, ← hV,
      angle_smul_left_of_pos _ _ (norm_pos_iff.mpr hu),
      angle_smul_right_of_pos _ _ (norm_pos_iff.mpr hv)]
  have hcone : discPositiveCone u v = discPositiveCone (U : ℂ) (V : ℂ) := by
    ext z
    change (z : ℂ) ∈ Submodule.span ℝ≥0 {u,v} ↔
      (z : ℂ) ∈ Submodule.span ℝ≥0 {(U : ℂ),(V : ℂ)}
    rw [← hU, ← hV]
    exact _root_.LowDimensionalTopology.Geometry.Euclidean.positiveCone_span_smul_mem_iff ‖u‖ ‖v‖ (norm_pos_iff.mpr
      hu) (norm_pos_iff.mpr hv)
  rw [hcone, hθ]
  exact discSubtendedAngle_positiveCone_circle U V (by rwa [← hθ])

end
end LowDimensionalTopology.Geometry.Hyperbolic
