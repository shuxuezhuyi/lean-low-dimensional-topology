module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.HalfPlaneRectifiableMinimizers
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.LocalGeodesicLength

/-!
# A locally minimizing original-surface arc has a geodesic branch trace

The competing curves are actual native C1 curves on the original surface.
Their native integral length agrees with the covering length by the preceding
bridge. Small endpoint balls ensure the genuine geodesic competitor remains in
the actual covering patch. The arbitrary original BV arc therefore has the
same full length as endpoint distance and the exact geodesic trace.

This theorem makes the branch and the minimizing inequality explicit. The
remaining intrinsic chartwise-BV interface is not hidden in a curve structure.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- An actual rectifiable branch arc that minimizes against every original
native C1 competitor in the patch has the unique hyperbolic segment trace.
No speed, absolute continuity or regularity of its original parameter is used. -/
theorem HyperbolicSurfaceModel.rectifiable_minimizing_arc_trace_in_cover_patch
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R)
    (E : OpenPartialHomeomorph ℍ X) (hpE : M.halfPlaneCover = E)
    (o : ℍ) {r : ℝ} (hpatch : Metric.ball o (3 * r) ⊆ E.source)
    {z w : ℍ} (hz : z ∈ Metric.ball o r) (hw : w ∈ Metric.ball o r) (hzw : z ≠ w)
    (c : RectifiableCurve) (hc : c.IsPathIn LiZhongQC.upperHalf z w)
    (hminimum : ∀ q : HyperbolicSurfaceC1CurvePiece M,
      (∀ t : I, q.curve t ∈ E.target) →
      q.curve 0 = M.halfPlaneCover z → q.curve 1 = M.halfPlaneCover w →
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) ≤ ENNReal.ofReal q.length) :
    c.curve '' Icc c.a c.b = ((↑) : ℍ → ℂ) '' closedHSegment z w := by
  obtain ⟨_a, _b, g, _ha, _hb, _hab, hg, _hga, _hgb, hgz, hgw, hi⟩ :=
    exists_ordered_ideal_normalizer z w hzw
  let a := Real.log (g • z).im
  let b := Real.log (g • w).im
  have hab : a < b := Real.log_lt_log (g • z).im_pos hi
  let γ := normalizerGeodesic g
  have hγ : IsHGeodesicParam γ :=
    ⟨normalizerGeodesic_isometry g hg, normalizerGeodesic_isHLine g hg⟩
  have hγa : γ a = z := normalizerGeodesic_parameter g z hgz
  have hγb : γ b = w := normalizerGeodesic_parameter g w hgw
  have hlen : b - a = dist z w := by
    have hd := metric_vertical_distance_of_im_le (hgz.trans hgw.symm) hi.le
    rw [realGL_distance] at hd
    exact hd.symm
  obtain ⟨q, hqpoint, hqlen⟩ := M.exists_projected_geodesic_c1_piece hγ a b hab.le
  have hqtrace (t : I) : γ (a + (b - a) * (t : ℝ)) ∈ closedHSegment z w := by
    have hlo : 0 ≤ (b - a) * (t : ℝ) := mul_nonneg (sub_nonneg.mpr hab.le) t.property.1
    have hhi : (b - a) * (t : ℝ) ≤ b - a :=
      mul_le_of_le_one_right (sub_nonneg.mpr hab.le) t.property.2
    exact ⟨γ, hγ, a, b, hab.le, hγa, hγb, a + (b - a) * (t : ℝ),
      ⟨by linarith, by linarith⟩, rfl⟩
  have hqU (t : I) : q.curve t ∈ E.target := by
    have hseg := hqtrace t
    have htri := dist_triangle_eq_of_mem_closedHSegment hseg
    have hzu : dist z (γ (a + (b - a) * (t : ℝ))) ≤ dist z w := by
      linarith [dist_nonneg (x := γ (a + (b - a) * (t : ℝ))) (y := w)]
    have hzwlt : dist z w < 2 * r := by
      have hz' : dist o z < r := by simpa only [Metric.mem_ball, dist_comm] using hz
      have hw' : dist o w < r := by simpa only [Metric.mem_ball, dist_comm] using hw
      have hd := dist_triangle z o w
      rw [dist_comm z o] at hd
      linarith
    have hball : γ (a + (b - a) * (t : ℝ)) ∈ Metric.ball o (3 * r) := by
      have hz' : dist o z < r := by simpa only [Metric.mem_ball, dist_comm] using hz
      rw [Metric.mem_ball, dist_comm]
      have hd := dist_triangle o z (γ (a + (b - a) * (t : ℝ)))
      linarith
    rw [hqpoint t, hpE]
    exact E.map_source (hpatch hball)
  have hq0 : q.curve 0 = M.halfPlaneCover z := by
    rw [hqpoint]
    simp only [Set.Icc.coe_zero, mul_zero, add_zero, hγa]
  have hq1 : q.curve 1 = M.halfPlaneCover w := by
    have he : a + (b - a) = b := by ring
    rw [hqpoint]
    simp only [Set.Icc.coe_one, mul_one, he, hγb]
  have hupper := hminimum q hqU hq0 hq1
  rw [hqlen, hlen] at hupper
  have hlower : ENNReal.ofReal (dist z w) ≤
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
    rw [← halfPlane_rectifiable_distance z w]
    exact iInf₂_le c hc
  exact rectifiable_trace_eq_closedHSegment_of_minimizing c hzw hc
    (le_antisymm hupper hlower)

end LowDimensionalTopology.Geometry.Surfaces
