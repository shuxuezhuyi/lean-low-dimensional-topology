module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicInversiveProducts
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open InnerProductGeometry
noncomputable section

/-- A concrete annular seed with actual native line normals; no hexagon is asserted. -/
theorem exists_annular_three_circle_seed (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ E r x : ℝ, ∃ hE : 0 < E, ∃ hr : 0 < r,
      1 < E ∧ 1 + r < x ∧ x + r < E ∧
      (HalfPlaneLine.circle 0 1 (by norm_num)).normalPairing
        (HalfPlaneLine.circle 0 E hE) = Real.cosh a ∧
      (HalfPlaneLine.circle 0 1 (by norm_num)).normalPairing
        (HalfPlaneLine.circle x r hr) = -Real.cosh b ∧
      (HalfPlaneLine.circle 0 E hE).normalPairing
        (HalfPlaneLine.circle x r hr) = Real.cosh c := by
  let E := Real.exp a
  let B := Real.cosh b
  let C := Real.cosh c
  let D := 2 * (B + E * C)
  let r := (E ^ 2 - 1) / D
  let x := Real.sqrt (r ^ 2 + 1 + 2 * r * B)
  have hE : 1 < E := Real.one_lt_exp_iff.mpr ha
  have hE0 : 0 < E := lt_trans zero_lt_one hE
  have hB : 1 < B := Real.one_lt_cosh.mpr hb.ne'
  have hC : 1 < C := Real.one_lt_cosh.mpr hc.ne'
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  have hC0 : 0 < C := lt_trans zero_lt_one hC
  have hD : 0 < D := by dsimp only [D]; positivity
  have hr : 0 < r := div_pos (by nlinarith : 0 < E ^ 2 - 1) hD
  have hrD : r * (2 * (B + E * C)) = E ^ 2 - 1 := by
    change ((E ^ 2 - 1) / D) * D = E ^ 2 - 1
    exact div_mul_cancel₀ _ hD.ne'
  have hrhalf : r < E / 2 := by
    change (E ^ 2 - 1) / D < E / 2
    apply (div_lt_iff₀ hD).mpr
    dsimp only [D]
    have hEB : 0 < E * B := mul_pos hE0 (lt_trans zero_lt_one hB)
    have hEC : 0 ≤ E ^ 2 * (C - 1) :=
      mul_nonneg (sq_nonneg E) (sub_nonneg.mpr hC.le)
    nlinarith only [hEB, hEC]
  have hxarg : 0 < r ^ 2 + 1 + 2 * r * B := by positivity
  have hx : 0 < x := Real.sqrt_pos.mpr hxarg
  have hx2 : x ^ 2 = r ^ 2 + 1 + 2 * r * B := Real.sq_sqrt hxarg.le
  have hinner : 1 + r < x := by
    have hgap : 0 < 2 * r * (B - 1) :=
      mul_pos (by positivity) (sub_pos.mpr hB)
    apply (sq_lt_sq₀ (by positivity : 0 ≤ 1 + r) hx.le).mp
    nlinarith only [hx2, hgap]
  have houter : x + r < E := by
    have hgap : 0 < 2 * r * E * (C - 1) :=
      mul_pos (by positivity) (sub_pos.mpr hC)
    have hs : x ^ 2 < (E - r) ^ 2 := by nlinarith only [hx2, hrD, hgap]
    have hEr : 0 ≤ E - r := by linarith
    have hlt := (sq_lt_sq₀ hx.le hEr).mp hs
    linarith
  have hcosh : Real.cosh a = (E + E⁻¹) / 2 := by
    simpa only [E, Real.log_exp] using (Real.cosh_log hE0)
  refine ⟨E, r, x, hE0, hr, hE, hinner, houter, ?_, ?_, ?_⟩
  · rw [hcosh]
    simp only [HalfPlaneLine.normalPairing, HalfPlaneLine.incenterNormal,
      HalfPlaneLine.incenterOffset,
      LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    field_simp [hE0.ne']
    ring
  · change (HalfPlaneLine.circle 0 1 (by norm_num)).normalPairing
        (HalfPlaneLine.circle x r hr) = -B
    simp only [HalfPlaneLine.normalPairing, HalfPlaneLine.incenterNormal,
      HalfPlaneLine.incenterOffset,
      LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    field_simp [hr.ne']
    nlinarith only [hx2]
  · change (HalfPlaneLine.circle 0 E hE0).normalPairing
        (HalfPlaneLine.circle x r hr) = C
    simp only [HalfPlaneLine.normalPairing, HalfPlaneLine.incenterNormal,
      HalfPlaneLine.incenterOffset,
      LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    field_simp [hE0.ne', hr.ne']
    nlinarith only [hx2, hrD]

end
end LowDimensionalTopology.Geometry.Hyperbolic
