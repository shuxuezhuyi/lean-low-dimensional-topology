/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

theorem complex_angle_I_sin_mul_norm (v : ℂ) :
    Real.sin (angle Complex.I v) * ‖v‖ = |v.re| := by
  have h := sin_angle_mul_norm_mul_norm Complex.I v
  rw [Complex.norm_I,one_mul] at h
  simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    mul_zero,mul_one,zero_add] at h
  convert h using 1
  rw [show v.re * v.re + v.im * v.im - v.im * v.im = v.re ^ 2 by ring,Real.sqrt_sq_eq_abs]

theorem upwardRay_angle_coordinates {z w : ℍ} (hzw : z ≠ w) (R : HRayAt z)
    (hEnd : R.idealEndpoint = ∞) :
    Real.sin (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
        (2 * z.im * w.im * Real.sinh (dist z w)) = 2 * z.im * |w.re - z.re| ∧
    Real.cos (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
        (2 * z.im * w.im * Real.sinh (dist z w)) =
      (w.re - z.re) ^ 2 + w.im ^ 2 - z.im ^ 2 := by
  obtain ⟨r,hr,he⟩ := hyperbolicDirection_pos_smul_tangent (hRayThrough z w hzw)
    (hRayThrough_mem _ _ _) hzw.symm
  have hang : hInteriorAngleMeasure R (hRayThrough z w hzw) =
      angle Complex.I (hyperbolicDirection z w) := by
    rw [hInteriorAngleMeasure,R.tangentVector_of_idealEndpoint_infty hEnd,he,
      angle_smul_right_of_pos _ _ hr]
  have hnorm : ‖hyperbolicDirection z w‖ = 2 * z.im * w.im * Real.sinh (dist z w) :=
    hyperbolicDirection_norm z w
  constructor
  · rw [hang,← hnorm,complex_angle_I_sin_mul_norm]
    change |2 * z.im * (w.re-z.re)| = _
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos z.im_pos]
  · have h := cos_angle_mul_norm_mul_norm Complex.I (hyperbolicDirection z w)
    rw [Complex.norm_I,one_mul,hnorm,←
      hang,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] at h
    simpa only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,hyperbolicDirection] using h

/-- The two ideal-vertex identities for genuine upward rays at arbitrary finite points. -/
theorem upwardRays_trigonometry {z w : ℍ} (hzw : z ≠ w) (hx : z.re ≠ w.re)
    (R : HRayAt z) (S : HRayAt w) (hR : R.idealEndpoint = ∞) (hS : S.idealEndpoint = ∞) :
    Real.cosh (dist z w) =
        (1 + Real.cos (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
          Real.cos (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) /
        (Real.sin (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
          Real.sin (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) ∧
    Real.sinh (dist z w) =
        (Real.cos (hInteriorAngleMeasure R (hRayThrough z w hzw)) +
          Real.cos (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) /
        (Real.sin (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
          Real.sin (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) := by
  let α := hInteriorAngleMeasure R (hRayThrough z w hzw)
  let β := hInteriorAngleMeasure S (hRayThrough w z hzw.symm)
  let d := dist z w
  let D := 2 * z.im * w.im * Real.sinh d
  have hs : 0 < Real.sinh d := Real.sinh_pos_iff.mpr (dist_pos.mpr hzw)
  have hD : D ≠ 0 := ne_of_gt (by dsimp only [D]; positivity)
  obtain ⟨hsa,hca⟩ := upwardRay_angle_coordinates hzw R hR
  obtain ⟨hsb,hcb⟩ := upwardRay_angle_coordinates hzw.symm S hS
  change Real.sin α * D = _ at hsa
  change Real.cos α * D = _ at hca
  have hsb' : Real.sin β * D = 2 * w.im * |w.re-z.re| := by
    simpa only [D,d,dist_comm,mul_comm,mul_left_comm,mul_assoc,abs_sub_comm] using hsb
  have hcb' : Real.cos β * D = (w.re-z.re)^2 + z.im^2-w.im^2 := by
    simpa only [D,d,dist_comm,mul_comm,mul_left_comm,mul_assoc,sub_sq_comm] using hcb
  have hsinα : Real.sin α = (2*z.im*|w.re-z.re|)/D := (eq_div_iff hD).mpr hsa
  have hsinβ : Real.sin β = (2*w.im*|w.re-z.re|)/D := (eq_div_iff hD).mpr hsb'
  have hcosα : Real.cos α = ((w.re-z.re)^2+w.im^2-z.im^2)/D := (eq_div_iff hD).mpr hca
  have hcosβ : Real.cos β = ((w.re-z.re)^2+z.im^2-w.im^2)/D := (eq_div_iff hD).mpr hcb'
  have habs := sq_abs (w.re-z.re)
  have hch : 2*z.im*w.im*Real.cosh d = (w.re-z.re)^2+z.im^2+w.im^2 := by
    dsimp only [d]
    rw [UpperHalfPlane.cosh_dist',mul_div_cancel₀ _ (by positivity : 2*z.im*w.im ≠ 0),sub_sq_comm]
  have hsh : Real.sinh d ^2 - Real.cosh d ^2 + 1 = 0 := by rw [Real.sinh_sq]; ring
  have ht : 0 < |w.re-z.re| := abs_pos.mpr (sub_ne_zero.mpr hx.symm)
  have hprod : Real.sin α * Real.sin β ≠ 0 := by
    rw [hsinα,hsinβ]
    exact mul_ne_zero (div_ne_zero (ne_of_gt (by positivity : 0 < 2*z.im*|w.re-z.re|)) hD)
      (div_ne_zero (ne_of_gt (by positivity : 0 < 2*w.im*|w.re-z.re|)) hD)
  constructor
  · apply (eq_div_iff hprod).mpr
    rw [hsinα,hsinβ,hcosα,hcosβ]
    field_simp
    dsimp only [D]
    linear_combination (4*z.im*w.im*Real.cosh d)*habs -
      (2*z.im*w.im*Real.cosh d - (w.re-z.re)^2+z.im^2+w.im^2)*hch -
      (4*z.im^2*w.im^2)*hsh
  · apply (eq_div_iff hprod).mpr
    rw [hsinα,hsinβ,hcosα,hcosβ]
    field_simp
    dsimp only [D]
    linear_combination (4*z.im*w.im*Real.sinh d)*habs

/-- Genuine shared-endpoint rays satisfy both one-ideal-vertex side-angle identities. -/
theorem hOneIdealTriangle_trigonometry {z w : ℍ} (hzw : z ≠ w)
    (R : HRayAt z) (S : HRayAt w) (hend : R.idealEndpoint = S.idealEndpoint)
    (hα : Real.sin (hInteriorAngleMeasure R (hRayThrough z w hzw)) ≠ 0) :
    Real.cosh (dist z w) =
        (1 + Real.cos (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
          Real.cos (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) /
        (Real.sin (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
          Real.sin (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) ∧
    Real.sinh (dist z w) =
        (Real.cos (hInteriorAngleMeasure R (hRayThrough z w hzw)) +
          Real.cos (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) /
        (Real.sin (hInteriorAngleMeasure R (hRayThrough z w hzw)) *
          Real.sin (hInteriorAngleMeasure S (hRayThrough w z hzw.symm))) := by
  obtain ⟨s,_,hR⟩ := R.exists_sl2_normalized_upward
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0 < g.val.det := by change 0 < s.val.det; rw [s.property]; norm_num
  have hS : (S.realGLMap g).idealEndpoint = ∞ := by
    rw [S.realGLMap_idealEndpoint g hg,← hend,← R.realGLMap_idealEndpoint g hg]
    exact hR
  have hne := (realGL_isometry g).injective.ne hzw
  have hθ : hInteriorAngleMeasure (R.realGLMap g) (hRayThrough (g • z) (g • w) hne) =
      hInteriorAngleMeasure R (hRayThrough z w hzw) := by
    rw [← hRayThrough_realGLMap,hInteriorAngleMeasure_realGLMap]
  have hφ : hInteriorAngleMeasure (S.realGLMap g) (hRayThrough (g • w) (g • z) hne.symm) =
      hInteriorAngleMeasure S (hRayThrough w z hzw.symm) := by
    rw [← hRayThrough_realGLMap,hInteriorAngleMeasure_realGLMap]
  have hx : (g • z).re ≠ (g • w).re := by
    intro he
    have hc := (upwardRay_angle_coordinates hne (R.realGLMap g) hR).1
    rw [hθ,he,sub_self,abs_zero,mul_zero] at hc
    rcases mul_eq_zero.mp hc with ha | hd
    · exact hα ha
    · exact (ne_of_gt (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ)<2)
        (g • z).im_pos) (g • w).im_pos) (Real.sinh_pos_iff.mpr (dist_pos.mpr hne)))) hd
  have he := upwardRays_trigonometry hne hx (R.realGLMap g) (S.realGLMap g) hR hS
  rwa [hθ,hφ,(realGL_isometry g).dist_eq] at he

/-- The finite-vertex realization of both formulas, with the remaining vertex genuinely ideal. -/
theorem ClosedDiscTriangle.oneIdeal_trigonometry_of_finite_vertices (T : ClosedDiscTriangle)
    (a b : 𝔻) (ha : T.a = discToClosedModel a) (hb : T.b = discToClosedModel b)
    (hc : ‖(T.c : ℂ)‖ = 1) :
    Real.cosh T.lengthC.toReal =
        (1 + Real.cos T.alpha * Real.cos T.beta) / (Real.sin T.alpha * Real.sin T.beta) ∧
      Real.sinh T.lengthC.toReal =
        (Real.cos T.alpha + Real.cos T.beta) / (Real.sin T.alpha * Real.sin T.beta) := by
  have hab : a ≠ b := by
    intro he
    exact T.a_ne_b (by rw [hb,ha,he])
  have habH : discToHalfPlane a ≠ discToHalfPlane b := cayleyHomeomorph.symm.injective.ne hab
  let U := T.cycle
  let R := T.cornerRayACAtA a ha
  let S := U.cornerRayABAtA b hb
  have hAB : T.cornerRayABAtA a ha = discRayThrough a b hab := by
    apply (discRayThrough_eq hab _ ?_).symm
    apply T.cornerAtA_sideC_finite_subset a ha
    change discToClosedModel b ∈ T.sideC
    rw [← hb,T.mem_sideC_iff_coordinate,T.coordinate_b]
    norm_num
  have hBA : U.cornerRayACAtA b hb = discRayThrough b a hab.symm := by
    apply (discRayThrough_eq hab.symm _ ?_).symm
    apply U.cornerAtA_sideB_finite_subset b hb
    change discToClosedModel a ∈ U.sideB
    rw [show discToClosedModel a = U.c from ha.symm,U.mem_sideB_iff_coordinate,U.coordinate_c]
    norm_num
  have hend : R.toHalfPlane.idealEndpoint = S.toHalfPlane.idealEndpoint := by
    rw [R.toHalfPlane_idealEndpoint,S.toHalfPlane_idealEndpoint]
    change extendedCayley.symm (T.cornerRayACAtA a ha).idealEndpoint =
      extendedCayley.symm (U.cornerRayABAtA b hb).idealEndpoint
    rw [T.cornerRayACAtA_idealEndpoint a ha hc,U.cornerRayABAtA_idealEndpoint b hb hc]
    rfl
  have hα : T.alpha = hInteriorAngleMeasure R.toHalfPlane
      (hRayThrough (discToHalfPlane a) (discToHalfPlane b) habH) := by
    rw [T.alpha_of_finite a ha,discInteriorAngleMeasure_eq_halfPlane,hAB,discRayThrough_toHalfPlane]
    exact hInteriorAngleMeasure_comm _ _
  have hβ : T.beta = hInteriorAngleMeasure S.toHalfPlane
      (hRayThrough (discToHalfPlane b) (discToHalfPlane a) habH.symm) := by
    change U.alpha = _
    rw [U.alpha_of_finite b hb,discInteriorAngleMeasure_eq_halfPlane,hBA,discRayThrough_toHalfPlane]
  have hlen : T.lengthC.toReal = dist (discToHalfPlane a) (discToHalfPlane b) := by
    have hn : 0 ≤ discPathDist a b := by rw [discPathDist_eq_halfPlane]; exact dist_nonneg
    rw [ClosedDiscTriangle.lengthC,ha,hb,extendedDiscSideLength_finite,ENNReal.toReal_ofReal hn,
      discPathDist_eq_halfPlane]
  have hαbounds := T.alpha_bounds_of_finite a ha
  have hsin : Real.sin (hInteriorAngleMeasure R.toHalfPlane
      (hRayThrough (discToHalfPlane a) (discToHalfPlane b) habH)) ≠ 0 := by
    rw [← hα]
    exact (Real.sin_pos_of_pos_of_lt_pi hαbounds.1 hαbounds.2).ne'
  have he := hOneIdealTriangle_trigonometry habH R.toHalfPlane S.toHalfPlane hend hsin
  rwa [← hα,← hβ,← hlen] at he

/-- both parts, in the genuine native finite-or-ideal triangle. -/
theorem ClosedDiscTriangle.one_ideal_vertex_cosh_sinh_finite_side_formulas (T : ClosedDiscTriangle)
    (hα : T.alpha ≠ 0) (hβ : T.beta ≠ 0) (hγ : T.gamma = 0) :
    Real.cosh T.lengthC.toReal =
        (1 + Real.cos T.alpha * Real.cos T.beta) / (Real.sin T.alpha * Real.sin T.beta) ∧
      Real.sinh T.lengthC.toReal =
        (Real.cos T.alpha + Real.cos T.beta) / (Real.sin T.alpha * Real.sin T.beta) := by
  have ha : ‖(T.a : ℂ)‖ < 1 := by
    by_contra! he
    exact hα (T.alpha_of_ideal (le_antisymm T.a.norm_le_one he))
  have hb : ‖(T.b : ℂ)‖ < 1 := by
    by_contra! he
    exact hβ (T.beta_of_ideal (le_antisymm T.b.norm_le_one he))
  have hc : ‖(T.c : ℂ)‖ = 1 := T.cycle.cycle.alpha_eq_zero_iff_ideal.mp hγ
  exact T.oneIdeal_trigonometry_of_finite_vertices (closedDiscFinitePoint T.a ha)
    (closedDiscFinitePoint T.b hb) (closedDiscFinitePoint_spec T.a ha).symm
    (closedDiscFinitePoint_spec T.b hb).symm hc

theorem ClosedHTriangle.one_ideal_vertex_cosh_sinh_finite_side_formulas (T : ClosedHTriangle)
    (hα : T.alpha ≠ 0) (hβ : T.beta ≠ 0) (hγ : T.gamma = 0) :
    Real.cosh T.lengthC.toReal =
        (1 + Real.cos T.alpha * Real.cos T.beta) / (Real.sin T.alpha * Real.sin T.beta) ∧
      Real.sinh T.lengthC.toReal =
        (Real.cos T.alpha + Real.cos T.beta) / (Real.sin T.alpha * Real.sin T.beta) :=
  T.toDiscTriangle.one_ideal_vertex_cosh_sinh_finite_side_formulas hα hβ hγ

end
end LowDimensionalTopology.Geometry.Hyperbolic
