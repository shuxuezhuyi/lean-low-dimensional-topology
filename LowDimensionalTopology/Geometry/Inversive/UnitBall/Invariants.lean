/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.NormalForm
public import LowDimensionalTopology.Geometry.Inversive.Bracket
/-!
# Distance ratios and local scale

The two-point quantities are preserved for all finite inputs whose images
are finite. In the unit ball, the actual punctured distance-ratio limit gives
the positive derivative scale and covariance of the density 2 / (1 - ‖x‖²).
Induced path-distance preservation is treated separately.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

def ballDistanceRatio (x y : Euclidean n) : ℝ :=
  dist x y^2 / ((1-‖x‖^2)*(1-‖y‖^2))

theorem inversion_unitBall_gap (c x : Euclidean n) (r : ℝ)
    (horth : ‖c‖^2 = 1+r^2) (hx : x ≠ c) :
    1-‖inversion c r x‖^2 = r^2/dist x c^2*(1-‖x‖^2) := by
  have h := norm_sq_boundaryOrthogonal_inversion c x r horth hx
  rw [dist_eq_norm]
  linear_combination -h

theorem ballDistanceRatio_linear (L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) (x y : Euclidean n) :
    ballDistanceRatio (L x) (L y) = ballDistanceRatio x y := by
  simp only [ballDistanceRatio,L.norm_map,L.isometry.dist_eq]

theorem ballDistanceRatio_boundaryOrthogonal_inversion (c x y : Euclidean n) (r : ℝ)
    (hr : 0 < r) (horth : ‖c‖^2 = 1+r^2) (hx : x ≠ c) (hy : y ≠ c) :
    ballDistanceRatio (inversion c r x) (inversion c r y) = ballDistanceRatio x y := by
  unfold ballDistanceRatio
  rw [inversion_unitBall_gap c x r horth hx,inversion_unitBall_gap c y r horth hy,
    sphereInversion_dist r hx hy]
  by_cases hx0 : 1-‖x‖^2 = 0
  · simp only [hx0,mul_zero,zero_mul,div_zero]
  by_cases hy0 : 1-‖y‖^2 = 0
  · simp only [hy0,mul_zero,div_zero]
  field_simp [hr.ne',dist_ne_zero.mpr hx,dist_ne_zero.mpr hy,hx0,hy0]

theorem generalMobius_ballDistanceRatio [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (x y : Euclidean n) (hx : f (x : ExtendedEuclidean n) ≠ ∞)
    (hy : f (y : ExtendedEuclidean n) ≠ ∞) :
    ballDistanceRatio (finiteEuclideanPart f x) (finiteEuclideanPart f y) = ballDistanceRatio x y := by
  obtain ⟨L,s,hs,he⟩ := ball_preserving_linearIsometry_mul_orthogonal_reflection f hf hB
  rw [he,finiteEuclideanPart_linear_mul,finiteEuclideanPart_linear_mul,ballDistanceRatio_linear]
  rcases hs with ⟨a,ha,rfl⟩ | ⟨c,r,hr,horth,rfl⟩
  · change ballDistanceRatio (planeReflectionFinite a 0 x) (planeReflectionFinite a 0 y) = _
    rw [← cartanPlaneLinearIsometry_apply,← cartanPlaneLinearIsometry_apply]
    exact ballDistanceRatio_linear _ x y
  · have hxc : x ≠ c := by
      intro h; subst x
      apply hx
      rw [he]
      change cartanLinearExtensionHom L (sphereInversion c r (c : ExtendedEuclidean n)) = ∞
      rw [sphereInversion_center,cartanLinearExtensionHom_infty]
    have hyc : y ≠ c := by
      intro h; subst y
      apply hy
      rw [he]
      change cartanLinearExtensionHom L (sphereInversion c r (c : ExtendedEuclidean n)) = ∞
      rw [sphereInversion_center,cartanLinearExtensionHom_infty]
    change ballDistanceRatio ((sphereInversion c r (x : ExtendedEuclidean n)).elim 0 id)
      ((sphereInversion c r (y : ExtendedEuclidean n)).elim 0 id) = _
    rw [sphereInversion_coe c r hxc,sphereInversion_coe c r hyc]
    exact ballDistanceRatio_boundaryOrthogonal_inversion c x y r hr horth hxc hyc
theorem PreservesUnitBall.maps_ball {f : ExtendedHomeomorph n} (hB : PreservesUnitBall f)
    (x : Euclidean n) (hx : ‖x‖ < 1) :
    f (x : ExtendedEuclidean n) ≠ ∞ ∧ ‖finiteEuclideanPart f x‖ < 1 := by
  have hxm : (x : ExtendedEuclidean n) ∈ extendedUnitBall := ⟨x,by simpa using hx,rfl⟩
  have hm : f (x : ExtendedEuclidean n) ∈ extendedUnitBall := by
    rw [← hB]
    exact Set.mem_image_of_mem _ hxm
  obtain ⟨y,hy,he⟩ := hm
  refine ⟨by rw [← he]; exact OnePoint.coe_ne_infty _, ?_⟩
  rw [finiteEuclideanPart,← he]
  simpa using hy

theorem sphereInversionHomeomorph_scale_limit (c x : Euclidean n) (r : ℝ)
    (hr : r ≠ 0) (hx : x ≠ c) :
    Tendsto (fun y : Euclidean n ↦
      dist (finiteEuclideanPart (sphereInversionHomeomorph c r hr) y)
        (finiteEuclideanPart (sphereInversionHomeomorph c r hr) x) / dist y x)
      (𝓝[≠] x) (𝓝 (r^2/dist x c^2)) := by
  apply (sphereInversion_scale_limit r hx).congr'
  filter_upwards [(eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds] with y hy
  simp only [finiteEuclideanPart,sphereInversionHomeomorph_apply,
    sphereInversion_coe c r hy,sphereInversion_coe c r hx]
  rfl

theorem generalMobius_ball_scale_limit [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (x : Euclidean n) (hx : ‖x‖ < 1) :
    Tendsto (fun y : Euclidean n ↦
      dist (finiteEuclideanPart f y) (finiteEuclideanPart f x) / dist y x)
      (𝓝[≠] x) (𝓝 ((1-‖finiteEuclideanPart f x‖^2)/(1-‖x‖^2))) := by
  obtain ⟨L,s,hs,he⟩ := ball_preserving_linearIsometry_mul_orthogonal_reflection f hf hB
  rw [he]
  simp only [finiteEuclideanPart_linear_mul,L.isometry.dist_eq,L.norm_map]
  rcases hs with ⟨a,ha,rfl⟩ | ⟨c,r,hr,horth,rfl⟩
  · have hfin : finiteEuclideanPart (planeReflectionHomeomorph a 0 ha) = cartanPlaneLinearIsometry a := by
      funext y
      exact (cartanPlaneLinearIsometry_apply a y).symm
    rw [hfin]
    simp only [(cartanPlaneLinearIsometry a).isometry.dist_eq,(cartanPlaneLinearIsometry a).norm_map]
    have hgap : 1-‖x‖^2 ≠ 0 := by nlinarith [norm_nonneg x]
    rw [div_self hgap]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (div_self (dist_ne_zero.mpr hy)).symm
  · have hxc := (boundaryOrthogonal_inversion_maps_ball c x r hr horth hx).1
    have hfin : finiteEuclideanPart (sphereInversionHomeomorph c r hr.ne') x = inversion c r x := by
      rw [finiteEuclideanPart,sphereInversionHomeomorph_apply,sphereInversion_coe c r hxc]
      rfl
    rw [hfin,inversion_unitBall_gap c x r horth hxc]
    have hgap : 1-‖x‖^2 ≠ 0 := by nlinarith [norm_nonneg x]
    rw [mul_div_cancel_right₀ _ hgap]
    simpa only [hfin] using sphereInversionHomeomorph_scale_limit c x r hr.ne' hxc

theorem PreservesUnitBall.norm_eq_one_iff [NeZero n] {f : ExtendedHomeomorph n}
    (hB : PreservesUnitBall f) (x : Euclidean n) (hx : f (x : ExtendedEuclidean n) ≠ ∞) :
    ‖finiteEuclideanPart f x‖ = 1 ↔ ‖x‖ = 1 := by
  have hS : f (x : ExtendedEuclidean n) ∈ extendedUnitSphere ↔
      (x : ExtendedEuclidean n) ∈ extendedUnitSphere := by
    have him : f (x : ExtendedEuclidean n) ∈ f '' extendedUnitSphere ↔
        (x : ExtendedEuclidean n) ∈ extendedUnitSphere := by
      constructor
      · rintro ⟨z,hz,he⟩
        exact f.injective he ▸ hz
      · intro hx
        exact ⟨(x : ExtendedEuclidean n),hx,rfl⟩
    simpa only [hB.maps_sphere] using him
  rw [← coe_finiteEuclideanPart f hx] at hS
  simpa only [extendedUnitSphere,Set.mem_image,OnePoint.coe_eq_coe,exists_eq_right,
    Metric.mem_sphere,dist_zero_right] using hS

theorem PreservesUnitBall.gap_ne_zero_iff [NeZero n] {f : ExtendedHomeomorph n}
    (hB : PreservesUnitBall f) (x : Euclidean n) (hx : f (x : ExtendedEuclidean n) ≠ ∞) :
    1-‖finiteEuclideanPart f x‖^2 ≠ 0 ↔ 1-‖x‖^2 ≠ 0 := by
  have hnorm := hB.norm_eq_one_iff x hx
  have hzero : 1-‖finiteEuclideanPart f x‖^2 = 0 ↔ 1-‖x‖^2 = 0 := by
    constructor <;> intro h
    · have hf1 : ‖finiteEuclideanPart f x‖ = 1 := by nlinarith [norm_nonneg (finiteEuclideanPart f x)]
      rw [hnorm.mp hf1]
      norm_num
    · have hx1 : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
      rw [hnorm.mpr hx1]
      norm_num
  exact not_congr hzero

def ballBracketRatio (x y : Euclidean n) : ℝ :=
  bracket x y^2 / ((1-‖x‖^2)*(1-‖y‖^2))

theorem ballBracketRatio_eq_distanceRatio_add_one (x y : Euclidean n)
    (hx : 1-‖x‖^2 ≠ 0) (hy : 1-‖y‖^2 ≠ 0) :
    ballBracketRatio x y = ballDistanceRatio x y+1 := by
  unfold ballBracketRatio ballDistanceRatio
  rw [bracket_sq_eq_distance_sq_add_norm_defects,dist_eq_norm]
  field_simp
  ring

theorem generalMobius_ballBracketRatio [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (x y : Euclidean n) (hx : f (x : ExtendedEuclidean n) ≠ ∞)
    (hy : f (y : ExtendedEuclidean n) ≠ ∞) :
    ballBracketRatio (finiteEuclideanPart f x) (finiteEuclideanPart f y) = ballBracketRatio x y := by
  by_cases hx0 : 1-‖x‖^2 = 0
  · have hfx : 1-‖finiteEuclideanPart f x‖^2 = 0 := by
      by_contra h
      exact ((hB.gap_ne_zero_iff x hx).mp h) hx0
    simp only [ballBracketRatio,hx0,hfx,zero_mul,div_zero]
  by_cases hy0 : 1-‖y‖^2 = 0
  · have hfy : 1-‖finiteEuclideanPart f y‖^2 = 0 := by
      by_contra h
      exact ((hB.gap_ne_zero_iff y hy).mp h) hy0
    simp only [ballBracketRatio,hy0,hfy,mul_zero,div_zero]
  rw [ballBracketRatio_eq_distanceRatio_add_one _ _ ((hB.gap_ne_zero_iff x hx).mpr hx0)
      ((hB.gap_ne_zero_iff y hy).mpr hy0),
    ballBracketRatio_eq_distanceRatio_add_one x y hx0 hy0,generalMobius_ballDistanceRatio f hf hB x y hx hy]

theorem generalMobius_ball_hasFDerivAt_positive_isometry [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (x : Euclidean n) (hx : ‖x‖ < 1) :
    ∃ O : Euclidean n ≃ₗᵢ[ℝ] Euclidean n,
      HasFDerivAt (finiteEuclideanPart f)
        (((1-‖finiteEuclideanPart f x‖^2)/(1-‖x‖^2)) • (O : Euclidean n →L[ℝ] Euclidean n)) x := by
  obtain ⟨hreg,_⟩ := hB.maps_ball x hx
  obtain ⟨μ,hμ,O,hderiv⟩ := Auxiliary.Analysis.conformalAt_iff_positive_isometry.mp
    (generalMobius_conformalAt hf hreg)
  have hlim := Auxiliary.Analysis.conformal_norm_ratio_tendsto hμ O hderiv
  simp only [← dist_eq_norm] at hlim
  have hμeq := tendsto_nhds_unique hlim (generalMobius_ball_scale_limit f hf hB x hx)
  exact ⟨O,hμeq ▸ hderiv⟩

theorem hasFDerivAt_positive_isometry_norm {F : Euclidean n → Euclidean n}
    {x : Euclidean n} {μ : ℝ} (hμ : 0 < μ) (O : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (hO : HasFDerivAt F (μ • (O : Euclidean n →L[ℝ] Euclidean n)) x) (v : Euclidean n) :
    ‖fderiv ℝ F x v‖ = μ*‖v‖ := by
  rw [hO.fderiv]
  change ‖μ • O v‖ = _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hμ,O.norm_map]

theorem generalMobius_ball_fderiv_norm [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (x : Euclidean n) (hx : ‖x‖ < 1) (v : Euclidean n) :
    ‖fderiv ℝ (finiteEuclideanPart f) x v‖ =
      ((1-‖finiteEuclideanPart f x‖^2)/(1-‖x‖^2))*‖v‖ := by
  obtain ⟨O,hO⟩ := generalMobius_ball_hasFDerivAt_positive_isometry f hf hB x hx
  have hnorm := (hB.maps_ball x hx).2
  have hpos : 0 < (1-‖finiteEuclideanPart f x‖^2)/(1-‖x‖^2) := by
    exact div_pos (sub_pos.mpr ((sq_lt_one_iff₀ (norm_nonneg _)).mpr hnorm))
      (sub_pos.mpr ((sq_lt_one_iff₀ (norm_nonneg _)).mpr hx))
  exact hasFDerivAt_positive_isometry_norm hpos O hO v

theorem generalMobius_ball_density_covariance [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (x : Euclidean n) (hx : ‖x‖ < 1) (v : Euclidean n) :
    2/(1-‖finiteEuclideanPart f x‖^2)*‖fderiv ℝ (finiteEuclideanPart f) x v‖ =
      2/(1-‖x‖^2)*‖v‖ := by
  rw [generalMobius_ball_fderiv_norm f hf hB x hx v]
  have hfNorm := (hB.maps_ball x hx).2
  have hfgap : 1-‖finiteEuclideanPart f x‖^2 ≠ 0 := by
    nlinarith [norm_nonneg (finiteEuclideanPart f x)]
  field_simp [hfgap]

end LowDimensionalTopology.Geometry.Inversive
