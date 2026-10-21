/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaNormalized
@[expose] public section
open Set InnerProductGeometry MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc Topology OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- A finite ideal endpoint to the right forces actual ray points to the right. -/
theorem HRayAt.exists_point_re_gt_of_endpoint {z : ℍ} (R : HRayAt z) (b : ℂ)
    (hEnd : R.idealEndpoint = (b : OnePoint ℂ)) (hb : z.re < b.re) :
    ∃ w ∈ R.val, z.re < w.re := by
  by_contra! hn
  have hmem : (b : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' R.val) := by
    have he : R.idealEndpoint ∈ hTraceIdealEndpoints R.val := by rw [R.trace_idealEndpoint]; exact mem_singleton _
    rw [hEnd] at he
    exact he.1
  have hsub : ((↑) : ℍ → ℂ) '' R.val ⊆ {v : ℂ | v.re ≤ z.re} := by
    rintro _ ⟨w,hw,rfl⟩
    exact hn w hw
  have he := finite_mem_extended_closure_mem_closed R.val _
    (isClosed_le Complex.continuous_re continuous_const) hsub b hmem
  change b.re ≤ z.re at he
  exact (not_le_of_gt hb) he

/-- The corresponding leftward statement uses the actual compactified endpoint. -/
theorem HRayAt.exists_point_re_lt_of_endpoint {z : ℍ} (R : HRayAt z) (b : ℂ)
    (hEnd : R.idealEndpoint = (b : OnePoint ℂ)) (hb : b.re < z.re) :
    ∃ w ∈ R.val, w.re < z.re := by
  by_contra! hn
  have hmem : (b : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' R.val) := by
    have he : R.idealEndpoint ∈ hTraceIdealEndpoints R.val := by rw [R.trace_idealEndpoint]; exact mem_singleton _
    rw [hEnd] at he
    exact he.1
  have hsub : ((↑) : ℍ → ℂ) '' R.val ⊆ {v : ℂ | z.re ≤ v.re} := by
    rintro _ ⟨w,hw,rfl⟩
    exact hn w hw
  have he := finite_mem_extended_closure_mem_closed R.val _
    (isClosed_le continuous_const Complex.continuous_re) hsub b hmem
  change z.re ≤ b.re at he
  exact (not_le_of_gt hb) he

theorem HRayAt.unitCircle_tangentVector_of_re_gt {z : ℍ} (R : HRayAt z)
    (hL : R.supportLine = .circle 0 1 (by norm_num)) {w : ℍ}
    (hw : w ∈ R.val) (hzw : z.re < w.re) : R.tangentVector = -(Complex.I * (z : ℂ)) := by
  have hs : ¬ R.longitudinal z < R.longitudinal R.directionPoint := by
    intro h
    have he := (R.mem_iff_longitudinal (R.subset_support hw)).mp hw
    rw [ite_eq_left h] at he
    simp only [HRayAt.longitudinal,hL,HalfPlaneLine.longitudinal,neg_apply,
      Complex.reCLM_apply,UpperHalfPlane.coe_re] at he
    linarith only [he,hzw]
  have hsign : R.tangentSign = -1 := ite_eq_right hs
  simp only [HRayAt.tangentVector,hsign,hL,HalfPlaneLine.tangentAt,Complex.ofReal_zero,sub_zero,neg_one_smul]

theorem HRayAt.unitCircle_tangentVector_of_re_lt {z : ℍ} (R : HRayAt z)
    (hL : R.supportLine = .circle 0 1 (by norm_num)) {w : ℍ}
    (hw : w ∈ R.val) (hzw : w.re < z.re) : R.tangentVector = Complex.I * (z : ℂ) := by
  have hs : R.longitudinal z < R.longitudinal R.directionPoint := by
    by_contra h
    have he := (R.mem_iff_longitudinal (R.subset_support hw)).mp hw
    rw [ite_eq_right h] at he
    simp only [HRayAt.longitudinal,hL,HalfPlaneLine.longitudinal,neg_apply,
      Complex.reCLM_apply,UpperHalfPlane.coe_re] at he
    linarith only [he,hzw]
  have hsign : R.tangentSign = 1 := ite_eq_left hs
  simp only [HRayAt.tangentVector,hsign,hL,HalfPlaneLine.tangentAt,Complex.ofReal_zero,sub_zero,one_smul]

theorem unitCircle_ray_angle_up_cos_of_re_gt {z : ℍ} (hz : ‖(z : ℂ)‖ = 1)
    (R S : HRayAt z) (hL : R.supportLine = .circle 0 1 (by norm_num))
    (hEnd : S.idealEndpoint = ∞) {w : ℍ} (hw : w ∈ R.val) (hzw : z.re < w.re) :
    Real.cos (hInteriorAngleMeasure S R) = -z.re := by
  rw [hInteriorAngleMeasure,S.tangentVector_of_idealEndpoint_infty hEnd,
    R.unitCircle_tangentVector_of_re_gt hL hw hzw,cos_angle]
  simp [hz]

theorem unitCircle_ray_angle_up_cos_of_re_lt {z : ℍ} (hz : ‖(z : ℂ)‖ = 1)
    (R S : HRayAt z) (hL : R.supportLine = .circle 0 1 (by norm_num))
    (hEnd : S.idealEndpoint = ∞) {w : ℍ} (hw : w ∈ R.val) (hzw : w.re < z.re) :
    Real.cos (hInteriorAngleMeasure S R) = z.re := by
  rw [hInteriorAngleMeasure,S.tangentVector_of_idealEndpoint_infty hEnd,
    R.unitCircle_tangentVector_of_re_lt hL hw hzw,cos_angle]
  simp [hz]

/-- The image of a genuine finite closed vertex is the usual half-plane action. -/
theorem realGL_closed_finite_vertex (z : 𝔻) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (a : ℂ) (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)
      (extendedCayley.symm (closedDiscToExtended (discToClosedModel z))) = (a : OnePoint ℂ)) :
    ((g • discToHalfPlane z : ℍ) : ℂ) = a := by
  change Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm ((z : ℂ) : OnePoint ℂ)) = _ at ha
  rw [extendedCayley_symm_coe_disc] at ha
  change Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ((((discToHalfPlane z : ℍ) : ℂ)) : OnePoint
    ℂ) = _ at ha
  rw [realMobiusMatrix_coe g hg] at ha
  exact OnePoint.coe_injective ha

/-- A transported genuine corner ray either contains the other finite vertex or has it as its true ideal endpoint. -/
theorem ClosedDiscTriangle.cornerAB_image_point_or_endpoint (T : ClosedDiscTriangle)
    (z : 𝔻) (ha : T.a = discToClosedModel z) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (b : ℂ) (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)
      (extendedCayley.symm (closedDiscToExtended T.b)) = (b : OnePoint ℂ)) :
    (∃ w ∈ ((T.cornerRayABAtA z ha).toHalfPlane.realGLMap g).val, w.re = b.re) ∨
      ((T.cornerRayABAtA z ha).toHalfPlane.realGLMap g).idealEndpoint = (b : OnePoint ℂ) := by
  rcases closedDisc_interior_or_ideal T.b with ⟨w,hw⟩ | hbI
  · left
    refine ⟨g • discToHalfPlane w,?_,?_⟩
    · rw [← HRayAt.realGLMap_carrier]
      refine ⟨discToHalfPlane w,?_,rfl⟩
      refine ⟨w,?_,rfl⟩
      apply T.cornerAtA_sideC_finite_subset z ha
      change discToClosedModel w ∈ T.sideC
      rw [hw,T.mem_sideC_iff_coordinate,T.coordinate_b]
      norm_num
    · have he := realGL_closed_finite_vertex w g hg b (by rwa [hw])
      exact congrArg Complex.re he
  · right
    rw [HRayAt.realGLMap_idealEndpoint _ g hg,DiscRayAt.toHalfPlane_idealEndpoint,
      T.cornerRayABAtA_idealEndpoint z ha hbI]
    exact hb

/-- Actual normalized corner support, without assuming a formula for the ray. -/
theorem ClosedDiscTriangle.cornerAB_image_support (T : ClosedDiscTriangle)
    (z : 𝔻) (ha : T.a = discToClosedModel z) (g : GL (Fin 2) ℝ)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier) :
    ((T.cornerRayABAtA z ha).toHalfPlane.realGLMap g).supportLine = .circle 0 1 (by norm_num) := by
  have hS : (T.cornerRayABAtA z ha).toHalfPlane.supportLine = T.sideLineC.toHalfPlane := by
    apply HalfPlaneLine.toDiscLine_injective
    change (T.cornerRayABAtA z ha).supportLine = T.sideLineC.toHalfPlane.toDiscLine
    rw [T.cornerRayABAtA_support,T.sideLineC.toHalfPlane_spec]
  apply HalfPlaneLine.carrier_injective
  rw [← HRayAt.realGLMap_support,hS,hline]

/-- A finite normalized corner with its next vertex to the right. -/
theorem ClosedDiscTriangle.alpha_cos_normalized_of_finite_re_lt (T : ClosedDiscTriangle)
    (z : 𝔻) (hz : T.a = discToClosedModel z) (hc : ‖(T.c : ℂ)‖ = 1)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (a b : ℂ) (hna : ‖a‖ = 1)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a
      : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b
      : OnePoint ℂ))
    (hab : a.re < b.re) : Real.cos T.alpha = -a.re := by
  let R := (T.cornerRayABAtA z hz).toHalfPlane.realGLMap g
  let S := (T.cornerRayACAtA z hz).toHalfPlane.realGLMap g
  have hza : ((g • discToHalfPlane z : ℍ) : ℂ) = a := realGL_closed_finite_vertex z g hg a (by rwa [← hz])
  have hnz : ‖((g • discToHalfPlane z : ℍ) : ℂ)‖ = 1 := by rwa [hza]
  have hE : S.idealEndpoint = ∞ := by
    rw [HRayAt.realGLMap_idealEndpoint _ g hg,DiscRayAt.toHalfPlane_idealEndpoint,
      T.cornerRayACAtA_idealEndpoint z hz hc]
    exact hpEnd
  have hdir : (g • discToHalfPlane z).re < b.re := by simpa only [← hza,UpperHalfPlane.coe_re] using hab
  have hpoint : ∃ w ∈ R.val, (g • discToHalfPlane z).re < w.re := by
    rcases T.cornerAB_image_point_or_endpoint z hz g hg b hb with ⟨w,hw,he⟩ | he
    · exact ⟨w,hw,he ▸ hdir⟩
    · exact R.exists_point_re_gt_of_endpoint b he hdir
  obtain ⟨w,hw,hzw⟩ := hpoint
  have he := unitCircle_ray_angle_up_cos_of_re_gt hnz R S (T.cornerAB_image_support z hz g hline) hE hw hzw
  have hangle : hInteriorAngleMeasure S R = T.alpha := by
    rw [hInteriorAngleMeasure_realGLMap,T.alpha_of_finite z hz,discInteriorAngleMeasure_eq_halfPlane]
    exact angle_comm _ _
  rw [hangle] at he
  simpa only [← hza,UpperHalfPlane.coe_re] using he

/-- A transported genuine third-vertex corner ray, allowing its target to be ideal. -/
theorem ClosedDiscTriangle.cornerAC_image_point_or_endpoint (T : ClosedDiscTriangle)
    (z : 𝔻) (ha : T.a = discToClosedModel z) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (b : ℂ) (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)
      (extendedCayley.symm (closedDiscToExtended T.c)) = (b : OnePoint ℂ)) :
    (∃ w ∈ ((T.cornerRayACAtA z ha).toHalfPlane.realGLMap g).val, w.re = b.re) ∨
      ((T.cornerRayACAtA z ha).toHalfPlane.realGLMap g).idealEndpoint = (b : OnePoint ℂ) := by
  rcases closedDisc_interior_or_ideal T.c with ⟨w,hw⟩ | hcI
  · left
    refine ⟨g • discToHalfPlane w,?_,?_⟩
    · rw [← HRayAt.realGLMap_carrier]
      refine ⟨discToHalfPlane w,?_,rfl⟩
      refine ⟨w,?_,rfl⟩
      apply T.cornerAtA_sideB_finite_subset z ha
      change discToClosedModel w ∈ T.sideB
      rw [hw,T.mem_sideB_iff_coordinate,T.coordinate_c]
      norm_num
    · have he := realGL_closed_finite_vertex w g hg b (by rwa [hw])
      exact congrArg Complex.re he
  · right
    rw [HRayAt.realGLMap_idealEndpoint _ g hg,DiscRayAt.toHalfPlane_idealEndpoint,
      T.cornerRayACAtA_idealEndpoint z ha hcI]
    exact hb

/-- The sign is determined by an actual point or by the actual compactified endpoint. -/
theorem unitCircle_ray_angle_up_cos {z : ℍ} (hz : ‖(z : ℂ)‖ = 1)
    (R S : HRayAt z) (hL : R.supportLine = .circle 0 1 (by norm_num))
    (hEnd : S.idealEndpoint = ∞) (b : ℂ) (hne : z.re ≠ b.re)
    (htarget : (∃ w ∈ R.val,w.re = b.re) ∨ R.idealEndpoint = (b : OnePoint ℂ)) :
    Real.cos (hInteriorAngleMeasure S R) = if z.re < b.re then -z.re else z.re := by
  by_cases hlt : z.re < b.re
  · rw [ite_eq_left hlt]
    have hpoint : ∃ w ∈ R.val,z.re < w.re := by
      rcases htarget with ⟨w,hw,he⟩ | he
      · exact ⟨w,hw,he ▸ hlt⟩
      · exact R.exists_point_re_gt_of_endpoint b he hlt
    obtain ⟨w,hw,hwz⟩ := hpoint
    exact unitCircle_ray_angle_up_cos_of_re_gt hz R S hL hEnd hw hwz
  · rw [ite_eq_right hlt]
    have hgt : b.re < z.re := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    have hpoint : ∃ w ∈ R.val,w.re < z.re := by
      rcases htarget with ⟨w,hw,he⟩ | he
      · exact ⟨w,hw,he ▸ hgt⟩
      · exact R.exists_point_re_lt_of_endpoint b he hgt
    obtain ⟨w,hw,hwz⟩ := hpoint
    exact unitCircle_ray_angle_up_cos_of_re_lt hz R S hL hEnd hw hwz

/-- Actual finite corner angle at the first normalized vertex, in either horizontal order. -/
theorem ClosedDiscTriangle.alpha_cos_normalized_of_finite (T : ClosedDiscTriangle)
    (z : 𝔻) (hz : T.a = discToClosedModel z) (hc : ‖(T.c : ℂ)‖ = 1)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (a b : ℂ) (hna : ‖a‖ = 1) (hne : a.re ≠ b.re)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a
      : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b
      : OnePoint ℂ)) :
    Real.cos T.alpha = if a.re < b.re then -a.re else a.re := by
  let R := (T.cornerRayABAtA z hz).toHalfPlane.realGLMap g
  let S := (T.cornerRayACAtA z hz).toHalfPlane.realGLMap g
  have hza : ((g • discToHalfPlane z : ℍ) : ℂ) = a := realGL_closed_finite_vertex z g hg a (by rwa [← hz])
  have hnz : ‖((g • discToHalfPlane z : ℍ) : ℂ)‖ = 1 := by rwa [hza]
  have hE : S.idealEndpoint = ∞ := by
    rw [HRayAt.realGLMap_idealEndpoint _ g hg,DiscRayAt.toHalfPlane_idealEndpoint,
      T.cornerRayACAtA_idealEndpoint z hz hc]
    exact hpEnd
  have hneq : (g • discToHalfPlane z).re ≠ b.re := by simpa only [← hza,UpperHalfPlane.coe_re] using hne
  have he := unitCircle_ray_angle_up_cos hnz R S (T.cornerAB_image_support z hz g hline) hE b hneq
    (T.cornerAB_image_point_or_endpoint z hz g hg b hb)
  have hangle : hInteriorAngleMeasure S R = T.alpha := by
    rw [hInteriorAngleMeasure_realGLMap,T.alpha_of_finite z hz,discInteriorAngleMeasure_eq_halfPlane]
    exact angle_comm _ _
  rw [hangle] at he
  simpa only [← hza,UpperHalfPlane.coe_re] using he

/-- Actual finite corner at the second vertex; the circular side is directed back to the first. -/
theorem ClosedDiscTriangle.beta_cos_normalized_of_finite (T : ClosedDiscTriangle)
    (z : 𝔻) (hz : T.b = discToClosedModel z) (hc : ‖(T.c : ℂ)‖ = 1)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (a b : ℂ) (hnb : ‖b‖ = 1) (hne : a.re ≠ b.re)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a
      : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b
      : OnePoint ℂ)) :
    Real.cos T.beta = if b.re < a.re then -b.re else b.re := by
  let U := T.cycle
  have hzU : U.a = discToClosedModel z := hz
  let R := (U.cornerRayACAtA z hzU).toHalfPlane.realGLMap g
  let S := (U.cornerRayABAtA z hzU).toHalfPlane.realGLMap g
  have hzb : ((g • discToHalfPlane z : ℍ) : ℂ) = b := realGL_closed_finite_vertex z g hg b (by rwa [← hz])
  have hnz : ‖((g • discToHalfPlane z : ℍ) : ℂ)‖ = 1 := by rwa [hzb]
  have hE : S.idealEndpoint = ∞ := by
    rw [HRayAt.realGLMap_idealEndpoint _ g hg,DiscRayAt.toHalfPlane_idealEndpoint,
      U.cornerRayABAtA_idealEndpoint z hzU hc]
    exact hpEnd
  have hS : (U.cornerRayACAtA z hzU).toHalfPlane.supportLine = T.sideLineC.toHalfPlane := by
    apply HalfPlaneLine.toDiscLine_injective
    change (U.cornerRayACAtA z hzU).supportLine = T.sideLineC.toHalfPlane.toDiscLine
    rw [U.cornerRayACAtA_support,T.sideLineC.toHalfPlane_spec]
    rfl
  have hL : R.supportLine = .circle 0 1 (by norm_num) := by
    apply HalfPlaneLine.carrier_injective
    rw [← HRayAt.realGLMap_support,hS,hline]
  have hneq : (g • discToHalfPlane z).re ≠ a.re := by simpa only [← hzb,UpperHalfPlane.coe_re] using Ne.symm hne
  have he := unitCircle_ray_angle_up_cos hnz R S hL hE a hneq
    (U.cornerAC_image_point_or_endpoint z hzU g hg a ha)
  have hangle : hInteriorAngleMeasure S R = T.beta := by
    rw [hInteriorAngleMeasure_realGLMap]
    change hInteriorAngleMeasure (U.cornerRayABAtA z hzU).toHalfPlane (U.cornerRayACAtA z hzU).toHalfPlane = U.alpha
    rw [U.alpha_of_finite z hzU,discInteriorAngleMeasure_eq_halfPlane]
  rw [hangle] at he
  simpa only [← hzb,UpperHalfPlane.coe_re] using he

/-- Real fractional-linear maps send an actual ideal vertex with a finite image to the real axis. -/
theorem realGL_closed_ideal_vertex_im (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ = 1)
    (g : GL (Fin 2) ℝ) (a : ℂ) (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)
      (extendedCayley.symm (closedDiscToExtended p)) = (a : OnePoint ℂ)) : a.im = 0 := by
  have hE : extendedCayley.symm (closedDiscToExtended p) ∈ halfPlaneIdealBoundary := by
    rw [idealBoundary_cayley_iff,extendedCayley.apply_symm_apply]
    simpa only [closedDiscToExtended,coe_mem_extendedDiscIdealBoundary] using hp
  have hgE : (a : OnePoint ℂ) ∈ halfPlaneIdealBoundary := by
    rw [← ha]
    change extendedCayley.symm (closedDiscToExtended p) ∈
      (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)) ⁻¹' halfPlaneIdealBoundary
    rwa [realMobiusMatrix_preimage_boundary]
  exact (coe_mem_halfPlaneIdealBoundary a).mp hgE

/-- An ideal vertex on the normalized semicircle is its appropriate endpoint. -/
theorem unitCircle_real_vertex_order (a b : ℂ) (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1)
    (hia : a.im = 0) (hne : a.re ≠ b.re) :
    (if a.re < b.re then -a.re else a.re) = 1 := by
  have hsq : a.re ^ 2 = 1 := by
    have hs := Complex.normSq_eq_norm_sq a
    rw [Complex.normSq_apply,hna,hia] at hs
    nlinarith only [hs]
  have hb : |b.re| ≤ 1 := by simpa only [hnb] using Complex.abs_re_le_norm b
  by_cases hlt : a.re < b.re
  · rw [ite_eq_left hlt]
    have han : a.re < 1 := lt_of_lt_of_le hlt (abs_le.mp hb).2
    nlinarith only [hsq,han]
  · rw [ite_eq_right hlt]
    have hgt : b.re < a.re := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    have hap : -1 < a.re := lt_of_le_of_lt (abs_le.mp hb).1 hgt
    nlinarith only [hsq,hap]

/-- The original first angle is identified for all finite/ideal statuses, with no smoothness assumptions. -/
theorem ClosedDiscTriangle.alpha_cos_normalized (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (a b : ℂ) (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hne : a.re ≠ b.re)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a
      : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b
      : OnePoint ℂ)) :
    Real.cos T.alpha = if a.re < b.re then -a.re else a.re := by
  rcases closedDisc_interior_or_ideal T.a with ⟨z,hz⟩ | haI
  · exact T.alpha_cos_normalized_of_finite z hz.symm hc g hg hline hpEnd a b hna hne ha hb
  · rw [T.alpha_of_ideal haI,Real.cos_zero]
    exact (unitCircle_real_vertex_order a b hna hnb (realGL_closed_ideal_vertex_im T.a haI g a ha) hne).symm

/-- The original second angle is likewise identified, including ideal endpoints. -/
theorem ClosedDiscTriangle.beta_cos_normalized (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (a b : ℂ) (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hne : a.re ≠ b.re)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a
      : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b
      : OnePoint ℂ)) :
    Real.cos T.beta = if b.re < a.re then -b.re else b.re := by
  rcases closedDisc_interior_or_ideal T.b with ⟨z,hz⟩ | hbI
  · exact T.beta_cos_normalized_of_finite z hz.symm hc g hg hline hpEnd a b hnb hne ha hb
  · rw [T.beta_of_ideal hbI,Real.cos_zero]
    exact (unitCircle_real_vertex_order b a hnb hna (realGL_closed_ideal_vertex_im T.b hbI g b hb)
      (Ne.symm hne)).symm

/-- The evaluated semicircle integral is the actual angle defect. -/
theorem arcsin_difference_eq_angle_defect (a b : ℝ) (hne : a ≠ b) (α β : ℝ)
    (hα : α ∈ Icc (0 : ℝ) Real.pi) (hβ : β ∈ Icc (0 : ℝ) Real.pi)
    (hca : Real.cos α = if a < b then -a else a)
    (hcb : Real.cos β = if b < a then -b else b) :
    Real.arcsin (max a b) - Real.arcsin (min a b) = Real.pi - α - β := by
  by_cases hab : a < b
  · rw [ite_eq_left hab] at hca
    rw [ite_eq_right (not_lt_of_ge hab.le)] at hcb
    have h₁ := Real.arccos_cos hα.1 hα.2
    have h₂ := Real.arccos_cos hβ.1 hβ.2
    rw [hca,Real.arccos_neg] at h₁
    rw [hcb] at h₂
    rw [max_eq_right hab.le,min_eq_left hab.le,Real.arcsin_eq_pi_div_two_sub_arccos,
      Real.arcsin_eq_pi_div_two_sub_arccos]
    linarith only [h₁,h₂]
  · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hne)
    rw [ite_eq_right hab] at hca
    rw [ite_eq_left hba] at hcb
    have h₁ := Real.arccos_cos hα.1 hα.2
    have h₂ := Real.arccos_cos hβ.1 hβ.2
    rw [hca] at h₁
    rw [hcb,Real.arccos_neg] at h₂
    rw [max_eq_left hba.le,min_eq_right hba.le,Real.arcsin_eq_pi_div_two_sub_arccos,
      Real.arcsin_eq_pi_div_two_sub_arccos]
    linarith only [h₁,h₂]

/-- For every genuine triangle with its third vertex ideal; the other vertices are arbitrary. -/
theorem ClosedDiscTriangle.halfPlane_area_eq_angle_defect_of_ideal (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) :
    volume T.halfPlaneInterior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  obtain ⟨g,hg,hpEnd,hline⟩ := T.exists_ideal_vertex_area_normalizer hc
  obtain ⟨a,b,hna,hnb,_,_,hne,ha,hb,hA,hB⟩ := T.normalized_sides_and_vertices hc g hg hpEnd hline
  rw [T.normalized_ideal_area hc g hg hpEnd hline a b hna hnb hne ha hb hA hB]
  have hα : T.alpha ∈ Icc (0 : ℝ) Real.pi := ⟨T.alpha_mem_Ico.1,T.alpha_mem_Ico.2.le⟩
  have hβ : T.beta ∈ Icc (0 : ℝ) Real.pi := ⟨T.cycle.alpha_mem_Ico.1,T.cycle.alpha_mem_Ico.2.le⟩
  have he := arcsin_difference_eq_angle_defect a.re b.re hne T.alpha T.beta hα hβ
    (T.alpha_cos_normalized hc g hg hline hpEnd a b hna hnb hne ha hb)
    (T.beta_cos_normalized hc g hg hline hpEnd a b hna hnb hne ha hb)
  rw [he,T.gamma_of_ideal hc,sub_zero]

/-- Cayley transports this genuine triangle's density area to its actual half-plane interior. -/
theorem ClosedDiscTriangle.area_eq_halfPlane_volume (T : ClosedDiscTriangle) :
    discHyperbolicArea T.interior = volume T.halfPlaneInterior := by
  rw [discHyperbolicArea_eq_halfPlane_volume T.interior T.interior_isOpen.measurableSet]
  congr 1
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change halfPlaneToDisc (discToHalfPlane z) ∈ T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  · intro hx
    exact ⟨halfPlaneToDisc x,hx,discToHalfPlane_halfPlaneToDisc x⟩

/-- The actual native disc density area is the angle defect whenever the third vertex is ideal. -/
theorem ClosedDiscTriangle.area_eq_angle_defect_of_ideal (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) :
    discHyperbolicArea T.interior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  rw [T.area_eq_halfPlane_volume,T.halfPlane_area_eq_angle_defect_of_ideal hc]

/-- Cyclic relabelling preserves the entire genuine closed triangle. -/
theorem ClosedDiscTriangle.cycle_closedCarrier (T : ClosedDiscTriangle) :
    T.cycle.closedCarrier = T.closedCarrier := by
  unfold ClosedDiscTriangle.closedCarrier
  congr 1
  ext x
  simp only [mem_insert_iff,mem_singleton_iff,ClosedDiscTriangle.cycle]
  tauto

/-- Hence cyclic relabelling preserves the entire native open interior. -/
theorem ClosedDiscTriangle.cycle_interior (T : ClosedDiscTriangle) :
    T.cycle.interior = T.interior := by
  unfold ClosedDiscTriangle.interior ClosedDiscTriangle.complexInterior ClosedDiscTriangle.complexClosedCarrier
  rw [T.cycle_closedCarrier]

/-- The genuine area formula for every finite/ideal triangle having at least one ideal vertex. -/
theorem ClosedDiscTriangle.area_eq_angle_defect_of_exists_ideal (T : ClosedDiscTriangle)
    (hI : ‖(T.a : ℂ)‖ = 1 ∨ ‖(T.b : ℂ)‖ = 1 ∨ ‖(T.c : ℂ)‖ = 1) :
    discHyperbolicArea T.interior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  rcases hI with ha | hb | hc
  · have he := T.cycle.area_eq_angle_defect_of_ideal ha
    rw [T.cycle_interior] at he
    have hγ : T.cycle.gamma = T.alpha := by rw [ClosedDiscTriangle.gamma,T.cycle_three]
    change discHyperbolicArea T.interior = ENNReal.ofReal (Real.pi - T.beta - T.gamma - T.cycle.gamma) at he
    rw [hγ] at he
    convert he using 2; ring
  · have he := T.cycle.cycle.area_eq_angle_defect_of_ideal hb
    rw [T.cycle.cycle_interior,T.cycle_interior] at he
    have hβ : T.cycle.cycle.beta = T.alpha := by rw [ClosedDiscTriangle.beta,T.cycle_three]
    have hγ : T.cycle.cycle.gamma = T.beta := by rw [ClosedDiscTriangle.gamma,T.cycle_three]; rfl
    change discHyperbolicArea T.interior = ENNReal.ofReal (Real.pi - T.gamma - T.cycle.cycle.beta -
      T.cycle.cycle.gamma) at he
    rw [hβ,hγ] at he
    convert he using 2; ring
  · exact T.area_eq_angle_defect_of_ideal hc

end
end LowDimensionalTopology.Geometry.Hyperbolic
