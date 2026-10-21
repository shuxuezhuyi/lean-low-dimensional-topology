/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.RayIsometries
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleData
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealAltitudeCounterexample

@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

theorem realGL_extended_image (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (S : Set ℍ) :
    extendedHalfPlanePoint '' ((g • · : ℍ → ℍ) '' S) =
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' (extendedHalfPlanePoint '' S) := by
  rw [image_image,image_image]
  apply image_congr
  intro z _
  exact (realMobiusMatrix_coe g hg z).symm

theorem realGL_traceIdealEndpoints (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (S : Set ℍ) :
    hTraceIdealEndpoints ((g • · : ℍ → ℍ) '' S) =
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' hTraceIdealEndpoints S := by
  rw [hTraceIdealEndpoints,realGL_extended_image g hg]
  change closure (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g) '' _) ∩ _ = _
  rw [← Homeomorph.image_closure]
  change (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' closure _) ∩ _ = _
  rw [← image_inter_preimage,realMobiusMatrix_preimage_boundary]
  rfl

theorem HRayAt.realGLMap_idealEndpoint {z : ℍ} (R : HRayAt z) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) :
    (R.realGLMap g).idealEndpoint = Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) R.idealEndpoint := by
  apply singleton_injective
  rw [← (R.realGLMap g).trace_idealEndpoint,← R.realGLMap_carrier,
    realGL_traceIdealEndpoints g hg,R.trace_idealEndpoint,image_singleton]

theorem HRayAt.supportLine_of_idealEndpoint_infty {z : ℍ} (R : HRayAt z)
    (hEnd : R.idealEndpoint = ∞) : R.supportLine = .vertical z.re := by
  apply R.supportLine.eq_of_shared_ideal_and_interior (.vertical z.re) z R.start_mem_support rfl ∞
  · simpa only [hEnd] using R.ideal_mem_support
  · rw [vertical_idealEndpoints]
    exact mem_insert_of_mem _ (mem_singleton _)

theorem HRayAt.tangentVector_of_idealEndpoint_infty {z : ℍ} (R : HRayAt z)
    (hEnd : R.idealEndpoint = ∞) : R.tangentVector = Complex.I := by
  have hL := R.supportLine_of_idealEndpoint_infty hEnd
  have htip : z.im < R.directionPoint.im := by
    by_contra ht
    have horder : ¬ R.longitudinal z < R.longitudinal R.directionPoint := by
      simpa only [HRayAt.longitudinal,hL,HalfPlaneLine.longitudinal,Complex.imCLM_apply,
        UpperHalfPlane.coe_im] using ht
    have hupper {w : ℍ} (hw : w ∈ R.val) : w.im ≤ z.im := by
      have he := (R.mem_iff_longitudinal (R.subset_support hw)).mp hw
      rw [ite_eq_right horder] at he
      simpa only [HRayAt.longitudinal,hL,HalfPlaneLine.longitudinal,Complex.imCLM_apply,
        UpperHalfPlane.coe_im] using he
    let φ : ℝ → ℂ := fun t => (z.re : ℂ) + (t : ℂ) * Complex.I
    let K := φ '' Icc 0 z.im
    have hK : IsCompact K := isCompact_Icc.image
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    have hE : IsClosed (((↑) : ℂ → OnePoint ℂ) '' K) :=
      (hK.image OnePoint.continuous_coe).isClosed
    have hsub : extendedHalfPlanePoint '' R.val ⊆ ((↑) : ℂ → OnePoint ℂ) '' K := by
      rintro _ ⟨w,hw,rfl⟩
      refine ⟨(w : ℂ),⟨w.im,⟨w.im_pos.le,hupper hw⟩,?_⟩,rfl⟩
      have hr : w.re = z.re := by
        have he := R.subset_support hw
        rwa [hL] at he
      apply Complex.ext <;> simp [φ,hr]
    have hin : (∞ : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' R.val) := by
      have he : R.idealEndpoint ∈ hTraceIdealEndpoints R.val := by
        rw [R.trace_idealEndpoint]
        exact mem_singleton _
      rw [hEnd] at he
      exact he.1
    obtain ⟨w,_,he⟩ := closure_minimal hsub hE hin
    exact OnePoint.coe_ne_infty w he
  have hs : R.tangentSign = 1 := by
    rw [HRayAt.tangentSign]
    apply ite_eq_left
    simpa only [HRayAt.longitudinal,hL,HalfPlaneLine.longitudinal,Complex.imCLM_apply,
      UpperHalfPlane.coe_im] using htip
  rw [HRayAt.tangentVector,hs,one_smul,hL,HalfPlaneLine.tangentAt]

/-- A genuine ray can be sent to the actual upward imaginary ray by a determinant-one action. -/
theorem HRayAt.exists_sl2_normalized_upward {z : ℍ} (R : HRayAt z) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      s • z = UpperHalfPlane.I ∧
        (R.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ s)).idealEndpoint = ∞ := by
  obtain ⟨s,k,hk,hz,hw⟩ := exists_sl2_normalized_pair z R.directionPoint
    (Ne.symm (show R.directionPoint ≠ z from R.directionPoint_mem.2))
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hb : (∞ : OnePoint ℂ) ∈ halfPlaneIdealBoundary := by simp [halfPlaneIdealBoundary]
  let C : HRayAt (g • z) := HRayAt.canonical (g • z) ∞ hb
  have htip : g • R.directionPoint ∈ C.val := by
    change s • R.directionPoint ∈ hRay (s • z) ∞
    rw [hz,hw,idealAltitude_base_ray]
    refine ⟨Real.log k,Real.log_nonneg hk.le,?_⟩
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [imaginaryAxisParam,metricProbe,Real.exp_log (lt_trans zero_lt_one hk)]
  have he : R.realGLMap g = C := (R.realGLMap g).eq_of_shared_point C
    ((realGL_isometry g).injective.ne
      (Ne.symm (show R.directionPoint ≠ z from R.directionPoint_mem.2)))
    (R.realGLMap_tip_mem g) htip
  refine ⟨s,hz,?_⟩
  change (R.realGLMap g).idealEndpoint = ∞
  rw [he]
  exact C.idealEndpoint_unique (isHLineRay_hRay _ _ hb)

theorem hRayThrough_realGLMap (z w : ℍ) (hzw : z ≠ w) (g : GL (Fin 2) ℝ) :
    (hRayThrough z w hzw).realGLMap g =
      hRayThrough (g • z) (g • w) ((realGL_isometry g).injective.ne hzw) := by
  apply HRayAt.eq_of_shared_point _ _ ((realGL_isometry g).injective.ne hzw)
  · rw [← HRayAt.realGLMap_carrier]
    exact mem_image_of_mem (g • ·) (hRayThrough_mem z w hzw)
  · exact hRayThrough_mem _ _ _

/-- Normalize a genuine ideal right triangle, using its actual common ideal end and ray angle. -/
theorem idealRightTriangle_normalize {a c : ℍ} (hac : a ≠ c) (A : HRayAt a) (C : HRayAt c)
    (hend : A.idealEndpoint = C.idealEndpoint)
    (hγ : hInteriorAngleMeasure (hRayThrough c a hac.symm) C = Real.pi / 2) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ, s • c = UpperHalfPlane.I ∧
      ‖((s • a : ℍ) : ℂ)‖ = 1 ∧
        (A.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ s)).idealEndpoint = ∞ := by
  obtain ⟨s,hc,hC⟩ := C.exists_sl2_normalized_upward
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0 < g.val.det := by
    change 0 < s.val.det
    rw [s.property]
    norm_num
  have hA : (A.realGLMap g).idealEndpoint = ∞ := by
    rw [A.realGLMap_idealEndpoint g hg,hend,← C.realGLMap_idealEndpoint g hg]
    exact hC
  have hCL : (C.realGLMap g).supportLine = .vertical 0 := by
    rw [(C.realGLMap g).supportLine_of_idealEndpoint_infty hC]
    change HalfPlaneLine.vertical (s • c).re = .vertical 0
    rw [hc]
    rfl
  let B := hRayThrough c a hac.symm
  have hO := (hInteriorAngleMeasure_eq_pi_div_two_iff (B.realGLMap g) (C.realGLMap g)).mp
    ((hInteriorAngleMeasure_realGLMap B C g).trans hγ)
  rw [hCL] at hO
  have haR : g • a ∈ (B.realGLMap g).val := by
    rw [← B.realGLMap_carrier]
    exact mem_image_of_mem (g • ·) (hRayThrough_mem c a hac.symm)
  have haL := (B.realGLMap g).subset_support haR
  refine ⟨s,hc,?_,hA⟩
  cases hL : (B.realGLMap g).supportLine with
  | vertical x =>
    rw [hL] at hO
    have he := ((HalfPlaneLine.vertical x).orthogonalAt_iff_coefficients (.vertical 0)
      (g • c) hO.1 hO.2.1).mp hO
    exact he.elim
  | circle d r hr =>
    rw [hL] at hO haL
    have he : d = 0 := ((HalfPlaneLine.circle d r hr).orthogonalAt_iff_coefficients (.vertical 0)
      (g • c) hO.1 hO.2.1).mp hO
    subst d
    have hp := hO.1
    change ‖((s • c : ℍ) : ℂ) - (0 : ℂ)‖ = r at hp
    rw [hc,sub_zero,UpperHalfPlane.coe_I,Complex.norm_I] at hp
    change ‖((s • a : ℍ) : ℂ) - (0 : ℂ)‖ = r at haL
    simpa only [sub_zero,← hp] using haL

theorem unitCircle_cosh_distance_I (z : ℍ) (hz : ‖(z : ℂ)‖ = 1) :
    Real.cosh (dist z UpperHalfPlane.I) = 1 / z.im := by
  have hn : ‖(z : ℂ) - (0 : ℂ)‖ = 1 := by simpa only [sub_zero] using hz
  have hcoords := norm_sub_real_eq_radius_sq hn
  simp only [sub_zero,one_pow] at hcoords
  rw [UpperHalfPlane.cosh_dist']
  norm_num
  rw [hcoords]
  field_simp
  norm_num

theorem unitCircle_sinh_distance_I (z : ℍ) (hz : ‖(z : ℂ)‖ = 1) :
    Real.sinh (dist z UpperHalfPlane.I) = |z.re| / z.im := by
  have hn : ‖(z : ℂ) - (0 : ℂ)‖ = 1 := by simpa only [sub_zero] using hz
  have hcoords := norm_sub_real_eq_radius_sq hn
  simp only [sub_zero,one_pow] at hcoords
  apply (sq_eq_sq₀ (Real.sinh_nonneg_iff.mpr dist_nonneg)
    (div_nonneg (abs_nonneg _) z.im_pos.le)).mp
  rw [Real.sinh_sq,unitCircle_cosh_distance_I z hz,div_pow,div_pow,sq_abs]
  field_simp
  nlinarith only [hcoords]

theorem unitCircle_tanh_distance_I (z : ℍ) (hz : ‖(z : ℂ)‖ = 1) :
    Real.tanh (dist z UpperHalfPlane.I) = |z.re| := by
  rw [Real.tanh_eq_sinh_div_cosh,unitCircle_sinh_distance_I z hz,unitCircle_cosh_distance_I z hz]
  field_simp

theorem unitCircle_parallelism_sin_cos (z : ℍ) (hz : ‖(z : ℂ)‖ = 1)
    (hne : z ≠ UpperHalfPlane.I) (R : HRayAt z) (hR : R.idealEndpoint = ∞) :
    Real.sin (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne)) = z.im ∧
      Real.cos (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne)) = |z.re| := by
  have hn : ‖(z : ℂ) - (0 : ℂ)‖ = 1 := by simpa only [sub_zero] using hz
  have hcoords := norm_sub_real_eq_radius_sq hn
  simp only [sub_zero,one_pow] at hcoords
  have hx : z.re ≠ 0 := by
    intro he
    have hy : z.im = 1 := by nlinarith [z.im_pos]
    apply hne
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact he
    · exact hy
  have hsinh := unitCircle_sinh_distance_I z hz
  have hnorm : ‖hyperbolicDirection z UpperHalfPlane.I‖ = 2 * |z.re| := by
    rw [hyperbolicDirection_norm,hsinh]
    norm_num
    field_simp
  obtain ⟨r,hr,he⟩ := hyperbolicDirection_pos_smul_tangent
    (hRayThrough z UpperHalfPlane.I hne) (hRayThrough_mem _ _ _) hne.symm
  have hangle : hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne) =
      angle Complex.I (hyperbolicDirection z UpperHalfPlane.I) := by
    rw [hInteriorAngleMeasure,R.tangentVector_of_idealEndpoint_infty hR,he,
      angle_smul_right_of_pos _ _ hr]
  have him : (hyperbolicDirection z UpperHalfPlane.I).im = 2 * z.re ^ 2 := by
    dsimp only [hyperbolicDirection]
    norm_num
    nlinarith only [hcoords]
  have hp := cos_angle_mul_norm_mul_norm Complex.I (hyperbolicDirection z UpperHalfPlane.I)
  rw [← hangle,Complex.norm_I,one_mul,hnorm,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] at hp
  simp only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,him] at hp
  have hc : Real.cos (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne)) = |z.re| := by
    apply mul_right_cancel₀ (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) (abs_pos.mpr hx)))
    calc
      _ = 2 * z.re ^ 2 := hp
      _ = |z.re| * (2 * |z.re|) := by rw [← sq_abs z.re]; ring
  refine ⟨?_,hc⟩
  apply (sq_eq_sq₀ (Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _) (angle_le_pi _ _))
    z.im_pos.le).mp
  change Real.sin (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne)) ^ 2 = z.im ^ 2
  have ht := Real.sin_sq_add_cos_sq (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne))
  rw [hc] at ht
  nlinarith only [ht,hcoords,sq_abs z.re]

theorem unitCircle_parallelism (z : ℍ) (hz : ‖(z : ℂ)‖ = 1)
    (hne : z ≠ UpperHalfPlane.I) (R : HRayAt z) (hR : R.idealEndpoint = ∞) :
    Real.sinh (dist z UpperHalfPlane.I) *
      Real.tan (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne)) = 1 ∧
    Real.cosh (dist z UpperHalfPlane.I) *
      Real.sin (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne)) = 1 ∧
    Real.tanh (dist z UpperHalfPlane.I) *
      (Real.cos (hInteriorAngleMeasure R (hRayThrough z UpperHalfPlane.I hne)))⁻¹ = 1 := by
  obtain ⟨hs,hc⟩ := unitCircle_parallelism_sin_cos z hz hne R hR
  have hAbs : |z.re| ≠ 0 := by
    intro he
    have hp := Real.sinh_pos_iff.mpr (dist_pos.mpr hne)
    rw [unitCircle_sinh_distance_I z hz,he,zero_div] at hp
    exact lt_irrefl (0 : ℝ) hp
  refine ⟨?_,?_,?_⟩
  · rw [Real.tan_eq_sin_div_cos,hs,hc,unitCircle_sinh_distance_I z hz]
    field_simp
  · rw [unitCircle_cosh_distance_I z hz,hs]
    exact one_div_mul_cancel z.im_ne_zero
  · rw [unitCircle_tanh_distance_I z hz,hc]
    exact mul_inv_cancel₀ hAbs

/-- All three angle-of-parallelism identities for arbitrary genuine rays sharing an ideal end. -/
theorem hIdealRightTriangle_parallelism {a c : ℍ} (hac : a ≠ c) (A : HRayAt a) (C : HRayAt c)
    (hend : A.idealEndpoint = C.idealEndpoint)
    (hγ : hInteriorAngleMeasure (hRayThrough c a hac.symm) C = Real.pi / 2) :
    Real.sinh (dist a c) * Real.tan (hInteriorAngleMeasure A (hRayThrough a c hac)) = 1 ∧
    Real.cosh (dist a c) * Real.sin (hInteriorAngleMeasure A (hRayThrough a c hac)) = 1 ∧
    Real.tanh (dist a c) * (Real.cos (hInteriorAngleMeasure A (hRayThrough a c hac)))⁻¹ = 1 := by
  obtain ⟨s,hc,hn,hA⟩ := idealRightTriangle_normalize hac A C hend hγ
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hc' : g • c = UpperHalfPlane.I := hc
  have hne : g • a ≠ UpperHalfPlane.I := by
    rw [← hc']
    exact (realGL_isometry g).injective.ne hac
  have hα : hInteriorAngleMeasure (A.realGLMap g) (hRayThrough (g • a) UpperHalfPlane.I hne) =
      hInteriorAngleMeasure A (hRayThrough a c hac) := by
    have he := hInteriorAngleMeasure_realGLMap A (hRayThrough a c hac) g
    rw [hRayThrough_realGLMap] at he
    simpa only [hc'] using he
  have hd : dist (g • a) UpperHalfPlane.I = dist a c := by
    rw [← hc',(realGL_isometry g).dist_eq]
  have h := unitCircle_parallelism (g • a) hn hne (A.realGLMap g) hA
  rwa [hα,hd] at h

theorem DiscRayAt.toHalfPlane_idealEndpoint {z : 𝔻} (R : DiscRayAt z) :
    R.toHalfPlane.idealEndpoint = extendedCayley.symm R.idealEndpoint :=
  R.toHalfPlane.idealEndpoint_unique R.isRay.toHalfPlane

theorem ClosedDiscTriangle.parallelism_of_finite_vertices (T : ClosedDiscTriangle) (a c : 𝔻)
    (ha : T.a = discToClosedModel a) (hc : T.c = discToClosedModel c)
    (hb : ‖(T.b : ℂ)‖ = 1) (hγ : T.gamma = Real.pi / 2) :
    Real.sinh T.lengthB.toReal * Real.tan T.alpha = 1 ∧
      Real.cosh T.lengthB.toReal * Real.sin T.alpha = 1 ∧
        Real.tanh T.lengthB.toReal * (Real.cos T.alpha)⁻¹ = 1 := by
  have hac : a ≠ c := by
    intro he
    apply T.c_ne_a
    rw [hc,ha,he]
  have hacH : discToHalfPlane a ≠ discToHalfPlane c := cayleyHomeomorph.symm.injective.ne hac
  let U := T.cycle.cycle
  let A := T.cornerRayABAtA a ha
  let C := U.cornerRayACAtA c hc
  have hAC : T.cornerRayACAtA a ha = discRayThrough a c hac := by
    apply (discRayThrough_eq hac _ ?_).symm
    apply T.cornerAtA_sideB_finite_subset a ha
    change discToClosedModel c ∈ T.sideB
    rw [← hc,T.mem_sideB_iff_coordinate,T.coordinate_c]
    norm_num
  have hCA : U.cornerRayABAtA c hc = discRayThrough c a hac.symm := by
    apply (discRayThrough_eq hac.symm _ ?_).symm
    apply U.cornerAtA_sideC_finite_subset c hc
    change discToClosedModel a ∈ U.sideC
    rw [show discToClosedModel a = U.b from ha.symm,U.mem_sideC_iff_coordinate,U.coordinate_b]
    norm_num
  have hend : A.toHalfPlane.idealEndpoint = C.toHalfPlane.idealEndpoint := by
    rw [A.toHalfPlane_idealEndpoint,C.toHalfPlane_idealEndpoint]
    change extendedCayley.symm (T.cornerRayABAtA a ha).idealEndpoint =
      extendedCayley.symm (U.cornerRayACAtA c hc).idealEndpoint
    rw [T.cornerRayABAtA_idealEndpoint a ha hb,U.cornerRayACAtA_idealEndpoint c hc hb]
    rfl
  have hα : T.alpha = hInteriorAngleMeasure A.toHalfPlane
      (hRayThrough (discToHalfPlane a) (discToHalfPlane c) hacH) := by
    rw [T.alpha_of_finite a ha,discInteriorAngleMeasure_eq_halfPlane,hAC,discRayThrough_toHalfPlane]
  have hγH : hInteriorAngleMeasure
      (hRayThrough (discToHalfPlane c) (discToHalfPlane a) hacH.symm) C.toHalfPlane = Real.pi / 2 := by
    have he := (U.alpha_of_finite c hc).symm.trans hγ
    rw [discInteriorAngleMeasure_eq_halfPlane,hCA,discRayThrough_toHalfPlane] at he
    exact he
  have hlen : T.lengthB.toReal = dist (discToHalfPlane a) (discToHalfPlane c) := by
    have hn : 0 ≤ discPathDist c a := by rw [discPathDist_eq_halfPlane]; exact dist_nonneg
    rw [ClosedDiscTriangle.lengthB,hc,ha,extendedDiscSideLength_finite,ENNReal.toReal_ofReal hn,
      discPathDist_eq_halfPlane,dist_comm]
  have he := hIdealRightTriangle_parallelism hacH A.toHalfPlane C.toHalfPlane hend hγH
  rwa [← hα,← hlen] at he

/-- All three parts, for a genuine finite-or-ideal native triangle. -/
theorem ClosedDiscTriangle.angle_parallelism_sinh_cosh_tanh_identities (T : ClosedDiscTriangle)
    (hα : T.alpha ≠ 0) (hβ : T.beta = 0) (hγ : T.gamma = Real.pi / 2) :
    Real.sinh T.lengthB.toReal * Real.tan T.alpha = 1 ∧
      Real.cosh T.lengthB.toReal * Real.sin T.alpha = 1 ∧
        Real.tanh T.lengthB.toReal * (Real.cos T.alpha)⁻¹ = 1 := by
  have hb : ‖(T.b : ℂ)‖ = 1 := T.cycle.alpha_eq_zero_iff_ideal.mp hβ
  have ha : ‖(T.a : ℂ)‖ < 1 := by
    by_contra! he
    exact hα (T.alpha_of_ideal (le_antisymm T.a.norm_le_one he))
  have hc : ‖(T.c : ℂ)‖ < 1 := by
    by_contra! he
    have hzero := T.gamma_of_ideal (le_antisymm T.c.norm_le_one he)
    rw [hγ] at hzero
    linarith [Real.pi_pos]
  exact T.parallelism_of_finite_vertices (closedDiscFinitePoint T.a ha) (closedDiscFinitePoint T.c hc)
    (closedDiscFinitePoint_spec T.a ha).symm (closedDiscFinitePoint_spec T.c hc).symm hb hγ

theorem ClosedHTriangle.angle_parallelism_sinh_cosh_tanh_identities (T : ClosedHTriangle)
    (hα : T.alpha ≠ 0) (hβ : T.beta = 0) (hγ : T.gamma = Real.pi / 2) :
    Real.sinh T.lengthB.toReal * Real.tan T.alpha = 1 ∧
      Real.cosh T.lengthB.toReal * Real.sin T.alpha = 1 ∧
        Real.tanh T.lengthB.toReal * (Real.cos T.alpha)⁻¹ = 1 :=
  T.toDiscTriangle.angle_parallelism_sinh_cosh_tanh_identities hα hβ hγ

end
end LowDimensionalTopology.Geometry.Hyperbolic
