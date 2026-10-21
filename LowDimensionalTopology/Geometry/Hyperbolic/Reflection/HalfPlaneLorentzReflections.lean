/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
/-! # Lorentz-coordinate formulas for genuine h-line reflections -/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology
noncomputable section

theorem halfPlanePointSpatial_explicit (z : ℍ) :
    halfPlanePointSpatial z=⟨(z.re^2+z.im^2-1)/(2*z.im),-z.re/z.im⟩ := by
  apply Complex.ext
  all_goals
    simp only [halfPlanePointSpatial,halfPlaneKleinCoordinate_explicit,halfPlaneKleinHeight,
      Complex.smul_re,Complex.smul_im,smul_eq_mul]
    field_simp

theorem HalfPlaneLine.normalTimeAt_vertical (a : ℝ) (z : ℍ) :
    (HalfPlaneLine.vertical a).normalTimeAt z=(a-z.re)/z.im := by
  simp only [HalfPlaneLine.normalTimeAt,halfPlanePointSpatial_explicit,halfPlaneKleinHeight,
    HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset,
      _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  field_simp
  ring

theorem HalfPlaneLine.normalTimeAt_circle (c r : ℝ) (hr : 0<r) (z : ℍ) :
    (HalfPlaneLine.circle c r hr).normalTimeAt z=
      -((z.re-c)^2+z.im^2-r^2)/(2*r*z.im) := by
  simp only [HalfPlaneLine.normalTimeAt,halfPlanePointSpatial_explicit,halfPlaneKleinHeight,
    HalfPlaneLine.incenterNormal, HalfPlaneLine.incenterOffset,
      _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  field_simp
  ring

theorem verticalReflection_re (a : ℝ) (z : ℍ) :
    (verticalReflection a z).re=2*a-z.re := by
  have h:=congrArg Complex.re (verticalReflection_coe a z)
  simpa only [Complex.sub_re,Complex.ofReal_re,Complex.conj_re,UpperHalfPlane.coe_re] using h

theorem verticalReflection_im (a : ℝ) (z : ℍ) :
    (verticalReflection a z).im=z.im := by
  have h:=congrArg Complex.im (verticalReflection_coe a z)
  simpa only [Complex.sub_im,Complex.ofReal_im,Complex.conj_im,zero_sub,neg_neg,UpperHalfPlane.coe_im] using h

theorem circleReflection_re (c r : ℝ) (hr : 0<r) (z : ℍ) :
    (circleReflection c r hr z).re=c+r^2*(z.re-c)/((z.re-c)^2+z.im^2) := by
  have h:=congrArg Complex.re (circleReflection_coe c r hr z)
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.div_re,←Complex.ofReal_pow,
    Complex.ofReal_im,Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im,
    sub_zero,Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
    mul_zero,zero_mul,add_zero,neg_mul_neg,neg_sq,zero_div,←sq] using h

theorem circleReflection_im (c r : ℝ) (hr : 0<r) (z : ℍ) :
    (circleReflection c r hr z).im=r^2*z.im/((z.re-c)^2+z.im^2) := by
  have h:=congrArg Complex.im (circleReflection_coe c r hr z)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.div_im,←Complex.ofReal_pow,Complex.ofReal_re,Complex.sub_re,Complex.sub_im,Complex.conj_re,
    Complex.conj_im,sub_zero,Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
    mul_zero,zero_mul,add_zero,zero_sub,mul_neg,neg_div,neg_mul_neg,neg_neg,neg_sq,zero_div,add_zero,zero_add,sub_neg_eq_add,←sq] using h


theorem halfPlaneKleinHeight_reflection (N : HalfPlaneLine) (z : ℍ) :
    halfPlaneKleinHeight (N.reflection z)=halfPlaneKleinHeight z+2*N.normalTimeAt z*N.incenterOffset := by
  cases N with
  | vertical a =>
    simp only [HalfPlaneLine.reflection,verticalReflection_re,verticalReflection_im,
      halfPlaneKleinHeight,HalfPlaneLine.normalTimeAt_vertical,HalfPlaneLine.incenterOffset]
    field_simp
    ring
  | circle c r hr =>
    have hq : (z.re-c)^2+z.im^2≠0 := ne_of_gt (by nlinarith [sq_nonneg (z.re-c),z.im_pos])
    simp only [HalfPlaneLine.reflection,circleReflection_re,circleReflection_im,
      halfPlaneKleinHeight,HalfPlaneLine.normalTimeAt_circle,HalfPlaneLine.incenterOffset]
    field_simp
    ring

theorem halfPlanePointSpatial_reflection (N : HalfPlaneLine) (z : ℍ) :
    halfPlanePointSpatial (N.reflection z)=halfPlanePointSpatial z+(2*N.normalTimeAt z) • N.incenterNormal := by
  cases N with
  | vertical a =>
    apply Complex.ext
    all_goals
      simp only [HalfPlaneLine.reflection,halfPlanePointSpatial_explicit,verticalReflection_re,
        verticalReflection_im,HalfPlaneLine.normalTimeAt_vertical,HalfPlaneLine.incenterNormal,
        Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
      field_simp
      ring
  | circle c r hr =>
    have hq : (z.re-c)^2+z.im^2≠0 := ne_of_gt (by nlinarith [sq_nonneg (z.re-c),z.im_pos])
    apply Complex.ext
    all_goals
      simp only [HalfPlaneLine.reflection,halfPlanePointSpatial_explicit,circleReflection_re,
        circleReflection_im,HalfPlaneLine.normalTimeAt_circle,HalfPlaneLine.incenterNormal,
        Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
      field_simp
      ring

theorem HalfPlaneLine.normalTimeAt_reflection (R N : HalfPlaneLine) (z : ℍ) :
    R.normalTimeAt (N.reflection z)=R.normalTimeAt z-2*R.normalPairing N*N.normalTimeAt z := by
  simp only [HalfPlaneLine.normalTimeAt,halfPlaneKleinHeight_reflection,halfPlanePointSpatial_reflection,
    inner_add_right,inner_smul_right,HalfPlaneLine.normalPairing]
  ring


theorem HalfPlaneLine.affine_reflection (R N : HalfPlaneLine) (z : ℍ) :
    (1-2*N.incenterOffset*hKleinAffine N.incenterNormal N.incenterOffset z)*
        hKleinAffine R.incenterNormal R.incenterOffset (N.reflection z)=
      hKleinAffine R.incenterNormal R.incenterOffset z-
        2*R.normalPairing N*hKleinAffine N.incenterNormal N.incenterOffset z := by
  have hH:=halfPlaneKleinHeight_reflection N z
  rw [N.normalTimeAt_eq_affine] at hH
  have ht:=R.normalTimeAt_reflection N z
  rw [R.normalTimeAt_eq_affine,R.normalTimeAt_eq_affine,N.normalTimeAt_eq_affine,hH] at ht
  apply (mul_left_cancel₀ (halfPlaneKleinHeight_pos z).ne')
  nlinarith only [ht]

def DiscLine.reflectionAffineDenominator (N : DiscLine) (p : 𝕔𝔻) : ℝ :=
  1-2*N.incenterOffset*closedDiscKleinAffine N.incenterNormal N.incenterOffset p

theorem lorentzReflection_denominator_pos (n x : ℂ) (t : ℝ)
    (hu : ‖n‖^2-t^2=1) (hx : ‖x‖≤1) :
    0<1-2*t*(inner ℝ n x-t) := by
  have hi : (inner ℝ n x)^2≤1+t^2 := by
    have he:=real_inner_mul_inner_self_le n x
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
    have hxn : ‖x‖^2≤1 := by nlinarith [norm_nonneg x]
    nlinarith [mul_nonneg (sq_nonneg ‖n‖) (sub_nonneg.mpr hxn)]
  by_contra hn
  have hb : 1+2*t^2≤2*t*inner ℝ n x := by linarith
  have ha : 0≤1+2*t^2 := by positivity
  have hs:=sq_le_sq₀ ha (ha.trans hb)
  have hs': (1+2*t^2)^2≤(2*t*inner ℝ n x)^2 := hs.mpr hb
  nlinarith [mul_nonneg (sq_nonneg (2*t)) (sub_nonneg.mpr hi)]

theorem DiscLine.reflectionAffineDenominator_pos (N : DiscLine) (p : 𝕔𝔻) :
    0<N.reflectionAffineDenominator p := by
  apply lorentzReflection_denominator_pos
  · exact N.toHalfPlane.incenterNormal_lorentz_unit
  · exact (closedPoincareToKlein p).norm_le_one


theorem HalfPlaneLine.affine_reflection_general (N : HalfPlaneLine) (n : ℂ) (t : ℝ) (z : ℍ) :
    (1-2*N.incenterOffset*hKleinAffine N.incenterNormal N.incenterOffset z)*
        hKleinAffine n t (N.reflection z)=
      hKleinAffine n t z-
        2*(inner ℝ n N.incenterNormal-t*N.incenterOffset)*
          hKleinAffine N.incenterNormal N.incenterOffset z := by
  have hH:=halfPlaneKleinHeight_reflection N z
  rw [N.normalTimeAt_eq_affine] at hH
  have hx:=congrArg (fun v : ℂ => inner ℝ n v) (halfPlanePointSpatial_reflection N z)
  simp only [halfPlanePointSpatial,inner_add_right,inner_smul_right] at hx
  rw [N.normalTimeAt_eq_affine,hH] at hx
  apply (mul_left_cancel₀ (halfPlaneKleinHeight_pos z).ne')
  unfold hKleinAffine at *
  nlinarith only [hx]

theorem DiscLine.closedAffine_reflection_general (N : DiscLine) (n : ℂ) (t : ℝ) (p : 𝕔𝔻) :
    N.reflectionAffineDenominator p*closedDiscKleinAffine n t (N.closedReflectionIsometry.closedMap p)=
      closedDiscKleinAffine n t p-
        2*(inner ℝ n N.incenterNormal-t*N.incenterOffset)*
          closedDiscKleinAffine N.incenterNormal N.incenterOffset p := by
  have hc (m : ℂ) (u : ℝ) : Continuous (closedDiscKleinAffine m u) :=
    (continuous_const.inner isClosedEmbedding_closedKleinCoordinate.continuous).sub continuous_const
  have hD : Continuous N.reflectionAffineDenominator :=
    continuous_const.sub ((continuous_const.mul continuous_const).mul (hc _ _))
  have he : (fun p : 𝕔𝔻 => N.reflectionAffineDenominator p*
      closedDiscKleinAffine n t (N.closedReflectionIsometry.closedMap p))=
      (fun p : 𝕔𝔻 => closedDiscKleinAffine n t p-
        2*(inner ℝ n N.incenterNormal-t*N.incenterOffset)*
          closedDiscKleinAffine N.incenterNormal N.incenterOffset p) := by
    apply denseRange_discToClosedModel.equalizer
    · exact hD.mul ((hc _ _).comp N.closedReflectionIsometry.closedMap.continuous)
    · exact (hc _ _).sub (continuous_const.mul (hc _ _))
    · funext z
      simp only [Function.comp_apply]
      rw [N.closedReflectionIsometry.finite_commutes]
      simpa only [DiscLine.reflectionAffineDenominator,closedDiscKleinAffine,
        closedKleinCoordinate_disc_inclusion,DiscLine.closedReflectionIsometry,
        DiscLine.reflection,DiscLine.incenterNormal,DiscLine.incenterOffset,
        halfPlaneKleinCoordinate,hKleinAffine,halfPlaneToDisc_discToHalfPlane] using
          N.toHalfPlane.affine_reflection_general n t (discToHalfPlane z)
  exact congrFun he p

theorem DiscLine.closedAffine_reflection (R N : DiscLine) (p : 𝕔𝔻) :
    N.reflectionAffineDenominator p*
        closedDiscKleinAffine R.incenterNormal R.incenterOffset (N.closedReflectionIsometry.closedMap p)=
      closedDiscKleinAffine R.incenterNormal R.incenterOffset p-
        2*R.toHalfPlane.normalPairing N.toHalfPlane*
          closedDiscKleinAffine N.incenterNormal N.incenterOffset p :=
  N.closedAffine_reflection_general R.incenterNormal R.incenterOffset p

end
end LowDimensionalTopology.Geometry.Hyperbolic
