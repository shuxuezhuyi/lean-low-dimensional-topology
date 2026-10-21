/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HypercycleDistance
/-!
# Genuine ideal-triangle angle and opposite-line distance

The two ideal vertices and the finite vertex are the actual native triangle
points. Its opposite line distance is the genuine path-metric infimum, and its
actual angle gives the exact half-angle identity. This yields the geometric
step from the explicit angle bound. Obtaining that bound from an
actual Fuchsian fundamental polygon is still a separate group-level obligation.

The uniform numerical bound requires order at least three; at order two its
claimed scalar comparison is false. Both the restriction and the exact scalar
counterexample are explicit below.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Set InnerProductGeometry LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Euclidean
open scoped UpperHalfPlane Complex.UnitDisc Topology OnePoint MatrixGroups
noncomputable section

theorem unitCircle_ideal_vertex_cosh_half_angle (z : ℍ) (b : ℂ) (hz : ‖(z:ℂ)‖=1)
    (hb : ‖b‖=1) (hbi : b.im=0) (hne : z.re≠b.re) (α : ℝ) (hα : α∈Ioo (0:ℝ) Real.pi)
    (hcos : Real.cos α=if z.re<b.re then -z.re else z.re) :
    Real.cosh ((HalfPlaneLine.vertical b.re).pointDist z)*Real.sin (α/2)=1 := by
  have hu : z.re^2+z.im^2=1:=by
    have h:=Complex.normSq_eq_norm_sq (z:ℂ)
    rw [hz,one_pow,Complex.normSq_apply] at h
    change z.re*z.re+z.im*z.im=1 at h
    nlinarith only [h]
  have hbunit : b.re^2=1:=by
    have h:=Complex.normSq_eq_norm_sq b
    rw [hb,one_pow,Complex.normSq_apply,hbi] at h
    nlinarith only [h]
  have hbound : |z.re|≤1:=by
    have h:=Complex.abs_re_le_norm (z:ℂ)
    change |z.re|≤‖(z:ℂ)‖ at h
    simpa only [hz] using h
  have hct : Real.cos α= -b.re*z.re:=by
    by_cases hh : z.re<b.re
    · rw [ite_eq_left hh] at hcos
      have hv : b.re=1:=by nlinarith [abs_le.mp hbound |>.1]
      rw [hv]
      simpa only [neg_mul,one_mul] using hcos
    · rw [ite_eq_right hh] at hcos
      have hv : b.re= -1:=by
        have hlt : b.re<z.re:=lt_of_le_of_ne (le_of_not_gt hh) hne.symm
        nlinarith [abs_le.mp hbound |>.2]
      rw [hv]
      simpa only [neg_neg,one_mul] using hcos
  let C:=Real.cosh ((HalfPlaneLine.vertical b.re).pointDist z)
  have hformula:=verticalLine_pointDist_cosh b.re z
  change C=‖(z:ℂ)-(b.re:ℂ)‖/z.im at hformula
  have he : C^2*z.im^2=(z.re-b.re)^2+z.im^2:=by
    have he':=congrArg (fun x:ℝ=>x^2) ((eq_div_iff z.im_pos.ne').mp hformula)
    rw [mul_pow] at he'
    have hn:=norm_sub_real_sq b.re z
    nlinarith only [he',hn]
  have hid : (C^2*(1-Real.cos α)-2)*z.im^2=0:=by
    rw [hct]
    linear_combination (1+b.re*z.re)*he+(b.re*z.re-1)*hu+
      (1+b.re*z.re-2*z.re^2)*hbunit
  have heq : C^2*(1-Real.cos α)=2:=by
    have h:=(mul_eq_zero.mp hid).resolve_right (pow_ne_zero 2 z.im_pos.ne')
    linarith only [h]
  have hhalf:=Real.cos_two_mul (α/2)
  rw [show 2*(α/2)=α by ring] at hhalf
  have htrig:=Real.sin_sq_add_cos_sq (α/2)
  have hp : 0<C*Real.sin (α/2):=mul_pos (Real.cosh_pos _)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hα.1]) (by linarith [hα.2,Real.pi_pos]))
  have hsin : 1-Real.cos α=2*Real.sin (α/2)^2:=by nlinarith only [hhalf,htrig]
  rw [hsin] at heq
  have hsquare : (C*Real.sin (α/2))^2=1:=by nlinarith only [heq]
  change C*Real.sin (α/2)=1
  nlinarith only [hsquare,hp]

/-- The actual opposite h-line distance of a finite vertex with two ideal neighbours. -/
theorem closedTriangle_cosh_pointDist_half_angle (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a=discToClosedModel z) (hb : ‖(T.b:ℂ)‖=1) (hc : ‖(T.c:ℂ)‖=1) :
    Real.cosh (T.sideLineA.pointDist z)*Real.sin (T.alpha/2)=1 := by
  obtain ⟨g,hg,hEnd,hline⟩:=T.exists_ideal_vertex_area_normalizer hc
  obtain ⟨a,b,hna,hnb,_hia,_hib,hne,hA,hB,hL,_hR⟩:=T.normalized_sides_and_vertices hc g hg hEnd hline
  have hza : ((g • discToHalfPlane z:ℍ):ℂ)=a:=realGL_closed_finite_vertex z g hg a (by rwa [←ha])
  have hbi : b.im=0:=realGL_closed_ideal_vertex_im T.b hb g b hB
  have hcos:=T.alpha_cos_normalized hc g hg hline hEnd a b hna hnb hne hA hB
  have hα : T.alpha∈Ioo (0:ℝ) Real.pi:=⟨T.alpha_pos_iff_finite.mpr (by rw [ha];exact z.norm_lt_one),T.alpha_mem_Ico.2⟩
  have hzunit : ‖((g • discToHalfPlane z:ℍ):ℂ)‖=1:=hza ▸ hna
  have hne' : (g • discToHalfPlane z:ℍ).re≠b.re:=by
    change ((g • discToHalfPlane z:ℍ):ℂ).re≠b.re
    simpa only [hza] using hne
  have hcos' : Real.cos T.alpha=if (g • discToHalfPlane z:ℍ).re<b.re then
      -(g • discToHalfPlane z:ℍ).re else (g • discToHalfPlane z:ℍ).re:=by
    change Real.cos T.alpha=if ((g • discToHalfPlane z:ℍ):ℂ).re<b.re then
      -((g • discToHalfPlane z:ℍ):ℂ).re else ((g • discToHalfPlane z:ℍ):ℂ).re
    simpa only [hza] using hcos
  have h:=unitCircle_ideal_vertex_cosh_half_angle (g • discToHalfPlane z) b hzunit hnb hbi hne' T.alpha hα hcos'
  rw [(T.sideLineA.toHalfPlane.pointDist_isometry_image (HalfPlaneLine.vertical b.re)
    (fun w:ℍ=>g • w) (realGL_isometry g) hL (discToHalfPlane z)),←T.sideLineA.pointDist_eq_halfPlane] at h
  exact h

theorem sin_pi_div_nat_pos (n : ℕ) (hn : 2≤n) : 0<Real.sin (Real.pi/(n:ℝ)) := by
  have hn0 : (0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)<n:=by exact_mod_cast (show 1<n by omega)
  exact Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hn0)
    ((div_lt_iff₀ hn0).mpr (by nlinarith only [hn1,Real.pi_pos]))

theorem csc_pi_div_nat_ge_two_div_sqrt_three (n : ℕ) (hn : 3≤n) :
    2/Real.sqrt 3≤1/Real.sin (Real.pi/(n:ℝ)) := by
  have hn3 : (3:ℝ)≤n:=by exact_mod_cast hn
  have hsqrt : 0<Real.sqrt 3:=by positivity
  have hangle : Real.pi/(n:ℝ)≤Real.pi/3:=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hn3
  have hnonneg : 0≤Real.pi/(n:ℝ):=div_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
  have hs : Real.sin (Real.pi/(n:ℝ))≤Real.sqrt 3/2:=by
    rw [←Real.sin_pi_div_three]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hangle
  apply (div_le_div_iff₀ hsqrt (sin_pi_div_nat_pos n (by omega))).mpr
  nlinarith only [hs]

/-- The source numerical universal lower bound requires order at least three. -/
theorem csc_pi_div_two_lt_two_div_sqrt_three :
    1/Real.sin (Real.pi/2)<2/Real.sqrt 3 := by
  rw [Real.sin_pi_div_two,div_one]
  have hsqrt : 0<Real.sqrt 3:=by positivity
  have hsquare : (Real.sqrt 3)^2=3:=Real.sq_sqrt (by norm_num)
  apply (lt_div_iff₀ hsqrt).mpr
  nlinarith only [hsquare,hsqrt]

/-- Exact geometric step; deriving the angle bound from a group fundamental polygon is separate. -/
theorem closedTriangle_cosh_pointDist_ge_csc_order (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a=discToClosedModel z) (hb : ‖(T.b:ℂ)‖=1) (hc : ‖(T.c:ℂ)‖=1)
    (n : ℕ) (hn : 2≤n) (hangle : T.alpha≤2*Real.pi/(n:ℝ)) :
    1/Real.sin (Real.pi/(n:ℝ))≤Real.cosh (T.sideLineA.pointDist z) := by
  have he:=closedTriangle_cosh_pointDist_half_angle T z ha hb hc
  have hn2 : (2:ℝ)≤n:=by exact_mod_cast hn
  have hhalf : T.alpha/2≤Real.pi/(n:ℝ):=by
    have hangle' : T.alpha≤2*(Real.pi/(n:ℝ)):=by simpa only [mul_div_assoc] using hangle
    linarith only [hangle']
  have hs:=Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤T.alpha/2 from by linarith [T.alpha_mem_Ico.1,Real.pi_pos])
    (show Real.pi/(n:ℝ)≤Real.pi/2 from div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hn2) hhalf
  apply (div_le_iff₀ (sin_pi_div_nat_pos n hn)).mpr
  have hp:=mul_le_mul_of_nonneg_left hs (Real.cosh_pos (T.sideLineA.pointDist z)).le
  linarith only [he,hp]

/-- The corrected universal numerical bound for the geometric step, with the necessary order restriction. -/
theorem closedTriangle_cosh_pointDist_ge_two_div_sqrt_three (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a=discToClosedModel z) (hb : ‖(T.b:ℂ)‖=1) (hc : ‖(T.c:ℂ)‖=1)
    (n : ℕ) (hn : 3≤n) (hangle : T.alpha≤2*Real.pi/(n:ℝ)) :
    2/Real.sqrt 3≤Real.cosh (T.sideLineA.pointDist z) :=
  (csc_pi_div_nat_ge_two_div_sqrt_three n hn).trans
    (closedTriangle_cosh_pointDist_ge_csc_order T z ha hb hc n (by omega) hangle)

end
end LowDimensionalTopology.Geometry.Hyperbolic
