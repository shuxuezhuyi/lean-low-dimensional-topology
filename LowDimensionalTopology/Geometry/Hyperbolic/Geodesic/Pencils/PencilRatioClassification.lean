/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.PencilRatios

/-!
# The genuine distance-ratio line criterion, with its required correction
-/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- Corrected P7 uses nonnegative weights not both zero, and an entire actual geodesic
contained in the level locus. It does not identify a two-branch locus with one line. -/
def HalfPlaneLine.IsDistanceRatioLine (L M N : HalfPlaneLine) : Prop :=
  ∃a b : ℝ,0≤a ∧ 0≤b ∧ 0<a+b ∧ N.carrier⊆L.sinhDistanceRatioLocus M a b

def DiscLine.IsDistanceRatioLine (L M N : DiscLine) : Prop :=
  ∃a b : ℝ,0≤a ∧ 0≤b ∧ 0<a+b ∧ N.carrier⊆L.sinhDistanceRatioLocus M a b

theorem HalfPlaneLine.isDistanceRatioLine_self_left (L M : HalfPlaneLine) : L.IsDistanceRatioLine M L := by
  refine ⟨1,0,by norm_num,le_rfl,by norm_num,?_⟩
  intro z hz
  have he : L.pointDist z=0:=Metric.infDist_zero_of_mem hz
  change 1*Real.sinh (L.pointDist z)=0*Real.sinh (M.pointDist z)
  rw [he,Real.sinh_zero,mul_zero,zero_mul]

theorem HalfPlaneLine.isDistanceRatioLine_self_right (L M : HalfPlaneLine) : L.IsDistanceRatioLine M M := by
  refine ⟨0,1,le_rfl,by norm_num,by norm_num,?_⟩
  intro z hz
  have he : M.pointDist z=0:=Metric.infDist_zero_of_mem hz
  change 0*Real.sinh (L.pointDist z)=1*Real.sinh (M.pointDist z)
  rw [he,Real.sinh_zero,mul_zero,zero_mul]

theorem quadratic_three_roots_coefficients (A B C x y z : ℝ) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hx : A*x^2+B*x+C=0) (hy : A*y^2+B*y+C=0) (hz : A*z^2+B*z+C=0) :
    A=0 ∧ B=0 ∧ C=0 := by
  have h1 : (x-y)*(A*(x+y)+B)=0:=by nlinarith only [hx,hy]
  have h2 : (x-z)*(A*(x+z)+B)=0:=by nlinarith only [hx,hz]
  have h1':=(mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hxy)
  have h2':=(mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hxz)
  have he : A*(y-z)=0:=by nlinarith only [h1',h2']
  have hA : A=0:=(mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hyz)
  have hB : B=0:=by rw [hA] at h1';simpa using h1'
  exact ⟨hA,hB,by rw [hA,hB] at hx;simpa using hx⟩

theorem circle_exists_point_real_part (c r : ℝ) (hr : 0<r) (x : ℝ) (hx : |x-c|<r) :
    ∃z : ℍ,z∈(HalfPlaneLine.circle c r hr).carrier ∧ z.re=x := by
  have hx2 : (x-c)^2<r^2 := by
    have h:=(sq_lt_sq₀ (abs_nonneg (x-c)) hr.le).mpr hx
    simpa only [sq_abs] using h
  have hy : 0<r^2-(x-c)^2:=sub_pos.mpr hx2
  let z:=metricProbe x (Real.sqrt (r^2-(x-c)^2)) (Real.sqrt_pos.mpr hy)
  refine ⟨z,?_,rfl⟩
  apply norm_sub_real_eq_of_sq hr
  change (x-c)^2+(Real.sqrt (r^2-(x-c)^2))^2=r^2
  rw [Real.sq_sqrt hy.le]
  ring

theorem HalfPlaneLine.quadratic_re_vanish (N : HalfPlaneLine) (A B C : ℝ)
    (h : ∀z∈N.carrier,A*z.re^2+B*z.re+C=0) :
    (∃d : ℝ,N=HalfPlaneLine.vertical d) ∨ (A=0 ∧ B=0 ∧ C=0) := by
  cases N with
  | vertical d => exact Or.inl ⟨d,rfl⟩
  | circle c r hr =>
    have hleft : |(c-r/2)-c|<r := by
      rw [show c-r/2-c= -(r/2) by ring,abs_neg,abs_of_pos (by positivity)]
      linarith
    have hright : |(c+r/2)-c|<r := by
      rw [show c+r/2-c=r/2 by ring,abs_of_pos (by positivity)]
      linarith
    obtain ⟨p,hp,hpx⟩:=circle_exists_point_real_part c r hr (c-r/2) hleft
    obtain ⟨q,hq,hqx⟩:=circle_exists_point_real_part c r hr c (by simpa using hr)
    obtain ⟨w,hw,hwx⟩:=circle_exists_point_real_part c r hr (c+r/2) hright
    right
    apply quadratic_three_roots_coefficients A B C (c-r/2) c (c+r/2)
      (by linarith) (by linarith) (by linarith)
    · simpa only [hpx] using h p hp
    · simpa only [hqx] using h q hq
    · simpa only [hwx] using h w hw

/-- Corrected P7 for the genuine parallel-line normal form, including both generators. -/
theorem vertical_isDistanceRatioLine_iff (A B : ℝ) (hAB : A≠B) (N : HalfPlaneLine) :
    (HalfPlaneLine.vertical A).IsDistanceRatioLine (.vertical B) N ↔ ∃x : ℝ,N=.vertical x := by
  constructor
  · rintro ⟨a,b,ha,hb,hsum,hN⟩
    have hpoly : ∀z∈N.carrier,(a^2-b^2)*z.re^2+(-2*a^2*A+2*b^2*B)*z.re+
        (a^2*A^2-b^2*B^2)=0 := by
      intro z hz
      have he:=hN hz
      change a*Real.sinh ((HalfPlaneLine.vertical A).pointDist z)=
        b*Real.sinh ((HalfPlaneLine.vertical B).pointDist z) at he
      rw [verticalLine_pointDist_sinh,verticalLine_pointDist_sinh,
        ←mul_div_assoc,←mul_div_assoc,div_left_inj' z.im_ne_zero] at he
      have he2:=congrArg (fun x : ℝ=>x^2) he
      rw [mul_pow,mul_pow,sq_abs,sq_abs] at he2
      nlinarith only [he2]
    rcases N.quadratic_re_vanish _ _ _ hpoly with he|he
    · exact he
    · have hab : a=b:=by nlinarith only [ha,hb,he.1]
      subst b
      have ha0 : 0<a:=by linarith only [hsum]
      have hh : a^2*(A-B)=0:=by nlinarith only [he.2.1]
      have hzero:=(mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 ha0.ne')
      exact False.elim (hAB (sub_eq_zero.mp hzero))
  · rintro ⟨x,rfl⟩
    have hsum : 0< |x-B| + |x-A| := by
      by_cases hx : x=A
      · rw [hx,sub_self,abs_zero,add_zero]
        exact abs_pos.mpr (sub_ne_zero.mpr hAB)
      · exact add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr (sub_ne_zero.mpr hx))
    refine ⟨|x-B|,|x-A|,abs_nonneg _,abs_nonneg _,hsum,?_⟩
    intro z hz
    change z.re=x at hz
    change |x-B| * Real.sinh ((HalfPlaneLine.vertical A).pointDist z)=
      |x-A| * Real.sinh ((HalfPlaneLine.vertical B).pointDist z)
    rw [verticalLine_pointDist_sinh,verticalLine_pointDist_sinh,hz]
    ring


theorem circle_radial_square_eq (c r : ℝ) (hr : 0<r) (z : ℍ)
    (hz : z∈(HalfPlaneLine.circle c r hr).carrier) :
    z.re^2+z.im^2=2*c*z.re+(r^2-c^2) := by
  have he:=norm_sub_real_eq_radius_sq hz
  nlinarith only [he]

theorem HalfPlaneLine.quadratic_radial_vanish (N : HalfPlaneLine) (A B C : ℝ)
    (h : ∀z∈N.carrier,A*(z.re^2+z.im^2)^2+B*(z.re^2+z.im^2)+C=0) :
    (∃(r : ℝ) (hr : 0<r),N=HalfPlaneLine.circle 0 r hr) ∨ (A=0 ∧ B=0 ∧ C=0) := by
  cases N with
  | vertical d =>
    right
    have hp:=h (metricProbe d 1 (by norm_num)) rfl
    have hq:=h (metricProbe d 2 (by norm_num)) rfl
    have hw:=h (metricProbe d 3 (by norm_num)) rfl
    norm_num [metricProbe] at hp hq hw
    exact quadratic_three_roots_coefficients A B C (d^2+1) (d^2+4) (d^2+9)
      (by linarith) (by linarith) (by linarith) hp hq hw
  | circle c r hr =>
    by_cases hc : c=0
    · subst c
      exact Or.inl ⟨r,hr,rfl⟩
    · have hleft : |(c-r/2)-c|<r := by
        rw [show c-r/2-c= -(r/2) by ring,abs_neg,abs_of_pos (by positivity)]
        linarith
      have hright : |(c+r/2)-c|<r := by
        rw [show c+r/2-c=r/2 by ring,abs_of_pos (by positivity)]
        linarith
      obtain ⟨p,hp,hpx⟩:=circle_exists_point_real_part c r hr (c-r/2) hleft
      obtain ⟨q,hq,hqx⟩:=circle_exists_point_real_part c r hr c (by simpa using hr)
      obtain ⟨w,hw,hwx⟩:=circle_exists_point_real_part c r hr (c+r/2) hright
      have hpQ : p.re^2+p.im^2=c^2+r^2-c*r := by
        rw [hpx]
        have he:=circle_radial_square_eq c r hr p hp
        rw [hpx] at he
        nlinarith only [he]
      have hqQ : q.re^2+q.im^2=c^2+r^2 := by
        rw [hqx]
        have he:=circle_radial_square_eq c r hr q hq
        rw [hqx] at he
        nlinarith only [he]
      have hwQ : w.re^2+w.im^2=c^2+r^2+c*r := by
        rw [hwx]
        have he:=circle_radial_square_eq c r hr w hw
        rw [hwx] at he
        nlinarith only [he]
      have hcr : c*r≠0:=mul_ne_zero hc hr.ne'
      right
      apply quadratic_three_roots_coefficients A B C (c^2+r^2-c*r) (c^2+r^2) (c^2+r^2+c*r)
      · intro he
        exact hcr (by nlinarith only [he])
      · intro he
        exact hcr (by nlinarith only [he])
      · intro he
        exact hcr (by nlinarith only [he])
      · simpa only [hpQ] using h p hp
      · simpa only [hqQ] using h q hq
      · simpa only [hwQ] using h w hw

theorem HalfPlaneLine.IsDistanceRatioLine.realGLMap {L M N : HalfPlaneLine}
    (h : L.IsDistanceRatioLine M N) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).IsDistanceRatioLine (M.realGLMap g) (N.realGLMap g) := by
  obtain ⟨a,b,ha,hb,hsum,hN⟩:=h
  refine ⟨a,b,ha,hb,hsum,?_⟩
  intro z hz
  rw [N.realGLMap_carrier] at hz
  obtain ⟨w,hw,rfl⟩:=hz
  change a*Real.sinh ((L.realGLMap g).pointDist (g • w))=
    b*Real.sinh ((M.realGLMap g).pointDist (g • w))
  rw [L.pointDist_isometry_image (L.realGLMap g) (g • ·) (realGL_isometry g) (L.realGLMap_carrier g).symm,
    M.pointDist_isometry_image (M.realGLMap g) (g • ·) (realGL_isometry g) (M.realGLMap_carrier g).symm]
  exact hN hw

theorem HalfPlaneLine.isDistanceRatioLine_realGLMap_iff (L M N : HalfPlaneLine) (g : GL (Fin 2) ℝ) :
    (L.realGLMap g).IsDistanceRatioLine (M.realGLMap g) (N.realGLMap g) ↔ L.IsDistanceRatioLine M N := by
  constructor
  · intro h
    simpa only [HalfPlaneLine.realGLMap_inv] using h.realGLMap g⁻¹
  · exact fun h=>h.realGLMap g

theorem DiscLine.isDistanceRatioLine_iff_halfPlane (L M N : DiscLine) :
    L.IsDistanceRatioLine M N ↔ L.toHalfPlane.IsDistanceRatioLine M.toHalfPlane N.toHalfPlane := by
  constructor
  · rintro ⟨a,b,ha,hb,hsum,hN⟩
    refine ⟨a,b,ha,hb,hsum,?_⟩
    intro z hz
    have hz' : halfPlaneToDisc z∈N.carrier:=(N.mem_carrier _).mpr
      (by simpa only [discToHalfPlane_halfPlaneToDisc] using hz)
    have he:=hN hz'
    change a*Real.sinh (L.pointDist (halfPlaneToDisc z))=
      b*Real.sinh (M.pointDist (halfPlaneToDisc z)) at he
    rw [L.pointDist_eq_halfPlane,M.pointDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc] at he
    exact he
  · rintro ⟨a,b,ha,hb,hsum,hN⟩
    refine ⟨a,b,ha,hb,hsum,?_⟩
    intro z hz
    change a*Real.sinh (L.pointDist z)=b*Real.sinh (M.pointDist z)
    rw [L.pointDist_eq_halfPlane,M.pointDist_eq_halfPlane]
    exact hN ((N.mem_carrier z).mp hz)


/-- Corrected P7 in the true concentric-circle normal form. -/
theorem concentric_isDistanceRatioLine_iff (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (N : HalfPlaneLine) :
    (HalfPlaneLine.circle 0 s hs).IsDistanceRatioLine (.circle 0 t ht) N ↔
      ∃(r : ℝ) (hr : 0<r),N=HalfPlaneLine.circle 0 r hr := by
  constructor
  · rintro ⟨a,b,ha,hb,hsum,hN⟩
    have hpoly : ∀z∈N.carrier,
        (a^2*t^2-b^2*s^2)*(z.re^2+z.im^2)^2+
        (-2*a^2*t^2*s^2+2*b^2*s^2*t^2)*(z.re^2+z.im^2)+
        (a^2*t^2*s^4-b^2*s^2*t^4)=0 := by
      intro z hz
      have he:=hN hz
      change a*Real.sinh ((HalfPlaneLine.circle 0 s hs).pointDist z)=
        b*Real.sinh ((HalfPlaneLine.circle 0 t ht).pointDist z) at he
      simp only [circleLine_pointDist_sinh,norm_sub_real_sq,sub_zero] at he
      rw [←mul_div_assoc,←mul_div_assoc,
        common_factor_div_eq_iff _ _ _ _ _ (by positivity),div_eq_div_iff hs.ne' ht.ne'] at he
      have he2:=congrArg (fun x : ℝ=>x^2) he
      simp only [mul_pow,sq_abs] at he2
      nlinarith only [he2]
    rcases N.quadratic_radial_vanish _ _ _ hpoly with he|he
    · exact he
    · have hane : a≠0 := by
        intro ha0
        have hbsq : b^2*s^2=0 := by rw [ha0] at he;nlinarith only [he.1]
        have hb0 : b=0:=sq_eq_zero_iff.mp ((mul_eq_zero.mp hbsq).resolve_right (pow_ne_zero 2 hs.ne'))
        rw [ha0,hb0] at hsum
        norm_num at hsum
      have hrel : b^2*s^2=a^2*t^2:=by linarith only [he.1]
      have hh : (a^2*t^2)*(t^2-s^2)=0:=by
        nlinarith only [he.2.1,congrArg (fun x : ℝ=>2*t^2*x) hrel]
      have hzero:=(mul_eq_zero.mp hh).resolve_left (mul_ne_zero (pow_ne_zero 2 hane) (pow_ne_zero 2 ht.ne'))
      have hst' : s=t:=by nlinarith only [hzero,hs,ht]
      exact False.elim (hst hst')
  · rintro ⟨u,hu,rfl⟩
    have hst2 : s^2≠t^2:=by intro h;apply hst;nlinarith only [h,hs,ht]
    have hsum : 0<s*|u^2-t^2| +t*|u^2-s^2| := by
      by_cases h : u^2=t^2
      · have hn : u^2≠s^2:=by intro hn;exact hst2 (hn.symm.trans h)
        exact add_pos_of_nonneg_of_pos (mul_nonneg hs.le (abs_nonneg _))
          (mul_pos ht (abs_pos.mpr (sub_ne_zero.mpr hn)))
      · exact add_pos_of_pos_of_nonneg (mul_pos hs (abs_pos.mpr (sub_ne_zero.mpr h)))
          (mul_nonneg ht.le (abs_nonneg _))
    refine ⟨s*|u^2-t^2|,t*|u^2-s^2|,mul_nonneg hs.le (abs_nonneg _),
      mul_nonneg ht.le (abs_nonneg _),hsum,?_⟩
    intro z hz
    have hzQ:=circle_radial_square_eq 0 u hu z hz
    norm_num at hzQ
    change (s*|u^2-t^2|)*Real.sinh ((HalfPlaneLine.circle 0 s hs).pointDist z)=
      (t*|u^2-s^2|)*Real.sinh ((HalfPlaneLine.circle 0 t ht).pointDist z)
    simp only [circleLine_pointDist_sinh,norm_sub_real_sq,sub_zero,hzQ]
    field_simp [hs.ne',ht.ne',z.im_ne_zero]

theorem orthogonal_imaginary_axis_iff_circle (N : HalfPlaneLine) :
    N.Orthogonal (HalfPlaneLine.vertical 0) ↔ ∃(r : ℝ) (hr : 0<r),N=HalfPlaneLine.circle 0 r hr := by
  rw [HalfPlaneLine.orthogonal_iff_coefficients]
  cases N with
  | vertical a =>
    constructor
    · exact False.elim
    · rintro ⟨r,hr,h⟩
      cases h
  | circle c r hr =>
    change c=0 ↔ _
    constructor
    · intro h
      subst c
      exact ⟨r,hr,rfl⟩
    · rintro ⟨u,hu,h⟩
      exact (HalfPlaneLine.circle.inj h).1

theorem concentric_isDistanceRatioLine_iff_orthogonal (s t : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s≠t) (N : HalfPlaneLine) :
    (HalfPlaneLine.circle 0 s hs).IsDistanceRatioLine (.circle 0 t ht) N ↔
      N.Orthogonal (HalfPlaneLine.vertical 0) := by
  rw [concentric_isDistanceRatioLine_iff s t hs ht hst N,orthogonal_imaginary_axis_iff_circle]


theorem axis_circle_ratio_squared (c r : ℝ) (hr : 0<r) (a b : ℝ) (z : ℍ)
    (h : a*Real.sinh ((HalfPlaneLine.vertical 0).pointDist z)=
      b*Real.sinh ((HalfPlaneLine.circle c r hr).pointDist z)) :
    (2*a*r*z.re)^2=b^2*(z.re^2+z.im^2-2*c*z.re+(c^2-r^2))^2 := by
  simp only [verticalLine_pointDist_sinh,circleLine_pointDist_sinh,norm_sub_real_sq,sub_zero] at h
  rw [←mul_div_assoc,←mul_div_assoc,div_eq_div_iff z.im_ne_zero (by positivity)] at h
  have he : (2*a*r*|z.re|)*z.im=(b*|(z.re-c)^2+z.im^2-r^2|)*z.im := by nlinarith only [h]
  have he':=mul_right_cancel₀ z.im_ne_zero he
  have hsq:=congrArg (fun x : ℝ=>x^2) he'
  simp only [mul_pow,sq_abs] at hsq
  nlinarith only [hsq]

/-- Corrected P7 for the true intersecting axis/circle normal form. -/
theorem axis_circle_isDistanceRatioLine_iff (c r : ℝ) (hr : 0<r) (p : ℍ)
    (hp0 : p∈(HalfPlaneLine.vertical 0).carrier) (hpC : p∈(HalfPlaneLine.circle c r hr).carrier)
    (N : HalfPlaneLine) :
    (HalfPlaneLine.vertical 0).IsDistanceRatioLine (.circle c r hr) N ↔ p∈N.carrier := by
  have hpRe : p.re=0:=hp0
  have hpCirc:=norm_sub_real_eq_radius_sq hpC
  rw [hpRe] at hpCirc
  constructor
  · rintro ⟨a,b,ha,hb,hsum,hN⟩
    have hsq (z : ℍ) (hz : z∈N.carrier) :
        (2*a*r*z.re)^2=b^2*(z.re^2+z.im^2-2*c*z.re+(c^2-r^2))^2 :=
      axis_circle_ratio_squared c r hr a b z (hN hz)
    cases N with
    | vertical d =>
      let K:=c^2-r^2-2*c*d
      have hpoly (y : ℝ) (hy : 0<y) :
          b^2*(d^2+y^2)^2+(2*b^2*K)*(d^2+y^2)+(b^2*K^2-4*a^2*r^2*d^2)=0 := by
        have he:=hsq (metricProbe d y hy) rfl
        change (2*a*r*d)^2=b^2*(d^2+y^2-2*c*d+(c^2-r^2))^2 at he
        dsimp only [K]
        nlinarith only [he]
      have h1:=hpoly 1 (by norm_num)
      have h2:=hpoly 2 (by norm_num)
      have h3:=hpoly 3 (by norm_num)
      norm_num at h1 h2 h3
      have hcoef:=quadratic_three_roots_coefficients (b^2) (2*b^2*K)
        (b^2*K^2-4*a^2*r^2*d^2) (d^2+1) (d^2+4) (d^2+9)
        (by linarith) (by linarith) (by linarith) h1 h2 h3
      have hb0 : b=0:=sq_eq_zero_iff.mp hcoef.1
      have haPos : 0<a:=by linarith only [hsum,hb0]
      have he : (4*a^2*r^2)*d^2=0:=by rw [hb0] at hcoef;nlinarith only [hcoef.2.2]
      have hd0 : d=0:=sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left (by positivity))
      change p.re=d
      rw [hpRe,hd0]
    | circle d u hu =>
      let K:=u^2-d^2+c^2-r^2
      have hpoly : ∀z∈(HalfPlaneLine.circle d u hu).carrier,
          (4*a^2*r^2-4*b^2*(d-c)^2)*z.re^2+(-4*b^2*(d-c)*K)*z.re-b^2*K^2=0 := by
        intro z hz
        have he:=hsq z hz
        rw [circle_radial_square_eq d u hu z hz] at he
        dsimp only [K]
        nlinarith only [he]
      have hcoef : 4*a^2*r^2-4*b^2*(d-c)^2=0 ∧ -4*b^2*(d-c)*K=0 ∧ -(b^2*K^2)=0 := by
        rcases (HalfPlaneLine.circle d u hu).quadratic_re_vanish _ _ _ hpoly with he|he
        · obtain ⟨v,he⟩:=he
          cases he
        · exact he
      have hbne : b≠0 := by
        intro hb0
        have haPos : 0<a:=by linarith only [hsum,hb0]
        have he : 4*a^2*r^2=0:=by rw [hb0] at hcoef;nlinarith only [hcoef.1]
        exact (by positivity : (4*a^2*r^2 : ℝ)≠0) he
      have hK : K=0 := by
        have he : b^2*K^2=0:=by linarith only [hcoef.2.2]
        exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hbne))
      apply norm_sub_real_eq_of_sq hu
      rw [hpRe]
      dsimp only [K] at hK
      nlinarith only [hpCirc,hK]
  · intro hpN
    cases N with
    | vertical d =>
      have hd : d=0:=by change p.re=d at hpN;linarith only [hpN,hpRe]
      rw [hd]
      exact (HalfPlaneLine.vertical 0).isDistanceRatioLine_self_left (.circle c r hr)
    | circle d u hu =>
      have hpCircN:=norm_sub_real_eq_radius_sq hpN
      rw [hpRe] at hpCircN
      have hK : u^2-d^2+c^2-r^2=0:=by nlinarith only [hpCirc,hpCircN]
      refine ⟨|d-c|,r,abs_nonneg _,hr.le,add_pos_of_nonneg_of_pos (abs_nonneg _) hr,?_⟩
      intro z hz
      have hzQ:=circle_radial_square_eq d u hu z hz
      have hT : (z.re-c)^2+z.im^2-r^2=2*(d-c)*z.re := by nlinarith only [hzQ,hK]
      change |d-c| * Real.sinh ((HalfPlaneLine.vertical 0).pointDist z)=
        r*Real.sinh ((HalfPlaneLine.circle c r hr).pointDist z)
      simp only [verticalLine_pointDist_sinh,circleLine_pointDist_sinh,norm_sub_real_sq,sub_zero]
      rw [hT,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      field_simp [hr.ne',z.im_ne_zero]


theorem HalfPlaneLine.realGLMap_mem_carrier (N : HalfPlaneLine) (g : GL (Fin 2) ℝ) (p : ℍ) :
    g • p∈(N.realGLMap g).carrier ↔ p∈N.carrier := by
  rw [N.realGLMap_carrier]
  constructor
  · rintro ⟨w,hw,he⟩
    exact (realGL_isometry g).injective he ▸ hw
  · exact mem_image_of_mem _

theorem HalfPlaneLine.realGLMap_mem_idealEndpoints (N : HalfPlaneLine) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (w : OnePoint ℂ) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) w∈(N.realGLMap g).idealEndpoints ↔ w∈N.idealEndpoints := by
  rw [N.idealEndpoints_realGL_image (N.realGLMap g) g hg (N.realGLMap_carrier g).symm]
  constructor
  · rintro ⟨a,ha,he⟩
    exact (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g)).injective he ▸ ha
  · exact mem_image_of_mem _

theorem infty_mem_idealEndpoints_iff_vertical (N : HalfPlaneLine) :
    (∞ : OnePoint ℂ)∈N.idealEndpoints ↔ ∃a : ℝ,N=HalfPlaneLine.vertical a := by
  constructor
  · exact N.eq_vertical_of_infty_ideal
  · rintro ⟨a,rfl⟩
    rw [vertical_idealEndpoints]
    exact mem_insert_of_mem _ (mem_singleton _)

/-- Corrected P7 for every actual parallel pair and its genuine common ideal end. -/
theorem HalfPlaneLine.parallel_isDistanceRatioLine_iff (L M : HalfPlaneLine) (hp : L.Parallel M)
    (w : OnePoint ℂ) (hwL : w∈L.idealEndpoints) (hwM : w∈M.idealEndpoints) (N : HalfPlaneLine) :
    L.IsDistanceRatioLine M N ↔ w∈N.idealEndpoints := by
  obtain ⟨g,a,b,hg,hab,hL,hM⟩:=L.exists_parallel_vertical_normalizer M hp
  have hL' : L.realGLMap g=.vertical a:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.vertical b:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have hwL':=(L.realGLMap_mem_idealEndpoints g hg w).mpr hwL
  have hwM':=(M.realGLMap_mem_idealEndpoints g hg w).mpr hwM
  rw [hL',vertical_idealEndpoints] at hwL'
  rw [hM',vertical_idealEndpoints] at hwM'
  simp only [mem_insert_iff,mem_singleton_iff] at hwL' hwM'
  have hw : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) w=∞ := by
    rcases hwL' with hwL'|hwL'
    · rcases hwM' with hwM'|hwM'
      · exfalso
        exact hab (Complex.ofReal_injective (OnePoint.coe_injective (hwL'.symm.trans hwM')))
      · exact hwM'
    · exact hwL'
  rw [←L.isDistanceRatioLine_realGLMap_iff M N g,hL',hM',vertical_isDistanceRatioLine_iff a b hab,
    ←infty_mem_idealEndpoints_iff_vertical,←hw]
  exact N.realGLMap_mem_idealEndpoints g hg w

/-- Corrected P7 for every actual intersecting pair and its genuine common point. -/
theorem HalfPlaneLine.intersecting_isDistanceRatioLine_iff (L M : HalfPlaneLine) (hi : L.Intersecting M)
    (p : ℍ) (hpL : p∈L.carrier) (hpM : p∈M.carrier) (N : HalfPlaneLine) :
    L.IsDistanceRatioLine M N ↔ p∈N.carrier := by
  obtain ⟨g,c,r,hr,_,_,hL,hM⟩:=L.exists_intersecting_axis_circle_normalizer M hi
  have hL' : L.realGLMap g=.vertical 0:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.circle c r hr:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have hpL' : g • p∈(HalfPlaneLine.vertical 0).carrier:=hL ▸ mem_image_of_mem _ hpL
  have hpM' : g • p∈(HalfPlaneLine.circle c r hr).carrier:=hM ▸ mem_image_of_mem _ hpM
  have he:=axis_circle_isDistanceRatioLine_iff c r hr (g • p) hpL' hpM' (N.realGLMap g)
  rw [←hL',←hM',L.isDistanceRatioLine_realGLMap_iff,N.realGLMap_mem_carrier] at he
  exact he

/-- Corrected P7 for every actual disjoint pair and its genuine common perpendicular. -/
theorem HalfPlaneLine.disjoint_isDistanceRatioLine_iff (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (C : HalfPlaneLine) (hLC : L.Orthogonal C) (hMC : M.Orthogonal C) (N : HalfPlaneLine) :
    L.IsDistanceRatioLine M N ↔ N.Orthogonal C := by
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩:=L.exists_concentric_normalizer M hd
  have hL' : L.realGLMap g=.circle 0 s hs:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.circle 0 t ht:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have hLC':=(L.orthogonal_realGL_image_iff C (L.realGLMap g) (C.realGLMap g) g
    (L.realGLMap_carrier g).symm (C.realGLMap_carrier g).symm).mpr hLC
  have hMC':=(M.orthogonal_realGL_image_iff C (M.realGLMap g) (C.realGLMap g) g
    (M.realGLMap_carrier g).symm (C.realGLMap_carrier g).symm).mpr hMC
  rw [hL'] at hLC'
  rw [hM'] at hMC'
  have hC:=concentric_commonOrthogonal_eq s t hs ht hst (C.realGLMap g) hLC' hMC'
  have he:=concentric_isDistanceRatioLine_iff_orthogonal s t hs ht hst (N.realGLMap g)
  rw [←hL',←hM',←hC,L.isDistanceRatioLine_realGLMap_iff,
    N.orthogonal_realGL_image_iff C (N.realGLMap g) (C.realGLMap g) g
      (N.realGLMap_carrier g).symm (C.realGLMap_carrier g).symm] at he
  exact he

theorem DiscLine.mem_idealEndpoints_iff_halfPlane (L : DiscLine) (w : OnePoint ℂ) :
    w∈L.idealEndpoints ↔ extendedCayley.symm w∈L.toHalfPlane.idealEndpoints := by
  rw [L.idealEndpoints_eq_cayley_image]
  constructor
  · rintro ⟨a,ha,he⟩
    have he':=congrArg extendedCayley.symm he
    simp only [extendedCayley.symm_apply_apply] at he'
    exact he' ▸ ha
  · intro hw
    exact ⟨extendedCayley.symm w,hw,extendedCayley.apply_symm_apply w⟩

theorem DiscLine.parallel_isDistanceRatioLine_iff (L M : DiscLine) (hp : L.Parallel M)
    (w : OnePoint ℂ) (hwL : w∈L.idealEndpoints) (hwM : w∈M.idealEndpoints) (N : DiscLine) :
    L.IsDistanceRatioLine M N ↔ w∈N.idealEndpoints := by
  rw [L.isDistanceRatioLine_iff_halfPlane M N,N.mem_idealEndpoints_iff_halfPlane w]
  exact L.toHalfPlane.parallel_isDistanceRatioLine_iff M.toHalfPlane (L.parallel_toHalfPlane M hp)
    (extendedCayley.symm w) ((L.mem_idealEndpoints_iff_halfPlane w).mp hwL)
    ((M.mem_idealEndpoints_iff_halfPlane w).mp hwM) N.toHalfPlane

theorem DiscLine.intersecting_isDistanceRatioLine_iff (L M : DiscLine) (hi : L.Intersecting M)
    (p : 𝔻) (hpL : p∈L.carrier) (hpM : p∈M.carrier) (N : DiscLine) :
    L.IsDistanceRatioLine M N ↔ p∈N.carrier := by
  rw [L.isDistanceRatioLine_iff_halfPlane M N,N.mem_carrier p]
  exact L.toHalfPlane.intersecting_isDistanceRatioLine_iff M.toHalfPlane (L.intersecting_toHalfPlane M hi)
    (discToHalfPlane p) ((L.mem_carrier p).mp hpL) ((M.mem_carrier p).mp hpM) N.toHalfPlane

theorem DiscLine.disjoint_isDistanceRatioLine_iff (L M : DiscLine) (hd : L.HDisjoint M)
    (C : DiscLine) (hLC : L.Orthogonal C) (hMC : M.Orthogonal C) (N : DiscLine) :
    L.IsDistanceRatioLine M N ↔ N.Orthogonal C := by
  rw [L.isDistanceRatioLine_iff_halfPlane M N,N.orthogonal_iff_halfPlane C]
  exact L.toHalfPlane.disjoint_isDistanceRatioLine_iff M.toHalfPlane ((L.hDisjoint_iff_halfPlane M).mp hd)
    C.toHalfPlane ((L.orthogonal_iff_halfPlane C).mp hLC) ((M.orthogonal_iff_halfPlane C).mp hMC) N.toHalfPlane

end
end LowDimensionalTopology.Geometry.Hyperbolic
