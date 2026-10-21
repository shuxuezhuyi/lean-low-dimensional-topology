/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Transversals

/-!
# Genuine lengths of alternate and complementary transversals
-/
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem concentric_lineDist_cosh (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Real.cosh ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht))=(s^2+t^2)/(2*s*t) := by
  rw [concentric_lineDist,Real.cosh_abs,Real.cosh_log (div_pos hs ht)]
  field_simp

theorem concentric_lineDist_sinh_half_sq (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Real.sinh ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)/2)^2=(s-t)^2/(4*s*t) := by
  let d:=(HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)
  have h1:=Real.cosh_two_mul (d/2)
  rw [show 2*(d/2)=d by ring] at h1
  have h2:=Real.cosh_sq_sub_sinh_sq (d/2)
  have h3:=concentric_lineDist_cosh s t hs ht
  change Real.cosh d=(s^2+t^2)/(2*s*t) at h3
  have h3':=(eq_div_iff (by positivity : 2*s*t≠0)).mp h3
  apply (eq_div_iff (by positivity : 4*s*t≠0)).mpr
  have he : 2*Real.sinh (d/2)^2=Real.cosh d-1:=by linarith only [h1,h2]
  nlinarith only [h3',congrArg (fun x : ℝ=>2*s*t*x) he]

theorem concentric_lineDist_cosh_half_sq (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Real.cosh ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)/2)^2=(s+t)^2/(4*s*t) := by
  rw [Real.cosh_sq,concentric_lineDist_sinh_half_sq s t hs ht]
  field_simp
  ring

/-- Normalize actual points on two concentric circles and one actual transversal circle. -/
theorem concentric_transversal_unit_coordinates (s t a u e : ℝ) (hs : 0<s) (ht : 0<t)
    (hu : 0<u) (ha : a≠0) (he : e^2=1) (hD : u^2-a^2=e*s*t)
    (p q : ℍ) (hpL : p∈(HalfPlaneLine.circle 0 s hs).carrier)
    (hpN : p∈(HalfPlaneLine.circle a u hu).carrier)
    (hqM : q∈(HalfPlaneLine.circle 0 t ht).carrier)
    (hqN : q∈(HalfPlaneLine.circle a u hu).carrier) :
    ∃x h : ℝ,0<h ∧ x^2+h^2=1 ∧ p.re=s*x ∧ p.im=s*h ∧
      q.re= -(e*t*x) ∧ q.im=t*h ∧ 2*a*x=s-e*t := by
  have hp2:=norm_sub_real_eq_radius_sq hpL
  have hpn2:=norm_sub_real_eq_radius_sq hpN
  have hq2:=norm_sub_real_eq_radius_sq hqM
  have hqn2:=norm_sub_real_eq_radius_sq hqN
  simp only [sub_zero] at hp2 hq2
  let x:=p.re/s
  let h:=p.im/s
  have h0 : 0<h:=div_pos p.im_pos hs
  have hpRe : p.re=s*x:=by dsimp [x];field_simp
  have hpIm : p.im=s*h:=by dsimp [h];field_simp
  have hunit : x^2+h^2=1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hs.ne')
    rw [hpRe,hpIm] at hp2
    nlinarith only [hp2]
  have hpx : 2*a*p.re=s*(s-e*t):=by nlinarith only [hp2,hpn2,hD]
  have hAx : 2*a*x=s-e*t := by
    apply mul_left_cancel₀ hs.ne'
    rw [hpRe] at hpx
    nlinarith only [hpx]
  have hqx : 2*a*q.re=t*(t-e*s):=by nlinarith only [hq2,hqn2,hD]
  have hqRe : q.re= -(e*t*x) := by
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ)≠0) ha)
    have hh:=congrArg (fun z : ℝ=>e*t*z) hAx
    have he':=congrArg (fun z : ℝ=>t^2*z) he
    nlinarith only [hqx,hh,he']
  have hqRe2 : q.re^2=t^2*x^2 := by rw [hqRe,neg_sq,mul_pow,mul_pow,he];ring
  have hqIm2 : q.im^2=(t*h)^2 := by
    nlinarith only [hq2,hqRe2,congrArg (fun z : ℝ=>t^2*z) hunit]
  have hqIm : q.im=t*h := by nlinarith only [hqIm2,q.im_pos,mul_pos ht h0]
  exact ⟨x,h,h0,hunit,hpRe,hpIm,hqRe,hqIm,hAx⟩

/-- Pure polynomial identities used only after genuine geometric normalization. -/
theorem transversal_unit_length_identities (s t a u e x h C S : ℝ)
    (hunit : x^2+h^2=1) (hAx : 2*a*x=s-e*t) (hD : u^2-a^2=e*s*t)
    (hUC : 2*u*C=|s+e*t|) (htrig : C^2+S^2=1) :
    a^2*((s+e*t)^2*x^2+(s-e*t)^2*h^2)=(s-e*t)^2*u^2 ∧ a^2*h^2=u^2*S^2 := by
  constructor
  · calc
      a^2*((s+e*t)^2*x^2+(s-e*t)^2*h^2)=
          (s-e*t)^2*a^2*(x^2+h^2)+e*s*t*(2*a*x)^2 := by ring
      _=(s-e*t)^2*a^2+e*s*t*(s-e*t)^2 := by rw [hunit,hAx,mul_one]
      _=(s-e*t)^2*u^2 := by nlinarith only [congrArg (fun z : ℝ=>(s-e*t)^2*z) hD]
  · have hh : 4*(a^2*h^2)=4*(u^2*S^2) := by
      calc
        4*(a^2*h^2)=4*a^2*(x^2+h^2)-(2*a*x)^2 := by ring
        _=4*a^2-(s-e*t)^2 := by rw [hunit,hAx,mul_one]
        _=4*u^2-(s+e*t)^2 := by nlinarith only [hD]
        _=4*u^2-(2*u*C)^2 := by rw [hUC,sq_abs]
        _=4*(u^2*S^2) := by nlinarith only [congrArg (fun z : ℝ=>4*u^2*z) htrig]
    linarith only [hh]


theorem alternate_point_norm_sub_sq (p q : ℍ) (s t x h : ℝ)
    (hpRe : p.re=s*x) (hpIm : p.im=s*h) (hqRe : q.re= -(t*x)) (hqIm : q.im=t*h) :
    ‖(p : ℂ)-(q : ℂ)‖^2=(s+t)^2*x^2+(s-t)^2*h^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  rw [hpRe,hpIm,hqRe,hqIm]
  ring

theorem complementary_point_norm_sub_conj_sq (p q : ℍ) (s t x h : ℝ)
    (hpRe : p.re=s*x) (hpIm : p.im=s*h) (hqRe : q.re=t*x) (hqIm : q.im=t*h) :
    ‖(p : ℂ)-star (q : ℂ)‖^2=(s-t)^2*x^2+(s+t)^2*h^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  rw [hpRe,hpIm,hqRe,hqIm]
  ring

theorem transversal_norm_square_sine_identity (a u R N h S : ℝ) (ha : a≠0)
    (hN : a^2*N=R^2*u^2) (hheight : a^2*h^2=u^2*S^2) : N*S^2=R^2*h^2 := by
  apply mul_left_cancel₀ (pow_ne_zero 2 ha)
  calc
    a^2*(N*S^2)=(a^2*N)*S^2 := by ring
    _=(R^2*u^2)*S^2 := by rw [hN]
    _=R^2*(a^2*h^2) := by rw [hheight];ring
    _=a^2*(R^2*h^2) := by ring

theorem concentric_alternate_segment_sinh_sq (s t a u θ : ℝ) (hs : 0<s) (ht : 0<t)
    (hu : 0<u) (ha : a≠0) (h0 : 0<θ) (hθ : θ<Real.pi/2)
    (hD : u^2-a^2=s*t) (hU : u=(s+t)/(2*Real.cos θ))
    (p q : ℍ) (hpL : p∈(HalfPlaneLine.circle 0 s hs).carrier)
    (hpN : p∈(HalfPlaneLine.circle a u hu).carrier)
    (hqM : q∈(HalfPlaneLine.circle 0 t ht).carrier)
    (hqN : q∈(HalfPlaneLine.circle a u hu).carrier) :
    Real.sinh (dist p q/2)^2*Real.sin θ^2=(s-t)^2/(4*s*t) := by
  obtain ⟨x,h,hh,hunit,hpRe,hpIm,hqRe,hqIm,hAx⟩:=
    concentric_transversal_unit_coordinates s t a u 1 hs ht hu ha (by norm_num)
      (by simpa only [one_mul] using hD) p q hpL hpN hqM hqN
  simp only [one_mul] at hqRe hAx
  have hc:=(acute_parameter_cos_bounds θ h0 hθ).1
  have hUC : 2*u*Real.cos θ=|s+1*t| := by
    rw [one_mul,abs_of_pos (add_pos hs ht)]
    have he:=(eq_div_iff (by positivity : 2*Real.cos θ≠0)).mp hU
    nlinarith only [he]
  have hi:=transversal_unit_length_identities s t a u 1 x h (Real.cos θ) (Real.sin θ)
    hunit (by simpa only [one_mul] using hAx) (by simpa only [one_mul] using hD) hUC (Real.cos_sq_add_sin_sq θ)
  simp only [one_mul] at hi
  have hnorm:=alternate_point_norm_sub_sq p q s t x h hpRe hpIm hqRe hqIm
  have hn : a^2*‖(p : ℂ)-(q : ℂ)‖^2=(s-t)^2*u^2:=by rw [hnorm];exact hi.1
  have he:=transversal_norm_square_sine_identity a u (s-t) (‖(p : ℂ)-(q : ℂ)‖^2) h (Real.sin θ) ha hn hi.2
  rw [UpperHalfPlane.sinh_half_dist,Complex.dist_eq,div_pow,mul_pow,
    Real.sq_sqrt (mul_pos p.im_pos q.im_pos).le,hpIm,hqIm]
  field_simp [hs.ne',ht.ne',hh.ne']
  nlinarith only [he]

theorem concentric_complementary_segment_cosh_sq (s t a u θ : ℝ) (hs : 0<s) (ht : 0<t)
    (hu : 0<u) (ha : a≠0) (h0 : 0<θ) (hθ : θ<Real.pi/2)
    (hD : u^2-a^2= -(s*t)) (hU : u=|s-t|/(2*Real.cos θ))
    (p q : ℍ) (hpL : p∈(HalfPlaneLine.circle 0 s hs).carrier)
    (hpN : p∈(HalfPlaneLine.circle a u hu).carrier)
    (hqM : q∈(HalfPlaneLine.circle 0 t ht).carrier)
    (hqN : q∈(HalfPlaneLine.circle a u hu).carrier) :
    Real.cosh (dist p q/2)^2*Real.sin θ^2=(s+t)^2/(4*s*t) := by
  obtain ⟨x,h,hh,hunit,hpRe,hpIm,hqRe,hqIm,hAx⟩:=
    concentric_transversal_unit_coordinates s t a u (-1) hs ht hu ha (by norm_num)
      (by nlinarith only [hD]) p q hpL hpN hqM hqN
  have hqRe' : q.re=t*x:=by nlinarith only [hqRe]
  have hAx' : 2*a*x=s-(-1)*t:=hAx
  have hc:=(acute_parameter_cos_bounds θ h0 hθ).1
  have hUC : 2*u*Real.cos θ=|s+(-1)*t| := by
    rw [neg_one_mul,←sub_eq_add_neg]
    have he:=(eq_div_iff (by positivity : 2*Real.cos θ≠0)).mp hU
    nlinarith only [he]
  have hi:=transversal_unit_length_identities s t a u (-1) x h (Real.cos θ) (Real.sin θ)
    hunit hAx' (by nlinarith only [hD]) hUC (Real.cos_sq_add_sin_sq θ)
  simp only [neg_one_mul,sub_neg_eq_add,←sub_eq_add_neg] at hi
  have hnorm:=complementary_point_norm_sub_conj_sq p q s t x h hpRe hpIm hqRe' hqIm
  have hn : a^2*‖(p : ℂ)-star (q : ℂ)‖^2=(s+t)^2*u^2:=by rw [hnorm];exact hi.1
  have he:=transversal_norm_square_sine_identity a u (s+t) (‖(p : ℂ)-star (q : ℂ)‖^2) h (Real.sin θ) ha hn hi.2
  change ‖(p : ℂ)-(starRingEnd ℂ) (q : ℂ)‖^2*Real.sin θ^2=(s+t)^2*h^2 at he
  rw [UpperHalfPlane.cosh_half_dist,Complex.dist_eq,div_pow,mul_pow,
    Real.sq_sqrt (mul_pos p.im_pos q.im_pos).le,hpIm,hqIm]
  field_simp [hs.ne',ht.ne',hh.ne']
  nlinarith only [he]

theorem concentric_alternate_segment_length (s t a u θ : ℝ) (hs : 0<s) (ht : 0<t)
    (hu : 0<u) (ha : a≠0) (h0 : 0<θ) (hθ : θ<Real.pi/2)
    (hD : u^2-a^2=s*t) (hU : u=(s+t)/(2*Real.cos θ))
    (p q : ℍ) (hpL : p∈(HalfPlaneLine.circle 0 s hs).carrier)
    (hpN : p∈(HalfPlaneLine.circle a u hu).carrier)
    (hqM : q∈(HalfPlaneLine.circle 0 t ht).carrier)
    (hqN : q∈(HalfPlaneLine.circle a u hu).carrier) :
    Real.sinh ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)/2)=
      Real.sinh (dist p q/2)*Real.sin θ := by
  have hleft : 0≤Real.sinh ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)/2) :=
    Real.sinh_nonneg_iff.mpr (div_nonneg ((HalfPlaneLine.circle 0 s hs).lineDist_nonneg _) (by norm_num))
  have hright : 0≤Real.sinh (dist p q/2)*Real.sin θ := mul_nonneg
    (Real.sinh_nonneg_iff.mpr (by positivity))
    (Real.sin_nonneg_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_pos]))
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow,concentric_lineDist_sinh_half_sq s t hs ht]
  exact (concentric_alternate_segment_sinh_sq s t a u θ hs ht hu ha h0 hθ hD hU p q hpL hpN hqM hqN).symm

theorem concentric_complementary_segment_length (s t a u θ : ℝ) (hs : 0<s) (ht : 0<t)
    (hu : 0<u) (ha : a≠0) (h0 : 0<θ) (hθ : θ<Real.pi/2)
    (hD : u^2-a^2= -(s*t)) (hU : u=|s-t|/(2*Real.cos θ))
    (p q : ℍ) (hpL : p∈(HalfPlaneLine.circle 0 s hs).carrier)
    (hpN : p∈(HalfPlaneLine.circle a u hu).carrier)
    (hqM : q∈(HalfPlaneLine.circle 0 t ht).carrier)
    (hqN : q∈(HalfPlaneLine.circle a u hu).carrier) :
    Real.cosh ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)/2)=
      Real.cosh (dist p q/2)*Real.sin θ := by
  have hleft:= (Real.cosh_pos ((HalfPlaneLine.circle 0 s hs).lineDist (.circle 0 t ht)/2)).le
  have hright : 0≤Real.cosh (dist p q/2)*Real.sin θ := mul_nonneg (Real.cosh_pos _).le
    (Real.sin_nonneg_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_pos]))
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow,concentric_lineDist_cosh_half_sq s t hs ht]
  exact (concentric_complementary_segment_cosh_sq s t a u θ hs ht hu ha h0 hθ hD hU p q hpL hpN hqM hqN).symm


theorem acute_circle_angle_center_ne_zero (s a u θ : ℝ) (hs : 0<s) (hu : 0<u)
    (h0 : 0<θ) (hθ : θ<Real.pi/2)
    (hC : |s^2+u^2-a^2|/(2*s*u)=Real.cos θ) : a≠0 := by
  have hc:=(acute_parameter_cos_bounds θ h0 hθ).2
  have hh : |s^2+u^2-a^2|<2*s*u:=
    (div_lt_one (by positivity : 0<2*s*u)).mp (hC.trans_lt hc)
  intro ha
  rw [ha,zero_pow (by norm_num : 2≠0),sub_zero,abs_of_pos (by positivity)] at hh
  nlinarith only [hh,sq_nonneg (s-u)]

/-- actual alternate-transversal segment and actual infimal line distance. -/
theorem HalfPlaneLine.alternate_transversal_length (L M N : HalfPlaneLine) (hd : L.HDisjoint M)
    (θ : ℝ) (hθ : θ<Real.pi/2) (hA : L.IsAlternateTransversal M θ N) (p q : ℍ)
    (hpL : p∈L.carrier) (hpN : p∈N.carrier) (hqM : q∈M.carrier) (hqN : q∈N.carrier) :
    Real.sinh (L.lineDist M/2)=Real.sinh (dist p q/2)*Real.sin θ := by
  have h0:=hA.1.1
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩:=L.exists_concentric_normalizer M hd
  have hL' : L.realGLMap g=.circle 0 s hs:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.circle 0 t ht:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have hA':=hA.realGLMap g
  rw [hL',hM'] at hA'
  obtain ⟨a,u,hu,hN,h1,h2⟩:=(concentric_transversal_iff_coefficients s t hs ht hst θ h0 hθ (N.realGLMap g)).mp hA'.1
  have hm:=(concentric_isAlternate_iff s t θ hs ht hst (N.realGLMap g) hA'.1).mp hA'
  rw [hN,circle_mem_concentricTransversalCentre_iff] at hm
  have hU : u=(s+t)/(2*Real.cos θ) := by
    rcases equal_circle_angle_coefficients s t a u (Real.cos θ) hs ht hst hu
      (acute_parameter_cos_bounds θ h0 hθ).1 h1 h2 with h | h
    · exact h.2
    · exfalso
      nlinarith only [hm,h.1,mul_pos hs ht]
  have hpL' : g • p∈(HalfPlaneLine.circle 0 s hs).carrier:=hL ▸ mem_image_of_mem _ hpL
  have hqM' : g • q∈(HalfPlaneLine.circle 0 t ht).carrier:=hM ▸ mem_image_of_mem _ hqM
  have hpN' : g • p∈(HalfPlaneLine.circle a u hu).carrier := by
    rw [←hN,N.realGLMap_carrier]
    exact mem_image_of_mem _ hpN
  have hqN' : g • q∈(HalfPlaneLine.circle a u hu).carrier := by
    rw [←hN,N.realGLMap_carrier]
    exact mem_image_of_mem _ hqN
  have he:=concentric_alternate_segment_length s t a u θ hs ht hu
    (acute_circle_angle_center_ne_zero s a u θ hs hu h0 hθ h1) h0 hθ hm hU
    (g • p) (g • q) hpL' hpN' hqM' hqN'
  rw [L.lineDist_isometry_image M _ _ (g • ·) (realGL_isometry g) hL hM,
    (realGL_isometry g).dist_eq] at he
  exact he

/-- actual complementary-transversal segment and actual infimal line distance. -/
theorem HalfPlaneLine.complementary_transversal_length (L M N : HalfPlaneLine) (hd : L.HDisjoint M)
    (θ : ℝ) (hθ : θ<Real.pi/2) (hA : L.IsComplementaryTransversal M θ N) (p q : ℍ)
    (hpL : p∈L.carrier) (hpN : p∈N.carrier) (hqM : q∈M.carrier) (hqN : q∈N.carrier) :
    Real.cosh (L.lineDist M/2)=Real.cosh (dist p q/2)*Real.sin θ := by
  have h0:=hA.1.1
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩:=L.exists_concentric_normalizer M hd
  have hL' : L.realGLMap g=.circle 0 s hs:=HalfPlaneLine.carrier_injective ((L.realGLMap_carrier g).trans hL)
  have hM' : M.realGLMap g=.circle 0 t ht:=HalfPlaneLine.carrier_injective ((M.realGLMap_carrier g).trans hM)
  have hA':=hA.realGLMap g
  rw [hL',hM'] at hA'
  obtain ⟨a,u,hu,hN,h1,h2⟩:=(concentric_transversal_iff_coefficients s t hs ht hst θ h0 hθ (N.realGLMap g)).mp hA'.1
  have hm:=(concentric_isComplementary_iff s t θ hs ht hst (N.realGLMap g) hA'.1).mp hA'
  rw [hN,circle_orthogonal_concentricBisector_iff] at hm
  have hU : u=|s-t|/(2*Real.cos θ) := by
    rcases equal_circle_angle_coefficients s t a u (Real.cos θ) hs ht hst hu
      (acute_parameter_cos_bounds θ h0 hθ).1 h1 h2 with h | h
    · exfalso
      nlinarith only [hm,h.1,mul_pos hs ht]
    · exact h.2
  have hpL' : g • p∈(HalfPlaneLine.circle 0 s hs).carrier:=hL ▸ mem_image_of_mem _ hpL
  have hqM' : g • q∈(HalfPlaneLine.circle 0 t ht).carrier:=hM ▸ mem_image_of_mem _ hqM
  have hpN' : g • p∈(HalfPlaneLine.circle a u hu).carrier := by
    rw [←hN,N.realGLMap_carrier]
    exact mem_image_of_mem _ hpN
  have hqN' : g • q∈(HalfPlaneLine.circle a u hu).carrier := by
    rw [←hN,N.realGLMap_carrier]
    exact mem_image_of_mem _ hqN
  have he:=concentric_complementary_segment_length s t a u θ hs ht hu
    (acute_circle_angle_center_ne_zero s a u θ hs hu h0 hθ h1) h0 hθ hm hU
    (g • p) (g • q) hpL' hpN' hqM' hqN'
  rw [L.lineDist_isometry_image M _ _ (g • ·) (realGL_isometry g) hL hM,
    (realGL_isometry g).dist_eq] at he
  exact he

theorem DiscLine.alternate_transversal_length (L M N : DiscLine) (hd : L.HDisjoint M)
    (θ : ℝ) (hθ : θ<Real.pi/2) (hA : L.IsAlternateTransversal M θ N) (p q : 𝔻)
    (hpL : p∈L.carrier) (hpN : p∈N.carrier) (hqM : q∈M.carrier) (hqN : q∈N.carrier) :
    Real.sinh (L.lineDist M/2)=Real.sinh (discPathDist p q/2)*Real.sin θ := by
  rw [L.lineDist_eq_halfPlane,discPathDist_eq_halfPlane]
  exact L.toHalfPlane.alternate_transversal_length M.toHalfPlane N.toHalfPlane
    ((L.hDisjoint_iff_halfPlane M).mp hd) θ hθ ((L.isAlternateTransversal_iff_halfPlane M N θ).mp hA)
    (discToHalfPlane p) (discToHalfPlane q) ((L.mem_carrier p).mp hpL) ((N.mem_carrier p).mp hpN)
    ((M.mem_carrier q).mp hqM) ((N.mem_carrier q).mp hqN)

theorem DiscLine.complementary_transversal_length (L M N : DiscLine) (hd : L.HDisjoint M)
    (θ : ℝ) (hθ : θ<Real.pi/2) (hA : L.IsComplementaryTransversal M θ N) (p q : 𝔻)
    (hpL : p∈L.carrier) (hpN : p∈N.carrier) (hqM : q∈M.carrier) (hqN : q∈N.carrier) :
    Real.cosh (L.lineDist M/2)=Real.cosh (discPathDist p q/2)*Real.sin θ := by
  rw [L.lineDist_eq_halfPlane,discPathDist_eq_halfPlane]
  exact L.toHalfPlane.complementary_transversal_length M.toHalfPlane N.toHalfPlane
    ((L.hDisjoint_iff_halfPlane M).mp hd) θ hθ ((L.isComplementaryTransversal_iff_halfPlane M N θ).mp hA)
    (discToHalfPlane p) (discToHalfPlane q) ((L.mem_carrier p).mp hpL) ((N.mem_carrier p).mp hpN)
    ((M.mem_carrier q).mp hqM) ((N.mem_carrier q).mp hqN)


/-- The source positive dilation genuinely preserves the actual imaginary axis. -/
theorem verticalDilationSL_axis_image (k : ℝ) (hk : 0<k) :
    let g:=Matrix.SpecialLinearGroup.mapGL ℝ (verticalDilationSL k hk)
    (g • · : ℍ→ℍ) '' (HalfPlaneLine.vertical 0).carrier=(HalfPlaneLine.vertical 0).carrier := by
  dsimp only
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ (verticalDilationSL k hk)
  change (g • · : ℍ→ℍ) '' (HalfPlaneLine.vertical 0).carrier=(HalfPlaneLine.vertical 0).carrier
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change (verticalDilationSL k hk • w).re=0
    rw [verticalDilationSL_re]
    change w.re=0 at hw
    rw [hw,mul_zero]
  · intro hz
    change z.re=0 at hz
    refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
    change (g⁻¹ • z).re=0
    have he:=verticalDilationSL_re k hk (g⁻¹ • z)
    change (g • (g⁻¹ • z)).re=k*(g⁻¹ • z).re at he
    rw [smul_inv_smul,hz] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hk.ne'

/-- The source dilation example uses its actual real Mobius isometry and actual angles.
The geodesic is genuinely transverse to the axis; coincidence has zero angle. -/
theorem positive_dilation_equal_angle_transversal (k : ℝ) (hk : 0<k) (L : HalfPlaneLine)
    (hL : L.Intersecting (HalfPlaneLine.vertical 0)) :
    let g:=Matrix.SpecialLinearGroup.mapGL ℝ (verticalDilationSL k hk)
    ∃θ : ℝ,L.IsThetaTransversal (L.realGLMap g) θ (HalfPlaneLine.vertical 0) := by
  dsimp only
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ (verticalDilationSL k hk)
  change ∃θ : ℝ,L.IsThetaTransversal (L.realGLMap g) θ (HalfPlaneLine.vertical 0)
  obtain ⟨p,hpL,hpC⟩:=hL.2.2
  let θ:=L.acuteAngle (HalfPlaneLine.vertical 0) p
  have h0 : 0<θ:=L.acuteAngle_pos _ p hpL hpC hL.1
  have hθ : θ≤Real.pi/2:=(L.acuteAngle_mem_Icc _ p).2
  have hC : (g • · : ℍ→ℍ) '' (HalfPlaneLine.vertical 0).carrier=(HalfPlaneLine.vertical 0).carrier:=
    verticalDilationSL_axis_image k hk
  have hpC' : g • p∈(HalfPlaneLine.vertical 0).carrier:=hC ▸ mem_image_of_mem _ hpC
  have hpL' : g • p∈(L.realGLMap g).carrier:=by
    rw [L.realGLMap_carrier]
    exact mem_image_of_mem _ hpL
  refine ⟨θ,h0,hθ,p,g • p,hpL,hpC,hpL',hpC',rfl,?_⟩
  exact L.acuteAngle_realGL_image (HalfPlaneLine.vertical 0) (L.realGLMap g) (HalfPlaneLine.vertical 0)
    g (L.realGLMap_carrier g).symm hC p hpL hpC

end
end LowDimensionalTopology.Geometry.Hyperbolic
