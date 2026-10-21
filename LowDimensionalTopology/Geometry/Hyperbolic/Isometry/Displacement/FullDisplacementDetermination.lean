/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementDetermination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The genuine native isometry associated with either determinant sign. -/
def hGLIsometry (g : GL (Fin 2) ℝ) : ℍ ≃ᵢ ℍ where
  toEquiv:=MulAction.toPerm g
  isometry_toFun:=realGL_isometry g

/-- A constant vertical quadratic correction cannot occur between two real quadratic modulus functions. -/
theorem hQuadraticNormSq_vertical_shift_zero (c t b C T B k : ℝ)
    (h : ∀x y : ℝ,0<y→hQuadraticNormSq c t b x y=hQuadraticNormSq C T B x y+k*y^2) : k=0 := by
  have h0:=h 0 1 (by norm_num)
  have h1:=h 1 1 (by norm_num)
  have hm1:=h (-1) 1 (by norm_num)
  have h2:=h 2 1 (by norm_num)
  have hm2:=h (-2) 1 (by norm_num)
  have h02:=h 0 2 (by norm_num)
  dsimp [hQuadraticNormSq] at h0 h1 hm1 h2 hm2 h02
  have hcc : c^2=C^2 := by
    linear_combination (1/24:ℝ)*h2+(1/24:ℝ)*hm2-(1/6:ℝ)*h1-(1/6:ℝ)*hm1+(1/4:ℝ)*h0
  have hct : c*t=C*T := by
    linear_combination (1/24:ℝ)*h2-(1/24:ℝ)*hm2-(1/12:ℝ)*h1+(1/12:ℝ)*hm1
  have hminus : t^2-2*c*b=T^2-2*C*B := by
    linear_combination (1/2:ℝ)*h1+(1/2:ℝ)*hm1-h0-3*hcc
  have hplus : t^2+2*c*b=T^2+2*C*B+k := by
    linear_combination (1/3:ℝ)*h02-(1/3:ℝ)*h0-5*hcc
  have htt : t^2=T^2 := by
    by_cases hc : c=0
    · have hC : C=0:=by rw [hc] at hcc;nlinarith
      simpa only [hc,hC,zero_mul,mul_zero,sub_zero] using hminus
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcc with he | he
      · rw [←he] at hct
        rw [mul_left_cancel₀ hc hct]
      · have hC : C=-c:=by linarith
        rw [hC] at hct
        have ht : t=-T := by apply mul_left_cancel₀ hc;linear_combination hct
        rw [ht,neg_sq]
  linarith

/-- With determinant modulus one, the same genuine quadratic controls sinh for direct maps
and cosh for reflected maps. -/
theorem hGL_normalized_half_displacement_polynomial (g : GL (Fin 2) ℝ)
    (hdet : |g.val.det|=1) (z : ℍ) :
    (if 0<g.val.det then Real.sinh (dist z (g • z)/2) else Real.cosh (dist z (g • z)/2))=
      ‖(g 1 0 : ℂ)*(z:ℂ)^2+((g 1 1 : ℂ)-g 0 0)*z-g 0 1‖/(2*z.im) := by
  let D:ℂ:=(g 1 0 : ℂ)*z+g 1 1
  have hd : D≠0:=UpperHalfPlane.denom_ne_zero g z
  have hn : 0<‖D‖:=norm_pos_iff.mpr hd
  have him : (g • z).im=z.im/‖D‖^2 := by
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    change |g.val.det| *z.im/Complex.normSq D= _
    rw [hdet,one_mul,Complex.normSq_eq_norm_sq]
  have hmetric :
      (if 0<g.val.det then Real.sinh (dist z (g • z)/2) else Real.cosh (dist z (g • z)/2))=
        ‖(z:ℂ)-(((g 0 0 : ℂ)*z+g 0 1)/D)‖/(2*Real.sqrt (z.im*(g • z).im)) := by
    by_cases hg : 0<g.val.det
    · rw [ite_eq_left hg,halfPlane_sinh_half_dist_eq_norm_formula,UpperHalfPlane.coe_smul_of_det_pos hg]
      rfl
    · have hg' : g.val.det<0:=lt_of_le_of_ne (not_lt.mp hg) g.det_ne_zero
      rw [ite_eq_right hg,halfPlane_cosh_half_dist_eq_conjugate_norm_formula,realGL_coe_of_det_neg g
        hg',Complex.conj_conj]
  rw [hmetric,him]
  have hs : Real.sqrt (z.im*(z.im/‖D‖^2))=z.im/‖D‖ := by
    rw [show z.im*(z.im/‖D‖^2)=(z.im/‖D‖)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [hs]
  have he : (z:ℂ)-(((g 0 0 : ℂ)*z+g 0 1)/D)=
      ((g 1 0 : ℂ)*(z:ℂ)^2+((g 1 1 : ℂ)-g 0 0)*z-g 0 1)/D := by
    field_simp
    dsimp [D]
    ring
  rw [he,norm_div]
  field_simp [z.im_ne_zero,hn.ne']

/-- The reflected branch contributes exactly one to the squared half-sinh polynomial formula. -/
theorem hGL_normalized_quadraticNormSq (g : GL (Fin 2) ℝ) (hdet : |g.val.det|=1)
    (x y : ℝ) (hy : 0<y) :
    hQuadraticNormSq (g 1 0) (g 1 1-g 0 0) (g 0 1) x y=
      4*y^2*(Real.sinh (dist (metricProbe x y hy) (g • metricProbe x y hy)/2)^2+
        if 0<g.val.det then 0 else 1) := by
  let z:=metricProbe x y hy
  have hp:=hGL_normalized_half_displacement_polynomial g hdet z
  have hn : ‖(g 1 0 : ℂ)*(z:ℂ)^2+((g 1 1 : ℂ)-g 0 0)*z-g 0 1‖^2=
      hQuadraticNormSq (g 1 0) (g 1 1-g 0 0) (g 0 1) x y := by
    rw [←Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_apply,pow_two,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,z,metricProbe,hQuadraticNormSq]
    ring
  by_cases hg : 0<g.val.det
  · rw [ite_eq_left hg] at hp
    have hs:=congrArg (fun t : ℝ=>t^2) hp
    rw [div_pow,hn] at hs
    rw [ite_eq_left hg,add_zero]
    change _=4*y^2*Real.sinh (dist z (g • z)/2)^2
    change Real.sinh (dist z (g • z)/2)^2= _/((2*y)^2) at hs
    exact (eq_div_iff (by positivity : (2*y)^2≠0)).mp hs |>.symm.trans (by ring)
  · rw [ite_eq_right hg] at hp
    have hs:=congrArg (fun t : ℝ=>t^2) hp
    rw [div_pow,hn] at hs
    rw [ite_eq_right hg]
    change _=4*y^2*(Real.sinh (dist z (g • z)/2)^2+1)
    change Real.cosh (dist z (g • z)/2)^2= _/((2*y)^2) at hs
    have he:=(eq_div_iff (by positivity : (2*y)^2≠0)).mp hs
    rw [Real.cosh_sq] at he
    linear_combination -he

/-- Equal genuine displacement functions recover both the determinant sign and the quadratic triple up to one global sign. -/
theorem hGL_normalized_displacement_coefficients (A B : GL (Fin 2) ℝ)
    (hAd : |A.val.det|=1) (hBd : |B.val.det|=1)
    (h : hDisplacement (hGLIsometry A)=hDisplacement (hGLIsometry B)) :
    A.val.det=B.val.det ∧
      ((A 1 0=B 1 0 ∧ A 1 1-A 0 0=B 1 1-B 0 0 ∧ A 0 1=B 0 1) ∨
      (A 1 0= -B 1 0 ∧ A 1 1-A 0 0= -(B 1 1-B 0 0) ∧ A 0 1= -B 0 1)) := by
  let u:ℝ:=if 0<A.val.det then 0 else 1
  let v:ℝ:=if 0<B.val.det then 0 else 1
  have hshift (x y : ℝ) (hy : 0<y) :
      hQuadraticNormSq (A 1 0) (A 1 1-A 0 0) (A 0 1) x y=
        hQuadraticNormSq (B 1 0) (B 1 1-B 0 0) (B 0 1) x y+(4*(u-v))*y^2 := by
    rw [hGL_normalized_quadraticNormSq A hAd x y hy,hGL_normalized_quadraticNormSq B hBd x y hy]
    have he:=congrFun h (metricProbe x y hy)
    change dist (metricProbe x y hy) (A • metricProbe x y hy)=
      dist (metricProbe x y hy) (B • metricProbe x y hy) at he
    rw [he]
    change 4*y^2*(_+u)=4*y^2*(_+v)+(4*(u-v))*y^2
    ring
  have hk:=hQuadraticNormSq_vertical_shift_zero _ _ _ _ _ _ _ hshift
  have huv : u=v := by linarith
  have hdet : A.val.det=B.val.det := by
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp hAd with ha | ha
    all_goals rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp hBd with hb | hb
    · exact ha.trans hb.symm
    · exfalso
      simp [u,v,ha,hb] at huv
    · exfalso
      simp [u,v,ha,hb] at huv
    · exact ha.trans hb.symm
  refine ⟨hdet,hQuadraticNormSq_sign _ _ _ _ _ _ ?_⟩
  intro x y hy
  simpa only [hk,zero_mul,add_zero] using hshift x y hy

/-- The harmless sign of any native real matrix representative does not change its actual isometry. -/
theorem hGLIsometry_neg (g : GL (Fin 2) ℝ) : hGLIsometry (-g)=hGLIsometry g := by
  apply IsometryEquiv.ext
  intro z
  exact UpperHalfPlane.neg_smul g z

/-- A native real inverse matrix gives exactly the inverse actual isometry. -/
theorem hGLIsometry_inverse (g : GL (Fin 2) ℝ) : hGLIsometry g⁻¹=(hGLIsometry g).symm := by
  apply IsometryEquiv.ext
  intro z
  apply (hGLIsometry g).injective
  rw [(hGLIsometry g).apply_symm_apply]
  change g • (g⁻¹ • z)=z
  exact smul_inv_smul g z

/-- Equal normalized centered triples recover the actual full real isometry up to inversion. -/
theorem hGL_equal_centered_coefficients (A B : GL (Fin 2) ℝ)
    (hd : A.val.det=B.val.det) (hc : A 1 0=B 1 0)
    (ht : A 1 1-A 0 0=B 1 1-B 0 0) (hb : A 0 1=B 0 1) :
    hGLIsometry A=hGLIsometry B ∨ hGLIsometry A=(hGLIsometry B).symm := by
  rw [Matrix.det_fin_two,Matrix.det_fin_two,←hc,←hb] at hd
  have hsq : (A 0 0+A 1 1)^2=(B 0 0+B 1 1)^2 := by
    nlinarith [congrArg (fun x : ℝ=>x^2) ht]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hs | hs
  · left
    have h00 : A 0 0=B 0 0:=by linarith
    have h11 : A 1 1=B 1 1:=by linarith
    have he : A=B := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j
      · exact h00
      · exact hb
      · exact hc
      · exact h11
    exact congrArg hGLIsometry he
  · right
    have h00 : A 0 0= -B 1 1:=by linarith
    have h11 : A 1 1= -B 0 0:=by linarith
    let u:ℝˣ:=Units.mk0 (-B.val.det) (neg_ne_zero.mpr B.det_ne_zero)
    have hprod : A*B=Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (A.val*B.val) i j=(Matrix.scalar (Fin 2) (-B.val.det)) i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.scalar,Matrix.diagonal,
          Matrix.det_fin_two,h00,h11,hb,hc] <;> ring
    apply IsometryEquiv.ext
    intro z
    have hz:=congrArg (fun g : GL (Fin 2) ℝ=>g • (B⁻¹ • z)) hprod
    change A • z=B⁻¹ • z
    simpa only [mul_smul,smul_inv_smul,UpperHalfPlane.glScalar_smul] using hz

/-- Full determinant-modulus-one matrices are determined up to exactly inverse action by displacement. -/
theorem hGL_normalized_displacement_determines_inverse_pair (A B : GL (Fin 2) ℝ)
    (hAd : |A.val.det|=1) (hBd : |B.val.det|=1) :
    hDisplacement (hGLIsometry A)=hDisplacement (hGLIsometry B) ↔
      hGLIsometry A=hGLIsometry B ∨ hGLIsometry A=(hGLIsometry B).symm := by
  constructor
  · intro h
    obtain ⟨hd,hcoeff⟩:=hGL_normalized_displacement_coefficients A B hAd hBd h
    rcases hcoeff with ⟨hc,ht,hb⟩ | ⟨hc,ht,hb⟩
    · exact hGL_equal_centered_coefficients A B hd hc ht hb
    · have hdneg : (-B).val.det=B.val.det := by
        change Matrix.det (-B.val)= _
        simp [Matrix.det_fin_two]
      have hc' : A 1 0=(-B) 1 0:=hc
      have hb' : A 0 1=(-B) 0 1:=hb
      have ht' : A 1 1-A 0 0=(-B) 1 1-(-B) 0 0 := by
        change A 1 1-A 0 0= -B 1 1-(-B 0 0)
        linarith
      simpa only [hGLIsometry_neg] using
        hGL_equal_centered_coefficients A (-B) (hd.trans hdneg.symm) hc' ht' hb'
  · rintro (he | he)
    · rw [he]
    · rw [he]
      funext z
      exact hDisplacement_inverse _ z

/-- Every native isometry, including reflected maps, has an actual determinant-modulus-one real representative. -/
theorem exists_normalized_hGLIsometry (f : ℍ ≃ᵢ ℍ) :
    ∃g : GL (Fin 2) ℝ,|g.val.det|=1 ∧ hGLIsometry g=f := by
  obtain ⟨A,hA | hA⟩:=isometry_exists_sl2_or_reflected f.isometry
  · refine ⟨Matrix.SpecialLinearGroup.mapGL ℝ A,?_,?_⟩
    · change |A.val.det|=1
      rw [A.det_coe,abs_one]
    · apply IsometryEquiv.ext
      intro z
      exact (congrFun hA z).symm
  · refine ⟨Matrix.SpecialLinearGroup.mapGL ℝ A*UpperHalfPlane.J,?_,?_⟩
    · change |(A.val*UpperHalfPlane.J.val).det|=1
      rw [Matrix.det_mul,A.det_coe]
      norm_num [UpperHalfPlane.J,Matrix.det_fin_two]
    · apply IsometryEquiv.ext
      intro z
      change (Matrix.SpecialLinearGroup.mapGL ℝ A*UpperHalfPlane.J) • z=f z
      rw [mul_smul]
      exact (congrFun hA z).symm

/-- For every genuine hyperbolic-plane isometry, with both orientations admitted. -/
theorem hDisplacement_determines_inverse_pair (f g : ℍ ≃ᵢ ℍ) :
    hDisplacement f=hDisplacement g ↔ f=g ∨ f=g.symm := by
  obtain ⟨A,hAd,rfl⟩:=exists_normalized_hGLIsometry f
  obtain ⟨B,hBd,rfl⟩:=exists_normalized_hGLIsometry g
  exact hGL_normalized_displacement_determines_inverse_pair A B hAd hBd

end LowDimensionalTopology.Geometry.Hyperbolic
