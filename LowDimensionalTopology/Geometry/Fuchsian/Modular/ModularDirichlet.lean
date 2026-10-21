/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletEquivariance
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordRegions
public import Mathlib.NumberTheory.Modular
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Surfaces

theorem integral_pair_quadratic_lower (m n : ℤ) (h : m≠0 ∨ n≠0) :
    (1:ℝ)≤(m:ℝ)^2+(n:ℝ)^2-|(m:ℝ)*(n:ℝ)| := by
  have hs : 0<m^2+n^2:=by
    rcases h with h|h
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg n]
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg m]
  have ha : 0<m^2+n^2-|m*n|:=by
    have he : |m*n|=|m| * |n|:=abs_mul m n
    nlinarith [sq_nonneg (|m|-|n|),sq_abs m,sq_abs n]
  have hi : 1≤m^2+n^2-|m*n|:=ha
  have hiR : (1:ℝ)≤((m^2+n^2-|m*n|:ℤ):ℝ):=by exact_mod_cast hi
  simpa only [Int.cast_sub,Int.cast_add,Int.cast_pow,Int.cast_abs,Int.cast_mul] using hiR

theorem integral_pair_norm_lower (m n : ℤ) (h : m≠0 ∨ n≠0) :
    (1:ℝ)≤(m:ℝ)^2+(n:ℝ)^2 := by
  have hh:=integral_pair_quadratic_lower m n h
  linarith [abs_nonneg ((m:ℝ)*(n:ℝ))]

theorem strip_cross_term_bound (t x : ℝ) (hx : |x|<1/2) :
    2*t*x≤|t| := by
  have hh:=abs_mul t (2*x)
  have hx' : |2*x|≤1:=by rw [abs_mul];norm_num;linarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hmul:=mul_le_mul_of_nonneg_left hx' (abs_nonneg t)
  calc
    2*t*x ≤ |t*(2*x)|:=by simpa only [mul_assoc,mul_comm,mul_left_comm] using le_abs_self (t*(2*x))
    _ ≤ |t|:=by rw [hh];simpa only [mul_one] using hmul

theorem strip_cross_term_strict (t x : ℝ) (ht : t≠0) (hx : |x|<1/2) :
    2*t*x < |t| := by
  have hx' : |2*x|<1:=by rw [abs_mul];norm_num;linarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  calc
    2*t*x ≤ |t*(2*x)|:=by simpa only [mul_assoc,mul_comm,mul_left_comm] using le_abs_self (t*(2*x))
    _ < |t|:=by rw [abs_mul];simpa only [mul_one] using mul_lt_mul_of_pos_left hx' (abs_pos.mpr ht)


theorem modular_matrix_distance_quadratic (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (x R Y : ℝ) (hx : |x|<1/2) (hR : 1<R) (hY : 1<Y)
    (hA : A≠1 ∧ A≠-1) :
    0<(((A 0 0:ℝ)^2+(A 1 0:ℝ)^2*R-2*(A 0 0:ℝ)*(A 1 0:ℝ)*x-1)*Y^2+
      ((A 0 1:ℝ)^2+(A 1 1:ℝ)^2*R-2*(A 0 1:ℝ)*(A 1 1:ℝ)*x-R)) := by
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1:=by
    simpa only [Matrix.det_fin_two] using A.property
  have hcol₁ : A 0 0≠0 ∨ A 1 0≠0:=by by_contra h;push Not at h;rw [h.1,h.2] at hdet;norm_num at hdet
  have hcol₂ : A 0 1≠0 ∨ A 1 1≠0:=by by_contra h;push Not at h;rw [h.1,h.2] at hdet;norm_num at hdet
  have hrow₂ : A 1 0≠0 ∨ A 1 1≠0:=by by_contra h;push Not at h;rw [h.1,h.2] at hdet;norm_num at hdet
  have h₁:=integral_pair_quadratic_lower _ _ hcol₁
  have h₂:=integral_pair_quadratic_lower _ _ hcol₂
  have hr:=integral_pair_norm_lower _ _ hrow₂
  have hx₁:=strip_cross_term_bound ((A 0 0:ℝ)*(A 1 0:ℝ)) x hx
  have hx₂:=strip_cross_term_bound ((A 0 1:ℝ)*(A 1 1:ℝ)) x hx
  have hb : 0≤((A 0 0:ℝ)^2+(A 0 1:ℝ)^2-1)+
      ((A 1 0:ℝ)^2+(A 1 1:ℝ)^2-1)*R-
      2*((A 0 0:ℝ)*(A 1 0:ℝ)+(A 0 1:ℝ)*(A 1 1:ℝ))*x:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hR.le)]
  by_cases hc : A 1 0=0
  · have had : A 0 0=1 ∧ A 1 1=1 ∨ A 0 0=-1 ∧ A 1 1=-1:=by
      rw [hc,mul_zero,sub_zero] at hdet
      exact Int.eq_one_or_neg_one_of_mul_eq_one' hdet
    have hb₀ : A 0 1≠0:=by
      intro he
      rcases had with had|had
      · apply hA.1;ext i j;fin_cases i <;> fin_cases j <;> simp [had.1,had.2,hc,he]
      · apply hA.2;ext i j;fin_cases i <;> fin_cases j <;> simp [had.1,had.2,hc,he]
    have hd₀ : A 1 1≠0:=by rcases had with had|had <;> omega
    have hprod : (A 0 1:ℝ)*(A 1 1:ℝ)≠0:=mul_ne_zero (by exact_mod_cast hb₀) (by exact_mod_cast hd₀)
    have hxS:=strip_cross_term_strict _ x hprod hx
    have hds : (A 1 1:ℝ)^2=1:=by rcases had with had|had <;> simp [had.2]
    have has : (A 0 0:ℝ)^2=1:=by rcases had with had|had <;> simp [had.1]
    simp only [hc,Int.cast_zero,zero_pow (by norm_num : 2≠0),zero_mul,mul_zero,sub_zero,has,hds] at *
    nlinarith
  · have hcR : (A 1 0:ℝ)≠0:=by exact_mod_cast hc
    have hp : 0<(A 0 0:ℝ)^2+(A 1 0:ℝ)^2*R-2*(A 0 0:ℝ)*(A 1 0:ℝ)*x-1:=by
      nlinarith [mul_pos (sq_pos_of_ne_zero hcR) (sub_pos.mpr hR)]
    have hy2 : 0<Y^2-1:=by nlinarith
    have hh:=mul_pos hp hy2
    nlinarith


theorem realSL_cosh_dist_numerator (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z w : ℍ) :
    Real.cosh (dist z (A•w))=1+
      Complex.normSq ((z:ℂ)*((A 1 0:ℂ)*(w:ℂ)+A 1 1)-((A 0 0:ℂ)*(w:ℂ)+A 0 1))/(2*z.im*w.im) := by
  let D : ℂ:=(A 1 0:ℂ)*(w:ℂ)+A 1 1
  let N : ℂ:=(A 0 0:ℂ)*(w:ℂ)+A 0 1
  have hd : D≠0:=UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A) w
  have hdR : Complex.normSq D≠0:=fun h=>hd (Complex.normSq_eq_zero.mp h)
  rw [UpperHalfPlane.cosh_dist,realSL_im_action,Complex.dist_eq,←Complex.normSq_eq_norm_sq]
  have he : (z:ℂ)-(A•w:ℍ)=( (z:ℂ)*D-N)/D:=by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self_apply]
    change (z:ℂ)-N/D=((z:ℂ)*D-N)/D
    field_simp
  rw [he,Complex.normSq_div]
  change 1+ (Complex.normSq ((z:ℂ)*D-N)/Complex.normSq D)/(2*z.im*(w.im/Complex.normSq D))=_
  field_simp [hdR,z.im_ne_zero,w.im_ne_zero]
  dsimp [D,N]
  congr 2
  ring


def modularDirichletCenter (Y : ℝ) (hY : 0<Y) : ℍ:=⟨⟨0,Y⟩,hY⟩

theorem realSL_cosh_dist_vertical (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ)
    (Y : ℝ) (hY : 0<Y) :
    Real.cosh (dist z (A•modularDirichletCenter Y hY))=
      (((A 1 1*z.re-A 0 1)^2+(A 1 1*z.im)^2)+
        Y^2*((A 1 0*z.re-A 0 0)^2+(A 1 0*z.im)^2))/(2*z.im*Y) := by
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1:=by simpa only [Matrix.det_fin_two] using A.property
  rw [realSL_cosh_dist_numerator]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  simp only [modularDirichletCenter,UpperHalfPlane.re,UpperHalfPlane.im,zero_mul,mul_zero,sub_zero,zero_add,add_zero]
  field_simp [z.im_ne_zero,hY.ne']
  simp only [UpperHalfPlane.coe_im]
  linear_combination -2*z.im*Y*hdet


theorem modularDirichlet_distance_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ)
    (Y : ℝ) (hY : 0<Y) :
    dist z (modularDirichletCenter Y hY)<dist z (A•modularDirichletCenter Y hY) ↔
      0<((A 0 0)^2+(A 1 0)^2*(z.re^2+z.im^2)-2*A 0 0*A 1 0*z.re-1)*Y^2+
        ((A 0 1)^2+(A 1 1)^2*(z.re^2+z.im^2)-2*A 0 1*A 1 1*z.re-(z.re^2+z.im^2)) := by
  have hc : Real.cosh (dist z (modularDirichletCenter Y hY))<
      Real.cosh (dist z (A•modularDirichletCenter Y hY)) ↔
      dist z (modularDirichletCenter Y hY)<dist z (A•modularDirichletCenter Y hY):=by
    rw [Real.cosh_lt_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg]
  rw [←hc,UpperHalfPlane.cosh_dist',realSL_cosh_dist_vertical]
  simp only [show (modularDirichletCenter Y hY).re=0 from rfl,
    show (modularDirichletCenter Y hY).im=Y from rfl,sub_zero]
  rw [div_lt_div_iff_of_pos_right (by positivity : 0<2*z.im*Y)]
  constructor <;> intro h <;> nlinarith only [h]


/-- The genuine action of the full integral special-linear group by native isometries. -/
def modularNativeHom : Matrix.SpecialLinearGroup (Fin 2) ℤ→*(ℍ ≃ᵢ ℍ) where
  toFun A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A)
  map_one':=by
    apply IsometryEquiv.ext
    intro z
    change (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))•z=z
    rw [map_one,one_smul]
  map_mul' A B:=by
    apply IsometryEquiv.ext
    intro z
    change (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (A*B))•z=_
    rw [map_mul,mul_smul]
    rfl

theorem modularNativeHom_apply (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    modularNativeHom A z=A•z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A)•z : ℍ):ℂ)=_
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

theorem modularNativeHom_neg_one : modularNativeHom (-1)=1 := by
  apply IsometryEquiv.ext
  intro z
  rw [modularNativeHom_apply]
  change (-1:Matrix.SpecialLinearGroup (Fin 2) ℤ)•z=z
  simp

theorem modularDirichletCenter_mem_fdo (Y : ℝ) (hY : 1<Y) :
    modularDirichletCenter Y (by linarith)∈ModularGroup.fdo := by
  constructor
  · change 1<0*0+Y*Y
    nlinarith
  · change |(0:ℝ)|<1/2
    norm_num

theorem modularNativeHom_ne_one_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    modularNativeHom A≠1 ↔ A≠1 ∧ A≠-1 := by
  constructor
  · intro h
    constructor
    · intro he;apply h;rw [he,map_one]
    · intro he;apply h;rw [he,modularNativeHom_neg_one]
  · rintro ⟨ha,hn⟩ he
    let z:=modularDirichletCenter 2 (by norm_num)
    have hz : z∈ModularGroup.fdo:=modularDirichletCenter_mem_fdo 2 (by norm_num)
    have hAz : A•z=z:=by
      rw [←modularNativeHom_apply,he]
      rfl
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz (hAz.symm ▸ hz) with h|h
    · exact ha h
    · exact hn h


theorem modularDirichlet_mem_iff (Y : ℝ) (hY : 0<Y) (z : ℍ) :
    z∈nativeDirichletDomain modularNativeHom.range (modularDirichletCenter Y hY) ↔
    ∀A : Matrix.SpecialLinearGroup (Fin 2) ℤ,A≠1→A≠-1→
      dist z (modularDirichletCenter Y hY)<dist z (A•modularDirichletCenter Y hY) := by
  constructor
  · intro hz A ha hn
    have hne : (⟨modularNativeHom A,⟨A,rfl⟩⟩ : modularNativeHom.range)≠1:=by
      intro he
      exact (modularNativeHom_ne_one_iff A).mpr ⟨ha,hn⟩ (congrArg Subtype.val he)
    simpa only [modularNativeHom_apply] using hz ⟨modularNativeHom A,⟨A,rfl⟩⟩ hne
  · intro hz g hg
    obtain ⟨A,hA⟩:=g.property
    have hne : modularNativeHom A≠1:=by
      intro he
      apply hg
      exact Subtype.ext (hA.symm.trans he)
    have hn:=(modularNativeHom_ne_one_iff A).mp hne
    change dist z (modularDirichletCenter Y hY)<dist z (g.val (modularDirichletCenter Y hY))
    rw [←hA,modularNativeHom_apply]
    exact hz A hn.1 hn.2

theorem modular_fdo_subset_dirichlet (Y : ℝ) (hY : 1<Y) :
    ModularGroup.fdo⊆nativeDirichletDomain modularNativeHom.range (modularDirichletCenter Y (by linarith)) := by
  intro z hz
  apply (modularDirichlet_mem_iff Y _ z).mpr
  intro A ha hn
  let B:=Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A
  have hact : B•modularDirichletCenter Y (by linarith)=A•modularDirichletCenter Y (by linarith):=by
    exact modularNativeHom_apply A _
  rw [←hact]
  apply (modularDirichlet_distance_iff B z Y _).mpr
  have hR : 1<z.re^2+z.im^2:=by
    simpa only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,←pow_two] using hz.1
  have hq:=modular_matrix_distance_quadratic A z.re (z.re^2+z.im^2) Y hz.2 hR hY ⟨ha,hn⟩
  exact hq

theorem modular_dirichlet_subset_fdo (Y : ℝ) (hY : 1<Y) :
    nativeDirichletDomain modularNativeHom.range (modularDirichletCenter Y (by linarith))⊆ModularGroup.fdo := by
  intro z hz
  have hall:=(modularDirichlet_mem_iff Y _ z).mp hz
  have hT:=hall ModularGroup.T (by decide) (by decide)
  have hTi:=hall ModularGroup.T⁻¹ (by decide) (by decide)
  have hS:=hall ModularGroup.S (by decide) (by decide)
  have hconvert (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A)•modularDirichletCenter Y (by linarith)=
        A•modularDirichletCenter Y (by linarith):=modularNativeHom_apply A _
  rw [←hconvert ModularGroup.T,modularDirichlet_distance_iff] at hT
  rw [←hconvert ModularGroup.T⁻¹,modularDirichlet_distance_iff] at hTi
  rw [←hconvert ModularGroup.S,modularDirichlet_distance_iff] at hS
  norm_num [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply,
    ModularGroup.T,ModularGroup.S,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] at hT hTi hS
  constructor
  · change 1<z.re*z.re+z.im*z.im
    have hy2 : 0<Y^2-1:=by nlinarith
    nlinarith
  · exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- The actual modular Dirichlet domain is independent of the vertical center above i. -/
theorem modular_dirichlet_domain (Y : ℝ) (hY : 1<Y) :
    nativeDirichletDomain modularNativeHom.range (modularDirichletCenter Y (by linarith))=ModularGroup.fdo :=
  subset_antisymm (modular_dirichlet_subset_fdo Y hY) (modular_fdo_subset_dirichlet Y hY)

end LowDimensionalTopology.Geometry.Fuchsian
