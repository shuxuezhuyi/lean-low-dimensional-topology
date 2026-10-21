/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularPolygonBoundary
public import Mathlib.Analysis.SpecificLimits.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian

def modularClosedShiftedPolygon (a : ℝ) : Set ℍ:=
  {z | a≤z.re ∧ z.re≤a+1 ∧ 1≤Complex.normSq (z:ℂ) ∧ 1≤Complex.normSq ((z:ℂ)-1)}

theorem modularClosedShiftedPolygon_isClosed (a : ℝ) : IsClosed (modularClosedShiftedPolygon a) := by
  apply IsClosed.inter (isClosed_le continuous_const UpperHalfPlane.continuous_re)
  apply IsClosed.inter (isClosed_le UpperHalfPlane.continuous_re continuous_const)
  exact (isClosed_le (f:=fun _ : ℍ=>(1:ℝ)) (g:=fun z=>Complex.normSq (z:ℂ)) continuous_const (by fun_prop)).inter (isClosed_le (f:=fun _ : ℍ=>(1:ℝ)) (g:=fun z=>Complex.normSq ((z:ℂ)-1)) continuous_const (by fun_prop))

theorem modularShiftedPolygon_isOpen (a : ℝ) : IsOpen (modularShiftedPolygon a) := by
  apply IsOpen.inter (isOpen_lt continuous_const UpperHalfPlane.continuous_re)
  apply IsOpen.inter (isOpen_lt UpperHalfPlane.continuous_re continuous_const)
  exact (isOpen_lt (f:=fun _ : ℍ=>(1:ℝ)) (g:=fun z=>Complex.normSq (z:ℂ)) continuous_const (by fun_prop)).inter (isOpen_lt (f:=fun _ : ℍ=>(1:ℝ)) (g:=fun z=>Complex.normSq ((z:ℂ)-1)) continuous_const (by fun_prop))

theorem modularShiftedPolygon_closure_subset (a : ℝ) :
    closure (modularShiftedPolygon a)⊆modularClosedShiftedPolygon a := by
  apply (modularClosedShiftedPolygon_isClosed a).closure_subset_iff.mpr
  exact fun _ h=>⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

theorem modularShiftedPolygon_nonempty (a : ℝ) : (modularShiftedPolygon a).Nonempty := by
  refine ⟨⟨⟨a+1/2,2⟩,by norm_num⟩,?_,?_,?_,?_⟩
  · change a<a+1/2
    linarith
  · change a+1/2<a+1
    linarith
  · change 1<(a+1/2)*(a+1/2)+2*2
    nlinarith [sq_nonneg (a+1/2)]
  · norm_num [Complex.normSq_apply]
    nlinarith [sq_nonneg (a+1/2-1)]

theorem modular_normSq_sub_one (z : ℍ) :
    Complex.normSq ((z:ℂ)-1)=Complex.normSq (z:ℂ)+1-2*z.re := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero]
  ring

theorem modular_closed_representative_shift (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z : ℍ) (hz : z∈ModularGroup.fd) :
    z∈modularClosedShiftedPolygon a ∨ ModularGroup.T•z∈modularClosedShiftedPolygon a := by
  have hx:=abs_le.mp hz.2
  by_cases hl : z.re<a
  · right
    have hc:=modular_T_coordinates z
    refine ⟨by linarith [hc.1],by linarith [hc.1],?_,?_⟩
    · rw [hc.2]
      linarith [hz.1]
    · rw [modular_normSq_sub_one,hc.2,hc.1]
      linarith [hz.1]
  · left
    refine ⟨le_of_not_gt hl,by linarith,hz.1,?_⟩
    rw [modular_normSq_sub_one]
    linarith [hz.1]

theorem modular_shifted_closed_orbit_cover (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) (z : ℍ) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℤ,A•z∈modularClosedShiftedPolygon a := by
  obtain ⟨A,hA⟩:=ModularGroup.exists_smul_mem_fd z
  rcases modular_closed_representative_shift a ha₁ ha₂ (A•z) hA with h|h
  · exact ⟨A,h⟩
  · exact ⟨ModularGroup.T*A,by simpa only [mul_smul] using h⟩


theorem modular_shift_raise_norm (x y D K r k : ℝ) (hK : |(x-k)*D|<y*K) (hr : 0<r) :
    (x+r*D-k)^2+(y+r*K)^2>(x-k)^2+y^2 := by
  have hp : 0<(x-k)*D+y*K:=by linarith [neg_abs_le ((x-k)*D)]
  nlinarith [mul_pos hr hp,sq_nonneg (r*D),sq_nonneg (r*K)]

def modularShiftSpeed (a : ℝ) (z : ℍ) : ℝ:=
  ((|z.re|+|z.re-1|)*|a+1/2-z.re|+1)/z.im

theorem modularShiftSpeed_pos (a : ℝ) (z : ℍ) : 0<modularShiftSpeed a z := by
  unfold modularShiftSpeed
  apply div_pos _ z.im_pos
  positivity

theorem modularShiftSpeed_bounds (a : ℝ) (z : ℍ) :
    |z.re*(a+1/2-z.re)|<z.im*modularShiftSpeed a z ∧
    |(z.re-1)*(a+1/2-z.re)|<z.im*modularShiftSpeed a z := by
  have he : z.im*modularShiftSpeed a z=(|z.re|+|z.re-1|)*|a+1/2-z.re|+1:=by
    unfold modularShiftSpeed
    field_simp [z.im_ne_zero]
  rw [he,abs_mul,abs_mul]
  constructor
  · nlinarith [mul_nonneg (abs_nonneg (z.re-1)) (abs_nonneg (a+1/2-z.re))]
  · nlinarith [mul_nonneg (abs_nonneg z.re) (abs_nonneg (a+1/2-z.re))]


def modularShiftApproach (a : ℝ) (z : ℍ) (n : ℕ) : ℍ:=
  let r : ℝ:=1/((n:ℝ)+1)
  ⟨⟨z.re+r*(a+1/2-z.re),z.im+r*modularShiftSpeed a z⟩,by
    have hr : 0<r:=by dsimp [r];positivity
    exact add_pos z.im_pos (mul_pos hr (modularShiftSpeed_pos a z))⟩

theorem modularShiftApproach_mem (a : ℝ) (z : ℍ) (hz : z∈modularClosedShiftedPolygon a) (n : ℕ) :
    modularShiftApproach a z n∈modularShiftedPolygon a := by
  let r : ℝ:=1/((n:ℝ)+1)
  have hr : 0<r:=by dsimp [r];positivity
  have hr₁ : r≤1:=by
    dsimp [r]
    exact (div_le_one (by positivity : 0<(n:ℝ)+1)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  change a<z.re+r*(a+1/2-z.re) ∧ z.re+r*(a+1/2-z.re)<a+1 ∧ _
  have hleft : 0≤(1-r)*(z.re-a):=mul_nonneg (sub_nonneg.mpr hr₁) (sub_nonneg.mpr hz.1)
  have hright : 0≤(1-r)*(a+1-z.re):=mul_nonneg (sub_nonneg.mpr hr₁) (sub_nonneg.mpr hz.2.1)
  refine ⟨by nlinarith,by nlinarith,?_,?_⟩
  · have hh:=modular_shift_raise_norm z.re z.im (a+1/2-z.re) (modularShiftSpeed a z) r 0
      (by simpa only [sub_zero] using (modularShiftSpeed_bounds a z).1) hr
    have hnorm:=hz.2.2.1
    rw [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] at hnorm
    change 1<(z.re+r*(a+1/2-z.re))*(z.re+r*(a+1/2-z.re))+
      (z.im+r*modularShiftSpeed a z)*(z.im+r*modularShiftSpeed a z)
    nlinarith
  · have hh:=modular_shift_raise_norm z.re z.im (a+1/2-z.re) (modularShiftSpeed a z) r 1
      (modularShiftSpeed_bounds a z).2 hr
    have hnorm:=hz.2.2.2
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero] at hnorm
    change 1<Complex.normSq ((modularShiftApproach a z n:ℂ)-1)
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
      sub_zero]
    change 1<(z.re+r*(a+1/2-z.re)-1)*(z.re+r*(a+1/2-z.re)-1)+
      (z.im+r*modularShiftSpeed a z)*(z.im+r*modularShiftSpeed a z)
    nlinarith

theorem modularShiftApproach_tendsto (a : ℝ) (z : ℍ) :
    Tendsto (modularShiftApproach a z) atTop (𝓝 z) := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.tendsto_nhds_iff]
  have hr:=tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  have hc : Continuous (fun r : ℝ=>(⟨z.re+r*(a+1/2-z.re),z.im+r*modularShiftSpeed a z⟩:ℂ)):=by
    have he : (fun r : ℝ=>(⟨z.re+r*(a+1/2-z.re),z.im+r*modularShiftSpeed a z⟩:ℂ))=
        (fun r : ℝ=>((z.re+r*(a+1/2-z.re):ℝ):ℂ)+((z.im+r*modularShiftSpeed a z:ℝ):ℂ)*Complex.I):=by
      funext r
      apply Complex.ext <;> simp
    rw [he]
    fun_prop
  have ht:=hc.continuousAt.tendsto.comp hr
  have he : (⟨z.re,z.im⟩:ℂ)=(z:ℂ):=by
    apply Complex.ext <;> simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  simpa only [Function.comp_def,modularShiftApproach,UpperHalfPlane.coe_mk,zero_mul,add_zero,he] using ht

theorem modularShiftedPolygon_closure (a : ℝ) :
    closure (modularShiftedPolygon a)=modularClosedShiftedPolygon a := by
  apply subset_antisymm (modularShiftedPolygon_closure_subset a)
  intro z hz
  exact mem_closure_of_tendsto (modularShiftApproach_tendsto a z)
    (Eventually.of_forall (modularShiftApproach_mem a z hz))

theorem modular_shifted_orbit_closure_cover (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) (z : ℍ) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℤ,A•z∈closure (modularShiftedPolygon a) := by
  rw [modularShiftedPolygon_closure]
  exact modular_shifted_closed_orbit_cover a ha₁ ha₂ z


theorem modular_fd_right_half_unique (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ)
    (hz : z∈ModularGroup.fd) (hAz : A•z∈ModularGroup.fd)
    (hN : 1<Complex.normSq (z:ℂ)) (hl : -(1/2)<z.re) (hAl : -(1/2)<(A•z).re) :
    A=1 ∨ A=-1 := by
  have hnrho : z≠UpperHalfPlane.ρ:=by
    intro he
    rw [he,Complex.normSq_eq_norm_sq,UpperHalfPlane.norm_ρ] at hN
    norm_num at hN
  have hnrho' : z≠(1:ℝ)+ᵥUpperHalfPlane.ρ:=by
    have hnorm : Complex.normSq (((1:ℝ)+ᵥUpperHalfPlane.ρ:ℍ):ℂ)=1:=by
      norm_num [UpperHalfPlane.ρ,UpperHalfPlane.coe_vadd,Complex.normSq_apply,←pow_two,div_pow]
    intro he
    rw [he,hnorm] at hN
    exact (lt_irrefl _ hN)
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz hAz with
    h|⟨_,hr⟩|⟨ht,hr⟩|⟨_,hn⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩
  · exact h
  · exact False.elim (by linarith)
  · rcases ht with rfl|rfl
    · rw [ModularGroup.re_T_inv_smul,hr] at hAl
      exact False.elim (by linarith)
    · rw [ModularGroup.SL_neg_smul,ModularGroup.re_T_inv_smul,hr] at hAl
      exact False.elim (by linarith)
  · rw [Complex.normSq_eq_norm_sq,hn,one_pow] at hN
    exact False.elim (lt_irrefl _ hN)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho he)
  · exact False.elim (hnrho he)
  · exact False.elim (hnrho he)


def modularShiftFold (z : ℍ) : Matrix.SpecialLinearGroup (Fin 2) ℤ:=
  if z.re≤1/2 then 1 else ModularGroup.T⁻¹

def modularShiftReduced (z : ℍ) : ℍ:=modularShiftFold z•z

theorem modularShiftReduced_spec (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z : ℍ) (hz : z∈modularShiftedPolygon a) :
    modularShiftReduced z∈ModularGroup.fd ∧
      1<Complex.normSq (modularShiftReduced z:ℂ) ∧ -(1/2)<(modularShiftReduced z).re ∧
      ((modularShiftFold z=1 ∧ a<(modularShiftReduced z).re) ∨
        (modularShiftFold z=ModularGroup.T⁻¹ ∧ (modularShiftReduced z).re<a)) := by
  by_cases hl : z.re≤1/2
  · simp only [modularShiftReduced,modularShiftFold,ite_eq_left hl,one_smul]
    exact ⟨⟨hz.2.2.1.le,abs_le.mpr ⟨by linarith [hz.1],hl⟩⟩,hz.2.2.1,
      by linarith [hz.1],Or.inl ⟨True.intro,hz.1⟩⟩
  · have hr : 1/2<z.re:=lt_of_not_ge hl
    have hD:=((modularShiftedPolygon_right a ha₂ z hr).mp hz).1
    simp only [modularShiftReduced,modularShiftFold,ite_eq_right hl]
    refine ⟨ModularGroup.fdo_subset_fd hD,hD.1,?_,Or.inr ⟨True.intro,?_⟩⟩
    · rw [ModularGroup.re_T_inv_smul]
      linarith
    · rw [ModularGroup.re_T_inv_smul]
      linarith [hz.2.1]

theorem modularShiftReduced_eq_fold (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z w : ℍ) (hz : z∈modularShiftedPolygon a) (hw : w∈modularShiftedPolygon a)
    (he : modularShiftReduced z=modularShiftReduced w) : modularShiftFold z=modularShiftFold w := by
  have hzspec:=(modularShiftReduced_spec a ha₁ ha₂ z hz).2.2.2
  have hwspec:=(modularShiftReduced_spec a ha₁ ha₂ w hw).2.2.2
  have hre:=congrArg UpperHalfPlane.re he
  rcases hzspec with ⟨hzf,hzr⟩|⟨hzf,hzr⟩ <;> rcases hwspec with ⟨hwf,hwr⟩|⟨hwf,hwr⟩
  · exact hzf.trans hwf.symm
  · exact False.elim (by linarith)
  · exact False.elim (by linarith)
  · exact hzf.trans hwf.symm

theorem modularShiftedPolygon_orbit_action_unique (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ)
    (hz : z∈modularShiftedPolygon a) (hAz : A•z∈modularShiftedPolygon a) :
    modularNativeHom A=1 := by
  let B:=modularShiftFold z
  let C:=modularShiftFold (A•z)
  let D:=C*A*B⁻¹
  have hact : D•modularShiftReduced z=modularShiftReduced (A•z):=by
    change (C*A*B⁻¹)•(B•z)=C•(A•z)
    rw [mul_smul,mul_smul,inv_smul_smul]
  have hzspec:=modularShiftReduced_spec a ha₁ ha₂ z hz
  have hAspec:=modularShiftReduced_spec a ha₁ ha₂ (A•z) hAz
  have hDid : D=1 ∨ D=-1:=modular_fd_right_half_unique D (modularShiftReduced z)
    hzspec.1 (hact.symm ▸ hAspec.1) hzspec.2.1 hzspec.2.2.1 (hact.symm ▸ hAspec.2.2.1)
  have heq : modularShiftReduced z=modularShiftReduced (A•z):=by
    rw [←hact]
    rcases hDid with h|h
    · rw [h,one_smul]
    · rw [h,ModularGroup.SL_neg_smul,one_smul]
  have hBC : B=C:=modularShiftReduced_eq_fold a ha₁ ha₂ z (A•z) hz hAz heq
  have hnat : modularNativeHom D=1:=by
    rcases hDid with h|h
    · rw [h,map_one]
    · rw [h,modularNativeHom_neg_one]
  have hc : (modularNativeHom B*modularNativeHom A)*(modularNativeHom B)⁻¹=1:=by
    simpa only [D,←hBC,map_mul,map_inv] using hnat
  have hh:=congrArg (fun x=>(modularNativeHom B)⁻¹*x*modularNativeHom B) hc
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using hh


theorem modular_re_gt_hConvex (a : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | a<z.re} := by
  let p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (a+1) 1 (by norm_num)
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (a-1) 1 (by norm_num)
  have he : {z : ℍ | a<z.re}={z : ℍ | dist z p<dist z q}:=by
    ext z
    simp only [Set.mem_ofPred_eq]
    have hh : Real.cosh (dist z p)<Real.cosh (dist z q) ↔ dist z p<dist z q:=by
      rw [Real.cosh_lt_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg]
    rw [←hh,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist']
    simp only [show p.re=a+1 from rfl,show p.im=1 from rfl,
      show q.re=a-1 from rfl,show q.im=1 from rfl,one_pow]
    change a<z.re ↔ ((z.re-(a+1))^2+z.im^2+1)/(2*z.im*1)<
      ((z.re-(a-1))^2+z.im^2+1)/(2*z.im*1)
    rw [div_lt_div_iff_of_pos_right (by positivity : 0<2*z.im*1)]
    constructor <;> intro h <;> nlinarith only [h]
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_closer_halfPlane_convex p q

theorem modularShiftedPolygon_hConvex
    (a : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedPolygon a) := by
  have hc (c : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | 1<Complex.normSq ((z:ℂ)-(c:ℂ))}:=by
    have he : {z : ℍ | 1<Complex.normSq ((z:ℂ)-(c:ℂ))}={z : ℍ | 1<‖(z:ℂ)-(c:ℂ)‖}:=by
      ext z
      simp only [Set.mem_ofPred_eq]
      rw [Complex.normSq_eq_norm_sq]
      constructor <;> intro h <;> nlinarith [norm_nonneg ((z:ℂ)-(c:ℂ))]
    rw [he]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_outside_circle c 1 (by norm_num)
  have hc₀ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | 1<Complex.normSq (z:ℂ)}:=by
    simpa only [Complex.ofReal_zero,sub_zero] using hc 0
  have hc₁ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | 1<Complex.normSq ((z:ℂ)-1)}:=by
    simpa only [Complex.ofReal_one] using hc 1
  intro z hz w hw u hu
  exact ⟨modular_re_gt_hConvex a z hz.1 w hw.1 hu,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex (a+1) z hz.2.1 w hw.2.1 hu,
    hc₀ z hz.2.2.1 w hw.2.2.1 hu,hc₁ z hz.2.2.2 w hw.2.2.2 hu⟩

theorem modularShiftedPolygon_isConnected (a : ℝ) : IsConnected (modularShiftedPolygon a) :=
  ⟨modularShiftedPolygon_nonempty a,(modularShiftedPolygon_hConvex a).isPreconnected⟩

theorem modularShiftedPolygon_orbit_unique (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z w : ℍ) (hz : z∈modularShiftedPolygon a) (hw : w∈modularShiftedPolygon a)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection modularNativeHom.range ℍ z=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection modularNativeHom.range ℍ w) : z=w := by
  obtain ⟨g,hgw⟩:=(Quotient.exact he : MulAction.orbitRel modularNativeHom.range ℍ z w)
  obtain ⟨A,hA⟩:=g.property
  have hAz : A•w=z:=by
    rw [←modularNativeHom_apply A w,hA]
    exact hgw
  have hn:=modularShiftedPolygon_orbit_action_unique a ha₁ ha₂ A w hw (hAz.symm ▸ hz)
  have hg : g=1:=Subtype.ext (hA.symm.trans hn)
  simpa only [hg,one_smul] using hgw.symm

theorem modularShiftedPolygon_closure_meetsEveryOrbit (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit modularNativeHom.range ℍ (closure (modularShiftedPolygon a)) := by
  intro z
  obtain ⟨A,hA⟩:=modular_shifted_orbit_closure_cover a ha₁ ha₂ z
  refine ⟨⟨modularNativeHom A,⟨A,rfl⟩⟩,?_⟩
  change modularNativeHom A z∈closure (modularShiftedPolygon a)
  rw [modularNativeHom_apply]
  exact hA


theorem modularShiftedPolygon_frontier_volume_zero (a : ℝ) : volume (frontier (modularShiftedPolygon a))=0 := by
  let L₁:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical a
  let L₂:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (a+1)
  let L₃:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num)
  let L₄:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 1 1 (by norm_num)
  have hsub : frontier (modularShiftedPolygon a)⊆L₁.carrier∪L₂.carrier∪L₃.carrier∪L₄.carrier:=by
    intro z hz
    rw [(modularShiftedPolygon_isOpen a).frontier_eq,modularShiftedPolygon_closure] at hz
    obtain ⟨hw,hnot⟩:=hz
    have hcircle (c : ℝ) (hc : Complex.normSq ((z:ℂ)-(c:ℂ))=1) :
        z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c 1 (by norm_num)).carrier:=by
      change ‖(z:ℂ)-(c:ℂ)‖=1
      rw [Complex.normSq_eq_norm_sq] at hc
      nlinarith [norm_nonneg ((z:ℂ)-(c:ℂ))]
    by_cases h₁ : z.re=a
    · exact Or.inl (Or.inl (Or.inl h₁))
    by_cases h₂ : z.re=a+1
    · exact Or.inl (Or.inl (Or.inr h₂))
    by_cases h₃ : Complex.normSq (z:ℂ)=1
    · exact Or.inl (Or.inr (hcircle 0 (by simpa only [Complex.ofReal_zero,sub_zero] using h₃)))
    by_cases h₄ : Complex.normSq ((z:ℂ)-1)=1
    · exact Or.inr (hcircle 1 (by simpa only [Complex.ofReal_one] using h₄))
    exact False.elim (hnot ⟨lt_of_le_of_ne hw.1 (Ne.symm h₁),lt_of_le_of_ne hw.2.1 h₂,
      lt_of_le_of_ne hw.2.2.1 (Ne.symm h₃),lt_of_le_of_ne hw.2.2.2 (Ne.symm h₄)⟩)
  exact measure_mono_null hsub
    (measure_union_null (measure_union_null (measure_union_null L₁.volume_zero L₂.volume_zero) L₃.volume_zero) L₄.volume_zero)

/-- The shifted modular polygon is a genuine fundamental domain for the actual full projective integral action. -/
theorem modularShiftedPolygon_fundamental (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain modularNativeHom.range ℍ volume (modularShiftedPolygon a) := by
  refine ⟨modularShiftedPolygon_isOpen a,modularShiftedPolygon_isConnected a,?_,
    modularShiftedPolygon_frontier_volume_zero a⟩
  exact exists_fundamentalSet_between _ _ subset_closure
    (modularShiftedPolygon_closure_meetsEveryOrbit a ha₁ ha₂)
    (fun z hz w hw he=>modularShiftedPolygon_orbit_unique a ha₁ ha₂ z w hz hw he)

end LowDimensionalTopology.Geometry.Fuchsian
