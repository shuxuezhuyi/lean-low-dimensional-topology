/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPointHeights
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.HorocyclicCycleBounds
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual finite-order elliptic half-sine is bounded using the whole
root group of its own order, without assuming a least rotation. -/
theorem elliptic_order_half_sine_lower (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) (hq : 3≤orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.sin (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))≤Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2) := by
  let K:=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
  have hcard : Nat.card K=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    B):=Nat.card_zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
  let : Finite K:=Nat.finite_of_card_ne_zero (by rw [hcard];omega)
  let : IsCyclic K:=inferInstance
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈K:=Subgroup.mem_zpowers _
  obtain ⟨q,hmodel⟩:=primitive_finite_cyclic_full_root_model K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hmem hB.1
  have hN : 1<Nat.card K:=by rw [hcard];omega
  have htrace:=primitive_realSL_trace_bound_of_full_root_model K hN q hmodel B hmem hB.1
  rw [hcard] at htrace
  have hrot:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).2.2.2
  have hθ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB
  have hsin : 0≤Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2):=
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
  have hqR : (2:ℝ)<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by exact_mod_cast (by omega : 2<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
  have hα:=pi_div_acute_of_two_lt (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) hqR
  have hs0 : 0≤Real.sin (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)):=
    (Real.sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2,Real.pi_pos])).le
  apply (sq_le_sq₀ hs0 hsin).mp
  nlinarith only [htrace,hrot,Real.sin_sq_add_cos_sq
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2),
    Real.sin_sq_add_cos_sq (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))]

/-- The exact scalar optimization underlying the order-dependent source bound. -/
theorem elliptic_order_radial_scalar (s v S C M : ℝ) (hs : 0<s) (hv : 0<v)
    (hS : 0<S) (hC : 0<C) (hcircle : S^2+C^2=1) (hSs : S≤s)
    (hheight : 2*C*v≤S) (hM : 0≤M) (hM2 : M^2=s/(4*v*(s*v+1))) :
    C/Real.sqrt (1+2*C-C^2)≤M := by
  have hD : 0<1+2*C-C^2:=by nlinarith only [hcircle,hC,sq_nonneg S]
  have hden : 0<4*v*(s*v+1):=by positivity
  have ht : 0≤2*C*v:=by positivity
  have hsquare:=(sq_le_sq₀ ht hS.le).mpr hheight
  have hprod:=mul_le_mul_of_nonneg_left hsquare hs.le
  have hlin:=mul_le_mul_of_nonneg_left hSs (show 0≤2*C by positivity)
  have hheight':=mul_le_mul_of_nonneg_left hheight (show 0≤2*C by positivity)
  have hcirclemul:=congrArg (fun x : ℝ=>s*x) hcircle
  have hcross : C^2*(4*v*(s*v+1))≤s*(1+2*C-C^2):=by
    nlinarith only [hprod,hlin,hheight',hcirclemul]
  have hquot : C^2/(1+2*C-C^2)≤s/(4*v*(s*v+1)):=
    (div_le_div_iff₀ hD hden).mpr hcross
  apply (sq_le_sq₀ (div_nonneg hC.le (Real.sqrt_nonneg _)) hM).mp
  rw [div_pow,Real.sq_sqrt hD.le,hM2]
  exact hquot

/-- The order-dependent source inequality for the actual unit-parabolic pair,
using the original group's actual elliptic order and original center. -/
theorem unitTranslation_elliptic_order_displacementM_bound
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) (hq : 3≤orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))/
      Real.sqrt (1+2*Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))-
        Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))^2)≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let θ:=Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  let s:=Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)
  have hqR : (2:ℝ)<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by exact_mod_cast (by omega : 2<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
  have hθ:=pi_div_acute_of_two_lt (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) hqR
  have hS : 0<Real.sin θ:=Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  have hC : 0<Real.cos θ:=Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hrot:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB
  have hs : 0<s:=Real.sin_pos_of_pos_of_lt_pi hrot.1 hrot.2
  have hheight:=realSL_elliptic_center_height H hd hT hpres B hBH hB hq
  change u.im≤Real.tan θ/2 at hheight
  rw [Real.tan_eq_sin_div_cos,div_div] at hheight
  have hheight' : 2*Real.cos θ*u.im≤Real.sin θ:=by
    have h:=(le_div_iff₀ (mul_pos hC (by norm_num : (0:ℝ)<2))).mp hheight
    nlinarith only [h]
  have hM:=translation_elliptic_displacementM_square B hB 1 (by norm_num)
  dsimp only at hM
  norm_num only [one_pow,abs_one,mul_one] at hM
  exact elliptic_order_radial_scalar s u.im (Real.sin θ) (Real.cos θ)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)) hs u.im_pos hS hC
    (Real.sin_sq_add_cos_sq θ) (elliptic_order_half_sine_lower B hB hq) hheight'
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _) hM


end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Genuine sphere conjugation carries a preserved set to its actual image. -/
theorem orderBound_conjugate_preserves_image (f q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D
  : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hf : f.val '' D=D) : (q*f*q⁻¹).val '' (q.val '' D)=q.val '' D := by
  calc
    (q*f*q⁻¹).val '' (q.val '' D)=(q.val ∘ f.val) '' D:=by
      rw [Set.image_image]
      congr 1
      funext z
      change q•(f•(q⁻¹•(q•z)))=q•(f•z)
      rw [inv_smul_smul]
    _=q.val '' (f.val '' D):=(Set.image_image q.val f.val D).symm
    _=q.val '' D:=by rw [hf]

/-- Positive real dilation changes the literal translation width by its scale. -/
theorem orderBound_dilation_translation (k : ℝ) (hk : 0<k) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t)) := by
  apply mobius_ext_on_halfPlane
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
  apply congrArg (fun u : ℍ=>((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
  apply UpperHalfPlane.ext
  rw [mul_smul,mul_smul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  have hu : (k:ℂ)*(((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹•z:ℍ):ℂ)=(z:ℂ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe k hk]
    exact congrArg (fun u : ℍ=>(u:ℂ)) (smul_inv_smul
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk) z)
  rw [mul_add,hu]
  push_cast
  ring

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- Real conjugation preserves the actual entire upper half-plane. -/
theorem orderBound_real_conjugate_halfPlane (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*f*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have h:=orderBound_conjugate_preserves_image f (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    q) _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet hf
  rwa [realSLMobius_image_openHalfPlane] at h

/-- The sharp actual elliptic-center height estimate is invariant under
normalization of any nonzero original translation width. -/
theorem translation_width_elliptic_point_height (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (t : ℝ) (ht : t≠0)
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (z : ℍ)
    (hfix : f.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (hq : 3≤orderOf f) :
    z.im/|t|≤Real.tan (Real.pi/orderOf f)/2 := by
  let k:=1/|t|
  have hk : 0<k:=one_div_pos.mpr (abs_pos.mpr ht)
  let Q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk
  let p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate p H
  let : DiscreteTopology H:=hd
  have hKd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete p H
  have hKpres : ∀ g∈K,g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    rintro g ⟨u,hu,rfl⟩
    exact orderBound_real_conjugate_halfPlane u Q (hpres u hu)
  have hTk : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t))∈K:=by
    have hm : p*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)*p⁻¹∈K:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),hT,rfl⟩
    have hscale : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (Q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*Q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t)):=
      orderBound_dilation_translation k hk t
    rw [←hscale]
    simpa only [map_mul,map_inv] using hm
  have hKT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K:=by
    have hsign : k*t=1 ∨ k*t= -1:=by
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · right;dsimp [k];rw [abs_of_neg hneg];field_simp
      · left;dsimp [k];rw [abs_of_pos hpos];field_simp
    rcases hsign with h | h
    · rw [h,_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] at hTk
      exact hTk
    · rw [h] at hTk
      have hinv:=K.inv_mem hTk
      rw [←map_inv,hTranslationSL_neg_one_inverse,inv_inv,_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] at hinv
      exact hinv
  have hfm : p*f*p⁻¹∈K:=⟨f,hf,rfl⟩
  have horder : orderOf (p*f*p⁻¹)=orderOf f:=(MulAut.conj p).orderOf_eq f
  have hfix' : (p*f*p⁻¹).val (((Q•z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(((Q•z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action Q z]
    change p•(f•(p⁻¹•(p•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))))=p•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [inv_smul_smul]
    exact congrArg p.val hfix
  have hb:=mobius_elliptic_point_height K hKd hKT hKpres (p*f*p⁻¹) hfm (Q•z) hfix'
    (by rwa [horder])
  rw [horder] at hb
  have him : (Q•z).im=k*z.im:=by
    change (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk•z:ℍ):ℂ)).im=k*(z:ℂ).im
    have h:=congrArg Complex.im (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe k hk z)
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using h
  rw [him] at hb
  change (1/|t|)*z.im≤_ at hb
  have hfactor : (1/|t|)*z.im=z.im/|t|:=by ring
  rw [hfactor] at hb
  exact hb



/-- The actual order-dependent source bound for every nonzero native
parabolic translation width, without a primitive-elliptic assumption. -/
theorem translation_elliptic_order_displacementM_bound
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (t : ℝ) (ht : t≠0) (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) (hq : 3≤orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))/
      Real.sqrt (1+2*Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))-
        Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))^2)≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let θ:=Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  let s:=Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)
  let v:=u.im/|t|
  have htpos : 0 < |t|:=abs_pos.mpr ht
  have hv : 0<v:=div_pos u.im_pos htpos
  have hqR : (2:ℝ)<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by exact_mod_cast (by omega : 2<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
  have hθ:=pi_div_acute_of_two_lt (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) hqR
  have hS : 0<Real.sin θ:=Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  have hC : 0<Real.cos θ:=Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hrot:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB
  have hs : 0<s:=Real.sin_pos_of_pos_of_lt_pi hrot.1 hrot.2
  have hfix : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ _).mpr rfl]
  have hheight:=translation_width_elliptic_point_height H hd t ht hT hpres (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hBH u hfix hq
  change v≤Real.tan θ/2 at hheight
  rw [Real.tan_eq_sin_div_cos,div_div] at hheight
  have hheight' : 2*Real.cos θ*v≤Real.sin θ:=by
    have h:=(le_div_iff₀ (mul_pos hC (by norm_num : (0:ℝ)<2))).mp hheight
    nlinarith only [h]
  have hM:=translation_elliptic_displacementM_square B hB t ht
  dsimp only at hM
  have hM' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2=
      s/(4*v*(s*v+1)):=by
    rw [hM]
    change s*t^2/(4*u.im*(s*u.im+|t|))=s/(4*(u.im/|t|)*(s*(u.im/|t|)+1))
    rw [←sq_abs t]
    have hsum : s*u.im+|t|≠0:=ne_of_gt (by positivity)
    field_simp [htpos.ne',u.im_ne_zero,hsum]
  exact elliptic_order_radial_scalar s v (Real.sin θ) (Real.cos θ)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)) hs hv hS hC
    (Real.sin_sq_add_cos_sq θ) (elliptic_order_half_sine_lower B hB hq) hheight'
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _) hM'

/-- Every member of the actual group generated by real matrices preserves the
whole original half-plane, by an actual constructed real lift. -/
theorem realSL_generated_preserves_halfPlane (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∀f∈Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),
      f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have hle : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range:=
    (Subgroup.closure_le _).mpr (by
      intro f hf
      rcases mem_insert_iff.mp hf with h | h
      · subst f;exact ⟨A,rfl⟩
      · rw [mem_singleton_iff] at h
        subst f;exact ⟨B,rfl⟩)
  intro f hf
  obtain ⟨C,hC⟩:=hle hf
  rw [←hC]
  exact realSLMobius_image_openHalfPlane C

/--
order at least three: the true bound for arbitrary
original native parabolic/elliptic transformations and the exact original
elliptic order. Sharpness and the nontriangle improvement are separate.
-/
theorem parabolic_elliptic_order_displacementM_bound
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hq : 3≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))/
      Real.sqrt (1+2*Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))-
        Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))^2)≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨q,t,ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hprojA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hnorm with he | he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hprojB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹):=by
    simp only [map_mul,map_inv]
  let G:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  let K:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=by
    let : DiscreteTopology G:=hd
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
    change DiscreteTopology (G.map (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)).toMonoidHom) at h
    dsimp only [G] at h
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at h
    exact h
  have hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈K:=Subgroup.subset_closure (by simp)
  have hBK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)∈K:=Subgroup.subset_closure (by simp)
  have hBq : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)):=by
    have h:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hB
    simpa only [map_mul,map_inv] using h
  have horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹))=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    have h:=(MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
    change orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)⁻¹)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) at h
    simpa only [map_mul,map_inv] using h
  have hb:=translation_elliptic_order_displacementM_bound K hKd t ht hT
    (realSL_generated_preserves_halfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)
      (q*B*q⁻¹)) (q*B*q⁻¹) hBK hBq
    (by rwa [horder])
  rw [horder] at hb
  have hnormI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=by
    rcases hnorm with he | he
    · rw [he]
    · rw [he]
      apply IsometryEquiv.ext
      intro z
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_neg_smul _ z
  rw [←hnormI,hSLIsometry_conjugation A q,hSLIsometry_conjugation B
    q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_conjugation] at hb
  exact hb

end
end LowDimensionalTopology.Geometry.Fuchsian
