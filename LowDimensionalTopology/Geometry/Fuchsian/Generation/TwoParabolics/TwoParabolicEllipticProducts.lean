/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicPositiveNormalForms
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPointHeights
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def twoParabolicCanonicalGroup (c : ℝ) : Subgroup Mobius.complexMobiusGroup :=
  Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)} : Set Mobius.complexMobiusGroup)

theorem twoParabolicCanonicalGroup_translation (c : ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈twoParabolicCanonicalGroup c := by
  have h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)∈twoParabolicCanonicalGroup c :=
    Subgroup.subset_closure (by simp)
  simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation] using h

theorem twoParabolicCanonicalGroup_model (c : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicModelSL c)∈twoParabolicCanonicalGroup c :=
  Subgroup.subset_closure (by simp)

theorem twoParabolicCanonicalGroup_preserves (c : ℝ) :
    ∀ f∈twoParabolicCanonicalGroup c,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have hreal : twoParabolicCanonicalGroup c≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases hf with rfl|rfl
    · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1,rfl⟩
    · exact ⟨twoParabolicModelSL c,rfl⟩
  intro f hf
  obtain ⟨A,rfl⟩ := hreal hf
  exact realSLMobius_image_openHalfPlane A

def twoParabolicCornerSL (c : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*twoParabolicModelSL (-c)

theorem twoParabolicCornerSL_mem (c : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)∈twoParabolicCanonicalGroup c := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*twoParabolicModelSL (-c))∈_
  rw [←twoParabolicModelSL_inverse,map_mul,map_inv]
  apply (twoParabolicCanonicalGroup c).mul_mem
  · exact Subgroup.subset_closure (by simp)
  · exact (twoParabolicCanonicalGroup c).inv_mem (twoParabolicCanonicalGroup_model c)

theorem twoParabolicCornerSL_trace (c : ℝ) : Matrix.trace (twoParabolicCornerSL c).val=2-c := by
  norm_num [twoParabolicCornerSL,twoParabolicModelSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.trace_fin_two,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem twoParabolicCornerSL_ne_one (c : ℝ) (hc : c≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)≠1 := by
  intro he
  have h1 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius 1 := by simpa only [map_one] using he
  rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign _ _).mp h1 with h|h
  all_goals
    have h0 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ=>A 1 0) h
    norm_num [twoParabolicCornerSL,twoParabolicModelSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] at h0
    exact hc (by linarith)

theorem twoParabolicCornerSL_elliptic (c : ℝ) (hc : 0<c) (h4 : c<4) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ (twoParabolicCornerSL_ne_one c hc.ne')).mpr
  rw [twoParabolicCornerSL_trace]
  nlinarith

def twoParabolicCorner (c : ℝ) (hc : 0<c) (h4 : c<4) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (1/2) (Real.sqrt ((4-c)/c)/2) (by
    exact div_pos (Real.sqrt_pos.mpr (div_pos (by linarith) hc)) (by norm_num))

theorem twoParabolicCorner_height_identity (c : ℝ) (hc : 0<c) (h4 : c<4) :
    c*(1+4*(twoParabolicCorner c hc h4).im^2)=4 := by
  have hs : (Real.sqrt ((4-c)/c))^2=(4-c)/c :=
    Real.sq_sqrt (by positivity)
  change c*(1+4*(Real.sqrt ((4-c)/c)/2)^2)=4
  have he : c*((4-c)/c)=4-c := by field_simp
  nlinarith [hs,he]

theorem twoParabolicCornerSL_fixed (c : ℝ) (hc : 0<c) (h4 : c<4) :
    twoParabolicCornerSL c • twoParabolicCorner c hc h4=twoParabolicCorner c hc h4 := by
  let z := twoParabolicCorner c hc h4
  have hz : z.re=1/2 := rfl
  have hzr : (twoParabolicCorner c hc h4).re=1/2 := rfl
  have hi := twoParabolicCorner_height_identity c hc h4
  have hden : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom (twoParabolicCornerSL c) z≠0 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom_ne_zero _ _
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  apply (div_eq_iff hden).mpr
  apply Complex.ext <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom,twoParabolicCornerSL,twoParabolicModelSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      Complex.mul_re,Complex.mul_im,hz]
  all_goals dsimp only [z]
  all_goals simp only [hzr]
  · nlinarith [hi]
  · ring

theorem twoParabolicCornerSL_finiteOrder (c : ℝ) (hc : 0<c) (h4 : c<4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c)) :
    IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)) :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elliptic_finiteOrder _ hd _ (twoParabolicCornerSL_mem c)
    (twoParabolicCornerSL_elliptic c hc h4)

theorem twoParabolicCorner_height_bound (c : ℝ) (hc : 0<c) (h4 : c<4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c))
    (hr : 3≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c))) :
    (twoParabolicCorner c hc h4).im≤
      Real.tan (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)))/2 := by
  apply mobius_elliptic_point_height (twoParabolicCanonicalGroup c) hd
    (twoParabolicCanonicalGroup_translation c) (twoParabolicCanonicalGroup_preserves c)
    _ (twoParabolicCornerSL_mem c) _ _ hr
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,twoParabolicCornerSL_fixed]

/-- The exact original fixed-center height and the universal height theorem bound
the positive model coefficient by the genuine elliptic transformation order. -/
theorem twoParabolic_parameter_order_lower (c : ℝ) (hc : 0<c) (h4 : c<4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c))
    (hr : 3≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c))) :
    4*(Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c))))^2≤c := by
  let θ := Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c))
  have hrR : (3:ℝ)≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)) := by exact_mod_cast hr
  have hθ := pi_div_acute_of_two_lt (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)))
    (by linarith only [hrR])
  have hcos : 0<Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have htan : Real.tan θ*Real.cos θ=Real.sin θ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have htrig : (1+(Real.tan θ)^2)*(Real.cos θ)^2=1 := by
    have he : (Real.tan θ)^2*(Real.cos θ)^2=(Real.sin θ)^2 := by
      rw [←mul_pow,htan]
    nlinarith [he,Real.sin_sq_add_cos_sq θ]
  have hb := twoParabolicCorner_height_bound c hc h4 hd hr
  have hy := (twoParabolicCorner c hc h4).im_pos
  have hsq : 4*(twoParabolicCorner c hc h4).im^2≤(Real.tan θ)^2 := by
    have he := mul_self_le_mul_self (by positivity : 0≤2*(twoParabolicCorner c hc h4).im)
      (show 2*(twoParabolicCorner c hc h4).im≤Real.tan θ by change _≤Real.tan θ/2 at hb;linarith)
    nlinarith [he]
  have hm := mul_le_mul_of_nonneg_left hsq hc.le
  have hh := twoParabolicCorner_height_identity c hc h4
  have hmain : 4≤c*(1+(Real.tan θ)^2) := by nlinarith [hm,hh]
  calc
    4*(Real.cos θ)^2≤(c*(1+(Real.tan θ)^2))*(Real.cos θ)^2 :=
      mul_le_mul_of_nonneg_right hmain (sq_nonneg _)
    _=c := by rw [mul_assoc,htrig,mul_one]

end LowDimensionalTopology.Geometry.Fuchsian
