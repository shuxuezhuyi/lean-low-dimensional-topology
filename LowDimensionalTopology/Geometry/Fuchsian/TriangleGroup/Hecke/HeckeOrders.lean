/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeCorners
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CoordinateRotationOrders
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.EllipticReflectionPencils
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularPolygonBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def standardHeckeCornerSL (n : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ)))*modularInversionSL

theorem standardHeckeCornerSL_fixed (n : ℕ) (hn : 3≤n) :
    standardHeckeCornerSL n • standardHeckeCorner n hn=standardHeckeCorner n hn := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ)))*modularInversionSL) • _=_
  rw [mul_smul]
  exact standardHeckeCorner_fixed n hn

theorem standardHeckeCornerSL_denom (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom (standardHeckeCornerSL n) (standardHeckeCorner n hn)=
      (standardHeckeCorner n hn:ℂ) := by
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLDenom,standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

theorem standardHeckeCorner_exp (n : ℕ) (hn : 3≤n) :
    (standardHeckeCorner n hn:ℂ)=Complex.exp (((Real.pi/(n:ℝ):ℝ):ℂ)*Complex.I) := by
  apply Complex.ext
  · simp [Complex.exp_re,standardHeckeCorner,_root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealAngleVertex]
  · simp [Complex.exp_im,standardHeckeCorner,_root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealAngleVertex]

/-- The actual corner coordinate multiplier is a primitive inverse nth root. -/
theorem standardHeckeCorner_multiplier (n : ℕ) (hn : 3≤n) :
    conj (standardHeckeCorner n hn:ℂ)/(standardHeckeCorner n hn:ℂ)=
      ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ))⁻¹ := by
  rw [standardHeckeCorner_exp]
  change conj (Complex.exp (((Real.pi/(n:ℝ):ℝ):ℂ)*Complex.I))/
    Complex.exp (((Real.pi/(n:ℝ):ℝ):ℂ)*Complex.I)=
      (Complex.exp (((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n:ℝ):ℂ)*Complex.I))⁻¹
  rw [←Complex.exp_conj,←Complex.exp_sub,←Complex.exp_neg]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_natCast]
  ring

theorem standardHeckeCorner_multiplier_primitive (n : ℕ) (hn : 3≤n) :
    IsPrimitiveRoot (conj (standardHeckeCorner n hn:ℂ)/(standardHeckeCorner n hn:ℂ)) n := by
  rw [standardHeckeCorner_multiplier]
  have h:= (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n (by omega)).map_of_injective
    (f:=Circle.coeHom) Circle.coe_injective
  exact h.inv

theorem fixed_center_coordinate_has_nonzero (v : ℍ) :
    ∃z : ℍ,((z:ℂ)-(v:ℂ))/((z:ℂ)-conj (v:ℂ))≠0 := by
  by_contra hall
  push Not at hall
  have he : UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 2 (by norm_num) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.fixed_center_coordinate_injective v ((hall UpperHalfPlane.I).trans (hall _).symm)
  have hi:=congrArg UpperHalfPlane.im he
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hi

/-- The source product has exact original native order n; this is derived from its
actual action on a faithful fixed-center coordinate and a genuine primitive root. -/
theorem standardHeckeCornerSL_order (n : ℕ) (hn : 3≤n) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n))=n := by
  let v:=standardHeckeCorner n hn
  let φ : ℍ→ℂ:=fun z=>((z:ℂ)-(v:ℂ))/((z:ℂ)-conj (v:ℂ))
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.orderOf_isometry_of_primitive_coordinate _ φ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fixed_center_coordinate_injective v)
    (fixed_center_coordinate_has_nonzero v)
    (conj (v:ℂ)/(v:ℂ)) n (by omega) (standardHeckeCorner_multiplier_primitive n hn)
  intro z
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fixed_center_cross_ratio (standardHeckeCornerSL n) v
    (standardHeckeCornerSL_fixed n hn) z
  rw [standardHeckeCornerSL_denom] at h
  exact h

theorem standardHeckeProduct_order (n : ℕ) (hn : 3≤n) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ))))*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)=n := by
  change orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _)=n
  rw [←map_mul]
  exact standardHeckeCornerSL_order n hn

theorem unitHeckeProduct_order (n : ℕ) (hn : 3≤n) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)*unitHeckeInversion n (by exact_mod_cast hn))=n := by
  let hN : (3:ℕ∞)≤n:=by exact_mod_cast hn
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL n hN)
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle n)))
  let S:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL
  have ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)=D*T*D⁻¹ := (unitHecke_translation n hN).symm
  have hg : unitHeckeInversion n hN=D*S*D⁻¹:=rfl
  rw [ht,hg,show D*T*D⁻¹*(D*S*D⁻¹)=D*(T*S)*D⁻¹ by group]
  have h:=(MulAut.conj D).orderOf_eq (T*S)
  change orderOf (D*(T*S)*D⁻¹)=orderOf (T*S) at h
  rw [h]
  simpa only [T,S,triangleOrderAngle_nat] using standardHeckeProduct_order n hn

theorem modularInversionSL_order_two : orderOf
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)=2 := by
  have h:=modular_I_fixed_order_two
  rw [modularNativeHom_S_eq] at h
  apply (orderOf_eq_iff (by decide : 0<(2:ℕ))).mpr
  refine ⟨h.2.2,?_⟩
  intro m hm hpos
  have he : m=1:=by omega
  simpa only [he,pow_one] using h.2.1

theorem unitHeckeInversion_order_two (q : ℕ∞) (hq : 3≤q) :
    orderOf (unitHeckeInversion q hq)=2 := by
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)
  have h:=(MulAut.conj D).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)
  change orderOf (unitHeckeInversion q hq)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL) at h
  exact h.trans modularInversionSL_order_two

theorem translationInversion_projective_ne_one (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*modularInversionSL)≠1 := by
  intro h
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*modularInversionSL)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (1:Matrix.SpecialLinearGroup (Fin 2) ℝ) := by simpa only [map_one] using h
  rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign _ _).mp he with hA|hA
  all_goals
    have hc:=congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) ℝ=>B 1 0) hA
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_neg,Matrix.mul_apply,Fin.sum_univ_two] at hc

theorem standardHeckeCornerSL_elliptic (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n)) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_of_fixed _ (translationInversion_projective_ne_one _)
    _ (standardHeckeCornerSL_fixed n hn)

/-- The infinite second order is a genuine parabolic corner, rather than an elliptic element. -/
theorem infiniteHeckeProduct_parabolic :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 2*modularInversionSL)) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff _ (translationInversion_projective_ne_one 2)).mpr
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.trace_fin_two,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

end LowDimensionalTopology.Geometry.Fuchsian
