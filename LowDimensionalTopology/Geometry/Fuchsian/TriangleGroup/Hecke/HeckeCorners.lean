/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeUnitNormalization
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

theorem translation_inversion_fixed_unit (z : ℍ) (hz : ‖(z:ℂ)‖=1) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*z.re))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL) z=z := by
  apply UpperHalfPlane.ext
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*z.re) • (modularInversionSL • z) : ℍ):ℂ)=(z:ℂ)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,modularInversionSL_action_coe]
  have hnorm : conj (z:ℂ)*(z:ℂ)=1 := by rw [Complex.conj_mul',hz];norm_num
  have hre : ((2*z.re:ℝ):ℂ)=(z:ℂ)+conj (z:ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re,Complex.add_re,Complex.conj_re]
      change 2*(z:ℂ).re=(z:ℂ).re+(z:ℂ).re
      ring
    · simp only [Complex.ofReal_im,Complex.add_im,Complex.conj_im]
      ring
  rw [hre]
  field_simp [z.ne_zero]
  linear_combination hnorm

theorem finiteHeckeAngle_mem (n : ℕ) (hn : 3≤n) : Real.pi/(n:ℝ)∈Ioo (0:ℝ) Real.pi := by
  have hnpos : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  exact ⟨div_pos Real.pi_pos hnpos,
    div_lt_self Real.pi_pos (by exact_mod_cast (show 1<n by omega))⟩

def standardHeckeCorner (n : ℕ) (hn : 3≤n) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealAngleVertex (Real.pi/(n:ℝ)) (finiteHeckeAngle_mem n hn)

def unitHeckeCorner (n : ℕ) (hn : 3≤n) : ℍ :=
  unitHeckeDilationSL n (by exact_mod_cast hn) • standardHeckeCorner n hn

theorem standardHeckeCorner_norm (n : ℕ) (hn : 3≤n) :
    ‖(standardHeckeCorner n hn:ℂ)‖=1 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealAngleVertex_norm _ _

theorem standardHeckeCorner_fixed (n : ℕ) (hn : 3≤n) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(n:ℝ))))*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL) (standardHeckeCorner n hn)=standardHeckeCorner n hn := by
  have h:=translation_inversion_fixed_unit _ (standardHeckeCorner_norm n hn)
  have he : (standardHeckeCorner n hn).re=Real.cos (Real.pi/(n:ℝ)):=rfl
  rw [he] at h
  exact h

theorem unitHeckeCorner_re (n : ℕ) (hn : 3≤n) : (unitHeckeCorner n hn).re=1/2 := by
  rw [unitHeckeCorner, unitHeckeDilationSL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,
    triangleOrderAngle_nat]
  change 1/(2*Real.cos (Real.pi/(n:ℝ)))*Real.cos (Real.pi/(n:ℝ))=1/2
  have hc : Real.cos (Real.pi/(n:ℝ))≠0 := by
    have h:=hecke_width_pos (n:ℕ∞) (by exact_mod_cast hn)
    rw [triangleOrderAngle_nat] at h
    linarith
  field_simp

theorem unitHeckeCorner_im (n : ℕ) (hn : 3≤n) :
    (unitHeckeCorner n hn).im=(1/2)*Real.tan (Real.pi/(n:ℝ)) := by
  rw [unitHeckeCorner, unitHeckeDilationSL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im,
    triangleOrderAngle_nat]
  change 1/(2*Real.cos (Real.pi/(n:ℝ)))*Real.sin (Real.pi/(n:ℝ))=_
  rw [Real.tan_eq_sin_div_cos]
  ring

theorem unitHeckeCorner_fixed (n : ℕ) (hn : 3≤n) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)*unitHeckeInversion n (by exact_mod_cast hn))
      (unitHeckeCorner n hn)=unitHeckeCorner n hn := by
  let hN : (3:ℕ∞)≤n:=by exact_mod_cast hn
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL n hN)
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle n)))
  let S:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL
  have hfix : (T*S) (standardHeckeCorner n hn)=standardHeckeCorner n hn := by
    simpa only [T,S,triangleOrderAngle_nat] using standardHeckeCorner_fixed n hn
  have ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)=D*T*D⁻¹ := (unitHecke_translation n hN).symm
  have hg : unitHeckeInversion n hN=D*S*D⁻¹:=rfl
  rw [ht,hg,show D*T*D⁻¹*(D*S*D⁻¹)=D*(T*S)*D⁻¹ by group]
  change D ((T*S) (D⁻¹ (D (standardHeckeCorner n hn))))=D (standardHeckeCorner n hn)
  have hi : D⁻¹ (D (standardHeckeCorner n hn))=standardHeckeCorner n hn := by
    change D.symm (D (standardHeckeCorner n hn))=standardHeckeCorner n hn
    exact D.symm_apply_apply _
  rw [hi,hfix]

end LowDimensionalTopology.Geometry.Fuchsian
