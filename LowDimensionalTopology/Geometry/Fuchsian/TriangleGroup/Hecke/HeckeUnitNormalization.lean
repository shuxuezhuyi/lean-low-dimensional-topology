/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeNormalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

theorem verticalDilationSL_inverse_coe (k : ℝ) (hk : 0<k) (z : ℍ) :
    (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹ • z : ℍ):ℂ)=(z:ℂ)/(k:ℂ) := by
  have h:=congrArg (fun w : ℍ=>(w:ℂ)) (smul_inv_smul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk) z)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe] at h
  apply (eq_div_iff (by exact_mod_cast hk.ne' : (k:ℂ)≠0)).mpr
  simpa only [mul_comm] using h

theorem dilation_conjugate_translation_native (k : ℝ) (hk : 0<k) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t)) := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t •
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)⁻¹ • z)) : ℍ):ℂ)=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k*t) • z : ℍ):ℂ)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe, verticalDilationSL_inverse_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  push_cast
  field_simp [show (k:ℂ)≠0 by exact_mod_cast hk.ne']

theorem hecke_width_pos (q : ℕ∞) (hq : 3≤q) : 0<2*Real.cos (triangleOrderAngle q) := by
  have h:=hecke_order_angle_bounds q hq
  have hθ : triangleOrderAngle q∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith only [h.1,h.2,Real.pi_pos]
  exact mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo hθ)

def unitHeckeDilationSL (q : ℕ∞) (hq : 3≤q) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (1/(2*Real.cos (triangleOrderAngle q)))
    (one_div_pos.mpr (hecke_width_pos q hq))

def unitHeckeInversion (q : ℕ∞) (hq : 3≤q) : ℍ≃ᵢℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL*
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq))⁻¹

def unitHeckeGroup (q : ℕ∞) (hq : 3≤q) : Subgroup (ℍ≃ᵢℍ) :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)) (standardHeckeGroup q hq)

theorem unitHecke_translation (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q)))*
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) := by
  unfold unitHeckeDilationSL
  rw [dilation_conjugate_translation_native]
  rw [one_div_mul_cancel (hecke_width_pos q hq).ne']

theorem unitHeckeGroup_generators (q : ℕ∞) (hq : 3≤q) :
    unitHeckeGroup q hq=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),unitHeckeInversion q hq}:Set (ℍ≃ᵢℍ)) := by
  rw [unitHeckeGroup,standardHeckeGroup_generators,native_subgroupConjugate_closure]
  simp only [image_insert_eq,image_singleton,unitHecke_translation,unitHeckeInversion]

theorem modularInversionSL_action_coe (z : ℍ) :
    ((modularInversionSL • z : ℍ):ℂ)= -1/(z:ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [modularInversionSL]

/-- The literal normalized source inversion, with no matrix-lift ambiguity. -/
theorem unitHeckeInversion_coe (q : ℕ∞) (hq : 3≤q) (z : ℍ) :
    ((unitHeckeInversion q hq z : ℍ):ℂ)=
      -1/(4*(Real.cos (triangleOrderAngle q):ℂ)^2*(z:ℂ)) := by
  change ((unitHeckeDilationSL q hq • (modularInversionSL •
    ((unitHeckeDilationSL q hq)⁻¹ • z)) : ℍ):ℂ)=_
  unfold unitHeckeDilationSL
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe, modularInversionSL_action_coe,
    verticalDilationSL_inverse_coe]
  have hc : (Real.cos (triangleOrderAngle q):ℂ)≠0 := by
    exact_mod_cast (show Real.cos (triangleOrderAngle q)≠0 by have h:=hecke_width_pos q hq;linarith)
  push_cast
  field_simp [hc,z.ne_zero]
  ring

theorem IsHeckeGroup.conformal_conjugate_unit {G : Subgroup (ℍ≃ᵢℍ)}
    (hG : IsHeckeGroup G) :
    ∃q : ℕ∞,∃hq : 3≤q,∃e : ℍ≃ᵢℍ,e∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e G=unitHeckeGroup q hq := by
  obtain ⟨q,hq,e,hc,he⟩:=hG.conformal_conjugate_standard
  refine ⟨q,hq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)*e,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup.mul_mem ⟨unitHeckeDilationSL q hq,rfl⟩ hc,?_⟩
  rw [←native_subgroupConjugate_compose,he]
  rfl

end LowDimensionalTopology.Geometry.Fuchsian
