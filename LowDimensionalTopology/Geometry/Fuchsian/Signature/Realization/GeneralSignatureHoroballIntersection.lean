/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordRegions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- An actual determinant-one map fixing infinity scales every genuine
half-plane height by the positive square of its triangular denominator. -/
theorem generalSignature_fixInfinity_height
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ = ∞) (z : ℍ) :
    (A • z).im = z.im / (A 1 1) ^ 2 := by
  have hc := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hA
  have hden : realSLDenominator A z = (A 1 1 : ℂ) := by
    change (A 1 0 : ℂ) * (z : ℂ) + A 1 1 = _
    rw [hc]
    simp
  rw [realSL_im_action, hden]
  simp [Complex.normSq_ofReal, pow_two]

/-- Two actual normalized cusp tails with the same ideal centre have a
common genuine half-plane point above any two prescribed height thresholds.
This is the geometric intersection used by the actual target cusp census. -/
theorem generalSignature_same_cusp_tails_intersect
    (q r : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcenter : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q⁻¹)).val ∞ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (r⁻¹)).val ∞)
    (Y Z : ℝ) : ∃ z : ℍ, Y < (q • z).im ∧ Z < (r • z).im := by
  let A := r * q⁻¹
  have hA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ = ∞ := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (r * q⁻¹)).val ∞ = ∞
    rw [map_mul]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r).val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q⁻¹)).val ∞) = ∞
    rw [hcenter, map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r).val.apply_symm_apply ∞
  have hc := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hA
  have hd : A 1 1 ≠ 0 := by
    have hdet := A.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    intro hz
    rw [hz, mul_zero] at hdet
    norm_num at hdet
  let D := (A 1 1) ^ 2
  have hD : 0 < D := sq_pos_of_ne_zero hd
  let T := max 0 (max Y (Z * D)) + 1
  have hT : 0 < T := by dsimp only [T]; linarith [le_max_left (0 : ℝ) (max Y (Z * D))]
  have hTY : Y < T := by
    dsimp only [T]
    linarith [le_max_left Y (Z * D), le_max_right (0 : ℝ) (max Y (Z * D))]
  have hTZ : Z * D < T := by
    dsimp only [T]
    linarith [le_max_right Y (Z * D), le_max_right (0 : ℝ) (max Y (Z * D))]
  let w : ℍ := ⟨⟨0, T⟩, hT⟩
  refine ⟨q⁻¹ • w, ?_, ?_⟩
  · rw [smul_inv_smul]
    exact hTY
  · rw [← mul_smul]
    change Z < (A • w).im
    rw [generalSignature_fixInfinity_height A hA w]
    exact (lt_div_iff₀ hD).mpr hTZ

end LowDimensionalTopology.Geometry.Fuchsian
