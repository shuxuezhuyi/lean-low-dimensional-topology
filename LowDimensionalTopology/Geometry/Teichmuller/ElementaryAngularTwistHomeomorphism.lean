module

public import LowDimensionalTopology.Geometry.Teichmuller.ElementaryAngularTwistSpatialDerivative
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.Linarith

/-!
# The same elementary angular map and its actual inverse

A clamped angle rewrites the original three-piece map as a single positive
radial factor. It gives continuity through both seams and preserves the
angle, so changing the sign of the parameter gives the actual inverse.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Complex
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

private def clippedAngle (θ : Width) (z : ℂ) : ℝ :=
  min (max (Complex.arg z - Real.pi / 2 + (θ : ℝ)) 0) (2 * (θ : ℝ))

private theorem coe_elementaryMap_eq_clipped (θ : Width) (t : ℝ) (z : ℍ) :
    (elementaryMap θ t z : ℂ) =
      (z : ℂ) * (Real.exp (shear θ t * clippedAngle θ z) : ℂ) := by
  classical
  rw [coe_elementaryMap]
  by_cases hlo : Complex.arg (z : ℂ) < Real.pi / 2 - (θ : ℝ)
  · have ha : Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ) ≤ 0 := by linarith
    rw [ite_eq_left hlo]
    simp only [clippedAngle, max_eq_right ha,
      min_eq_left (by linarith [θ.property.1] : (0 : ℝ) ≤ 2 * (θ : ℝ)),
      mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one]
  · rw [ite_eq_right hlo]
    have ha : 0 ≤ Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ) := by
      linarith [le_of_not_gt hlo]
    by_cases hhi : Complex.arg (z : ℂ) ≤ Real.pi / 2 + (θ : ℝ)
    · have hb : Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ) ≤ 2 * (θ : ℝ) := by
        linarith
      rw [ite_eq_left hhi]
      simp only [clippedAngle, max_eq_left ha, min_eq_left hb]
    · have hb : 2 * (θ : ℝ) ≤ Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ) := by
        linarith [lt_of_not_ge hhi]
      have hs : shear θ t * (2 * (θ : ℝ)) = -t :=
        div_mul_cancel₀ _ (mul_ne_zero (by norm_num) θ.property.1.ne')
      rw [ite_eq_right hhi]
      simp only [clippedAngle, max_eq_left ha, min_eq_right hb, hs]

private theorem continuousOn_elementaryMapPlane (θ : Width) (t : ℝ) :
    ContinuousOn (elementaryMapPlane θ t) LiZhongQC.upperHalf := by
  have harg : ContinuousOn Complex.arg LiZhongQC.upperHalf :=
    Complex.continuousOn_arg.mono (fun z hz =>
      Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz)))
  have hclip : ContinuousOn (clippedAngle θ) LiZhongQC.upperHalf :=
    (((harg.sub continuousOn_const).add continuousOn_const).sup
      continuousOn_const).inf continuousOn_const
  have hreal : ContinuousOn (fun z : ℂ => Real.exp (shear θ t * clippedAngle θ z))
      LiZhongQC.upperHalf :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hclip)
  have hformula : ContinuousOn
      (fun z : ℂ => z * (Real.exp (shear θ t * clippedAngle θ z) : ℂ))
      LiZhongQC.upperHalf :=
    continuousOn_id.mul (Complex.continuous_ofReal.comp_continuousOn hreal)
  apply hformula.congr
  intro z hz
  exact (elementaryMapPlane_coe θ t (⟨z, hz⟩ : ℍ)).trans
    (coe_elementaryMap_eq_clipped θ t (⟨z, hz⟩ : ℍ))

private theorem arg_elementaryMap (θ : Width) (t : ℝ) (z : ℍ) :
    Complex.arg (elementaryMap θ t z : ℂ) = Complex.arg (z : ℂ) := by
  rw [coe_elementaryMap_eq_clipped, mul_comm]
  exact Complex.arg_real_mul _ (Real.exp_pos _)

private theorem elementaryMap_neg_leftInverse (θ : Width) (t : ℝ) (z : ℍ) :
    elementaryMap θ (-t) (elementaryMap θ t z) = z := by
  have hclip : clippedAngle θ (elementaryMap θ t z : ℂ) = clippedAngle θ z := by
    simp only [clippedAngle, arg_elementaryMap]
  have hs : shear θ (-t) = -shear θ t := by simp only [shear, neg_neg, neg_div]
  have he : shear θ t * clippedAngle θ z + shear θ (-t) * clippedAngle θ z = 0 := by
    rw [hs]
    ring
  apply UpperHalfPlane.ext
  rw [coe_elementaryMap_eq_clipped, hclip, coe_elementaryMap_eq_clipped,
    mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, he,
    Real.exp_zero, Complex.ofReal_one, mul_one]

private theorem elementaryMapPlane_mem (θ : Width) (t : ℝ) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) :
    elementaryMapPlane θ t z ∈ LiZhongQC.upperHalf := by
  rw [elementaryMapPlane_coe θ t (⟨z, hz⟩ : ℍ)]
  exact (elementaryMap θ t (⟨z, hz⟩ : ℍ)).im_pos

private theorem elementaryMapPlane_neg_leftInverse (θ : Width) (t : ℝ) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) :
    elementaryMapPlane θ (-t) (elementaryMapPlane θ t z) = z := by
  rw [elementaryMapPlane_coe θ t (⟨z, hz⟩ : ℍ),
    elementaryMapPlane_coe θ (-t) (elementaryMap θ t (⟨z, hz⟩ : ℍ)),
    elementaryMap_neg_leftInverse]

/-- The original elementary map is continuous through both seams, has the
actual parameter-negated inverse, and is a homeomorphism of the whole H. -/
theorem elementaryMap_inverse_continuous (θ : Width) (t : ℝ) :
    Continuous (elementaryMap θ t) ∧
      (∀ z : ℍ, elementaryMap θ (-t) (elementaryMap θ t z) = z) ∧
      (∀ z : ℍ, elementaryMap θ t (elementaryMap θ (-t) z) = z) ∧
      LiZhongQC.IsHomeomorphOnto (elementaryMapPlane θ t)
        LiZhongQC.upperHalf LiZhongQC.upperHalf := by
  have hc := continuousOn_elementaryMapPlane θ t
  have hci := continuousOn_elementaryMapPlane θ (-t)
  have hnative : Continuous (elementaryMap θ t) := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    have h := hc.comp_continuous UpperHalfPlane.continuous_coe
      (fun z : ℍ => z.im_pos)
    simpa only [Function.comp_def, elementaryMapPlane_coe] using h
  have hleft := elementaryMap_neg_leftInverse θ t
  have hright (z : ℍ) : elementaryMap θ t (elementaryMap θ (-t) z) = z := by
    simpa only [neg_neg] using elementaryMap_neg_leftInverse θ (-t) z
  have hinj : InjOn (elementaryMapPlane θ t) LiZhongQC.upperHalf := by
    intro z hz w hw he
    have h := congrArg (elementaryMapPlane θ (-t)) he
    rw [elementaryMapPlane_neg_leftInverse θ t hz,
      elementaryMapPlane_neg_leftInverse θ t hw] at h
    exact h
  have hrightP (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      elementaryMapPlane θ t (elementaryMapPlane θ (-t) z) = z := by
    simpa only [neg_neg] using elementaryMapPlane_neg_leftInverse θ (-t) hz
  have himage : elementaryMapPlane θ t '' LiZhongQC.upperHalf =
      LiZhongQC.upperHalf := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact elementaryMapPlane_mem θ t hz
    · intro z hz
      exact ⟨elementaryMapPlane θ (-t) z, elementaryMapPlane_mem θ (-t) hz,
        hrightP z hz⟩
  have hinv (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      Function.invFunOn (elementaryMapPlane θ t) LiZhongQC.upperHalf z =
        elementaryMapPlane θ (-t) z := by
    have h := hinj.leftInvOn_invFunOn (elementaryMapPlane_mem θ (-t) hz)
    simpa only [hrightP z hz] using h
  refine ⟨hnative, hleft, hright, hc, hinj, himage, ?_⟩
  exact hci.congr (fun z hz => hinv z hz)

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
