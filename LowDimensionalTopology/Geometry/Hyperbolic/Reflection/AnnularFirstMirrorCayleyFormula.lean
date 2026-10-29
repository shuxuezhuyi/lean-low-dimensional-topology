module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The first actual annular mirror becomes negative conjugation in the
existing Cayley disc. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The original unit-semicircle mirror is negative conjugation in the actual Cayley disc. -/
theorem halfPlaneToDisc_unitCircleReflection (z : ℍ) :
    halfPlaneToDisc (circleReflection 0 1 zero_lt_one z) =
      -star (halfPlaneToDisc z) := by
  apply Complex.UnitDisc.coe_injective
  have hc : starRingEnd ℂ (z : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_zero, sub_zero] using conj_sub_real_ne_zero 0 z
  have hm : starRingEnd ℂ (z : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.I_im,
      Complex.zero_im, UpperHalfPlane.coe_im] at hi
    linarith [z.im_pos]
  have hd : 1 / starRingEnd ℂ (z : ℂ) + Complex.I ≠ 0 := by
    simpa only [circleReflection_coe, Complex.ofReal_zero, Complex.ofReal_one,
      one_pow, zero_add, sub_zero] using
      cayley_denom_ne_zero (circleReflection 0 1 zero_lt_one z)
  change cayleyFormula (circleReflection 0 1 zero_lt_one z) =
    -starRingEnd ℂ (cayleyFormula z)
  simp only [cayleyFormula, circleReflection_coe, Complex.ofReal_zero,
    Complex.ofReal_one, one_pow, zero_add, sub_zero, map_div₀, map_sub,
    map_add, Complex.conj_I, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [← neg_div]
  apply (div_eq_div_iff hd hm).mpr
  field_simp [hc]
  ring_nf
  simp [Complex.I_sq]

/-- The source-order first mirror retains that exact formula for every annular pair. -/
theorem halfPlaneToDisc_annularPairFirstMirror
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (z : ℍ) :
    halfPlaneToDisc ((annularPairReflectionMirrors E r x hE hr 0).reflection z) =
      -star (halfPlaneToDisc z) := by
  change halfPlaneToDisc (circleReflection 0 1 zero_lt_one z) = _
  exact halfPlaneToDisc_unitCircleReflection z

end LowDimensionalTopology.Geometry.Hyperbolic
