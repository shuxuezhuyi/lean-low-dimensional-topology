/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.IsometryCoefficients
public import LowDimensionalTopology.Geometry.Mobius.Circle.IsometricCircles

/-!
# Actual perpendicular bisectors and classical isometric circles
-/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem disc_radial_dist_eq_iff_norm (z w : 𝔻) :
    discPathDist z 0 = discPathDist w 0 ↔ ‖(z : ℂ)‖ = ‖(w : ℂ)‖ := by
  have hc : Real.cosh (discPathDist z 0) = Real.cosh (discPathDist w 0) ↔
      discPathDist z 0 = discPathDist w 0 := by
    rw [discPathDist_eq_halfPlane,discPathDist_eq_halfPlane]
    exact ⟨Real.cosh_injOn dist_nonneg dist_nonneg,congrArg Real.cosh⟩
  rw [← hc,disc_cosh_distance,disc_cosh_distance]
  simp only [Complex.UnitDisc.coe_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
    sub_zero,sub_zero,mul_one]
  have hz : 1 - ‖(z : ℂ)‖^2 ≠ 0 := ne_of_gt (sub_pos.mpr z.sq_norm_lt_one)
  have hw : 1 - ‖(w : ℂ)‖^2 ≠ 0 := ne_of_gt (sub_pos.mpr w.sq_norm_lt_one)
  rw [add_right_inj,div_eq_div_iff hz hw]
  constructor
  · intro he
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith
  · intro he
    rw [he]

theorem disc_coefficient_norm_difference (a c z : ℂ) (h : ‖a‖^2-‖c‖^2=1) :
    ‖a*z+conj c‖^2 - ‖c*z+conj a‖^2 = ‖z‖^2-1 := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im] at h ⊢
  linear_combination (z.re*z.re+z.im*z.im-1)*h

theorem discCoefficientAction_one_sub_norm_sq (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) (z : 𝔻) :
    (1-‖(discCoefficientAction a c h z : ℂ)‖^2)*‖c*z+conj a‖^2 = 1-‖(z : ℂ)‖^2 := by
  have hd : ‖c*(z : ℂ)+conj a‖ ≠ 0 := norm_ne_zero_iff.mpr (disc_coefficient_denom_ne_zero h z)
  rw [discCoefficientAction_coe,norm_div,div_pow]
  rw [sub_mul,one_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  linarith [disc_coefficient_norm_difference a c (z : ℂ) h]

theorem discCoefficientAction_norm_eq_iff (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) (z : 𝔻) :
    ‖(discCoefficientAction a c h z : ℂ)‖ = ‖(z : ℂ)‖ ↔ ‖c*z+conj a‖=1 := by
  have he := discCoefficientAction_one_sub_norm_sq a c h z
  have hp : 0 < 1-‖(z : ℂ)‖^2 := sub_pos.mpr z.sq_norm_lt_one
  constructor
  · intro hh
    rw [hh] at he
    have hmul : (1-‖(z : ℂ)‖^2)*(‖c*z+conj a‖^2-1)=0 := by nlinarith [he]
    have hs := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
    nlinarith [norm_nonneg (c*(z : ℂ)+conj a)]
  · intro hh
    rw [hh,one_pow,mul_one] at he
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith

theorem disc_coefficient_inverse_unit (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) :
    ‖conj a‖^2-‖-c‖^2=1 := by simpa only [Complex.norm_conj,norm_neg] using h

theorem discCoefficientsToSL_inverse (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) :
    discCoefficientsToSL (conj a) (-c) (disc_coefficient_inverse_unit a c h) =
      (discCoefficientsToSL a c h)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [discCoefficientsToSL] <;> ring

theorem discCoefficientAction_inverse_apply (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) (z : 𝔻) :
    discCoefficientAction (conj a) (-c) (disc_coefficient_inverse_unit a c h)
      (discCoefficientAction a c h z) = z := by
  change halfPlaneToDisc (discCoefficientsToSL (conj a) (-c) (disc_coefficient_inverse_unit a c h) •
    discToHalfPlane (halfPlaneToDisc (discCoefficientsToSL a c h • discToHalfPlane z))) = z
  rw [discToHalfPlane_halfPlaneToDisc,discCoefficientsToSL_inverse a c h,
    inv_smul_smul,halfPlaneToDisc_discToHalfPlane]

theorem discCoefficientAction_inverse_origin (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) :
    discCoefficientAction (conj a) (-c) (disc_coefficient_inverse_unit a c h)
      (discCoefficientAction a c h 0) = 0 := discCoefficientAction_inverse_apply a c h 0

theorem discCoefficientAction_origin_ne_zero {a c : ℂ} (h : ‖a‖^2-‖c‖^2=1) (hc : c ≠ 0) :
    discCoefficientAction a c h 0 ≠ 0 := by
  intro he
  have hn := discCoefficientAction_origin_norm_sq a c h
  rw [he,Complex.UnitDisc.coe_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] at hn
  have hnc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  exact (div_ne_zero (pow_ne_zero 2 hnc) (pow_ne_zero 2 (disc_coefficientA_ne_zero h))) hn.symm

theorem discCoefficientAction_equidistant_origin (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) (z : 𝔻) :
    discPathDist z 0 = discPathDist z (discCoefficientAction a c h 0) ↔ ‖-c*z+a‖=1 := by
  let := discHyperbolicMetric
  let f := discCoefficientAction (conj a) (-c) (disc_coefficient_inverse_unit a c h)
  have hf := discCoefficientAction_isometry (conj a) (-c) (disc_coefficient_inverse_unit a c h)
  have he : discPathDist z (discCoefficientAction a c h 0) = discPathDist (f z) 0 := by
    rw [← discHyperbolicMetric_distance,← discHyperbolicMetric_distance]
    calc
      dist z (discCoefficientAction a c h 0) = dist (f z) (f (discCoefficientAction a c h 0)) :=
        (hf.dist_eq z (discCoefficientAction a c h 0)).symm
      _ = dist (f z) 0 := congrArg (dist (f z)) (discCoefficientAction_inverse_origin a c h)
  rw [he,disc_radial_dist_eq_iff_norm,eq_comm,discCoefficientAction_norm_eq_iff]
  simp only [Complex.conj_conj]

theorem discCoefficientAction_inverse_isometricCircle_det (a c : ℂ) (h : ‖a‖^2-‖c‖^2=1) :
    conj a*a-(-conj c)*(-c)=1 := by
  have hd := discIsometryMatrix_det a c h
  rw [discIsometryMatrix,Matrix.det_fin_two] at hd
  change a*conj a-conj c*c=1 at hd
  convert hd using 1
  ring

theorem discCoefficientAction_bisector_isometricCircle {a c : ℂ}
    (h : ‖a‖^2-‖c‖^2=1) (hc : c ≠ 0) :
    DiscEquidistantLocus 0 (discCoefficientAction a c h 0) =
      {z : 𝔻 | (z : ℂ) ∈ Mobius.isometricCircle (conj a) (-conj c) (-c) a} := by
  ext z
  change (discPathDist z 0 = discPathDist z (discCoefficientAction a c h 0)) ↔
    (z : ℂ) ∈ Mobius.isometricCircle (conj a) (-conj c) (-c) a
  rw [Mobius.mem_isometricCircle_iff _ _ _ _ _ (neg_ne_zero.mpr hc),
    discCoefficientAction_inverse_isometricCircle_det a c h,norm_one,Real.sqrt_one]
  exact discCoefficientAction_equidistant_origin a c h z

theorem discCoefficientAction_perpendicularBisector_isometricCircle {a c : ℂ}
    (h : ‖a‖^2-‖c‖^2=1) (hc : c ≠ 0) :
    ∃! N : DiscLine, IsDiscPerpendicularBisector N 0 (discCoefficientAction a c h 0) ∧
      N.carrier = {z : 𝔻 | (z : ℂ) ∈ Mobius.isometricCircle (conj a) (-conj c) (-c) a} := by
  have hn : (0 : 𝔻) ≠ discCoefficientAction a c h 0 :=
    (discCoefficientAction_origin_ne_zero h hc).symm
  obtain ⟨N,hN,huniq⟩ := existsUnique_discPerpendicularBisector hn
  refine ⟨N,⟨hN,?_⟩,fun M hM => huniq M hM.1⟩
  rw [hN.carrier_eq hn,discCoefficientAction_bisector_isometricCircle h hc]


theorem disc_formula_perpendicularBisector_isometricCircle (f : 𝔻 → 𝔻) (a c : ℂ)
    (h : ‖a‖^2-‖c‖^2=1) (hc : c ≠ 0)
    (hf : ∀ z : 𝔻, (f z : ℂ) = (a*z+conj c)/(c*z+conj a)) :
    ∃! N : DiscLine, IsDiscPerpendicularBisector N 0 (f 0) ∧
      N.carrier = {z : 𝔻 | (z : ℂ) ∈ Mobius.isometricCircle (conj a) (-conj c) (-c) a} := by
  have he : f = discCoefficientAction a c h := by
    funext z
    apply Complex.UnitDisc.coe_injective
    rw [hf,discCoefficientAction_coe]
  rw [he]
  exact discCoefficientAction_perpendicularBisector_isometricCircle h hc


theorem disc_formula_perpendicularBisector_isometricCircle_of_origin_ne (f : 𝔻 → 𝔻) (a c : ℂ)
    (h : ‖a‖^2-‖c‖^2=1) (h0 : f 0 ≠ 0)
    (hf : ∀ z : 𝔻, (f z : ℂ) = (a*z+conj c)/(c*z+conj a)) :
    ∃! N : DiscLine, IsDiscPerpendicularBisector N 0 (f 0) ∧
      N.carrier = {z : 𝔻 | (z : ℂ) ∈ Mobius.isometricCircle (conj a) (-conj c) (-c) a} := by
  have hc : c ≠ 0 := by
    intro hc
    apply h0
    apply Complex.UnitDisc.coe_injective
    rw [hf]
    simp only [hc,Complex.UnitDisc.coe_zero,mul_zero,map_zero,add_zero,zero_add,zero_div]
  exact disc_formula_perpendicularBisector_isometricCircle f a c h hc hf

end
end LowDimensionalTopology.Geometry.Hyperbolic
