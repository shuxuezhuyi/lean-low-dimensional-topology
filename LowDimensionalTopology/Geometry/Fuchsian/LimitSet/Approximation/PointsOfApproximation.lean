module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonCycles
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianLimitSets
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.IsometryCoefficients
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DiscCircleDistance
public import Mathlib.Analysis.Asymptotics.Lemmas
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Asymptotics
open scoped Topology OnePoint Complex.UnitDisc ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual native-disc action has exactly the original normalized matrix displacement. -/
theorem disc_group_matrix_norm_displacement
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2 = 2*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction g 0)) := by
  obtain ⟨a, c, hdet, hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form g.val (P.image_eq g)
  have hn : ‖a‖^2-‖c‖^2 = 1 := by simpa only [Complex.normSq_eq_norm_sq] using hdet
  let M := _root_.LowDimensionalTopology.Geometry.Mobius.coefficientMatrix a (conj c) c (conj a)
    (show a*conj a-conj c*c ≠ 0 from by rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_determinant hdet]; norm_num)
  have he : g.val = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection M := by
    apply Subtype.ext
    exact hform
  rw [he, _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm_projection]
  change _root_.LowDimensionalTopology.Geometry.Mobius.matrixNormalizedNorm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIsometryMatrix a c)^2 = _
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_formula_normalizedNorm_displacement (P.discAction g) a c hn
  left
  intro z
  change (P.finiteCoordinate (g • P.finiteCoordinate.symm z) : ℂ) = _
  rw [P.finite_smul g a c hdet hform, P.finiteCoordinate.apply_symm_apply]
  rfl

theorem disc_inverse_cosh_radial_bounds (z : 𝔻) :
    1-‖(z : ℂ)‖ ≤ (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z))⁻¹ ∧
      (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z))⁻¹ ≤ 2*(1-‖(z : ℂ)‖) := by
  let r := ‖(z : ℂ)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := z.norm_lt_one
  have hden : 0 < 1+r^2 := by positivity
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance_zero, inv_div]
  constructor
  · apply (le_div_iff₀ hden).mpr
    have h := mul_nonneg hr (sq_nonneg (1-r))
    change (1-r)*(1+r^2) ≤ 1-r^2
    nlinarith only [h]
  · apply (div_le_iff₀ hden).mpr
    have h := mul_nonneg (show 0 ≤ 1-r by linarith only [hr1])
      (show 0 ≤ 1-r+2*r^2 by nlinarith only [hr1, sq_nonneg r])
    change 1-r^2 ≤ 2*(1-r)*(1+r^2)
    nlinarith only [h]

theorem disc_group_inverse_norm_sq_radial_bounds
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) :
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2)⁻¹ ≤ 1-‖(P.discAction g 0 : ℂ)‖ ∧
      1-‖(P.discAction g 0 : ℂ)‖ ≤ 2*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2)⁻¹ := by
  have h := disc_inverse_cosh_radial_bounds (P.discAction g 0)
  rw [disc_group_matrix_norm_displacement P g, mul_inv_rev]
  norm_num
  constructor <;> linarith only [h.1, h.2]

theorem disc_group_matrix_norm_sq_pos {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (g : H) : 0 < _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2 := by
  rw [disc_group_matrix_norm_displacement P g]
  exact mul_pos (by norm_num) (Real.cosh_pos _)

/-- The source inverse-square norm rate for the genuine original group orbit. -/
def HasDiscOrbitMatrixRate
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (g : ℕ → H) (ξ : ℂ) (w : 𝔻) : Prop :=
  (fun n => ξ-(P.discAction (g n) w : ℂ)) =O[atTop]
    (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹)

/-- The fastest Euclidean radial rate, in the actual finite unit-disc coordinate. -/
def HasDiscOrbitRadialRate
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (g : ℕ → H) (ξ : ℂ) : Prop :=
  (fun n => ξ-(P.discAction (g n) 0 : ℂ)) =O[atTop]
    (fun n => 1-‖(P.discAction (g n) 0 : ℂ)‖)

theorem disc_group_radial_bigO_inverse_norm_sq
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) :
    (fun n => 1-‖(P.discAction (g n) 0 : ℂ)‖) =O[atTop]
      (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) := by
  apply IsBigO.of_bound 2
  apply Filter.Eventually.of_forall
  intro n
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (P.discAction (g n) 0).norm_lt_one),
    abs_of_pos (inv_pos.mpr (disc_group_matrix_norm_sq_pos P (g n)))] using
      (disc_group_inverse_norm_sq_radial_bounds P (g n)).2

theorem disc_group_inverse_norm_sq_bigO_radial
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) :
    (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) =O[atTop]
      (fun n => 1-‖(P.discAction (g n) 0 : ℂ)‖) := by
  apply IsBigO.of_bound 1
  apply Filter.Eventually.of_forall
  intro n
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (P.discAction (g n) 0).norm_lt_one),
    abs_of_pos (inv_pos.mpr (disc_group_matrix_norm_sq_pos P (g n))), one_mul] using
      (disc_group_inverse_norm_sq_radial_bounds P (g n)).1

theorem disc_orbit_radial_iff_matrix_rate
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) :
    HasDiscOrbitRadialRate P g ξ ↔ HasDiscOrbitMatrixRate P g ξ 0 :=
  ⟨fun h => h.trans (disc_group_radial_bigO_inverse_norm_sq P g),
    fun h => h.trans (disc_group_inverse_norm_sq_bigO_radial P g)⟩

/-- For the original actual Fuchsian group, including elementary cases. -/
def IsFuchsianPointOfApproximation {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (ξ : ℂ) : Prop :=
  (ξ : Mobius.ExtendedComplex) ∈ fuchsianLimitSet H ∧
    ∀ w : 𝔻, ∃ g : ℕ → H, Function.Injective g ∧ HasDiscOrbitMatrixRate P g ξ w

/-- The original split-limit-set convention, with actual parabolic fixed points. -/
def HasSplitFuchsianLimitSet
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : Prop :=
  ∀ ξ : ℂ, (ξ : Mobius.ExtendedComplex) ∈ fuchsianLimitSet H →
    (∃ g : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧ g.val.val (ξ : Mobius.ExtendedComplex) = (ξ : Mobius.ExtendedComplex)) ∨
      IsFuchsianPointOfApproximation P ξ

theorem fuchsian_limit_finite_norm_one {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (ξ : ℂ)
    (hξ : (ξ : Mobius.ExtendedComplex) ∈ fuchsianLimitSet H) :
    ‖ξ‖ = 1 := by
  have h := P.asFuchsianDisc.limitSet_subset_frontier hξ
  change (ξ : Mobius.ExtendedComplex) ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at h
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle] at h
  simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe, sub_zero] using h

theorem disc_coefficient_sub_origin_formula (a c : ℂ) (h : ‖a‖^2-‖c‖^2 = 1) (z : 𝔻) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction a c h z : ℂ)-(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction a c h 0 : ℂ) =
      (z : ℂ)/((c*(z : ℂ)+conj a)*conj a) := by
  have ha : conj a ≠ 0 := by
    intro he
    apply norm_ne_zero_iff.mp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficientA_ne_zero h)
    simpa only [map_zero, Complex.conj_conj] using congrArg (starRingEnd ℂ) he
  have hd := _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_determinant
    (show Complex.normSq a-Complex.normSq c = 1 from by
      simpa only [Complex.normSq_eq_norm_sq] using h)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction_coe]
  simp only [Complex.UnitDisc.coe_zero, mul_zero, zero_add]
  have hz : (z : ℂ)*c+conj a ≠ 0 := by
    simpa only [mul_comm] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficient_denom_ne_zero h z
  field_simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficient_denom_ne_zero h z, hz, ha]
  linear_combination (z : ℂ)*hd

/-- Uniform shrinking of the actual image of every fixed interior basepoint. -/
theorem disc_coefficient_sub_origin_bound (a c : ℂ) (h : ‖a‖^2-‖c‖^2 = 1) (z : 𝔻) :
    ‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction a c h z : ℂ)-(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction a c h 0 : ℂ)‖ ≤
      (‖(z : ℂ)‖/(1-‖(z : ℂ)‖))*(1-‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction a c h 0 : ℂ)‖^2) := by
  have ha : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg a) (Ne.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficientA_ne_zero h))
  have hz : 0 < 1-‖(z : ℂ)‖ := sub_pos.mpr z.norm_lt_one
  have hca : ‖c‖ ≤ ‖a‖ := by nlinarith only [h, norm_nonneg a, norm_nonneg c]
  have htriangle : ‖a‖ ≤ ‖c*(z : ℂ)+conj a‖+‖c‖*‖(z : ℂ)‖ := by
    calc
      ‖a‖ = ‖conj a‖ := (Complex.norm_conj a).symm
      _ = ‖(c*(z : ℂ)+conj a)-c*(z : ℂ)‖ := by congr 1; ring
      _ ≤ ‖c*(z : ℂ)+conj a‖+‖c*(z : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul]
  have hden : ‖a‖*(1-‖(z : ℂ)‖) ≤ ‖c*(z : ℂ)+conj a‖ := by
    have hmul := mul_le_mul_of_nonneg_right hca (norm_nonneg (z : ℂ))
    nlinarith only [htriangle, hmul]
  calc
    _ = ‖(z : ℂ)‖/(‖c*(z : ℂ)+conj a‖*‖a‖) := by
      rw [disc_coefficient_sub_origin_formula, norm_div, norm_mul, Complex.norm_conj]
    _ ≤ ‖(z : ℂ)‖/((‖a‖*(1-‖(z : ℂ)‖))*‖a‖) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos (mul_pos ha hz) ha)
        (mul_le_mul_of_nonneg_right hden ha.le)
    _ = (‖(z : ℂ)‖/(1-‖(z : ℂ)‖))*(1/‖a‖^2) := by
      field_simp [ha.ne', hz.ne']
    _ = _ := by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction_origin_one_sub_norm_sq]

theorem disc_group_sub_origin_bound {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (z : 𝔻) :
    ‖(P.discAction g z : ℂ)-(P.discAction g 0 : ℂ)‖ ≤
      (4*‖(z : ℂ)‖/(1-‖(z : ℂ)‖))*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2)⁻¹ := by
  obtain ⟨a, c, hdet, hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form g.val (P.image_eq g)
  have hn : ‖a‖^2-‖c‖^2 = 1 := by simpa only [Complex.normSq_eq_norm_sq] using hdet
  have he (w : 𝔻) : P.discAction g w = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction a c hn w := by
    apply Complex.UnitDisc.coe_injective
    change (P.finiteCoordinate (g • P.finiteCoordinate.symm w) : ℂ) = _
    rw [P.finite_smul g a c hdet hform, P.finiteCoordinate.apply_symm_apply]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction_coe]
    rfl
  have hc := disc_coefficient_sub_origin_bound a c hn z
  rw [← he z, ← he 0] at hc
  let C := ‖(z : ℂ)‖/(1-‖(z : ℂ)‖)
  have hC : 0 ≤ C := div_nonneg (norm_nonneg _) (sub_pos.mpr z.norm_lt_one).le
  have hr : 1-‖(P.discAction g 0 : ℂ)‖^2 ≤ 2*(1-‖(P.discAction g 0 : ℂ)‖) := by
    nlinarith only [sq_nonneg (1-‖(P.discAction g 0 : ℂ)‖)]
  calc
    _ ≤ C*(1-‖(P.discAction g 0 : ℂ)‖^2) := hc
    _ ≤ C*(2*(1-‖(P.discAction g 0 : ℂ)‖)) := mul_le_mul_of_nonneg_left hr hC
    _ ≤ C*(2*(2*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (disc_group_inverse_norm_sq_radial_bounds P g).2 (by norm_num)) hC
    _ = _ := by dsimp only [C]; ring

theorem disc_orbit_basepoint_difference_bigO
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (z : 𝔻) :
    (fun n => (P.discAction (g n) z : ℂ)-(P.discAction (g n) 0 : ℂ)) =O[atTop]
      (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) := by
  apply IsBigO.of_bound (4*‖(z : ℂ)‖/(1-‖(z : ℂ)‖))
  apply Filter.Eventually.of_forall
  intro n
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (disc_group_matrix_norm_sq_pos P (g n)))]
    using disc_group_sub_origin_bound P (g n) z

theorem disc_orbit_matrix_rate_all_basepoints_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) :
    (∀ w : 𝔻, HasDiscOrbitMatrixRate P g ξ w) ↔ HasDiscOrbitMatrixRate P g ξ 0 := by
  constructor
  · exact fun h => h 0
  · intro h w
    have hd := h.sub (disc_orbit_basepoint_difference_bigO P g w)
    have he : (fun n => (ξ-(P.discAction (g n) 0 : ℂ))-
        ((P.discAction (g n) w : ℂ)-(P.discAction (g n) 0 : ℂ))) =
        (fun n => ξ-(P.discAction (g n) w : ℂ)) := by funext n; ring
    change (fun n => (ξ-(P.discAction (g n) 0 : ℂ))-
      ((P.discAction (g n) w : ℂ)-(P.discAction (g n) 0 : ℂ))) =O[atTop]
      (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) at hd
    rw [he] at hd
    exact hd

theorem fuchsian_pointOfApproximation_iff_single_sequence
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (ξ : ℂ) :
    IsFuchsianPointOfApproximation P ξ ↔
      (ξ : Mobius.ExtendedComplex) ∈ fuchsianLimitSet H ∧
        ∃ g : ℕ → H, Function.Injective g ∧ HasDiscOrbitMatrixRate P g ξ 0 := by
  constructor
  · exact fun h => ⟨h.1, h.2 0⟩
  · rintro ⟨hξ, g, hg, hrate⟩
    exact ⟨hξ, fun w => ⟨g, hg, (disc_orbit_matrix_rate_all_basepoints_iff P g ξ).mpr hrate w⟩⟩

theorem injective_disc_orbit_inverse_norm_sq_tendsto_zero
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (hg : Function.Injective g) :
    Tendsto (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp (_root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_injective_sequence_norm_tendsto H P.discrete g hg)
  simpa only [Function.comp_apply, inv_pow, zero_pow (by omega : 2 ≠ 0)] using h.pow 2

theorem disc_orbit_matrix_rate_tendsto {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) (w : 𝔻)
    (hg : Function.Injective g) (h : HasDiscOrbitMatrixRate P g ξ w) :
    Tendsto (fun n => (P.discAction (g n) w : ℂ)) atTop (𝓝 ξ) := by
  have hzero := h.trans_tendsto (injective_disc_orbit_inverse_norm_sq_tendsto_zero P g hg)
  have he : Tendsto (fun n => ξ-(ξ-(P.discAction (g n) w : ℂ))) atTop (𝓝 (ξ-0)) :=
    tendsto_const_nhds.sub hzero
  simpa only [sub_sub_cancel, sub_zero] using he

theorem disc_pathDist_nonneg (z w : 𝔻) : 0 ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z w := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
  exact dist_nonneg

theorem cosh_add_le_double_product (x y : ℝ) (hy : 0 ≤ y) :
    Real.cosh (x+y) ≤ 2*Real.cosh x*Real.cosh y := by
  rw [Real.cosh_add]
  have h := mul_le_mul (Real.sinh_lt_cosh (x := x)).le (Real.sinh_lt_cosh (x := y)).le
    (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos x).le
  nlinarith only [h]

theorem disc_cosh_from_origin_le (z w : 𝔻) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) ≤
      2*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w)*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist w z) := by
  have htriangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w+_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist w z := by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    exact dist_triangle _ _ _
  have hcos : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) ≤
      Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w+_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist w z) :=
    Real.cosh_le_cosh.mpr (by
      simpa only [abs_of_nonneg (disc_pathDist_nonneg 0 z),
        abs_of_nonneg (add_nonneg (disc_pathDist_nonneg 0 w) (disc_pathDist_nonneg w z))]
        using htriangle)
  exact hcos.trans (cosh_add_le_double_product _ _ (disc_pathDist_nonneg w z))

theorem disc_inverse_cosh_comparison (z w : 𝔻) :
    (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z))⁻¹ ≤
      (2*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z w))*(Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w))⁻¹ := by
  have h := disc_cosh_from_origin_le w z
  rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)).mpr
  nlinarith only [h]

theorem disc_group_orbit_pair_distance {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (z w : 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.discAction g z) (P.discAction g w) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z w := by
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using (P.discAction_isometry g).dist_eq z w

theorem disc_group_inverse_cosh_vs_norm_bounds
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (w : 𝔻) :
    (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction g w)))⁻¹ ≤
        (4*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w))*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2)⁻¹ ∧
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm g.val^2)⁻¹ ≤
        (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w))*(Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction g w)))⁻¹ := by
  have h₁ := disc_inverse_cosh_comparison (P.discAction g w) (P.discAction g 0)
  have h₂ := disc_inverse_cosh_comparison (P.discAction g 0) (P.discAction g w)
  rw [disc_group_orbit_pair_distance P g w 0] at h₁
  rw [disc_group_orbit_pair_distance P g 0 w] at h₂
  have hcomm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist w 0 = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w := by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    exact dist_comm _ _
  rw [hcomm] at h₁
  rw [disc_group_matrix_norm_displacement P g, mul_inv_rev]
  norm_num
  constructor <;> nlinarith only [h₁, h₂]

theorem disc_orbit_matrix_iff_inverse_cosh_rate
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) (w : 𝔻) :
    HasDiscOrbitMatrixRate P g ξ w ↔
      (fun n => ξ-(P.discAction (g n) w : ℂ)) =O[atTop]
        (fun n => (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction (g n) w)))⁻¹) := by
  have hcos : (fun n => (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction (g n) w)))⁻¹) =O[atTop]
      (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) := by
    apply IsBigO.of_bound (4*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w))
    apply Filter.Eventually.of_forall
    intro n
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.cosh_pos _)),
      abs_of_pos (inv_pos.mpr (disc_group_matrix_norm_sq_pos P (g n)))] using
      (disc_group_inverse_cosh_vs_norm_bounds P (g n) w).1
  have hnorm : (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) =O[atTop]
      (fun n => (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction (g n) w)))⁻¹) := by
    apply IsBigO.of_bound (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w))
    apply Filter.Eventually.of_forall
    intro n
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.cosh_pos _)),
      abs_of_pos (inv_pos.mpr (disc_group_matrix_norm_sq_pos P (g n)))] using
      (disc_group_inverse_cosh_vs_norm_bounds P (g n) w).2
  exact ⟨fun h => h.trans hnorm, fun h => h.trans hcos⟩

theorem disc_orbit_matrix_iff_euclidean_radial_rate
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) (w : 𝔻) :
    HasDiscOrbitMatrixRate P g ξ w ↔
      (fun n => ξ-(P.discAction (g n) w : ℂ)) =O[atTop]
        (fun n => 1-‖(P.discAction (g n) w : ℂ)‖) := by
  have hradial : (fun n => 1-‖(P.discAction (g n) w : ℂ)‖) =O[atTop]
      (fun n => (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction (g n) w)))⁻¹) := by
    apply IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro n
    simpa only [Real.norm_eq_abs, one_mul, abs_of_pos (inv_pos.mpr (Real.cosh_pos _)),
      abs_of_pos (sub_pos.mpr (P.discAction (g n) w).norm_lt_one)] using
      (disc_inverse_cosh_radial_bounds (P.discAction (g n) w)).1
  have hcos : (fun n => (Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction (g n) w)))⁻¹) =O[atTop]
      (fun n => 1-‖(P.discAction (g n) w : ℂ)‖) := by
    apply IsBigO.of_bound 2
    apply Filter.Eventually.of_forall
    intro n
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.cosh_pos _)),
      abs_of_pos (sub_pos.mpr (P.discAction (g n) w).norm_lt_one)] using
      (disc_inverse_cosh_radial_bounds (P.discAction (g n) w)).2
  exact (disc_orbit_matrix_iff_inverse_cosh_rate P g ξ w).trans
    ⟨fun h => h.trans hcos, fun h => h.trans hradial⟩

theorem disc_orbit_matrix_rate_iff_origin
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) (w : 𝔻) :
    HasDiscOrbitMatrixRate P g ξ w ↔ HasDiscOrbitMatrixRate P g ξ 0 := by
  constructor
  · intro h
    have hd := h.add (disc_orbit_basepoint_difference_bigO P g w)
    have he : (fun n => (ξ-(P.discAction (g n) w : ℂ))+
        ((P.discAction (g n) w : ℂ)-(P.discAction (g n) 0 : ℂ))) =
        (fun n => ξ-(P.discAction (g n) 0 : ℂ)) := by funext n; ring
    change (fun n => (ξ-(P.discAction (g n) w : ℂ))+
      ((P.discAction (g n) w : ℂ)-(P.discAction (g n) 0 : ℂ))) =O[atTop]
      (fun n => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) at hd
    rw [he] at hd
    exact hd
  · exact fun h => (disc_orbit_matrix_rate_all_basepoints_iff P g ξ).mpr h w

theorem disc_orbit_rate_basepoint_independent
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) (w v : 𝔻) :
    HasDiscOrbitMatrixRate P g ξ w ↔ HasDiscOrbitMatrixRate P g ξ v :=
  (disc_orbit_matrix_rate_iff_origin P g ξ w).trans (disc_orbit_matrix_rate_iff_origin P g ξ v).symm

theorem disc_boundary_approach_lower_bound (ξ : ℂ) (hξ : ‖ξ‖ = 1) (z : 𝔻) :
    1-‖(z : ℂ)‖ ≤ ‖ξ-(z : ℂ)‖ := by
  simpa only [hξ] using norm_sub_norm_le ξ (z : ℂ)

theorem disc_cosh_radial_scaled_identity (z : 𝔻) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z)*(1-‖(z : ℂ)‖) =
      (1+‖(z : ℂ)‖^2)/(1+‖(z : ℂ)‖) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance_zero]
  field_simp [ne_of_gt (sub_pos.mpr z.sq_norm_lt_one),
    ne_of_gt (show 0 < 1+‖(z : ℂ)‖ by positivity)]
  ring

theorem disc_cosh_radial_asymptotic {z : ℕ → 𝔻}
    (hz : Tendsto (fun n => ‖(z n : ℂ)‖) atTop (𝓝 1)) :
    Tendsto (fun n => Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (z n))*(1-‖(z n : ℂ)‖)) atTop (𝓝 1) := by
  simp_rw [disc_cosh_radial_scaled_identity]
  have hnum : Tendsto (fun n => 1+‖(z n : ℂ)‖^2) atTop (𝓝 ((1 : ℝ)+1^2)) :=
    tendsto_const_nhds.add (hz.pow 2)
  have hden : Tendsto (fun n => 1+‖(z n : ℂ)‖) atTop (𝓝 ((1 : ℝ)+1)) :=
    tendsto_const_nhds.add hz
  have hdiv := hnum.div hden (by norm_num : (1 : ℝ)+1 ≠ 0)
  have he : ((fun n => 1+‖(z n : ℂ)‖^2)/(fun n => 1+‖(z n : ℂ)‖)) =
      (fun n => (1+‖(z n : ℂ)‖^2)/(1+‖(z n : ℂ)‖)) := by
    funext n
    exact Pi.div_apply _ _ _
  rw [he] at hdiv
  simpa using hdiv

theorem injective_disc_orbit_norm_tendsto_one
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (hg : Function.Injective g) (w : 𝔻) :
    Tendsto (fun n => ‖(P.discAction (g n) w : ℂ)‖) atTop (𝓝 1) := by
  have hN := injective_disc_orbit_inverse_norm_sq_tendsto_zero P g hg
  have hbound : Tendsto (fun n => (4*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w))*
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (g n).val^2)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hN : Tendsto _ atTop (𝓝 ((4*Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 w))*0)))
  have hz : Tendsto (fun n => 1-‖(P.discAction (g n) w : ℂ)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => (sub_pos.mpr (P.discAction (g n) w).norm_lt_one).le)
      (fun n => (disc_inverse_cosh_radial_bounds (P.discAction (g n) w)).1.trans
        (disc_group_inverse_cosh_vs_norm_bounds P (g n) w).1) hbound
  have he : Tendsto (fun n => 1-(1-‖(P.discAction (g n) w : ℂ)‖)) atTop (𝓝 ((1 : ℝ)-0)) :=
    tendsto_const_nhds.sub hz
  simpa only [sub_sub_cancel, sub_zero] using he

theorem injective_disc_orbit_cosh_radial_asymptotic
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (hg : Function.Injective g) (w : 𝔻) :
    Tendsto (fun n => Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (P.discAction (g n) w))*
      (1-‖(P.discAction (g n) w : ℂ)‖)) atTop (𝓝 1) :=
  disc_cosh_radial_asymptotic (injective_disc_orbit_norm_tendsto_one P g hg w)

theorem fuchsian_limit_unitDisc_finite {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (ζ : Mobius.ExtendedComplex)
    (hζ : ζ ∈ fuchsianLimitSet H) :
    ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ ζ = (ξ : Mobius.ExtendedComplex) := by
  have h := P.asFuchsianDisc.limitSet_subset_frontier hζ
  change ζ ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at h
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle] at h
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mem_complexUnitCircle_iff ζ).mp h

/-- The finite-coordinate split convention is exactly the condition on every
original point of the extended-complex limit set. -/
theorem split_fuchsian_limitSet_iff_all_points
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) :
    HasSplitFuchsianLimitSet P ↔ ∀ ζ : Mobius.ExtendedComplex, ζ ∈ fuchsianLimitSet H →
      (∃ g : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧ g.val.val ζ = ζ) ∨
        ∃ ξ : ℂ, ζ = (ξ : Mobius.ExtendedComplex) ∧ IsFuchsianPointOfApproximation P ξ := by
  constructor
  · intro h ζ hζ
    obtain ⟨ξ, _, rfl⟩ := fuchsian_limit_unitDisc_finite P ζ hζ
    rcases h ξ hζ with hp | ha
    · exact Or.inl hp
    · exact Or.inr ⟨ξ, rfl, ha⟩
  · intro h ξ hξ
    rcases h (ξ : Mobius.ExtendedComplex) hξ with hp | ⟨η, he, ha⟩
    · exact Or.inl hp
    · have he' : ξ = η := OnePoint.coe_injective he
      exact Or.inr (he'.symm ▸ ha)

end LowDimensionalTopology.Geometry.Fuchsian
