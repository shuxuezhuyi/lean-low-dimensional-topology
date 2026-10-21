/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Counting.MobiusCounting
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint ENNReal NNReal
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- Height followed by two actual horizontal coordinates. -/
abbrev MobiusCountingCoordinates := ℝ × (ℝ × ℝ)

def mobiusCountingHeightMeasure : Measure ℝ :=
  volume.withDensity (fun y : ℝ => ENNReal.ofReal ((y ^ 3)⁻¹))

def mobiusCountingVolume : Measure MobiusCountingCoordinates :=
  mobiusCountingHeightMeasure.prod volume

/-- A box whose three side lengths scale with its positive central height. -/
def mobiusCountingBox (c y x₁ x₂ : ℝ) : Set MobiusCountingCoordinates :=
  Ioo ((1 - c) * y) ((1 + c) * y) ×ˢ
    (Ioo (x₁ - c * y) (x₁ + c * y) ×ˢ Ioo (x₂ - c * y) (x₂ + c * y))

theorem mobiusCountingBox_measurable (c y x₁ x₂ : ℝ) :
    MeasurableSet (mobiusCountingBox c y x₁ x₂) :=
  measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)

theorem mobiusCountingHeightMeasure_lower {c y : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hy : 0 < y) :
    ENNReal.ofReal ((2 * y)⁻¹ ^ 3 * (2 * c * y)) ≤
      mobiusCountingHeightMeasure (Ioo ((1 - c) * y) ((1 + c) * y)) := by
  rw [mobiusCountingHeightMeasure, withDensity_apply _ measurableSet_Ioo]
  have h : (∫⁻ _ : ℝ in Ioo ((1 - c) * y) ((1 + c) * y), ENNReal.ofReal ((2 * y)⁻¹ ^ 3)) ≤
      ∫⁻ t : ℝ in Ioo ((1 - c) * y) ((1 + c) * y), ENNReal.ofReal ((t ^ 3)⁻¹) := by
    apply setLIntegral_mono' measurableSet_Ioo
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    have ht0 : 0 < t := by
      have hlow : 0 < (1 - c) * y := mul_pos (by linarith) hy
      exact hlow.trans ht.1
    have ht2 : t ≤ 2 * y := by nlinarith [ht.2]
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) ((inv_le_inv₀ (by positivity) ht0).mpr ht2) 3
  rw [setLIntegral_const, Real.volume_Ioo] at h
  have hlen : (1 + c) * y - (1 - c) * y = 2 * c * y := by ring
  rw [hlen, ← ENNReal.ofReal_mul (by positivity)] at h
  exact h

theorem mobiusCountingBox_volume_lower {c y : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hy : 0 < y)
    (x₁ x₂ : ℝ) : ENNReal.ofReal (c ^ 3) ≤ mobiusCountingVolume (mobiusCountingBox c y x₁ x₂) := by
  rw [mobiusCountingVolume, mobiusCountingBox, Measure.prod_prod, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  have hx₁ : x₁ + c * y - (x₁ - c * y) = 2 * c * y := by ring
  have hx₂ : x₂ + c * y - (x₂ - c * y) = 2 * c * y := by ring
  rw [hx₁, hx₂]
  have h := mul_le_mul_of_nonneg_right (mobiusCountingHeightMeasure_lower hc hc1 hy)
    (show 0 ≤ ENNReal.ofReal (2 * c * y) * ENNReal.ofReal (2 * c * y) from zero_le)
  apply le_trans ?_ h
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : ((2 * y)⁻¹ ^ 3 * (2 * c * y)) * ((2 * c * y) * (2 * c * y)) = c ^ 3 := by
    field_simp
  exact le_of_eq he.symm

/-- A coordinate cusp region with a lower height cutoff and square horizontal sections. -/
def mobiusCountingRegion (A l : ℝ) : Set MobiusCountingCoordinates :=
  {p | l < p.1 ∧ |p.2.1| < A * Real.sqrt p.1 ∧ |p.2.2| < A * Real.sqrt p.1}

theorem mobiusCountingRegion_measurable (A l : ℝ) : MeasurableSet (mobiusCountingRegion A l) := by
  apply IsOpen.measurableSet
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt (continuous_fst.comp continuous_snd).abs
      (continuous_const.mul continuous_fst.sqrt)).inter
      (isOpen_lt (continuous_snd.comp continuous_snd).abs
        (continuous_const.mul continuous_fst.sqrt)))

theorem mobiusCounting_inverse_square_integral {l : ℝ} (hl : 0 < l) :
    (∫⁻ y : ℝ in Ioi l, ENNReal.ofReal ((y ^ 2)⁻¹)) = ENNReal.ofReal l⁻¹ := by
  have he : (∫⁻ y : ℝ in Ioi l, ENNReal.ofReal ((y ^ 2)⁻¹)) =
      ∫⁻ y : ℝ in Ioi l, ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change ENNReal.ofReal ((y ^ 2)⁻¹) = ENNReal.ofReal (y ^ (-2 : ℝ))
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt (hl.trans hy)), Real.rpow_two]
  rw [he, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hl)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hl]
    norm_num [Real.rpow_neg_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (le_of_lt (hl.trans hy)) _

theorem mobiusCountingRegion_section (A : ℝ) (hA : 0 ≤ A) {l y : ℝ} (hl : 0 < l) :
    (volume : Measure (ℝ × ℝ)) (Prod.mk y ⁻¹' mobiusCountingRegion A l) =
      if l < y then ENNReal.ofReal (4 * A ^ 2 * y) else 0 := by
  by_cases hy : l < y
  · have he : Prod.mk y ⁻¹' mobiusCountingRegion A l =
        Ioo (-(A * Real.sqrt y)) (A * Real.sqrt y) ×ˢ
          Ioo (-(A * Real.sqrt y)) (A * Real.sqrt y) := by
      ext p
      simp only [Set.mem_preimage, mobiusCountingRegion, mem_ofPred_eq, hy, true_and,
        Set.mem_prod, Set.mem_Ioo, abs_lt]
    rw [he, ite_eq_left hy, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    have hlen : A * Real.sqrt y - -(A * Real.sqrt y) = 2 * A * Real.sqrt y := by ring
    rw [hlen, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ y)]
  · have he : Prod.mk y ⁻¹' mobiusCountingRegion A l = ∅ := by
      ext p
      simp [mobiusCountingRegion, hy]
    rw [he, measure_empty, ite_eq_right hy]

theorem mobiusCountingRegion_volume (A : ℝ) (hA : 0 ≤ A) {l : ℝ} (hl : 0 < l) :
    mobiusCountingVolume (mobiusCountingRegion A l) = ENNReal.ofReal (4 * A ^ 2 / l) := by
  rw [mobiusCountingVolume, Measure.prod_apply (mobiusCountingRegion_measurable A l)]
  simp_rw [mobiusCountingRegion_section A hA hl]
  rw [mobiusCountingHeightMeasure, lintegral_withDensity_eq_lintegral_mul volume]
  · have he : (fun y : ℝ => ENNReal.ofReal ((y ^ 3)⁻¹) *
        (if l < y then ENNReal.ofReal (4 * A ^ 2 * y) else 0)) =
        (Ioi l).indicator (fun y => ENNReal.ofReal (4 * A ^ 2) * ENNReal.ofReal ((y ^ 2)⁻¹)) := by
      funext y
      by_cases hy : l < y
      · have hy0 : 0 < y := hl.trans hy
        rw [ite_eq_left hy, Set.indicator_of_mem (show y ∈ Ioi l from hy), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      · rw [ite_eq_right hy, mul_zero, Set.indicator_of_notMem (show y ∉ Ioi l from hy)]
    change (∫⁻ y : ℝ, ENNReal.ofReal ((y ^ 3)⁻¹) *
      (if l < y then ENNReal.ofReal (4 * A ^ 2 * y) else 0)) = _
    rw [he, lintegral_indicator measurableSet_Ioi,
      lintegral_const_mul _ (by fun_prop), mobiusCounting_inverse_square_integral hl,
      ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv]
  · fun_prop
  · apply Measurable.ite measurableSet_Ioi
    · fun_prop
    · fun_prop

/-- Actual positive-height quaternion points in the weighted product coordinates. -/
def mobiusCountingH3Coordinates (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : MobiusCountingCoordinates :=
  (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val, ((Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
    q.val).re, (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val).im))

def mobiusCountingSeparation (p q : MobiusCountingCoordinates) : ℝ :=
  ((p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2 + (p.1 - q.1) ^ 2) / (p.1 * q.1)

theorem mobiusCountingSeparation_comm (p q : MobiusCountingCoordinates) :
    mobiusCountingSeparation p q = mobiusCountingSeparation q p := by
  unfold mobiusCountingSeparation
  congr 1 <;> ring

theorem mobiusCounting_quaternion_dist_sq (p q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    dist p q ^ 2 = (p.val.re - q.val.re) ^ 2 +
      (p.val.imI - q.val.imI) ^ 2 + (p.val.imJ - q.val.imJ) ^ 2 := by
  rw [dist_eq_norm]
  change ‖(p.val : Quaternion ℝ) - q.val‖ ^ 2 = _
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  have hp : p.val.imK = 0 := p.property
  have hq : q.val.imK = 0 := q.property
  simp only [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.imI_sub,
    Quaternion.imJ_sub, Quaternion.imK_sub, hp, hq]
  ring

theorem mobiusCountingSeparation_eq_native (p q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusCountingSeparation (mobiusCountingH3Coordinates p) (mobiusCountingH3Coordinates q) =
      Hyperbolic.poincareSeparation (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm p.val)
        (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val) := by
  unfold Hyperbolic.poincareSeparation
  rw [← Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.dist_map,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,
      Mobius.euclideanThreeQuaternion_symm_height,
    Mobius.euclideanThreeQuaternion_symm_height, mobiusCounting_quaternion_dist_sq]
  rfl

theorem mobiusCountingSeparation_smul (f : Mobius.complexMobiusGroup) (p q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusCountingSeparation (mobiusCountingH3Coordinates (f • p)) (mobiusCountingH3Coordinates (f • q)) =
      mobiusCountingSeparation (mobiusCountingH3Coordinates p) (mobiusCountingH3Coordinates q) := by
  have h := Hyperbolic.poincareHalfSpaceHomeomorph_preservesSeparation (Mobius.mobiusRealRepresentative f)
    (Mobius.upperHalfSpaceHyperbolicHomeomorph p) (Mobius.upperHalfSpaceHyperbolicHomeomorph q)
  rw [← Mobius.upperHalfSpaceHyperbolicHomeomorph_smul f p,
    ← Mobius.upperHalfSpaceHyperbolicHomeomorph_smul f q] at h
  rw [mobiusCountingSeparation_eq_native, mobiusCountingSeparation_eq_native]
  exact h

theorem mobiusCounting_norm_sq_separation (f : Mobius.complexMobiusGroup) :
    Mobius.mobiusNormalizedNorm f ^ 2 = 2 + mobiusCountingSeparation
      (mobiusCountingH3Coordinates Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (mobiusCountingH3Coordinates (f
        • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) := by
  rw [mobiusCountingSeparation_eq_native]
  exact Mobius.mobius_norm_sq_separation f

theorem mobiusCountingH3Coordinates_j : mobiusCountingH3Coordinates Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    = (1, (0, 0)) := rfl

/-- The actual norm bound cuts out the quadratic coordinate cusp. -/
theorem mobiusCountingH3_norm_identity (f : Mobius.complexMobiusGroup) :
    let p := mobiusCountingH3Coordinates (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    p.2.1 ^ 2 + p.2.2 ^ 2 + p.1 ^ 2 + 1 = Mobius.mobiusNormalizedNorm f ^ 2 * p.1 := by
  have h := mobiusCounting_norm_sq_separation f
  rw [mobiusCountingH3Coordinates_j] at h
  change Mobius.mobiusNormalizedNorm f ^ 2 = 2 +
    ((0 - (mobiusCountingH3Coordinates (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)).2.1) ^ 2 +
      (0 - (mobiusCountingH3Coordinates (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)).2.2) ^ 2 +
      (1 - (mobiusCountingH3Coordinates (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)).1) ^ 2) /
        (1 * (mobiusCountingH3Coordinates (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)).1) at h
  let p := mobiusCountingH3Coordinates (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
  have hp : 0 < p.1 := (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).property
  change p.2.1 ^ 2 + p.2.2 ^ 2 + p.1 ^ 2 + 1 = _
  change Mobius.mobiusNormalizedNorm f ^ 2 = 2 + ((0 - p.2.1) ^ 2 + (0 - p.2.2) ^ 2 + (1 - p.1) ^ 2) / (1 * p.1) at h
  have hm := congrArg (fun a : ℝ => a * p.1) h
  field_simp at hm
  nlinarith

theorem mobiusCountingNorm_sq_ge_two (f : Mobius.complexMobiusGroup) : 2 ≤ Mobius.mobiusNormalizedNorm f ^ 2 := by
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  rw [Mobius.mobiusNormalizedNorm_specialLinearProjection]
  have h := Mobius.specialLinear_matrixNorm_lower A
  nlinarith [Auxiliary.Algebra.matrixNorm_nonneg (A : Auxiliary.Algebra.ComplexMatrix2), Real.sq_sqrt (by norm_num
    : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg (2 : ℝ)]

/-- Discreteness supplies a uniform positive gap away from the actual j-stabilizer. -/
theorem mobiusCounting_discrete_norm_gap (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ g : H, g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≠
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ →
      ε ≤ Mobius.mobiusNormalizedNorm g.val ^ 2 - 2 := by
  let S : Set H := {g | Mobius.mobiusNormalizedNorm g.val ≤ 2 ∧ g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    ≠ Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ}
  have hs : S.Finite := (Mobius.discreteMobius_norm_sublevel_finite H hd 2).subset (fun _ h => h.1)
  have hp (g : H) (hg : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≠
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) : 0 < Mobius.mobiusNormalizedNorm g.val ^ 2 - 2 := by
    have hne : Mobius.mobiusNormalizedNorm g.val ^ 2 ≠ 2 := fun he => hg ((Mobius.mobius_fixJ_iff_norm g.val).mpr he)
    have hle := mobiusCountingNorm_sq_ge_two g.val
    exact sub_pos.mpr (lt_of_le_of_ne hle hne.symm)
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S (fun g : H => Mobius.mobiusNormalizedNorm g.val ^ 2 - 2) hs hne
    refine ⟨min 1 (Mobius.mobiusNormalizedNorm a.val ^ 2 - 2), lt_min (by norm_num) (hp a ha.2), min_le_left _ _, ?_⟩
    intro g hg
    by_cases hNg : Mobius.mobiusNormalizedNorm g.val ≤ 2
    · exact (min_le_right _ _).trans (hmin g ⟨hNg, hg⟩)
    · have hN := mobiusCountingNorm_positive g.val
      exact (min_le_left _ _).trans (by nlinarith)
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro g hg
    have hNg : ¬Mobius.mobiusNormalizedNorm g.val ≤ 2 := fun he => hne ⟨g, he, hg⟩
    have hN := mobiusCountingNorm_positive g.val
    nlinarith

/-- Distinct actual orbit points have uniform coordinate separation. -/
theorem mobiusCounting_orbit_separated (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g h : H, g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≠ h •
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ →
      ε ≤ mobiusCountingSeparation (mobiusCountingH3Coordinates (g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ))
        (mobiusCountingH3Coordinates (h • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) := by
  obtain ⟨ε, hε, _, hgap⟩ := mobiusCounting_discrete_norm_gap H hd
  refine ⟨ε, hε, fun g h hgh => ?_⟩
  have hn : (h⁻¹ * g) • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≠
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
    intro he
    apply hgh
    simpa only [mul_smul, smul_inv_smul] using congrArg (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      h • q) he
  have hg := hgap (h⁻¹ * g) hn
  have hinv := mobiusCountingSeparation_smul h.val⁻¹ (g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (h •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
  change mobiusCountingSeparation (mobiusCountingH3Coordinates (h⁻¹ • (g •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)))
    (mobiusCountingH3Coordinates (h⁻¹ • (h • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ))) = _ at hinv
  rw [inv_smul_smul, ← mul_smul] at hinv
  rw [← hinv, mobiusCountingSeparation_comm]
  have he := mobiusCounting_norm_sq_separation (h⁻¹ * g).val
  change Mobius.mobiusNormalizedNorm (h⁻¹ * g).val ^ 2 = 2 + mobiusCountingSeparation
    (mobiusCountingH3Coordinates Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (mobiusCountingH3Coordinates ((h⁻¹ * g) • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) at he
  linarith

/-- Intersecting relative boxes force a small normalized coordinate separation. -/
theorem mobiusCountingBox_inter_separation {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (p q w : MobiusCountingCoordinates) (hp : 0 < p.1) (hq : 0 < q.1)
    (hwp : w ∈ mobiusCountingBox c p.1 p.2.1 p.2.2)
    (hwq : w ∈ mobiusCountingBox c q.1 q.2.1 q.2.2) :
    mobiusCountingSeparation p q ≤ 24 * c ^ 2 := by
  have hpy : |w.1 - p.1| < c * p.1 := by
    apply abs_lt.mpr
    constructor <;> nlinarith [hwp.1.1, hwp.1.2]
  have hqy : |w.1 - q.1| < c * q.1 := by
    apply abs_lt.mpr
    constructor <;> nlinarith [hwq.1.1, hwq.1.2]
  have hpx₁ : |p.2.1 - w.2.1| < c * p.1 := by
    rw [abs_sub_comm]
    exact abs_lt.mpr ⟨by linarith [hwp.2.1.1], by linarith [hwp.2.1.2]⟩
  have hqx₁ : |w.2.1 - q.2.1| < c * q.1 :=
    abs_lt.mpr ⟨by linarith [hwq.2.1.1], by linarith [hwq.2.1.2]⟩
  have hpx₂ : |p.2.2 - w.2.2| < c * p.1 := by
    rw [abs_sub_comm]
    exact abs_lt.mpr ⟨by linarith [hwp.2.2.1], by linarith [hwp.2.2.2]⟩
  have hqx₂ : |w.2.2 - q.2.2| < c * q.1 :=
    abs_lt.mpr ⟨by linarith [hwq.2.2.1], by linarith [hwq.2.2.2]⟩
  have hd₁ : |p.2.1 - q.2.1| ≤ c * (p.1 + q.1) := by
    have h := abs_sub_le p.2.1 w.2.1 q.2.1
    linarith
  have hd₂ : |p.2.2 - q.2.2| ≤ c * (p.1 + q.1) := by
    have h := abs_sub_le p.2.2 w.2.2 q.2.2
    linarith
  have hdy : |p.1 - q.1| ≤ c * (p.1 + q.1) := by
    have h := abs_sub_le p.1 w.1 q.1
    rw [abs_sub_comm p.1 w.1] at h
    linarith
  have hp3 : p.1 ≤ 3 * q.1 := by
    nlinarith [hwp.1.1, hwq.1.2, mul_nonneg (sub_nonneg.mpr hc1) hp.le,
      mul_nonneg (sub_nonneg.mpr hc1) hq.le]
  have hq3 : q.1 ≤ 3 * p.1 := by
    nlinarith [hwq.1.1, hwp.1.2, mul_nonneg (sub_nonneg.mpr hc1) hp.le,
      mul_nonneg (sub_nonneg.mpr hc1) hq.le]
  have hsum : (p.1 + q.1) ^ 2 ≤ 8 * (p.1 * q.1) := by
    nlinarith [mul_le_mul_of_nonneg_left hp3 hp.le, mul_le_mul_of_nonneg_left hq3 hq.le]
  have hs₁ : (p.2.1 - q.2.1) ^ 2 ≤ (c * (p.1 + q.1)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hd₁
  have hs₂ : (p.2.2 - q.2.2) ^ 2 ≤ (c * (p.1 + q.1)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hd₂
  have hsy : (p.1 - q.1) ^ 2 ≤ (c * (p.1 + q.1)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdy
  apply (div_le_iff₀ (mul_pos hp hq)).mpr
  calc
    (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2 + (p.1 - q.1) ^ 2
        ≤ 3 * c ^ 2 * (p.1 + q.1) ^ 2 := by nlinarith
    _ ≤ 3 * c ^ 2 * (8 * (p.1 * q.1)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Every relative box about a norm-bounded actual orbit point lies in a quartic-volume cusp region. -/
theorem mobiusCountingBox_subset_region {c t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (ht : 0 < t)
    (p : MobiusCountingCoordinates) (hp : 0 < p.1)
    (hn : p.2.1 ^ 2 + p.2.2 ^ 2 + p.1 ^ 2 + 1 ≤ t ^ 2 * p.1) :
    mobiusCountingBox c p.1 p.2.1 p.2.2 ⊆ mobiusCountingRegion (4 * t) (1 / (4 * t ^ 2)) := by
  intro w hw
  have hwy : p.1 < 2 * w.1 := by
    nlinarith [hw.1.1, mul_nonneg (sub_nonneg.mpr hc1) hp.le]
  have hw0 : 0 < w.1 := by linarith
  have hybig : 1 ≤ t ^ 2 * p.1 := by nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2, sq_nonneg p.1]
  have hysmall : p.1 ≤ t ^ 2 := by nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2]
  have hsqrt : Real.sqrt p.1 ≤ t := by
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg p.1]
  have hsqrtw : Real.sqrt p.1 ≤ 2 * Real.sqrt w.1 := by
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hw0.le, Real.sqrt_nonneg p.1, Real.sqrt_nonneg w.1]
  have hcy : c * p.1 ≤ t * Real.sqrt p.1 := by
    have hcp : c * p.1 ≤ p.1 := mul_le_of_le_one_left hp.le (by linarith)
    have hs := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg p.1)
    nlinarith [Real.sq_sqrt hp.le]
  have hpx₁ : |p.2.1| ≤ t * Real.sqrt p.1 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hp.le]
    nlinarith [sq_nonneg p.2.2, sq_nonneg p.1]
  have hpx₂ : |p.2.2| ≤ t * Real.sqrt p.1 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hp.le]
    nlinarith [sq_nonneg p.2.1, sq_nonneg p.1]
  have hwx₁ : |w.2.1 - p.2.1| < c * p.1 :=
    abs_lt.mpr ⟨by linarith [hw.2.1.1], by linarith [hw.2.1.2]⟩
  have hwx₂ : |w.2.2 - p.2.2| < c * p.1 :=
    abs_lt.mpr ⟨by linarith [hw.2.2.1], by linarith [hw.2.2.2]⟩
  refine ⟨?_, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < 4 * t ^ 2)).mpr
    have hm := mul_lt_mul_of_pos_left hwy (sq_pos_of_pos ht)
    nlinarith
  · have hb := norm_le_insert w.2.1 p.2.1
    have ha : |w.2.1| ≤ |p.2.1| + |w.2.1 - p.2.1| := by
      simpa only [Real.norm_eq_abs, abs_sub_comm p.2.1 w.2.1] using norm_le_norm_add_norm_sub p.2.1 w.2.1
    have hm := mul_le_mul_of_nonneg_left hsqrtw (by positivity : 0 ≤ 2 * t)
    nlinarith
  · have ha : |w.2.2| ≤ |p.2.2| + |w.2.2 - p.2.2| := by
      simpa only [Real.norm_eq_abs, abs_sub_comm p.2.2 w.2.2] using norm_le_norm_add_norm_sub p.2.2 w.2.2
    have hm := mul_le_mul_of_nonneg_left hsqrtw (by positivity : 0 ≤ 2 * t)
    nlinarith

/-- Quantitative counting of any finite separated family in the norm cusp. -/
theorem mobiusCounting_separated_card_bound {ι : Type*} [Fintype ι]
    (p : ι → MobiusCountingCoordinates) {c t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (ht : 0 < t)
    (hp : ∀ i, 0 < (p i).1)
    (hn : ∀ i, (p i).2.1 ^ 2 + (p i).2.2 ^ 2 + (p i).1 ^ 2 + 1 ≤ t ^ 2 * (p i).1)
    (hsep : ∀ i j, i ≠ j → 24 * c ^ 2 < mobiusCountingSeparation (p i) (p j)) :
    (Fintype.card ι : ℝ) ≤ (256 / c ^ 3) * t ^ 4 := by
  classical
  let B (i : ι) := mobiusCountingBox c (p i).1 (p i).2.1 (p i).2.2
  have hdis : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro w hwi hwj
    exact (not_le_of_gt (hsep i j hij))
      (mobiusCountingBox_inter_separation hc hc1 (p i) (p j) w (hp i) (hp j) hwi hwj)
  have hsub : (⋃ i, B i) ⊆ mobiusCountingRegion (4 * t) (1 / (4 * t ^ 2)) := by
    intro w hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    exact mobiusCountingBox_subset_region hc hc1 ht (p i) (hp i) (hn i) hi
  have hmeas (i : ι) : MeasurableSet (B i) := mobiusCountingBox_measurable _ _ _ _
  have hmeasure : (∑ i, mobiusCountingVolume (B i)) ≤ ENNReal.ofReal (256 * t ^ 4) := by
    have hUnion : mobiusCountingVolume (⋃ i, B i) = ∑' i : ι, mobiusCountingVolume (B i) := measure_iUnion hdis hmeas
    rw [tsum_fintype] at hUnion
    rw [← hUnion]
    have h := measure_mono (μ := mobiusCountingVolume) hsub
    rw [mobiusCountingRegion_volume (4 * t) (by positivity) (by positivity)] at h
    have he : 4 * (4 * t) ^ 2 / (1 / (4 * t ^ 2)) = 256 * t ^ 4 := by
      field_simp
      ring
    rwa [he] at h
  have hcard : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (c ^ 3) ≤ ENNReal.ofReal (256 * t ^ 4) := by
    calc
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (c ^ 3) = ∑ _ : ι, ENNReal.ofReal (c ^ 3) := by simp
      _ ≤ ∑ i, mobiusCountingVolume (B i) := Finset.sum_le_sum fun i _ => mobiusCountingBox_volume_lower hc hc1
        (hp i) _ _
      _ ≤ _ := hmeasure
  have he : ENNReal.ofReal ((Fintype.card ι : ℝ) * c ^ 3) ≤ ENNReal.ofReal (256 * t ^ 4) := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hcard
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 256 * t ^ 4)).mp he
  have heq : (256 / c ^ 3) * t ^ 4 = (256 * t ^ 4) / c ^ 3 := by ring
  rw [heq]
  exact (le_div_iff₀ (pow_pos hc 3)).mpr hr

/-- A finite family of group elements has at most stabilizer-cardinality many elements per orbit point. -/
theorem mobiusCounting_card_le_orbit_mul_stabilizer {G X : Type*} [Group G] [MulAction G X]
    (s : Set G) (hs : s.Finite) (x : X) (hK : (MulAction.stabilizer G x : Set G).Finite) :
    Nat.card s ≤ Nat.card (Set.range (fun g : s => g.val • x)) * Nat.card (MulAction.stabilizer G x) := by
  classical
  let Y := Set.range (fun g : s => g.val • x)
  let rep (y : Y) : s := Classical.choose y.property
  have hrep (y : Y) : (rep y).val • x = y.val := Classical.choose_spec y.property
  let φ (g : s) : Y × MulAction.stabilizer G x :=
    let y : Y := ⟨g.val • x, ⟨g, rfl⟩⟩
    (y, ⟨(rep y).val⁻¹ * g.val, by
      change ((rep y).val⁻¹ * g.val) • x = x
      rw [mul_smul, show g.val • x = (rep y).val • x from (hrep y).symm,
        inv_smul_smul]⟩)
  have hinj : Function.Injective φ := by
    intro a b he
    have hfirst : (φ a).1 = (φ b).1 := congrArg Prod.fst he
    have hsecond : (φ a).2.val = (φ b).2.val := congrArg (fun p : Y × MulAction.stabilizer G x => p.2.val) he
    change (rep (φ a).1).val⁻¹ * a.val = (rep (φ b).1).val⁻¹ * b.val at hsecond
    rw [hfirst] at hsecond
    exact Subtype.ext (mul_left_cancel hsecond)
  let : Finite s := hs.to_subtype
  let : Finite Y := (Set.finite_range (fun g : s => g.val • x)).to_subtype
  let : Finite (MulAction.stabilizer G x) := hK.to_subtype
  have h := Nat.card_le_card_of_injective φ hinj
  simpa only [Nat.card_prod] using h

/-- The actual finite normalized-norm counting function of the discrete subgroup. -/
def mobiusNormCountingFunction (H : Subgroup Mobius.complexMobiusGroup) (t : ℝ) : ℕ :=
  Nat.card {g : H // Mobius.mobiusNormalizedNorm g.val ≤ t}

/-- The exact quartic counting bound for every actual discrete Mobius subgroup. -/
theorem normCountingFunction_le_quartic (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → (mobiusNormCountingFunction H t : ℝ) ≤ C * t ^ 4 := by
  classical
  obtain ⟨ε, hε, hsep⟩ := mobiusCounting_orbit_separated H hd
  let c : ℝ := min (1 / 4) (ε / 100)
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hcsmall : 24 * c ^ 2 < ε := by
    have hquarter : c ≤ 1 / 4 := min_le_left _ _
    have heps : c ≤ ε / 100 := min_le_right _ _
    nlinarith
  let K := MulAction.stabilizer H Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  have hK : (K : Set H).Finite := (discreteMobius_isDiscontinuous_H3 H hd).finite_stabilizer
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  let C : ℝ := (256 / c ^ 3) * ((Nat.card K : ℝ) + 1)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let S : Set H := {g | Mobius.mobiusNormalizedNorm g.val ≤ t}
  have hS : S.Finite := Mobius.discreteMobius_norm_sublevel_finite H hd t
  let : Finite S := hS.to_subtype
  let Y := Set.range (fun g : S => g.val • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
  let : Finite Y := (Set.finite_range (fun g : S => g.val • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)).to_subtype
  let : Fintype Y := Fintype.ofFinite Y
  have hY : (Fintype.card Y : ℝ) ≤ (256 / c ^ 3) * t ^ 4 := by
    apply mobiusCounting_separated_card_bound (fun y : Y => mobiusCountingH3Coordinates y.val) hc hc1 ht0
    · intro y
      exact y.val.property
    · intro y
      obtain ⟨g, he⟩ := y.property
      have hnorm := mobiusCountingH3_norm_identity g.val.val
      have hN : Mobius.mobiusNormalizedNorm g.val.val ≤ t := g.property
      have hNsq : Mobius.mobiusNormalizedNorm g.val.val ^ 2 ≤ t ^ 2 := by
        nlinarith [mobiusCountingNorm_positive g.val.val]
      have hm := mul_le_mul_of_nonneg_right hNsq (le_of_lt ((g.val •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).property))
      change (mobiusCountingH3Coordinates y.val).2.1 ^ 2 + (mobiusCountingH3Coordinates y.val).2.2 ^ 2 +
        (mobiusCountingH3Coordinates y.val).1 ^ 2 + 1 ≤ _
      rw [← he]
      exact hnorm.le.trans hm
    · intro y z hyz
      obtain ⟨g, hg⟩ := y.property
      obtain ⟨h, hh⟩ := z.property
      change g.val • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = y.val at hg
      change h.val • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = z.val at hh
      have hne : g.val • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≠ h.val •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
        intro he
        exact hyz (Subtype.ext ((hg.symm.trans he).trans hh))
      have hs := hsep g.val h.val hne
      rw [hg, hh] at hs
      exact hcsmall.trans_le hs
  have hcard := mobiusCounting_card_le_orbit_mul_stabilizer S hS Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ hK
  have hreal : (mobiusNormCountingFunction H t : ℝ) ≤ (Fintype.card Y : ℝ) * (Nat.card K : ℝ) := by
    change (Nat.card S : ℝ) ≤ (Fintype.card Y : ℝ) * (Nat.card K : ℝ)
    have he : Nat.card Y = Fintype.card Y := Nat.card_eq_fintype_card
    rw [he] at hcard
    exact_mod_cast hcard
  calc
    (mobiusNormCountingFunction H t : ℝ) ≤ (Fintype.card Y : ℝ) * (Nat.card K : ℝ) := hreal
    _ ≤ ((256 / c ^ 3) * t ^ 4) * (Nat.card K : ℝ) := mul_le_mul_of_nonneg_right hY (Nat.cast_nonneg _)
    _ ≤ C * t ^ 4 := by
      dsimp only [C]
      nlinarith [pow_nonneg ht0.le 4, div_pos (by norm_num : (0 : ℝ) < 256) (pow_pos hc 3)]

/-- In the standard asymptotic notation. -/
theorem normCountingFunction_isBigO_quartic (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) :
    Asymptotics.IsBigO atTop (fun t : ℝ => (mobiusNormCountingFunction H t : ℝ)) (fun t => t ^ 4) := by
  obtain ⟨C, _, hC⟩ := normCountingFunction_le_quartic H hd
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  change |(mobiusNormCountingFunction H t : ℝ)| ≤ C * |t ^ 4|
  rw [abs_of_nonneg (Nat.cast_nonneg (mobiusNormCountingFunction H t) : (0 : ℝ) ≤ _),
    abs_of_nonneg (pow_nonneg (lt_of_lt_of_le zero_lt_one ht).le 4)]
  exact hC t ht

end
end LowDimensionalTopology.Geometry.DiscreteGroups
