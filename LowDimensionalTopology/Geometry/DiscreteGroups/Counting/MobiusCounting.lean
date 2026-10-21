/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.MobiusPackings
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteMobiusGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusLocalDomains
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.OpenPos
@[expose] public section
open Set Filter MeasureTheory Matrix
open scoped Topology OnePoint ENNReal NNReal
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
noncomputable section
local instance mobiusCountingChordalMetric : MetricSpace Mobius.ExtendedComplex := Mobius.complexChordalMetricSpace
local instance mobiusCountingSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex := borel
    Mobius.ExtendedComplex
local instance mobiusCountingSphereBorelSpace : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- An injective sequence in a discrete Möbius subgroup has unbounded normalized norm. -/
theorem mobius_discrete_norm_divergence (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (u : ℕ → H) (hu : Function.Injective u) :
    Tendsto (fun n => Mobius.mobiusNormalizedNorm (u n).val) atTop atTop :=
  Mobius.discreteMobius_injective_sequence_norm_tendsto H hd u hu

/-- The genuine two-dimensional Hausdorff measure of the chordal sphere. -/
def mobiusChordalArea : Measure Mobius.ExtendedComplex := μH[2]

theorem mobiusCounting_coe_lipschitz : LipschitzWith 2 (OnePoint.some : ℂ → Mobius.ExtendedComplex) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change Mobius.complexChordalDist z w ≤ (2 : ℝ) * dist z w
  rw [Mobius.complexChordalDist_coe_coe, dist_eq_norm]
  apply div_le_self (by positivity)
  have hz : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by
    nlinarith [sq_nonneg ‖z‖])
  have hw : 1 ≤ Real.sqrt (1 + ‖w‖ ^ 2) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by
    nlinarith [sq_nonneg ‖w‖])
  nlinarith

/-- The inverse global chordal distortion estimate, with the source matrix norm. -/
theorem mobius_chordal_antilipschitz_bound (f : Mobius.complexMobiusGroup) (z w : Mobius.ExtendedComplex) :
    Mobius.complexChordalDist z w ≤ Mobius.mobiusNormalizedNorm f ^ 2 *
      Mobius.complexChordalDist (f.val z) (f.val w) := by
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  obtain ⟨v, hv⟩ := Mobius.complexCompactPairPoint_surjective z
  obtain ⟨u, hu⟩ := Mobius.complexCompactPairPoint_surjective w
  rw [← hv, ← hu, Mobius.mobiusNormalizedNorm_specialLinearProjection]
  change Mobius.complexChordalDist (Mobius.complexProjectivePoint v.val) (Mobius.complexProjectivePoint u.val) ≤
    Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * Mobius.complexChordalDist
      ((Mobius.mobiusSpecialLinearProjection A).val (Mobius.complexProjectivePoint v.val))
      ((Mobius.mobiusSpecialLinearProjection A).val (Mobius.complexProjectivePoint u.val))
  rw [Mobius.invariantDisc_specialLinear_action]
  have hd := Mobius.fractionalLinear_homogeneous_chordal_sq (Matrix.SpecialLinearGroup.toGL A)
    v.val u.val (Mobius.complexCompactPair_ne_zero v) (Mobius.complexCompactPair_ne_zero u)
  have h0 := Mobius.complexChordalDist_projective_sq v.val u.val
    (Mobius.complexCompactPair_ne_zero v) (Mobius.complexCompactPair_ne_zero u)
  have hvb := Mobius.complexVectorQuadratic_mulVec_le (A : Auxiliary.Algebra.ComplexMatrix2) v.val
  have hub := Mobius.complexVectorQuadratic_mulVec_le (A : Auxiliary.Algebra.ComplexMatrix2) u.val
  have hvp : 0 < Mobius.complexVectorQuadratic (Matrix.SpecialLinearGroup.toGL A • v.val) :=
    Mobius.complexVectorQuadratic_pos ((smul_ne_zero_iff_ne _).mpr (Mobius.complexCompactPair_ne_zero v))
  have hup : 0 < Mobius.complexVectorQuadratic (Matrix.SpecialLinearGroup.toGL A • u.val) :=
    Mobius.complexVectorQuadratic_pos ((smul_ne_zero_iff_ne _).mpr (Mobius.complexCompactPair_ne_zero u))
  change Mobius.complexVectorQuadratic (Matrix.SpecialLinearGroup.toGL A • v.val) ≤
    Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * Mobius.complexVectorQuadratic v.val at hvb
  change Mobius.complexVectorQuadratic (Matrix.SpecialLinearGroup.toGL A • u.val) ≤
    Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * Mobius.complexVectorQuadratic u.val at hub
  rw [v.property, mul_one] at hvb
  rw [u.property, mul_one] at hub
  change Mobius.complexChordalDist (Mobius.complexProjectivePoint v.val) (Mobius.complexProjectivePoint u.val) ^ 2 =
    4 * ‖v.val 0 * u.val 1 - v.val 1 * u.val 0‖ ^ 2 /
      (Mobius.complexVectorQuadratic v.val * Mobius.complexVectorQuadratic u.val) at h0
  rw [v.property, u.property, one_mul, div_one] at h0
  have hdet : ‖((Matrix.SpecialLinearGroup.toGL A : Mobius.FractionalLinearMatrix) :
    Auxiliary.Algebra.ComplexMatrix2).det‖ = 1 := by
    change ‖(A : Auxiliary.Algebra.ComplexMatrix2).det‖ = 1
    rw [A.det_coe, norm_one]
  rw [hdet, one_pow, mul_one] at hd
  have he := (eq_div_iff (mul_pos hvp hup).ne').mp hd
  have hprod := mul_le_mul hvb hub (le_of_lt hup) (sq_nonneg (Auxiliary.Algebra.matrixNorm (A :
    Auxiliary.Algebra.ComplexMatrix2)))
  have hineq := mul_le_mul_of_nonneg_left hprod
    (sq_nonneg (Mobius.complexChordalDist (Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A)
      (Mobius.complexProjectivePoint v.val))
      (Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A) (Mobius.complexProjectivePoint u.val))))
  apply (sq_le_sq₀ (Mobius.complexChordalDist_nonneg _ _)
    (mul_nonneg (sq_nonneg _) (Mobius.complexChordalDist_nonneg _ _))).mp
  calc
    Mobius.complexChordalDist (Mobius.complexProjectivePoint v.val) (Mobius.complexProjectivePoint u.val) ^ 2
        = 4 * ‖v.val 0 * u.val 1 - v.val 1 * u.val 0‖ ^ 2 := h0
    _ ≤ Mobius.complexChordalDist (Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A)
      (Mobius.complexProjectivePoint v.val))
      (Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A) (Mobius.complexProjectivePoint u.val)) ^ 2 *
      (Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * Auxiliary.Algebra.matrixNorm (A :
        Auxiliary.Algebra.ComplexMatrix2) ^ 2) := he.symm.trans_le hineq
    _ = _ := by ring

theorem mobiusCounting_antilipschitz (f : Mobius.complexMobiusGroup) :
    AntilipschitzWith ⟨Mobius.mobiusNormalizedNorm f ^ 2, sq_nonneg _⟩ f.val := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  exact mobius_chordal_antilipschitz_bound f z w

theorem mobiusCounting_lipschitz (f : Mobius.complexMobiusGroup) :
    LipschitzWith ⟨Mobius.mobiusNormalizedNorm f⁻¹ ^ 2, sq_nonneg _⟩ f.val := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := mobius_chordal_antilipschitz_bound f⁻¹ (f.val z) (f.val w)
  change Mobius.complexChordalDist (f.val z) (f.val w) ≤ Mobius.mobiusNormalizedNorm f⁻¹ ^ 2 *
    Mobius.complexChordalDist z w
  change Mobius.complexChordalDist (f.val z) (f.val w) ≤ Mobius.mobiusNormalizedNorm f⁻¹ ^ 2 *
    Mobius.complexChordalDist (f.val.symm (f.val z)) (f.val.symm (f.val w)) at h
  simpa only [Equiv.symm_apply_apply] using h

theorem mobiusChordalArea_image_upper (f : Mobius.complexMobiusGroup) (s : Set Mobius.ExtendedComplex) :
    mobiusChordalArea (f.val '' s) ≤
      (ENNReal.ofNNReal ⟨Mobius.mobiusNormalizedNorm f⁻¹ ^ 2, sq_nonneg _⟩) ^ 2 * mobiusChordalArea s := by
  have h := (mobiusCounting_lipschitz f).hausdorffMeasure_image_le (d := 2) (by norm_num) s
  simpa only [ENNReal.rpow_two, mobiusChordalArea] using h

theorem mobiusChordalArea_finite : mobiusChordalArea Set.univ < ⊤ := by
  let B : Set ℂ := Metric.closedBall 0 1
  let C : Set Mobius.ExtendedComplex := OnePoint.some '' B
  have hB : (μH[2] : Measure ℂ) B < ⊤ := by
    have h := (isCompact_closedBall (0 : ℂ) (1 : ℝ)).measure_lt_top
      (μ := (μH[(Module.finrank ℝ ℂ)] : Measure ℂ))
    simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using h
  have hC : mobiusChordalArea C < ⊤ := by
    have h := mobiusCounting_coe_lipschitz.hausdorffMeasure_image_le (d := 2) (by norm_num) B
    apply lt_of_le_of_lt h
    rw [ENNReal.rpow_two]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hB
  have hRC : mobiusChordalArea (mobiusReciprocal.val '' C) < ⊤ :=
    (mobiusChordalArea_image_upper mobiusReciprocal C).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hC)
  have hcover : (Set.univ : Set Mobius.ExtendedComplex) ⊆ C ∪ mobiusReciprocal.val '' C := by
    intro z _
    induction z using OnePoint.rec with
    | infty =>
      right
      exact ⟨(0 : ℂ), ⟨0, by simp [B], rfl⟩, mobiusReciprocal_zero⟩
    | coe z =>
      by_cases hz : ‖z‖ ≤ 1
      · left
        exact ⟨z, by simpa [B] using hz, rfl⟩
      · right
        have hn : z ≠ 0 := by intro he; apply hz; simp [he]
        refine ⟨(z⁻¹ : ℂ), ⟨z⁻¹, ?_, rfl⟩, ?_⟩
        · simpa [B, norm_inv] using (inv_le_one₀ (norm_pos_iff.mpr hn)).mpr (le_of_lt (lt_of_not_ge hz))
        · rw [mobiusReciprocal_coe z⁻¹ (inv_ne_zero hn), inv_inv]
  exact (measure_mono hcover).trans_lt
    ((measure_union_le C (mobiusReciprocal.val '' C)).trans_lt (ENNReal.add_lt_top.mpr ⟨hC, hRC⟩))

def mobiusCountingFiniteCoordinate (z : Mobius.ExtendedComplex) : ℂ := z.elim 0 id

theorem mobiusCountingFiniteCoordinate_coe (z : ℂ) : mobiusCountingFiniteCoordinate z = z := rfl

/-- A bounded finite chart has a quantitative inverse chordal estimate. -/
theorem mobiusCounting_chart_inverse_bound {R : ℝ} (hR : 0 ≤ R) (z w : ℂ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    dist z w ≤ ((1 + R ^ 2) / 2) * Mobius.complexChordalDist z w := by
  have h0 := Mobius.complexChordalDist_coe_coe_sq z w
  have hden : 0 < (1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2) := by positivity
  have he := (eq_div_iff hden.ne').mp h0
  have hz2 : 1 + ‖z‖ ^ 2 ≤ 1 + R ^ 2 := by nlinarith [norm_nonneg z]
  have hw2 : 1 + ‖w‖ ^ 2 ≤ 1 + R ^ 2 := by nlinarith [norm_nonneg w]
  have hp := mul_le_mul hz2 hw2 (by positivity : 0 ≤ 1 + ‖w‖ ^ 2) (by positivity : 0 ≤ 1 + R ^ 2)
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (Mobius.complexChordalDist z w))
  have hs : (2 * ‖z - w‖) ^ 2 ≤ ((1 + R ^ 2) * Mobius.complexChordalDist z w) ^ 2 := by
    calc
      (2 * ‖z - w‖) ^ 2 = 4 * ‖z - w‖ ^ 2 := by ring
      _ ≤ Mobius.complexChordalDist z w ^ 2 * ((1 + R ^ 2) * (1 + R ^ 2)) := he.symm.trans_le hm
      _ = _ := by ring
  have h := (sq_le_sq₀ (by positivity) (mul_nonneg (by positivity) (Mobius.complexChordalDist_nonneg z w))).mp hs
  rw [dist_eq_norm]
  nlinarith

theorem mobiusCountingFiniteCoordinate_lipschitzOn {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith ⟨(1 + R ^ 2) / 2, by positivity⟩ mobiusCountingFiniteCoordinate
      (OnePoint.some '' Metric.closedBall (0 : ℂ) R) := by
  apply LipschitzOnWith.of_dist_le_mul
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  change dist z w ≤ ((1 + R ^ 2) / 2) * Mobius.complexChordalDist z w
  apply mobiusCounting_chart_inverse_bound hR z w
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hw

theorem mobiusChordalArea_finite_chart_positive {z : ℂ} {r : ℝ} (hr : 0 < r) :
    0 < mobiusChordalArea (OnePoint.some '' Metric.ball z r) := by
  let R : ℝ := ‖z‖ + r
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hsub : OnePoint.some '' Metric.ball z r ⊆ OnePoint.some '' Metric.closedBall (0 : ℂ) R := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_norm_add_const_of_dist_le (le_of_lt (Metric.mem_ball.mp hw))

  have hL := (mobiusCountingFiniteCoordinate_lipschitzOn hR).mono hsub
  have h := hL.hausdorffMeasure_image_le (d := 2) (by norm_num)
  have he : mobiusCountingFiniteCoordinate '' (OnePoint.some '' Metric.ball z r) = Metric.ball z r := by
    rw [Set.image_image]
    simp only [mobiusCountingFiniteCoordinate_coe, Set.image_id']
  rw [he] at h
  have hp : 0 < (μH[2] : Measure ℂ) (Metric.ball z r) := by
    have hpos := (Metric.isOpen_ball : IsOpen (Metric.ball z r)).measure_pos (μ := (μH[(Module.finrank ℝ ℂ)] :
      Measure ℂ))
      (Metric.nonempty_ball.mpr hr)
    simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hpos
  exact (ENNReal.mul_pos_iff.mp (hp.trans_le h)).2

/-- Every nonempty open sphere set has positive actual two-dimensional chordal measure. -/
theorem mobiusChordalArea_open_positive (U : Set Mobius.ExtendedComplex) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < mobiusChordalArea U := by
  obtain ⟨w, hwU, z, rfl⟩ := OnePoint.denseRange_coe.inter_open_nonempty U hU hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.preimage OnePoint.continuous_coe) z hwU
  exact (mobiusChordalArea_finite_chart_positive hr).trans_le (measure_mono (Set.image_subset_iff.mpr hball))

local instance mobiusCountingAreaNullSingleton : NullSingletonClass mobiusChordalArea :=
  Measure.nullSingletonClass_hausdorff Mobius.ExtendedComplex (by norm_num : (0 : ℝ) < 2)

/-- A nonidentity actual Mobius map has finitely many boundary fixed points. -/
theorem mobiusCounting_fixedPoints_finite (f : Mobius.complexMobiusGroup) (hf : f ≠ 1) :
    (Function.fixedPoints f.val).Finite := by
  rcases Mobius.mobius_nonidentity_fixedPoint_dichotomy f hf with ⟨a, ha⟩ | ⟨a, b, _, hab⟩
  · apply (Set.finite_singleton a).subset
    intro z hz
    exact (ha z).mp hz
  · apply (Set.toFinite ({a, b} : Set Mobius.ExtendedComplex)).subset
    intro z hz
    exact (Set.mem_insert_iff).mpr ((hab z).mp hz)

/-- In an open ordinary set, avoid all nonidentity fixed points to obtain a free point. -/
theorem mobiusCounting_ordinary_free_point (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hne : (mobiusOrdinarySet H).Nonempty) :
    ∃ z ∈ mobiusOrdinarySet H, ∀ g : H, g • z = z → g = 1 := by
  let : Countable H := Mobius.discreteMobius_countable H hd
  let E : Set Mobius.ExtendedComplex := ⋃ g : {g : H // g ≠ 1}, Function.fixedPoints g.val.val.val
  have hE : mobiusChordalArea E = 0 := by
    apply measure_iUnion_null
    intro g
    exact (mobiusCounting_fixedPoints_finite g.val.val
      (fun he => g.property (Subtype.ext he))).countable.measure_zero mobiusChordalArea
  have hnot : ¬mobiusOrdinarySet H ⊆ E := by
    intro h
    have hle := measure_mono (μ := mobiusChordalArea) h
    rw [hE] at hle
    exact (not_le_of_gt (mobiusChordalArea_open_positive _ (mobiusOrdinarySet_isOpen H) hne)) hle
  obtain ⟨z, hz, hzE⟩ := Set.not_subset.mp hnot
  refine ⟨z, hz, fun g hg => ?_⟩
  by_contra hn
  exact hzE (Set.mem_iUnion.mpr ⟨⟨g, hn⟩, hg⟩)

/-- A nonempty ordinary set contains a genuine nonempty open packing, without a stabilizer hypothesis. -/
theorem mobiusCounting_ordinary_openPacking (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H)
    (hne : (mobiusOrdinarySet H).Nonempty) :
    ∃ D : Set Mobius.ExtendedComplex, IsOpen D ∧ D.Nonempty ∧ D ⊆ mobiusOrdinarySet H ∧ IsMobiusPacking H D := by
  obtain ⟨z, hz, hfree⟩ := mobiusCounting_ordinary_free_point H hd hne
  obtain ⟨q, r, _, _, hD, hzD, hcl, _, hsep⟩ := mobius_discontinuous_roundDisc H
    (mobiusOrdinarySet H) (mobiusOrdinarySet_isOpen H)
    (fun g _ hz => mobiusOrdinarySet_invariant H g hz)
    (mobius_ordinary_discontinuous H hH hd) z hz
  refine ⟨mobiusNormalizedDisc q r, hD.isOpen, ⟨z, hzD⟩, subset_closure.trans hcl, ?_⟩
  intro g hg
  exact (hsep g).2 (fun he => hg (hfree g he))

theorem mobiusCountingNorm_positive (f : Mobius.complexMobiusGroup) : 0 < Mobius.mobiusNormalizedNorm f := by
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  rw [Mobius.mobiusNormalizedNorm_specialLinearProjection]
  exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).trans_le (Mobius.specialLinear_matrixNorm_lower A)

def mobiusCountingSquaredNorm (f : Mobius.complexMobiusGroup) : ℝ≥0 :=
  ⟨Mobius.mobiusNormalizedNorm f ^ 2, sq_nonneg _⟩

def mobiusCountingCriticalWeight (f : Mobius.complexMobiusGroup) : ℝ≥0 :=
  (mobiusCountingSquaredNorm f ^ 2)⁻¹

theorem mobiusCountingCriticalWeight_coe (f : Mobius.complexMobiusGroup) :
    (mobiusCountingCriticalWeight f : ℝ) = (Mobius.mobiusNormalizedNorm f ^ 4)⁻¹ := by
  rw [mobiusCountingCriticalWeight, NNReal.coe_inv]
  change ((Mobius.mobiusNormalizedNorm f ^ 2) ^ 2)⁻¹ = (Mobius.mobiusNormalizedNorm f ^ 4)⁻¹
  congr 1
  ring

/-- Actual Mobius images have the critical fourth-power chordal-area lower bound. -/
theorem mobiusChordalArea_image_lower (f : Mobius.complexMobiusGroup) (D : Set Mobius.ExtendedComplex) :
    (mobiusCountingCriticalWeight f : ℝ≥0∞) * mobiusChordalArea D ≤ mobiusChordalArea (f.val '' D) := by
  have h := (mobiusCounting_antilipschitz f).le_hausdorffMeasure_image (d := 2) (by norm_num) D
  rw [ENNReal.rpow_two] at h
  have hK : mobiusCountingSquaredNorm f ≠ 0 := by
    intro he
    have hr := congrArg (fun k : ℝ≥0 => (k : ℝ)) he
    change Mobius.mobiusNormalizedNorm f ^ 2 = 0 at hr
    exact (pow_ne_zero 2 (mobiusCountingNorm_positive f).ne') hr
  have hcancel : (mobiusCountingCriticalWeight f : ℝ≥0∞) *
      (mobiusCountingSquaredNorm f : ℝ≥0∞) ^ 2 = 1 := by
    rw [mobiusCountingCriticalWeight, ENNReal.coe_inv (pow_ne_zero 2 hK), ENNReal.coe_pow]
    exact ENNReal.inv_mul_cancel (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hK))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  calc
    (mobiusCountingCriticalWeight f : ℝ≥0∞) * mobiusChordalArea D
        ≤ (mobiusCountingCriticalWeight f : ℝ≥0∞) *
          ((mobiusCountingSquaredNorm f : ℝ≥0∞) ^ 2 * mobiusChordalArea (f.val '' D)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = mobiusChordalArea (f.val '' D) := by rw [← mul_assoc, hcancel, one_mul]

/-- A nonempty open packing yields summability of the actual normalized fourth-power weights. -/
theorem mobiusCounting_critical_summable_of_openPacking (H : Subgroup Mobius.complexMobiusGroup)
    (D : Set Mobius.ExtendedComplex) (hD : IsOpen D) (hne : D.Nonempty) (hp : IsMobiusPacking H D) :
    Summable (fun g : H => (Mobius.mobiusNormalizedNorm g.val ^ 4)⁻¹) := by
  have hd : Mobius.IsDiscreteMobiusSubgroup H := isMobiusDiscontinuousOn_open_discrete H
    (mobiusSaturation H D) (mobiusSaturation_isOpen H hD)
    (hne.mono (subset_mobiusSaturation H D)) (mobius_openPacking_saturation_discontinuous H D hD hp)
  let : Countable H := Mobius.discreteMobius_countable H hd
  have hmeas (g : H) : MeasurableSet (g.val.val '' D) :=
    ((Mobius.mobiusBoundaryHomeomorph g.val).isOpenMap _ hD).measurableSet
  have hsum : (∑' g : H, mobiusChordalArea (g.val.val '' D)) < ⊤ := by
    rw [← measure_iUnion (fun g h hgh => DiscreteGroups.IsMobiusPacking.disjoint_translates hp g h hgh) hmeas]
    exact (measure_mono (Set.subset_univ _)).trans_lt mobiusChordalArea_finite
  have hbound : (∑' g : H, (mobiusCountingCriticalWeight g.val : ℝ≥0∞)) * mobiusChordalArea D < ⊤ := by
    rw [← ENNReal.tsum_mul_right]
    exact (ENNReal.tsum_le_tsum (fun (g : H) => mobiusChordalArea_image_lower g.val D)).trans_lt hsum
  have hfinite : (∑' g : H, (mobiusCountingCriticalWeight g.val : ℝ≥0∞)) ≠ ⊤ := by
    intro he
    rw [he, ENNReal.top_mul (ne_of_gt (mobiusChordalArea_open_positive D hD hne))] at hbound
    exact (lt_irrefl ⊤) hbound
  have hs := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hfinite
  simpa only [mobiusCountingCriticalWeight_coe] using hs

/-- Critical convergence for discrete non-elementary groups with a nonempty ordinary set. -/
theorem summable_normalizedNorm_inv_four_of_nonElementary_ordinarySet (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H) (hd : Mobius.IsDiscreteMobiusSubgroup H)
    (hne : (mobiusOrdinarySet H).Nonempty) :
    Summable (fun g : H => (Mobius.mobiusNormalizedNorm g.val ^ 4)⁻¹) := by
  obtain ⟨D, hD, hneD, _, hp⟩ := mobiusCounting_ordinary_openPacking H hH hd hne
  exact mobiusCounting_critical_summable_of_openPacking H D hD hneD hp

end
end LowDimensionalTopology.Geometry.DiscreteGroups
