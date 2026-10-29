module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RectifiableNormalizedLength
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Convex.Basic

/-!
# Actual weighted subpaths of a globally Lipschitz parametrization

The affine subpaths are genuine source curves. Their weighted lengths are the
literal restrictions of the original weighted derivative integral. No
injectivity, finite density, or absence of repeated traversal is assumed.
-/

public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LowDimensionalTopology.Geometry

/-- A genuine Lipschitz curve traversing precisely the original parameter interval. -/
@[expose] def lipschitzAffineSubpath {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (a b : ℝ) : LiZhongQC.LRCurve where
  toFun := F ∘ AffineMap.lineMap a b
  locallyLipschitzOn :=
    (hF.comp (lipschitzWith_lineMap a b)).locallyLipschitz.locallyLipschitzOn

/-- The actual weighted integral of a subpath, allowing a constant affine clock. -/
theorem lipschitzAffineSubpath_rhoLength {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {a b : ℝ} (hab : a ≤ b)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    (lipschitzAffineSubpath hF a b).rhoLength ρ =
      ∫⁻ r in Ioo a b, ρ (F r) * ‖deriv F r‖ₑ := by
  have hmono : Monotone (AffineMap.lineMap a b : ℝ → ℝ) := by
    intro x y hxy
    simp only [AffineMap.lineMap_apply_ring']
    simpa only [add_comm a] using
      add_le_add_right (mul_le_mul_of_nonneg_right hxy (sub_nonneg.mpr hab)) a
  have hchange := LiZhongQC.s26v_b_reparam_lintegral zero_le_one hmono
    (lipschitzWith_lineMap a b).continuous
    hF.lipschitzOnWith.absolutelyContinuousOnInterval
    (hF.comp (lipschitzWith_lineMap a b)).lipschitzOnWith.absolutelyContinuousOnInterval
    (hρ.comp hF.continuous.measurable)
  simpa only [lipschitzAffineSubpath, LiZhongQC.LRCurve.rhoLength,
    AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, Function.comp_apply]
    using hchange

theorem lipschitzAffineSubpath_isPathIn {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {D : Set ℂ}
    (hD : F '' Icc 0 1 ⊆ D) {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    LiZhongQC.IsPathIn D (F a) (F b) (lipschitzAffineSubpath hF a b) := by
  refine ⟨⟨_, (hF.comp (lipschitzWith_lineMap a b)).lipschitzOnWith⟩, ?_, ?_, ?_⟩
  · change F (AffineMap.lineMap a b 0) = F a
    rw [AffineMap.lineMap_apply_zero]
  · change F (AffineMap.lineMap a b 1) = F b
    rw [AffineMap.lineMap_apply_one]
  · rintro _ ⟨t, ht, rfl⟩
    exact hD ⟨_, (convex_Icc (0 : ℝ) 1).lineMap_mem ha hb ht, rfl⟩

/-- The source infimum is bounded by the actual weighted length of this subpath. -/
theorem metricDist_le_lipschitz_subinterval {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {D : Set ℂ}
    (hD : F '' Icc 0 1 ⊆ D) {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : a ≤ b)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    LiZhongQC.metricDist D ρ (F a) (F b) ≤
      ∫⁻ r in Ioo a b, ρ (F r) * ‖deriv F r‖ₑ := by
  calc
    LiZhongQC.metricDist D ρ (F a) (F b) ≤
        (lipschitzAffineSubpath hF a b).rhoLength ρ :=
      iInf₂_le (lipschitzAffineSubpath hF a b)
        (lipschitzAffineSubpath_isPathIn hF hD ha hb)
    _ = _ := lipschitzAffineSubpath_rhoLength hF hab hρ

/-- Exact additivity at a parameter value, including infinite weighted lengths. -/
theorem lintegral_Ioo_split_unit (f : ℝ → ℝ≥0∞) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∫⁻ r in Ioo 0 t, f r) + (∫⁻ r in Ioo t 1, f r) =
      ∫⁻ r in Ioo 0 1, f r := by
  calc
    (∫⁻ r in Ioo 0 t, f r) + (∫⁻ r in Ioo t 1, f r) =
        (∫⁻ r in Ioc 0 t, f r) + (∫⁻ r in Ioc t 1, f r) := by
      rw [setLIntegral_congr (f := f) (Ioo_ae_eq_Ioc (μ := volume) (a := 0) (b := t)),
        setLIntegral_congr (f := f) (Ioo_ae_eq_Ioc (μ := volume) (a := t) (b := 1))]
    _ = ∫⁻ r in Ioc 0 t ∪ Ioc t 1, f r :=
      (lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)).symm
    _ = ∫⁻ r in Ioc 0 1, f r := by rw [Ioc_union_Ioc_eq_Ioc ht.1 ht.2]
    _ = ∫⁻ r in Ioo 0 1, f r :=
      (setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume))).symm

/-- Every intermediate point gives a true pair of source distance lower bounds. -/
theorem metricDist_add_le_lipschitz_length {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {D : Set ℂ}
    (hD : F '' Icc 0 1 ⊆ D) {t : ℝ} (ht : t ∈ Icc 0 1)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    LiZhongQC.metricDist D ρ (F 0) (F t) +
        LiZhongQC.metricDist D ρ (F t) (F 1) ≤
      ∫⁻ r in Ioo 0 1, ρ (F r) * ‖deriv F r‖ₑ := by
  calc
    LiZhongQC.metricDist D ρ (F 0) (F t) +
        LiZhongQC.metricDist D ρ (F t) (F 1) ≤
        (∫⁻ r in Ioo 0 t, ρ (F r) * ‖deriv F r‖ₑ) +
          (∫⁻ r in Ioo t 1, ρ (F r) * ‖deriv F r‖ₑ) :=
      add_le_add
        (metricDist_le_lipschitz_subinterval hF hD ⟨le_rfl, zero_le_one⟩ ht ht.1 hρ)
        (metricDist_le_lipschitz_subinterval hF hD ht ⟨zero_le_one, le_rfl⟩ ht.2 hρ)
    _ = _ := lintegral_Ioo_split_unit _ ht

end LowDimensionalTopology.Geometry
