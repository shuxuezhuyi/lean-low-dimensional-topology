module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments

/-!
# Actual equivariant geodesics retain their matrix period

A complete unit-speed geodesic with actual deck period `A` lies on the actual
axis of `A`. Its positive period is the full translation length of that same
matrix, including proper powers. Two such oriented parametrizations differ
only by a shift of their actual real parameter.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Unit-speed parametrizations of the same complete metric line differ only
by a parameter shift, with a possible reversal of orientation. -/
private theorem isometries_real_same_range
    {E : Type*} [MetricSpace E] {γ δ : ℝ → E}
    (hγ : Isometry γ) (hδ : Isometry δ) (hrange : range γ = range δ) :
    ∃ c : ℝ, (∀ t : ℝ, γ t = δ (t + c)) ∨ (∀ t : ℝ, γ t = δ (c - t)) := by
  obtain ⟨c, hc⟩ : γ 0 ∈ range δ := hrange ▸ mem_range_self 0
  obtain ⟨d, hd⟩ : γ 1 ∈ range δ := hrange ▸ mem_range_self 1
  have hdc : |d - c| = 1 := by
    simpa only [hd, hc, hγ.dist_eq, Real.dist_eq, sub_zero, abs_one] using
      (hδ.dist_eq d c).symm
  have hdcSq : (d - c) ^ 2 = (1 : ℝ) ^ 2 := by
    exact (sq_abs (d - c)).symm.trans (congrArg (fun x : ℝ => x ^ 2) hdc)
  have hdistances (t r : ℝ) (hr : δ r = γ t) :
      (r - c) ^ 2 = t ^ 2 ∧ (r - d) ^ 2 = (t - 1) ^ 2 := by
    have h0 : |r - c| = |t| := by
      simpa only [hr, hc, hγ.dist_eq, Real.dist_eq, sub_zero] using
        (hδ.dist_eq r c).symm
    have h1 : |r - d| = |t - 1| := by
      simpa only [hr, hd, hγ.dist_eq, Real.dist_eq] using (hδ.dist_eq r d).symm
    constructor
    · exact (sq_abs (r - c)).symm.trans
        ((congrArg (fun x : ℝ => x ^ 2) h0).trans (sq_abs t))
    · exact (sq_abs (r - d)).symm.trans
        ((congrArg (fun x : ℝ => x ^ 2) h1).trans (sq_abs (t - 1)))
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdcSq with hforward | hreverse
  · refine ⟨c, Or.inl ?_⟩
    intro t
    obtain ⟨r, hr⟩ : γ t ∈ range δ := hrange ▸ mem_range_self t
    obtain ⟨h0, h1⟩ := hdistances t r hr
    have hd' : d = c + 1 := by linarith
    rw [hd'] at h1
    have hr' : r = t + c := by nlinarith [h0, h1]
    exact hr.symm.trans (congrArg δ hr')
  · refine ⟨c, Or.inr ?_⟩
    intro t
    obtain ⟨r, hr⟩ : γ t ∈ range δ := hrange ▸ mem_range_self t
    obtain ⟨h0, h1⟩ := hdistances t r hr
    have hd' : d = c - 1 := by linarith
    rw [hd'] at h1
    have hr' : r = c - t := by nlinarith [h0, h1]
    exact hr.symm.trans (congrArg δ hr')

/-- The actual equivariant period determines both the complete axis and its
full translation length; no primitive stabilizer generator is chosen. -/
theorem equivariant_hGeodesic_axis_and_period
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ) (T : ℝ)
    (hperiod : ∀ t : ℝ, γ (t + T) = A • γ t) :
    range γ = (hHyperbolicAxis A hA ht).carrier ∧
      |T| = hTranslationLength (hSLIsometry A) := by
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hγ.2
  have hinv : (A • · : ℍ → ℍ) '' L.carrier = L.carrier := by
    rw [hL]
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t + T, hperiod t⟩
    · rintro ⟨t, rfl⟩
      refine ⟨γ (t - T), mem_range_self _, ?_⟩
      simpa only [sub_add_cancel] using (hperiod (t - T)).symm
  have haxis : range γ = (hHyperbolicAxis A hA ht).carrier :=
    hL.symm.trans (congrArg HalfPlaneLine.carrier
      (hHyperbolicAxis_unique_invariant A hA ht L hinv))
  refine ⟨haxis, ?_⟩
  have hmem : γ 0 ∈ (hHyperbolicAxis A hA ht).carrier := haxis ▸ mem_range_self 0
  have hzero : γ T = A • γ 0 := by simpa only [zero_add] using hperiod 0
  calc
    |T| = dist (γ 0) (γ T) := by rw [hγ.1.dist_eq, Real.dist_eq, zero_sub, abs_neg]
    _ = dist (γ 0) (A • γ 0) := by rw [hzero]
    _ = hTranslationLength (hSLIsometry A) :=
      (hHyperbolic_translation_minimum A hA ht (γ 0)).mpr hmem

/-- Two complete unit-speed geodesic lifts with the same actual matrix and
positive periods have the same full period and differ only by a parameter
shift. This preserves every proper-power traversal. -/
theorem equivariant_hGeodesic_unique_up_to_shift
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    {γ δ : ℝ → ℍ} (hγ : IsHGeodesicParam γ) (hδ : IsHGeodesicParam δ)
    {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hγperiod : ∀ t : ℝ, γ (t + T) = A • γ t)
    (hδperiod : ∀ t : ℝ, δ (t + U) = A • δ t) :
    T = U ∧ T = hTranslationLength (hSLIsometry A) ∧
      ∃ c : ℝ, ∀ t : ℝ, γ t = δ (t + c) := by
  obtain ⟨hγaxis, hγlen⟩ := equivariant_hGeodesic_axis_and_period A hA ht hγ T hγperiod
  obtain ⟨hδaxis, hδlen⟩ := equivariant_hGeodesic_axis_and_period A hA ht hδ U hδperiod
  have hlenT : T = hTranslationLength (hSLIsometry A) := by
    simpa only [abs_of_pos hT] using hγlen
  have hlenU : U = hTranslationLength (hSLIsometry A) := by
    simpa only [abs_of_pos hU] using hδlen
  refine ⟨hlenT.trans hlenU.symm, hlenT, ?_⟩
  obtain ⟨c, hshift | hreverse⟩ := isometries_real_same_range hγ.1 hδ.1
    (hγaxis.trans hδaxis.symm)
  · exact ⟨c, hshift⟩
  · have hbase : γ 0 = δ c := by simpa only [sub_zero] using hreverse 0
    have hbad : δ (c - T) = δ (c + U) := by
      calc
        δ (c - T) = γ T := (hreverse T).symm
        _ = A • γ 0 := by simpa only [zero_add] using hγperiod 0
        _ = A • δ c := by rw [hbase]
        _ = δ (c + U) := (hδperiod c).symm
    have heq := hδ.1.injective hbad
    exfalso
    linarith

end LowDimensionalTopology.Geometry.Hyperbolic
