/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
@[expose] public section
open Set MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc ENNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem triangleArea_integrableOn_inv_sq_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi c) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hc
  simpa [Real.rpow_neg_natCast,one_div] using h

theorem triangleArea_integral_inv_sq_Ioi {c : ℝ} (hc : 0 < c) :
    (∫ y : ℝ in Ioi c, 1 / y ^ 2) = 1 / c := by
  have h := integral_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hc
  norm_num [Real.rpow_neg_natCast,Real.rpow_neg_one,one_div] at h ⊢
  exact h

theorem triangleArea_lintegral_inv_sq_Ioi {c : ℝ} (hc : 0 < c) :
    (∫⁻ y : ℝ in Ioi c, ENNReal.ofReal (1 / y ^ 2)) = ENNReal.ofReal (1 / c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (triangleArea_integrableOn_inv_sq_Ioi hc)
    (ae_of_all _ (fun y => div_nonneg zero_le_one (sq_nonneg y))),triangleArea_integral_inv_sq_Ioi hc]

theorem triangleArea_integral_inv_sqrt {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ x in a..b, 1 / Real.sqrt (1-x^2)) = Real.arcsin b - Real.arcsin a := by
  have hpos {x : ℝ} (hx : x ∈ Icc a b) : 0 < 1-x^2 := by
    have hleft : 0 < 1+x := by linarith only [ha,hx.1]
    have hright : 0 < 1-x := by linarith only [hb,hx.2]
    nlinarith only [mul_pos hleft hright]
  have hcont : ContinuousOn (fun x : ℝ => 1 / Real.sqrt (1-x^2)) (Icc a b) :=
    continuousOn_const.div ((continuousOn_const.sub (continuousOn_id.pow 2)).sqrt)
      (fun x hx => (Real.sqrt_pos.mpr (hpos hx)).ne')
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hcont.intervalIntegrable_of_Icc hab)
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact Real.hasDerivAt_arcsin (by linarith only [ha,hx.1]) (by linarith only [hb,hx.2])

/-- A genuine upper-half-plane region above a graph over a prescribed horizontal set. -/
def halfPlaneAboveGraph (f : ℝ → ℝ) (s : Set ℝ) : Set ℍ :=
  {z | z.re ∈ s ∧ f z.re < z.im}

theorem halfPlaneAboveGraph_complex_image (f : ℝ → ℝ) (s : Set ℝ)
    (hpos : ∀ x ∈ s, 0 < f x) :
    ((↑) : ℍ → ℂ) '' halfPlaneAboveGraph f s = {z : ℂ | z.re ∈ s ∧ f z.re < z.im} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact hw
  · intro hz
    exact ⟨⟨z,lt_trans (hpos z.re hz.1) hz.2⟩,hz,rfl⟩

/-- Tonelli's theorem applied to the actual density-defined upper-half-plane area. -/
theorem halfPlaneAboveGraph_volume (f : ℝ → ℝ) (s : Set ℝ) (hf : Measurable f)
    (hs : MeasurableSet s) (hpos : ∀ x ∈ s, 0 < f x) :
    volume (halfPlaneAboveGraph f s) = ∫⁻ x in s, ENNReal.ofReal (1 / f x) := by
  let A : Set (ℝ × ℝ) := {p | p.1 ∈ s ∧ f p.1 < p.2}
  let W : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (1 / p.2^2)
  have hA : MeasurableSet A :=
    (hs.preimage measurable_fst).inter (measurableSet_lt (hf.comp measurable_fst) measurable_snd)
  have hW : Measurable W := by dsimp only [W]; fun_prop
  rw [UpperHalfPlane.volume_eq_lintegral,halfPlaneAboveGraph_complex_image f s hpos]
  simp_rw [halfPlane_area_weight]
  calc
    _ = ∫⁻ p in A, W p := by
      simpa only [Complex.measurableEquivRealProd_apply,Set.preimage_ofPred_eq,W,A] using
        Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
          Complex.measurableEquivRealProd.measurableEmbedding W A
    _ = ∫⁻ x in s, ∫⁻ y in Ioi (f x), ENNReal.ofReal (1 / y^2) := by
      rw [← lintegral_indicator hA,Measure.volume_eq_prod,lintegral_prod _ (hW.indicator hA).aemeasurable,
        ← lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]
        rw [← lintegral_indicator measurableSet_Ioi]
        apply lintegral_congr
        intro y
        by_cases hy : f x < y <;> simp [A,W,hx,hy]
      · rw [Set.indicator_of_notMem hx]
        calc
          _ = ∫⁻ _y : ℝ, (0 : ℝ≥0∞) := lintegral_congr (fun y => by
            have hn : (x,y) ∉ A := fun h => hx h.1
            exact Set.indicator_of_notMem hn W)
          _ = 0 := lintegral_zero
    _ = _ := setLIntegral_congr_fun hs (fun x hx => triangleArea_lintegral_inv_sq_Ioi (hpos x hx))

/-- Actual hyperbolic area above the unit semicircle over a compact interior horizontal interval. -/
theorem halfPlaneAboveUnitCircle_volume {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) (hb : b < 1) :
    volume (halfPlaneAboveGraph (fun x => Real.sqrt (1-x^2)) (Ioo a b)) =
      ENNReal.ofReal (Real.arcsin b - Real.arcsin a) := by
  have hpos {x : ℝ} (hx : x ∈ Icc a b) : 0 < 1-x^2 := by
    have hleft : 0 < 1+x := by linarith only [ha,hx.1]
    have hright : 0 < 1-x := by linarith only [hb,hx.2]
    nlinarith only [mul_pos hleft hright]
  have hcont : ContinuousOn (fun x : ℝ => 1 / Real.sqrt (1-x^2)) (Icc a b) :=
    continuousOn_const.div ((continuousOn_const.sub (continuousOn_id.pow 2)).sqrt)
      (fun x hx => (Real.sqrt_pos.mpr (hpos hx)).ne')
  rw [halfPlaneAboveGraph_volume _ _ (by fun_prop) measurableSet_Ioo
    (fun x hx => Real.sqrt_pos.mpr (hpos ⟨hx.1.le,hx.2.le⟩))]
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (ae_of_all _ (fun x => div_nonneg zero_le_one (Real.sqrt_nonneg _)))]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hab,
    triangleArea_integral_inv_sqrt ha hab hb]

/-- The singularities at the two ideal ends of the semicircle are integrable. -/
theorem triangleArea_intervalIntegrable_inv_sqrt_closed {a b : ℝ}
    (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (1-x^2)) volume a b := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    Real.continuous_arcsin.continuousOn
  · intro x hx
    simp only [min_eq_left hab,max_eq_right hab] at hx
    exact Real.hasDerivAt_arcsin (by linarith only [ha,hx.1]) (by linarith only [hb,hx.2])
  · intro x _
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem triangleArea_integral_inv_sqrt_closed {a b : ℝ}
    (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ x in a..b, 1 / Real.sqrt (1-x^2)) = Real.arcsin b - Real.arcsin a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    Real.continuous_arcsin.continuousOn _ (triangleArea_intervalIntegrable_inv_sqrt_closed ha hab hb)
  intro x hx
  exact Real.hasDerivAt_arcsin (by linarith only [ha,hx.1]) (by linarith only [hb,hx.2])

/-- The true weighted area formula allows either or both ends to be ideal. -/
theorem halfPlaneAboveUnitCircle_volume_closed {a b : ℝ}
    (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    volume (halfPlaneAboveGraph (fun x => Real.sqrt (1-x^2)) (Ioo a b)) =
      ENNReal.ofReal (Real.arcsin b - Real.arcsin a) := by
  have hpos {x : ℝ} (hx : x ∈ Ioo a b) : 0 < 1-x^2 := by
    have hleft : 0 < 1+x := by linarith only [ha,hx.1]
    have hright : 0 < 1-x := by linarith only [hb,hx.2]
    nlinarith only [mul_pos hleft hright]
  have hi : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (1-x^2)) (Ioo a b) :=
    (triangleArea_intervalIntegrable_inv_sqrt_closed ha hab hb).1.mono_set Ioo_subset_Ioc_self
  rw [halfPlaneAboveGraph_volume _ _ (by fun_prop) measurableSet_Ioo
    (fun x hx => Real.sqrt_pos.mpr (hpos hx))]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun x => div_nonneg zero_le_one (Real.sqrt_nonneg _)))]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hab,
    triangleArea_integral_inv_sqrt_closed ha hab hb]

end
end LowDimensionalTopology.Geometry.Hyperbolic
