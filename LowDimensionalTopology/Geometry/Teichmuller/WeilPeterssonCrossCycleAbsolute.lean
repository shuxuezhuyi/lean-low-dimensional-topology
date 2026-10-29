module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonWeightedFlatRow
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCauchySquareComposition
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCrossKernelCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Absolute estimates for the concrete six-cross cycle
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Pointwise ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open LiZhongQC GammaMeasurableBeltrami

private instance crossCycleFlat_sigmaFinite : SigmaFinite flatArea := by
  apply SigmaFinite.of_map flatArea UpperHalfPlane.measurableEmbedding_coe.measurable.aemeasurable
  rw [map_flat_coe]
  infer_instance

abbrev CrossCycleFive := ((ℍ × ℍ) × ℍ) × (ℍ × ℍ)

private abbrev cycleTwoArea : Measure (ℍ × ℍ) := flatArea.prod flatArea

private abbrev cycleThreeArea : Measure ((ℍ × ℍ) × ℍ) := Measure.prod cycleTwoArea flatArea

abbrev cycleFiveArea : Measure CrossCycleFive :=
  Measure.prod ((flatArea.prod flatArea).prod flatArea) (flatArea.prod flatArea)

private def cycleWeight (x : ℍ) : ℝ := x.im ^ (-(1 / 2 : ℝ))

def cycleMass : ℝ := Real.pi * ∫ t : ℝ in Ioi 0, t ^ (-(1 / 2 : ℝ)) / (1 + t)

def cycleKernel (x y : ℍ) : ℝ := ‖cauchySquare (conj (x : ℂ)) y‖

private def cycleEdge (x y : ℍ) : ℝ := cycleKernel x y * cycleWeight y / cycleWeight x

private theorem cycleWeight_pos (x : ℍ) : 0 < cycleWeight x :=
  Real.rpow_pos_of_pos x.im_pos _

private theorem cycleMass_nonneg : 0 ≤ cycleMass := by
  refine mul_nonneg Real.pi_pos.le (setIntegral_nonneg measurableSet_Ioi ?_)
  intro t ht
  have ht0 : 0 < t := ht
  exact div_nonneg (Real.rpow_nonneg ht0.le _) (by linarith)

theorem cycleKernel_symm (x y : ℍ) : cycleKernel x y = cycleKernel y x := by
  have h : cauchySquare (conj (x : ℂ)) y = conj (cauchySquare (conj (y : ℂ)) x) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
    congr 1
    ring
  exact (congrArg norm h).trans (Complex.norm_conj _)

private theorem cycleEdge_nonneg (x y : ℍ) : 0 ≤ cycleEdge x y :=
  div_nonneg (mul_nonneg (norm_nonneg _) (cycleWeight_pos y).le) (cycleWeight_pos x).le

private theorem cycleEdge_row (x : ℍ) :
    Integrable (cycleEdge x) flatArea ∧ (∫ y : ℍ, cycleEdge x y ∂flatArea) = cycleMass := by
  have h := cauchySquare_weighted_absolute_flatArea x
  refine ⟨h.1.div_const (cycleWeight x), ?_⟩
  rw [show cycleEdge x = (fun y : ℍ =>
    cycleKernel x y * cycleWeight y / cycleWeight x) from rfl, integral_div]
  change (∫ y : ℍ, ‖cauchySquare (conj (x : ℂ)) y‖ *
    y.im ^ (-(1 / 2 : ℝ)) ∂flatArea) / cycleWeight x = _
  rw [h.2]
  exact mul_div_cancel_right₀ cycleMass (cycleWeight_pos x).ne'

private def cycleTwoPath (x : ℍ) (p : ℍ × ℍ) : ℝ := cycleEdge x p.1 * cycleEdge p.1 p.2

private theorem cycleTwoPath_nonneg (x : ℍ) (p : ℍ × ℍ) : 0 ≤ cycleTwoPath x p :=
  mul_nonneg (cycleEdge_nonneg _ _) (cycleEdge_nonneg _ _)

private theorem cycleTwoPath_mass (x : ℍ) :
    Integrable (cycleTwoPath x) cycleTwoArea ∧
      (∫ p : ℍ × ℍ, cycleTwoPath x p ∂cycleTwoArea) = cycleMass ^ 2 := by
  have hm : Measurable (cycleTwoPath x) := by
    unfold cycleTwoPath cycleEdge cycleKernel cycleWeight cauchySquare
    fun_prop
  have hrow (y : ℍ) : Integrable (fun z : ℍ => cycleTwoPath x (y, z)) flatArea := by
    simpa only [cycleTwoPath] using (cycleEdge_row y).1.const_mul (cycleEdge x y)
  have he (y : ℍ) : (∫ z : ℍ, cycleTwoPath x (y, z) ∂flatArea) =
      cycleEdge x y * cycleMass := by
    rw [show (fun z : ℍ => cycleTwoPath x (y, z)) =
      (fun z : ℍ => cycleEdge x y * cycleEdge y z) from rfl,
      integral_const_mul, (cycleEdge_row y).2]
  have hi : Integrable (cycleTwoPath x) cycleTwoArea := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨Eventually.of_forall hrow, ?_⟩
    simp_rw [Real.norm_of_nonneg (cycleTwoPath_nonneg x _), he]
    exact (cycleEdge_row x).1.mul_const cycleMass
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  simp_rw [he]
  rw [integral_mul_const, (cycleEdge_row x).2]
  ring

private theorem cycleAnchor_square (x : ℍ) :
    Integrable (fun y : ℍ => cycleKernel x y ^ 2) flatArea := by
  have hplane := (cauchySquare_composition x x).1.re
  have hi : IntegrableOn (fun y : ℂ => ‖cauchySquare (conj y) x‖ ^ 2) upperHalf := by
    refine hplane.congr_fun (fun y _ => ?_) isOpen_upperHalf.measurableSet
    have hc : cauchySquare y (conj (x : ℂ)) = conj (cauchySquare (conj y) x) := by
      simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
    change (cauchySquare (conj y) x * cauchySquare y (conj (x : ℂ))).re = _
    rw [hc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  change Integrable _ ((volume : Measure ℂ).restrict upperHalf) at hi
  rw [← map_flat_coe] at hi
  have hflat := UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp hi
  refine hflat.congr (Eventually.of_forall fun y => ?_)
  change ‖cauchySquare (conj (y : ℂ)) x‖ ^ 2 = cycleKernel x y ^ 2
  rw [show ‖cauchySquare (conj (y : ℂ)) x‖ = cycleKernel y x from rfl,
    cycleKernel_symm y x]

private def cycleAnchorThree (x : ℍ) (p : (ℍ × ℍ) × ℍ) : ℝ :=
  cycleKernel x p.1.1 ^ 2 * cycleTwoPath p.1.1 (p.1.2, p.2)

private theorem cycleAnchorThree_nonneg (x : ℍ) (p : (ℍ × ℍ) × ℍ) :
    0 ≤ cycleAnchorThree x p :=
  mul_nonneg (sq_nonneg _) (cycleTwoPath_nonneg _ _)

private theorem cycleAnchorThree_mass (x : ℍ) :
    Integrable (cycleAnchorThree x) cycleThreeArea ∧
      (∫ p : (ℍ × ℍ) × ℍ, cycleAnchorThree x p ∂cycleThreeArea) =
        cycleMass ^ 2 * ∫ y : ℍ, cycleKernel x y ^ 2 ∂flatArea := by
  let f : ℍ × (ℍ × ℍ) → ℝ := fun p => cycleKernel x p.1 ^ 2 * cycleTwoPath p.1 p.2
  have hm : Measurable f := by
    unfold f cycleTwoPath cycleEdge cycleKernel cycleWeight cauchySquare
    fun_prop
  have hr (y : ℍ) : Integrable (fun p : ℍ × ℍ => f (y, p)) cycleTwoArea := by
    simpa only [f] using (cycleTwoPath_mass y).1.const_mul (cycleKernel x y ^ 2)
  have he (y : ℍ) : (∫ p : ℍ × ℍ, f (y, p) ∂cycleTwoArea) =
      cycleKernel x y ^ 2 * cycleMass ^ 2 := by
    rw [show (fun p : ℍ × ℍ => f (y, p)) =
      (fun p : ℍ × ℍ => cycleKernel x y ^ 2 * cycleTwoPath y p) from rfl,
      integral_const_mul, (cycleTwoPath_mass y).2]
  have hi : Integrable f (flatArea.prod cycleTwoArea) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨Eventually.of_forall hr, ?_⟩
    have hpos (y : ℍ) (p : ℍ × ℍ) : 0 ≤ f (y, p) := by
      exact mul_nonneg (sq_nonneg _) (cycleTwoPath_nonneg _ _)
    simp_rw [Real.norm_of_nonneg (hpos _ _), he]
    exact (cycleAnchor_square x).mul_const _
  have hassoc := measurePreserving_prodAssoc flatArea flatArea flatArea
  refine ⟨hassoc.integrable_comp_of_integrable hi, ?_⟩
  calc
    _ = ∫ p : ℍ × (ℍ × ℍ), f p ∂(flatArea.prod cycleTwoArea) :=
      hassoc.integral_comp' f
    _ = ∫ y : ℍ, cycleKernel x y ^ 2 * cycleMass ^ 2 ∂flatArea := by
      rw [integral_prod _ hi]
      exact integral_congr_ae (Eventually.of_forall he)
    _ = _ := by rw [integral_mul_const]; ring

private def cycleEndpointSquare (x : ℍ) (p : CrossCycleFive) : ℝ :=
  cycleAnchorThree x p.1 * cycleTwoPath p.1.2 p.2

private theorem cycleEndpointSquare_nonneg (x : ℍ) (p : CrossCycleFive) :
    0 ≤ cycleEndpointSquare x p :=
  mul_nonneg (cycleAnchorThree_nonneg _ _) (cycleTwoPath_nonneg _ _)

private theorem cycleEndpointSquare_mass (x : ℍ) :
    Integrable (cycleEndpointSquare x) cycleFiveArea ∧
      (∫ p : CrossCycleFive, cycleEndpointSquare x p ∂cycleFiveArea) =
        cycleMass ^ 4 * ∫ y : ℍ, cycleKernel x y ^ 2 ∂flatArea := by
  have hm : Measurable (cycleEndpointSquare x) := by
    unfold cycleEndpointSquare cycleAnchorThree cycleTwoPath cycleEdge cycleKernel cycleWeight
    unfold cauchySquare
    fun_prop
  have hr (p : (ℍ × ℍ) × ℍ) :
      Integrable (fun q : ℍ × ℍ => cycleEndpointSquare x (p, q)) cycleTwoArea := by
    simpa only [cycleEndpointSquare] using
      (cycleTwoPath_mass p.2).1.const_mul (cycleAnchorThree x p)
  have he (p : (ℍ × ℍ) × ℍ) :
      (∫ q : ℍ × ℍ, cycleEndpointSquare x (p, q) ∂cycleTwoArea) =
        cycleAnchorThree x p * cycleMass ^ 2 := by
    rw [show (fun q : ℍ × ℍ => cycleEndpointSquare x (p, q)) =
      (fun q : ℍ × ℍ => cycleAnchorThree x p * cycleTwoPath p.2 q) from rfl,
      integral_const_mul, (cycleTwoPath_mass p.2).2]
  have hi : Integrable (cycleEndpointSquare x) cycleFiveArea := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨Eventually.of_forall hr, ?_⟩
    simp_rw [Real.norm_of_nonneg (cycleEndpointSquare_nonneg x _), he]
    exact (cycleAnchorThree_mass x).1.mul_const _
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  simp_rw [he]
  rw [integral_mul_const, (cycleAnchorThree_mass x).2]
  ring

private def cycleReverse : CrossCycleFive ≃ᵐ CrossCycleFive :=
  (MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl (ℍ × ℍ)).prodCongr MeasurableEquiv.prodComm)).trans
    (MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℍ)).trans
        (MeasurableEquiv.prodAssoc.trans
          (((MeasurableEquiv.refl (ℍ × ℍ)).prodCongr MeasurableEquiv.prodComm).trans
            (MeasurableEquiv.prodAssoc.symm.trans
              ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℍ)).prodCongr
                MeasurableEquiv.prodComm))))))

private theorem cycleReverse_apply (p : CrossCycleFive) :
    cycleReverse p = (((p.2.2, p.2.1), p.1.2), (p.1.1.2, p.1.1.1)) := rfl

private theorem cycleReverse_measurePreserving :
    MeasurePreserving cycleReverse cycleFiveArea cycleFiveArea := by
  have h₁ := measurePreserving_prodAssoc cycleTwoArea flatArea cycleTwoArea
  have h₂ := (MeasurePreserving.id cycleTwoArea).prod
    (Measure.measurePreserving_swap (μ := flatArea) (ν := cycleTwoArea))
  have h₃ := (measurePreserving_prodAssoc cycleTwoArea cycleTwoArea flatArea).symm
  have h₄ := (Measure.measurePreserving_swap (μ := cycleTwoArea) (ν := cycleTwoArea)).prod
    (MeasurePreserving.id flatArea)
  have h₅ := measurePreserving_prodAssoc cycleTwoArea cycleTwoArea flatArea
  have h₆ := (MeasurePreserving.id cycleTwoArea).prod
    (Measure.measurePreserving_swap (μ := cycleTwoArea) (ν := flatArea))
  have h₇ := (measurePreserving_prodAssoc cycleTwoArea flatArea cycleTwoArea).symm
  have h₈ := ((Measure.measurePreserving_swap (μ := flatArea) (ν := flatArea)).prod
    (MeasurePreserving.id flatArea)).prod
      (Measure.measurePreserving_swap (μ := flatArea) (ν := flatArea))
  exact h₈.comp (h₇.comp (h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))))))

def cycleSixNorm (x : ℍ) (p : CrossCycleFive) : ℝ :=
  cycleKernel x p.1.1.1 * cycleKernel p.1.1.1 p.1.1.2 *
    cycleKernel p.1.1.2 p.1.2 * cycleKernel p.1.2 p.2.1 *
      cycleKernel p.2.1 p.2.2 * cycleKernel p.2.2 x

private theorem cycleSixNorm_factor (x : ℍ) (p : CrossCycleFive) :
    cycleSixNorm x p =
      Real.sqrt (cycleEndpointSquare x p) * Real.sqrt (cycleEndpointSquare x (cycleReverse p)) := by
  have hpos : 0 ≤ cycleSixNorm x p := by
    unfold cycleSixNorm cycleKernel
    positivity
  apply (sq_eq_sq₀ hpos (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt (cycleEndpointSquare_nonneg _ _),
    Real.sq_sqrt (cycleEndpointSquare_nonneg _ _), cycleReverse_apply]
  simp only [cycleSixNorm, cycleEndpointSquare, cycleAnchorThree, cycleTwoPath, cycleEdge]
  rw [cycleKernel_symm x p.2.2, cycleKernel_symm p.2.2 p.2.1,
    cycleKernel_symm p.2.1 p.1.2, cycleKernel_symm p.1.2 p.1.1.2,
    cycleKernel_symm p.1.1.2 p.1.1.1]
  field_simp [(cycleWeight_pos p.1.1.1).ne', (cycleWeight_pos p.1.1.2).ne',
    (cycleWeight_pos p.1.2).ne', (cycleWeight_pos p.2.1).ne', (cycleWeight_pos p.2.2).ne']

theorem cycleSixNorm_integrable (x : ℍ) :
    Integrable (cycleSixNorm x) cycleFiveArea ∧
      (∫ p : CrossCycleFive, cycleSixNorm x p ∂cycleFiveArea) ≤
        cycleMass ^ 4 * ∫ y : ℍ, cycleKernel x y ^ 2 ∂flatArea := by
  let a : CrossCycleFive → ℝ := fun p => Real.sqrt (cycleEndpointSquare x p)
  let b : CrossCycleFive → ℝ := fun p => a (cycleReverse p)
  have hm : Measurable a := by
    unfold a cycleEndpointSquare cycleAnchorThree cycleTwoPath cycleEdge cycleKernel cycleWeight
    unfold cauchySquare
    fun_prop
  have hasq (p : CrossCycleFive) : a p ^ 2 = cycleEndpointSquare x p :=
    Real.sq_sqrt (cycleEndpointSquare_nonneg _ _)
  have ha : MemLp a 2 cycleFiveArea := by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    exact (cycleEndpointSquare_mass x).1.congr
      (Eventually.of_forall fun p => (hasq p).symm)
  have hb : MemLp b 2 cycleFiveArea :=
    ha.comp_measurePreserving cycleReverse_measurePreserving
  have hf (p : CrossCycleFive) : cycleSixNorm x p = a p * b p := cycleSixNorm_factor x p
  refine ⟨(ha.integrable_mul hb).congr (Eventually.of_forall fun p => (hf p).symm), ?_⟩
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hcs := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp a (ENNReal.ofReal (2 : ℝ)) cycleFiveArea from htwo ▸ ha)
    (show MemLp b (ENNReal.ofReal (2 : ℝ)) cycleFiveArea from htwo ▸ hb)
  have haint : (∫ p : CrossCycleFive, ‖a p‖ ^ (2 : ℝ) ∂cycleFiveArea) =
      cycleMass ^ 4 * ∫ y : ℍ, cycleKernel x y ^ 2 ∂flatArea := by
    simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, hasq]
    exact (cycleEndpointSquare_mass x).2
  have hbint : (∫ p : CrossCycleFive, ‖b p‖ ^ (2 : ℝ) ∂cycleFiveArea) =
      cycleMass ^ 4 * ∫ y : ℍ, cycleKernel x y ^ 2 ∂flatArea := by
    change (∫ p : CrossCycleFive, (fun q => ‖a q‖ ^ (2 : ℝ)) (cycleReverse p)
      ∂cycleFiveArea) = _
    exact (cycleReverse_measurePreserving.integral_comp'
      (fun q => ‖a q‖ ^ (2 : ℝ))).trans haint
  have hmass0 : 0 ≤ cycleMass ^ 4 * ∫ y : ℍ, cycleKernel x y ^ 2 ∂flatArea := by
    exact mul_nonneg (by positivity) (integral_nonneg fun y => sq_nonneg _)
  have hint : (∫ p : CrossCycleFive, cycleSixNorm x p ∂cycleFiveArea) =
      ∫ p : CrossCycleFive, ‖a p‖ * ‖b p‖ ∂cycleFiveArea := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      change cycleSixNorm x p = ‖Real.sqrt (cycleEndpointSquare x p)‖ *
        ‖Real.sqrt (cycleEndpointSquare x (cycleReverse p))‖
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact hf p
  rw [hint]
  simpa only [haint, hbint, ← Real.sqrt_eq_rpow, ← pow_two, Real.sq_sqrt hmass0] using hcs

theorem cycle_lower_norm (a b : ℍ) :
    ‖cauchySquare a (conj (b : ℂ))‖ = cycleKernel a b := by
  calc
    _ = ‖conj (cauchySquare a (conj (b : ℂ)))‖ := (Complex.norm_conj _).symm
    _ = _ := by
      simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
      rfl

theorem cycleAnchor_mass_bound (x : ℍ) :
    (∫ y : ℍ, cycleKernel x y ^ 2 ∂flatArea) ≤ Real.pi / (4 * x.im ^ 2) := by
  have hplane : (∫ y : ℂ in upperHalf, ‖cauchySquare (conj y) x‖ ^ 2) =
      (-(Real.pi : ℂ) * cauchySquare x (conj (x : ℂ))).re := by
    calc
      _ = ∫ y : ℂ in upperHalf,
          (cauchySquare (conj y) x * cauchySquare y (conj (x : ℂ))).re := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          have hc : cauchySquare y (conj (x : ℂ)) = conj (cauchySquare (conj y) x) := by
            simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
          change ‖cauchySquare (conj y) x‖ ^ 2 =
            (cauchySquare (conj y) x * cauchySquare y (conj (x : ℂ))).re
          rw [hc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      _ = _ := (integral_re (cauchySquare_composition x x).1).trans
        (congrArg Complex.re (cauchySquare_composition x x).2)
  have hn : ‖(x : ℂ) - conj (x : ℂ)‖ ^ 2 = 4 * x.im ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, sub_re, conj_re, sub_im, conj_im,
      UpperHalfPlane.coe_im, sub_self]
    ring
  calc
    _ = ∫ y : ℍ, ‖cauchySquare (conj (y : ℂ)) x‖ ^ 2 ∂flatArea := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change cycleKernel x y ^ 2 = ‖cauchySquare (conj (y : ℂ)) x‖ ^ 2
        rw [cycleKernel_symm x y]
        rfl
    _ = ∫ y : ℂ in upperHalf, ‖cauchySquare (conj y) x‖ ^ 2 := by
      rw [← map_flat_coe]
      exact (UpperHalfPlane.measurableEmbedding_coe.integral_map (μ := flatArea)
        (fun y : ℂ => ‖cauchySquare (conj y) x‖ ^ 2)).symm
    _ = _ := hplane
    _ ≤ ‖-(Real.pi : ℂ) * cauchySquare x (conj (x : ℂ))‖ := Complex.re_le_norm _
    _ = _ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, cauchySquare, norm_div, norm_one, norm_pow, hn]
      ring

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (p : ℍ → X) {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

abbrev CrossCycleSix := ℍ × CrossCycleFive

def cycleSixArea : Measure CrossCycleSix := flatArea.prod cycleFiveArea
def cycleSixHyperbolicArea : Measure CrossCycleSix :=
  (volume : Measure ℍ).prod
    ((((volume : Measure ℍ).prod (volume : Measure ℍ)).prod (volume : Measure ℍ)).prod
      ((volume : Measure ℍ).prod (volume : Measure ℍ)))

def cycleDensityTwo (a : ℍ × ℍ) : ℝ≥0∞ :=
  hyperbolicDensity a.1 * hyperbolicDensity a.2

def cycleDensityThree (a : (ℍ × ℍ) × ℍ) : ℝ≥0∞ :=
  cycleDensityTwo a.1 * hyperbolicDensity a.2

def cycleDensityFive (a : CrossCycleFive) : ℝ≥0∞ :=
  cycleDensityThree a.1 * cycleDensityTwo a.2

def cycleDensitySix (a : CrossCycleSix) : ℝ≥0∞ :=
  hyperbolicDensity a.1 * cycleDensityFive a.2

private theorem cycleDensityTwo_measurable : Measurable cycleDensityTwo :=
  (measurable_hyperbolicDensity.comp measurable_fst).mul
    (measurable_hyperbolicDensity.comp measurable_snd)

private theorem cycleDensityThree_measurable : Measurable cycleDensityThree :=
  (cycleDensityTwo_measurable.comp measurable_fst).mul
    (measurable_hyperbolicDensity.comp measurable_snd)

private theorem cycleDensityFive_measurable : Measurable cycleDensityFive :=
  (cycleDensityThree_measurable.comp measurable_fst).mul
    (cycleDensityTwo_measurable.comp measurable_snd)

theorem cycleDensitySix_measurable : Measurable cycleDensitySix :=
  (measurable_hyperbolicDensity.comp measurable_fst).mul
    (cycleDensityFive_measurable.comp measurable_snd)

theorem cycleDensitySix_finite (a : CrossCycleSix) : cycleDensitySix a < ⊤ := by
  exact ENNReal.mul_lt_top (by simp [hyperbolicDensity])
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by simp [hyperbolicDensity]) (by simp [hyperbolicDensity]))
        (by simp [hyperbolicDensity]))
      (ENNReal.mul_lt_top (by simp [hyperbolicDensity]) (by simp [hyperbolicDensity])))

theorem cycleSix_hyperbolic_withDensity :
    cycleSixHyperbolicArea = cycleSixArea.withDensity cycleDensitySix := by
  have h₂ : (volume : Measure ℍ).prod (volume : Measure ℍ) =
      cycleTwoArea.withDensity cycleDensityTwo := by
    change (flatArea.withDensity hyperbolicDensity).prod
      (flatArea.withDensity hyperbolicDensity) = _
    exact MeasureTheory.prod_withDensity measurable_hyperbolicDensity measurable_hyperbolicDensity
  have h₃ : ((volume : Measure ℍ).prod (volume : Measure ℍ)).prod (volume : Measure ℍ) =
      cycleThreeArea.withDensity cycleDensityThree := by
    rw [h₂]
    change (cycleTwoArea.withDensity cycleDensityTwo).prod
      (flatArea.withDensity hyperbolicDensity) = _
    exact MeasureTheory.prod_withDensity cycleDensityTwo_measurable measurable_hyperbolicDensity
  have h₅ :
      (((volume : Measure ℍ).prod (volume : Measure ℍ)).prod (volume : Measure ℍ)).prod
          ((volume : Measure ℍ).prod (volume : Measure ℍ)) =
        cycleFiveArea.withDensity cycleDensityFive := by
    rw [h₃, h₂]
    exact MeasureTheory.prod_withDensity cycleDensityThree_measurable cycleDensityTwo_measurable
  change (volume : Measure ℍ).prod
    ((((volume : Measure ℍ).prod (volume : Measure ℍ)).prod (volume : Measure ℍ)).prod
      ((volume : Measure ℍ).prod (volume : Measure ℍ))) = _
  rw [h₅]
  change (flatArea.withDensity hyperbolicDensity).prod
    (cycleFiveArea.withDensity cycleDensityFive) = _
  exact MeasureTheory.prod_withDensity measurable_hyperbolicDensity cycleDensityFive_measurable
theorem cycle_denominator_conj_ne_zero (γ : Deck) (x : ℍ) :
    conj (denominator γ x) ≠ 0 := by
  intro h
  apply denominator_ne_zero γ x
  simpa only [Complex.conj_conj, map_zero] using congrArg conj h

theorem cycle_height_deck (γ : Deck) (x : ℍ) :
    ((γ • x : ℍ).im : ℂ) = (x.im : ℂ) /
      (denominator γ x * conj (denominator γ x)) := by
  have him : (γ • x : ℍ).im = x.im / Complex.normSq (denominator γ x) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  rw [Complex.mul_conj]
  exact_mod_cast him

include hp in
theorem cycle_harmonic_coefficient_deck
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : Deck) (hγ : γ ∈ Γ) (x : ℍ) :
    NativeHarmonicBeltrami.coefficient R p q (γ • x) =
      NativeHarmonicBeltrami.coefficient R p q x * conj (denominator γ x) ^ 2 /
        denominator γ x ^ 2 := by
  have h := NativeHarmonicBeltrami.coefficient_compatible R p hp q γ hγ x
  unfold phase at h
  simp only [map_pow] at h
  field_simp [denominator_ne_zero γ x, cycle_denominator_conj_ne_zero γ x] at h ⊢
  linear_combination -h

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
