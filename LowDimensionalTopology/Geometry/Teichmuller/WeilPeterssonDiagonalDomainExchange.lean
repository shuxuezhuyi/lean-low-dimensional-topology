module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCrossKernelCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneMeasure
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The actual diagonal fundamental-region exchange

The original harmonic functions satisfy their proved pointwise tensor law.
Together with the actual cross-kernel covariance, the three squared heights
give an invariant density for the genuine projective action. Existing
fundamental-domain preimage and integral equality theorems exchange the
original first and third integration regions. The actual hyperbolic density
then returns the same flat-area product integral. Absolute convergence and
conversion to iterated integrals are separate proved prerequisites.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Pointwise ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces GammaMeasurableBeltrami

local notation "Q" => ℍ × (ℍ × ℍ)
local notation "μQ" => Measure.prod (volume : Measure ℍ) (Measure.prod (volume : Measure ℍ) volume)
local notation "λQ" => Measure.prod flatArea (Measure.prod flatArea flatArea)

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (p : ℍ → X) {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

private theorem denominatorConj_ne_zero (γ : Deck) (z : ℍ) :
    conj (denominator γ z) ≠ 0 := by
  intro h
  apply denominator_ne_zero γ z
  simpa only [Complex.conj_conj, map_zero] using congrArg conj h

private theorem deck_height_complex (γ : Deck) (z : ℍ) :
    ((γ • z : ℍ).im : ℂ) = (z.im : ℂ) /
      (denominator γ z * conj (denominator γ z)) := by
  have him : (γ • z : ℍ).im = z.im / Complex.normSq (denominator γ z) := by
    simp [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
      Matrix.SpecialLinearGroup.det_mapGL, UpperHalfPlane.denom, denominator]
  rw [Complex.mul_conj]
  exact_mod_cast him

include hp in
private theorem harmonicCoefficient_smul
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : Deck) (hγ : γ ∈ Γ) (z : ℍ) :
    NativeHarmonicBeltrami.coefficient R p q (γ • z) =
      NativeHarmonicBeltrami.coefficient R p q z * conj (denominator γ z) ^ 2 /
        denominator γ z ^ 2 := by
  have h := NativeHarmonicBeltrami.coefficient_compatible R p hp q γ hγ z
  unfold phase at h
  simp only [map_pow] at h
  field_simp [denominator_ne_zero γ z, denominatorConj_ne_zero γ z] at h ⊢
  linear_combination -h

private def harmonicDiagonalDensity
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (w : Q) : ℂ :=
  ((w.1.im : ℂ) ^ 2 * (w.2.1.im : ℂ) ^ 2 * (w.2.2.im : ℂ) ^ 2) *
    sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
      (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2

include hp in
private theorem harmonicDiagonalDensity_deck
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (γ : Deck) (hγ : γ ∈ Γ) (w : Q) :
    harmonicDiagonalDensity R p q r (γ • w) = harmonicDiagonalDensity R p q r w := by
  unfold harmonicDiagonalDensity sesquilinearIntegrand
  simp only [Prod.smul_fst, Prod.smul_snd]
  rw [deck_height_complex, deck_height_complex, deck_height_complex,
    cauchySquare_cross_smul, cauchySquare_cross_smul, cauchySquare_lower_smul,
    harmonicCoefficient_smul R p hp q γ hγ w.2.2,
    harmonicCoefficient_smul R p hp r γ hγ w.2.1]
  simp only [map_mul, map_div₀, map_pow, Complex.conj_conj]
  field_simp [denominator_ne_zero γ w.1, denominator_ne_zero γ w.2.1,
    denominator_ne_zero γ w.2.2, denominatorConj_ne_zero γ w.1,
    denominatorConj_ne_zero γ w.2.1, denominatorConj_ne_zero γ w.2.2]

private def tripleHyperbolicDensity (w : Q) : ℝ≥0∞ :=
  hyperbolicDensity w.1 * (hyperbolicDensity w.2.1 * hyperbolicDensity w.2.2)

private theorem tripleHyperbolicDensity_measurable : Measurable tripleHyperbolicDensity :=
  (measurable_hyperbolicDensity.comp measurable_fst).mul
    (((measurable_hyperbolicDensity.comp measurable_fst).mul
      (measurable_hyperbolicDensity.comp measurable_snd)).comp measurable_snd)

private theorem tripleHyperbolicDensity_finite (w : Q) : tripleHyperbolicDensity w < ⊤ := by
  exact ENNReal.mul_lt_top (by simp [hyperbolicDensity])
    (ENNReal.mul_lt_top (by simp [hyperbolicDensity]) (by simp [hyperbolicDensity]))

private theorem tripleHyperbolic_measure :
    μQ = Measure.withDensity λQ tripleHyperbolicDensity := by
  let : SFinite flatArea :=
    sfinite_of_absolutelyContinuous GammaMeasurableBeltrami.flat_absolutelyContinuous_hyperbolic
  change Measure.prod (Measure.withDensity flatArea hyperbolicDensity)
    (Measure.prod (Measure.withDensity flatArea hyperbolicDensity)
      (Measure.withDensity flatArea hyperbolicDensity)) = _
  rw [MeasureTheory.prod_withDensity measurable_hyperbolicDensity measurable_hyperbolicDensity]
  exact MeasureTheory.prod_withDensity measurable_hyperbolicDensity
    (show Measurable (fun w : ℍ × ℍ => hyperbolicDensity w.1 * hyperbolicDensity w.2) from
      (measurable_hyperbolicDensity.comp measurable_fst).mul
        (measurable_hyperbolicDensity.comp measurable_snd))

private theorem harmonicDiagonalDensity_flat_cancel
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (w : Q) :
    (tripleHyperbolicDensity w).toReal • harmonicDiagonalDensity R p q r w =
      sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2 := by
  simp only [tripleHyperbolicDensity, ENNReal.toReal_mul, hyperbolicDensity, ENNReal.coe_toReal,
    NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk,
    harmonicDiagonalDensity, Complex.real_smul]
  push_cast
  field_simp [w.1.im_ne_zero, w.2.1.im_ne_zero, w.2.2.im_ne_zero]

private theorem harmonicDiagonalDensity_to_flat
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (S : Set Q) (hS : MeasurableSet S) :
    (∫ w in S, harmonicDiagonalDensity R p q r w ∂μQ) =
      ∫ w in S, sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2 ∂λQ := by
  rw [tripleHyperbolic_measure, MeasureTheory.restrict_withDensity hS tripleHyperbolicDensity,
    integral_withDensity_eq_integral_toReal_smul tripleHyperbolicDensity_measurable
      (Eventually.of_forall tripleHyperbolicDensity_finite)]
  exact integral_congr_ae (Eventually.of_forall (harmonicDiagonalDensity_flat_cancel R p q r))

private theorem harmonicDiagonalDensity_integrable_flat
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (S : Set Q) (hS : MeasurableSet S) :
    IntegrableOn (harmonicDiagonalDensity R p q r) S μQ ↔
      IntegrableOn (fun w => sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2) S λQ := by
  unfold IntegrableOn
  rw [tripleHyperbolic_measure, MeasureTheory.restrict_withDensity hS tripleHyperbolicDensity,
    integrable_withDensity_iff_integrable_smul' tripleHyperbolicDensity_measurable
      (Eventually.of_forall tripleHyperbolicDensity_finite)]
  exact integrable_congr (Eventually.of_forall (harmonicDiagonalDensity_flat_cancel R p q r))

variable (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include hp hF in
/-- The original first-region and third-region diagonal product integrals
are the same and have equivalent absolute integrability, for the actual
harmonic coefficients on the given cover. The original ordered triple and
its flat measure are retained. -/
theorem harmonic_diagonal_domain_exchange
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    (IntegrableOn (fun w : Q =>
      sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2)
      {w | w.1 ∈ F} λQ ↔
      IntegrableOn (fun w : Q =>
        sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
          (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2)
        {w | w.2.2 ∈ F} λQ) ∧
    ((∫ w : Q in {w | w.1 ∈ F},
      sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2 ∂λQ) =
      ∫ w : Q in {w | w.2.2 ∈ F},
        sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
          (NativeHarmonicBeltrami.coefficient R p r) w.1 w.1 w.2.1 w.2.2 ∂λQ) := by
  let G := Γ.map Hyperbolic.realSLMobius
  let := P.nativeAction
  let : Countable G := Mobius.discreteMobius_countable G P.discrete
  have hmp (g : G) : MeasurePreserving (fun w : Q => g • w) μQ μQ := by
    have h := Hyperbolic.nativeIsometry_measurePreserving (P.nativeHom g)
    exact h.prod (h.prod h)
  let : MeasurableConstSMul G Q := ⟨fun g => (hmp g).measurable⟩
  let : SMulInvariantMeasure G Q μQ :=
    ⟨fun g S hS => (hmp g).measure_preimage hS.nullMeasurableSet⟩
  have hfund := hF.measureFundamentalDomain P
  have hfirst : MeasureTheory.IsFundamentalDomain G {w : Q | w.1 ∈ F} μQ :=
    hfund.preimage_of_equiv
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℍ))
        (ν := Measure.prod (volume : Measure ℍ) volume)) Function.bijective_id
      (fun _ _ => rfl)
  have hlast : MeasureTheory.IsFundamentalDomain G {w : Q | w.2.2 ∈ F} μQ :=
    hfund.preimage_of_equiv
      ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℍ)) (ν := volume)).comp
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℍ))
          (ν := Measure.prod (volume : Measure ℍ) volume)))
      Function.bijective_id (fun _ _ => rfl)
  have hinv (g : G) (w : Q) :
      harmonicDiagonalDensity R p q r (g • w) = harmonicDiagonalDensity R p q r w := by
    obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp g.property
    change harmonicDiagonalDensity R p q r (g • w.1, (g • w.2.1, g • w.2.2)) = _
    rw [P.nativeAction_realSL g A hAg w.1, P.nativeAction_realSL g A hAg w.2.1,
      P.nativeAction_realSL g A hAg w.2.2]
    exact harmonicDiagonalDensity_deck R p hp q r A hA w
  have hiff := hfirst.integrableOn_iff hlast hinv
  rw [harmonicDiagonalDensity_integrable_flat R p q r {w : Q | w.1 ∈ F}
      (hF.1.measurableSet.preimage measurable_fst),
    harmonicDiagonalDensity_integrable_flat R p q r {w : Q | w.2.2 ∈ F}
      (hF.1.measurableSet.preimage (measurable_snd.comp measurable_snd))] at hiff
  refine ⟨hiff, ?_⟩
  have he := hfirst.setIntegral_eq hlast hinv
  rw [harmonicDiagonalDensity_to_flat R p q r {w : Q | w.1 ∈ F}
      (hF.1.measurableSet.preimage measurable_fst),
    harmonicDiagonalDensity_to_flat R p q r {w : Q | w.2.2 ∈ F}
      (hF.1.measurableSet.preimage (measurable_snd.comp measurable_snd))] at he
  exact he

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
