module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyFormula
public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpOperators
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S23_QCOnSurfaces
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The normalized Cauchy integral of a transported angular coefficient

The coefficient is the actual real Möbius pullback on the upper half-plane,
extended by zero to the plane. Its unit phase preserves the original bound.
The normalized three-pole integral is absolutely integrable at every point
and continuous, and vanishes at both finite normalization points.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

open scoped Classical in
/-- The actual Möbius-transported infinitesimal coefficient, extended by zero. -/
def pullbackInfinitesimalZeroExtension (θ : Width) (γ : Deck) (ζ : ℂ) : ℂ :=
  {ζ : ℂ | 0 < ζ.im}.indicator
    (fun ζ => infinitesimalZeroExtension θ
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) ζ) *
        (((γ 1 0 : ℂ) * ζ + γ 1 1) ^ 2 /
          conj (((γ 1 0 : ℂ) * ζ + γ 1 1) ^ 2))) ζ

/-- On the native upper half-plane this is the literal weighted deck action. -/
theorem pullbackInfinitesimalZeroExtension_coe (θ : Width) (γ : Deck) (ζ : ℍ) :
    pullbackInfinitesimalZeroExtension θ γ (ζ : ℂ) =
      infinitesimal θ (γ • ζ) * GammaMeasurableBeltrami.phase γ ζ := by
  classical
  have hmem : (ζ : ℂ) ∈ {w : ℂ | 0 < w.im} := ζ.im_pos
  rw [pullbackInfinitesimalZeroExtension, indicator_of_mem hmem]
  have hγ : LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) ζ =
      ((γ • ζ : ℍ) : ℂ) :=
    (LiZhongQC.h23l_b_coe_smul γ ζ).symm
  rw [hγ, infinitesimalZeroExtension_coe]
  rfl

/-- The extension is zero on the closed lower half-plane. -/
theorem pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos
    (θ : Width) (γ : Deck) {ζ : ℂ} (hζ : ζ.im ≤ 0) :
    pullbackInfinitesimalZeroExtension θ γ ζ = 0 := by
  classical
  have hnot : ζ ∉ {w : ℂ | 0 < w.im} := not_lt.mpr hζ
  simp only [pullbackInfinitesimalZeroExtension, indicator_of_notMem hnot]

/-- The derivative quotient in the transported coefficient is the genuine one. -/
theorem pullbackInfinitesimalZeroExtension_eq_derivative
    (θ : Width) (γ : Deck) {ζ : ℂ} (hζ : 0 < ζ.im) :
    pullbackInfinitesimalZeroExtension θ γ ζ =
      infinitesimalZeroExtension θ
        (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) ζ) *
        (conj (deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) ζ) /
          deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) ζ) := by
  classical
  have hden : (γ 1 0 : ℂ) * ζ + γ 1 1 ≠ 0 :=
    LiZhongQC.h23l_b_den_ne γ hζ
  have hd := LiZhongQC.hasDerivAt_mobiusFn
    (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) hden
  rw [LiZhongQC.h23l_b_det γ] at hd
  have hmem : ζ ∈ {w : ℂ | 0 < w.im} := hζ
  rw [pullbackInfinitesimalZeroExtension, indicator_of_mem hmem, hd.deriv]
  congr 1
  simp only [one_div, map_inv₀, inv_div_inv]

/-- The transported coefficient is measurable for actual planar area. -/
theorem measurable_pullbackInfinitesimalZeroExtension (θ : Width) (γ : Deck) :
    Measurable (pullbackInfinitesimalZeroExtension θ γ) := by
  classical
  have hγ : Measurable
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) := by
    unfold LiZhongQC.mobiusFn
    fun_prop
  have hphase : Measurable fun ζ : ℂ =>
      ((γ 1 0 : ℂ) * ζ + γ 1 1) ^ 2 /
        conj (((γ 1 0 : ℂ) * ζ + γ 1 1) ^ 2) := by
    fun_prop
  exact (((measurable_infinitesimalZeroExtension θ).comp hγ).mul hphase).indicator
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet

/-- Every transported coefficient has the same original pointwise bound. -/
theorem norm_pullbackInfinitesimalZeroExtension_le
    (θ : Width) (γ : Deck) (ζ : ℂ) :
    ‖pullbackInfinitesimalZeroExtension θ γ ζ‖ ≤ 1 / (4 * (θ : ℝ)) := by
  by_cases hζ : 0 < ζ.im
  · let w : ℍ := ⟨ζ, hζ⟩
    change ‖pullbackInfinitesimalZeroExtension θ γ (w : ℂ)‖ ≤ _
    rw [pullbackInfinitesimalZeroExtension_coe, norm_mul,
      GammaMeasurableBeltrami.norm_phase, mul_one]
    exact norm_infinitesimal_le θ (γ • w)
  · rw [pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ
      (le_of_not_gt hζ), norm_zero]
    have hθ : 0 < (θ : ℝ) := θ.property.1
    positivity

/-- Its measurable coefficient predicate uses a bound without a subunit restriction. -/
theorem isBeltramiCoeff_pullbackInfinitesimalZeroExtension (θ : Width) (γ : Deck) :
    LiZhongQC.IsBeltramiCoeff (pullbackInfinitesimalZeroExtension θ γ) univ
      (1 / (4 * (θ : ℝ))) := by
  simp only [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ]
  exact ⟨(measurable_pullbackInfinitesimalZeroExtension θ γ).aestronglyMeasurable,
    Eventually.of_forall (norm_pullbackInfinitesimalZeroExtension_le θ γ)⟩

/-- The original three-pole integrand is globally absolutely integrable at every point. -/
theorem integrable_pullbackInfinitesimalZeroExtension_mul_firstVariationKernel
    (θ : Width) (γ : Deck) (z : ℂ) :
    Integrable (fun ζ : ℂ => pullbackInfinitesimalZeroExtension θ γ ζ *
      Quasiconformal.firstVariationKernel z ζ) (volume : Measure ℂ) := by
  exact (LiZhongQC.ah_ker_integrable z).bdd_mul
    (measurable_pullbackInfinitesimalZeroExtension θ γ).aestronglyMeasurable
    (Eventually.of_forall (norm_pullbackInfinitesimalZeroExtension_le θ γ))

/-- The literal derivative-quotient integrand is absolutely integrable on the upper half-plane. -/
theorem integrableOn_pullbackCauchySourceKernel (θ : Width) (γ : Deck) (z : ℂ) :
    IntegrableOn (fun ζ : ℂ =>
      infinitesimalZeroExtension θ
        (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) ζ) *
        (conj (deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) ζ) /
          deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) ζ) *
        Quasiconformal.firstVariationKernel z ζ)
      {ζ : ℂ | 0 < ζ.im} (volume : Measure ℂ) := by
  apply (integrable_pullbackInfinitesimalZeroExtension_mul_firstVariationKernel
    θ γ z).integrableOn.congr_fun
    (fun ζ hζ => congrArg (fun c : ℂ => c * Quasiconformal.firstVariationKernel z ζ)
      (pullbackInfinitesimalZeroExtension_eq_derivative θ γ hζ))
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet

/-- The actual normalized Cauchy integral of the transported coefficient. -/
def pullbackCauchyTerm (θ : Width) (γ : Deck) (z : ℂ) : ℂ :=
  LiZhongQC.ahVar (pullbackInfinitesimalZeroExtension θ γ) z

/-- The whole-plane definition equals the original upper-plane derivative-quotient area integral. -/
theorem pullbackCauchyTerm_eq_upperHalfPlane (θ : Width) (γ : Deck) (z : ℂ) :
    pullbackCauchyTerm θ γ z = -(1 / (Real.pi : ℂ)) *
      ∫ ζ in {ζ : ℂ | 0 < ζ.im},
        infinitesimalZeroExtension θ
          (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) ζ) *
          (conj (deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) ζ) /
            deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) ζ) *
          Quasiconformal.firstVariationKernel z ζ := by
  have hH : MeasurableSet {ζ : ℂ | 0 < ζ.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have harea : (∫ ζ, pullbackInfinitesimalZeroExtension θ γ ζ *
      Quasiconformal.firstVariationKernel z ζ) =
      ∫ ζ in {ζ : ℂ | 0 < ζ.im}, pullbackInfinitesimalZeroExtension θ γ ζ *
        Quasiconformal.firstVariationKernel z ζ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ζ hζ
    rw [pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ
      (le_of_not_gt hζ), zero_mul]
  unfold pullbackCauchyTerm LiZhongQC.ahVar
  change -(1 / (Real.pi : ℂ)) *
      (∫ ζ, pullbackInfinitesimalZeroExtension θ γ ζ *
        Quasiconformal.firstVariationKernel z ζ) = _
  rw [harea]
  apply congrArg (fun c : ℂ => -(1 / (Real.pi : ℂ)) * c)
  apply setIntegral_congr_fun hH
  intro ζ hζ
  exact congrArg (fun c : ℂ => c * Quasiconformal.firstVariationKernel z ζ)
    (pullbackInfinitesimalZeroExtension_eq_derivative θ γ hζ)

/-- The actual integral vanishes at zero. -/
@[simp] theorem pullbackCauchyTerm_zero (θ : Width) (γ : Deck) :
    pullbackCauchyTerm θ γ 0 = 0 := by
  simp [pullbackCauchyTerm, LiZhongQC.ahVar, LiZhongQC.ahKer]

/-- The actual integral vanishes at one. -/
@[simp] theorem pullbackCauchyTerm_one (θ : Width) (γ : Deck) :
    pullbackCauchyTerm θ γ 1 = 0 := by
  simp [pullbackCauchyTerm, LiZhongQC.ahVar, LiZhongQC.ahKer]

/-- The actual transported integral is continuous on the entire complex plane. -/
theorem continuous_pullbackCauchyTerm (θ : Width) (γ : Deck) :
    Continuous (pullbackCauchyTerm θ γ) := by
  have hθ : 0 < (θ : ℝ) := θ.property.1
  let C : ℝ := (1 / Real.pi) * (1 / (4 * (θ : ℝ)))
  have hC : 0 < C := by dsimp only [C]; positivity
  apply Metric.continuous_iff.2
  intro z ε hε
  obtain ⟨δ, hδ, hK⟩ := LiZhongQC.ah_ker_continuous z (ε / C) (div_pos hε hC)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have hk := hK a (by simpa only [dist_eq_norm] using ha)
  have hb := LiZhongQC.ahF_var_sub_bound a z
    (isBeltramiCoeff_pullbackInfinitesimalZeroExtension θ γ)
  rw [dist_eq_norm]
  calc ‖pullbackCauchyTerm θ γ a - pullbackCauchyTerm θ γ z‖
      ≤ (1 / Real.pi) * (∫ ζ, ‖LiZhongQC.ahKer a ζ - LiZhongQC.ahKer z ζ‖) *
          (1 / (4 * (θ : ℝ))) := hb
    _ = (∫ ζ, ‖LiZhongQC.ahKer a ζ - LiZhongQC.ahKer z ζ‖) * C := by
      dsimp only [C]
      ring
    _ < ε := (lt_div_iff₀ hC).mp hk

/-- Transport by the identity recovers the original zero extension pointwise. -/
@[simp] theorem pullbackInfinitesimalZeroExtension_one (θ : Width) (ζ : ℂ) :
    pullbackInfinitesimalZeroExtension θ 1 ζ = infinitesimalZeroExtension θ ζ := by
  by_cases hζ : 0 < ζ.im
  · let w : ℍ := ⟨ζ, hζ⟩
    change pullbackInfinitesimalZeroExtension θ 1 (w : ℂ) =
      infinitesimalZeroExtension θ (w : ℂ)
    have hp : GammaMeasurableBeltrami.phase (1 : Deck) w = 1 := by
      simp [GammaMeasurableBeltrami.phase, GammaMeasurableBeltrami.denominator]
    rw [pullbackInfinitesimalZeroExtension_coe, one_smul, hp, mul_one,
      infinitesimalZeroExtension_coe]
  · rw [pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ 1
      (le_of_not_gt hζ),
      infinitesimalZeroExtension_eq_zero_of_im_nonpos θ (le_of_not_gt hζ)]

/-- The identity-matrix term is exactly the previously defined original integral. -/
@[simp] theorem pullbackCauchyTerm_identity (θ : Width) :
    pullbackCauchyTerm θ 1 = firstCauchyTerm θ := by
  have hc : pullbackInfinitesimalZeroExtension θ 1 = infinitesimalZeroExtension θ :=
    funext (pullbackInfinitesimalZeroExtension_one θ)
  funext z
  unfold pullbackCauchyTerm firstCauchyTerm
  rw [hc]

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
