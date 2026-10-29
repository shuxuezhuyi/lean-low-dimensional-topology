module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceCompactFundamentalDomain
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticCayleyL1Transport
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The compact fundamental-domain seed after quadratic Cayley pullback

The actual half-plane kernel seed has a literal integral expression without a
Cayley denominator at the boundary point one. Compactness of the original
fundamental domain gives a larger closed disc on which its integration
kernel has no pole. Every integral on that disc is genuinely integrable.
This module does not yet assert holomorphic extension to a neighborhood.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.CompactPoincareSeed

open Surfaces LiZhongQC Hyperbolic WeightedQuadraticBergman

/-- The actual linear denominator remaining after quadratic Cayley pullback. -/
def seedDenominator (ζ z : ℂ) : ℂ :=
  (conj ζ - Complex.I) - (conj ζ + Complex.I) * z

/-- The literal integral extending the pulled-back fundamental-domain seed. -/
def extendedSeed (F : Set ℂ) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-48 / Real.pi : ℂ) * ∫ ζ in F,
    (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ z ^ 4

/-- The base factor is nonzero throughout the original upper half-plane. -/
theorem seedDenominator_base_ne_zero {ζ : ℂ} (hζ : 0 < ζ.im) :
    conj ζ - Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.I_im, Complex.zero_im] at hi
  linarith

/-- This factorization also covers the point where the Cayley numerator is zero. -/
theorem seedDenominator_factor {ζ : ℂ} (hζ : 0 < ζ.im) (z : ℂ) :
    seedDenominator ζ z =
      (conj ζ - Complex.I) * (1 - conj (cayleyFormula ζ) * z) := by
  have ha := seedDenominator_base_ne_zero hζ
  have he : conj (cayleyFormula ζ) =
      (conj ζ + Complex.I) / (conj ζ - Complex.I) := by
    simp only [cayleyFormula, map_div₀, map_sub, map_add, Complex.conj_I,
      sub_neg_eq_add, ← sub_eq_add_neg]
  rw [he]
  unfold seedDenominator
  symm
  calc
    (conj ζ - Complex.I) *
        (1 - ((conj ζ + Complex.I) / (conj ζ - Complex.I)) * z) =
      (conj ζ - Complex.I) -
        (((conj ζ + Complex.I) / (conj ζ - Complex.I)) *
          (conj ζ - Complex.I)) * z := by ring
    _ = _ := by rw [div_mul_cancel₀ _ ha]

/-- A compact subset of the original half-plane gives one pole-free closed disc
strictly larger than the unit disc. No nonemptiness assumption is needed. -/
theorem exists_seedPoleFree_radius {F : Set ℂ} (hFC : IsCompact F)
    (hFH : F ⊆ upperHalf) :
    ∃ r : ℝ, 1 < r ∧ ∀ ζ ∈ F, ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      seedDenominator ζ z ≠ 0 := by
  have hpos : ∀ ζ ∈ F, 0 < ζ.im := by
    intro ζ hζ
    simpa only [upperHalf, Set.mem_ofPred_eq] using hFH hζ
  have hT : ContinuousOn cayleyFormula F := by
    intro ζ hζ
    exact (hasDerivAt_cayleyFormula (UpperHalfPlane.mk ζ (hpos ζ hζ))).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hbound⟩ := hFC.exists_forall_le' hT.norm.neg (a := (-1 : ℝ))
    (fun ζ hζ => by
      have hn : ‖cayleyFormula ζ‖ < 1 :=
        cayley_mem_disc (UpperHalfPlane.mk ζ (hpos ζ hζ))
      change -1 < -‖cayleyFormula ζ‖
      linarith)
  let ρ : ℝ := max (-m) 0
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  have hρ1 : ρ < 1 := max_lt_iff.mpr ⟨by linarith, by norm_num⟩
  have hρ : ∀ ζ ∈ F, ‖cayleyFormula ζ‖ ≤ ρ := by
    intro ζ hζ
    have hmζ : m ≤ -‖cayleyFormula ζ‖ := hbound ζ hζ
    exact (show ‖cayleyFormula ζ‖ ≤ -m by linarith).trans (le_max_left _ _)
  let r : ℝ := 2 / (1 + ρ)
  have hd : 0 < 1 + ρ := by linarith
  have hr : 1 < r := (lt_div_iff₀ hd).mpr (by linarith)
  have hrρ : r * ρ < 1 := by
    calc
      r * ρ = (2 * ρ) / (1 + ρ) := by dsimp only [r]; ring
      _ < 1 := (div_lt_one hd).mpr (by linarith)
  refine ⟨r, hr, ?_⟩
  intro ζ hζ z hz
  have hzr : ‖z‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hn : ‖conj (cayleyFormula ζ) * z‖ < 1 := by
    calc
      ‖conj (cayleyFormula ζ) * z‖ = ‖cayleyFormula ζ‖ * ‖z‖ := by
        rw [norm_mul, Complex.norm_conj]
      _ ≤ ρ * r := mul_le_mul (hρ ζ hζ) hzr (norm_nonneg _) hρ0
      _ < 1 := by simpa only [mul_comm] using hrρ
  rw [seedDenominator_factor (hpos ζ hζ)]
  refine mul_ne_zero (seedDenominator_base_ne_zero (hpos ζ hζ)) ?_
  apply sub_ne_zero.mpr
  intro he
  rw [← he, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

private theorem inverseCayleyDerivative_sq (z : ℂ) :
    inverseCayleyDerivative z ^ 2 = (-4 : ℂ) / (1 - z) ^ 4 := by
  unfold inverseCayleyDerivative
  rw [div_pow, mul_pow, ← pow_mul]
  norm_num

/-- The square of the actual derivative cancels the Cayley denominator in each
kernel summand, at every original disc point. -/
theorem kernel_quadratic_pullback (φ : ℂ → ℂ) (ζ : ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    h36p_c_K φ ζ (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2 =
      (-4 : ℂ) * (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ z ^ 4 := by
  have hn : 1 - z ≠ 0 := inverseCayley_denom_ne_zero
    (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))
  have hS : inverseCayleyFormula z * (1 - z) = Complex.I * (1 + z) := by
    unfold inverseCayleyFormula
    rw [mul_assoc, div_mul_cancel₀ _ hn]
  have he : seedDenominator ζ z =
      (conj ζ - inverseCayleyFormula z) * (1 - z) := by
    rw [sub_mul, hS]
    unfold seedDenominator
    ring
  unfold h36p_c_K
  rw [inverseCayleyDerivative_sq, div_mul_div_comm, he, mul_pow]
  ring

/-- The exact unscaled seed pulls back to this literal integral at every disc
point. This identity does not assume integrability from a Bochner value. -/
theorem extendedSeed_eq_inverseCayleyPullback (F : Set ℂ) (hF : MeasurableSet F)
    (φ : ℂ → ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    extendedSeed F φ z = inverseCayleyPullback (AutomorphicPoincare.seed F φ) z := by
  have he (ζ : ℂ) :
      (-48 / Real.pi : ℂ) * ((ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ z ^ 4) =
        ((12 / Real.pi : ℂ) * h36p_c_K φ ζ (inverseCayleyFormula z)) *
          inverseCayleyDerivative z ^ 2 := by
    symm
    calc
      ((12 / Real.pi : ℂ) * h36p_c_K φ ζ (inverseCayleyFormula z)) *
          inverseCayleyDerivative z ^ 2 =
        (12 / Real.pi : ℂ) *
          (h36p_c_K φ ζ (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2) := by ring
      _ = (12 / Real.pi : ℂ) *
          ((-4 : ℂ) * (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ z ^ 4) := by
        rw [kernel_quadratic_pullback φ ζ hz]
      _ = _ := by ring
  calc
    extendedSeed F φ z = ∫ ζ in F,
        (-48 / Real.pi : ℂ) * ((ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ z ^ 4) := by
      rw [integral_const_mul]
      rfl
    _ = ∫ ζ in F, ((12 / Real.pi : ℂ) * h36p_c_K φ ζ (inverseCayleyFormula z)) *
        inverseCayleyDerivative z ^ 2 :=
      setIntegral_congr_fun hF fun ζ _ => he ζ
    _ = inverseCayleyPullback (AutomorphicPoincare.seed F φ) z := by
      rw [integral_mul_const, integral_const_mul]
      rfl

/-- Every pole-free compact-domain integral is genuinely integrable. -/
theorem extendedSeed_integrableOn {F : Set ℂ} (hFC : IsCompact F) {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ F) {z : ℂ}
    (hpole : ∀ ζ ∈ F, seedDenominator ζ z ≠ 0) :
    IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ z ^ 4) F := by
  have hn : ContinuousOn (fun ζ : ℂ => (ζ.im : ℂ) ^ 2 * φ ζ) F :=
    ((Complex.continuous_ofReal.comp Complex.continuous_im).pow 2).continuousOn.mul hφ
  have hd : Continuous (fun ζ : ℂ => seedDenominator ζ z) := by
    unfold seedDenominator
    exact (Complex.continuous_conj.sub continuous_const).sub
      ((Complex.continuous_conj.add continuous_const).mul continuous_const)
  exact ContinuousOn.integrableOn_compact hFC
    (hn.div (hd.pow 4).continuousOn fun ζ hζ => pow_ne_zero 4 (hpole ζ hζ))

/-- The original compact cover itself supplies the compact integration domain,
a larger pole-free closed disc, true integrability and the actual pulled-back
seed formula. No independent fundamental-domain data are supplied. -/
theorem source_compact_seed_transport
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (φ : ℂ → ℂ) (hφ : ContinuousOn φ upperHalf) :
    ∃ F : Set ℂ, IsFundamentalDomainH Γ F ∧ IsCompact F ∧
      ∃ r : ℝ, 1 < r ∧
        (∀ ζ ∈ F, ∀ z ∈ Metric.closedBall (0 : ℂ) r, seedDenominator ζ z ≠ 0) ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) r,
          IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ z ^ 4) F) ∧
        EqOn (extendedSeed F φ) (inverseCayleyPullback (AutomorphicPoincare.seed F φ))
          (Metric.ball (0 : ℂ) 1) := by
  obtain ⟨F, hF, hFC⟩ := exists_sourceCompactFundamentalDomainH R hΓ hp
  obtain ⟨r, hr, hpole⟩ := exists_seedPoleFree_radius hFC hF.1
  refine ⟨F, hF, hFC, r, hr, hpole, ?_, ?_⟩
  · intro z hz
    exact extendedSeed_integrableOn hFC (hφ.mono hF.1) fun ζ hζ => hpole ζ hζ z hz
  · intro z hz
    exact extendedSeed_eq_inverseCayleyPullback F hFC.measurableSet φ hz

end LowDimensionalTopology.Geometry.Teichmuller.CompactPoincareSeed
