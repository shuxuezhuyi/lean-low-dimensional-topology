module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeInverseBersGermAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslation
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual inverse Bers germ has an invertible genuine derivative

The original coordinate translation recovers every vector of the actual
section ball and has the proved fixed-base linear norm estimate. Applying
that estimate to genuine scaled secants of the analytic inverse germ gives
a lower norm bound for its actual Frechet derivative. In particular this
derivative is injective without assuming any derivative of the coordinate
translation. The original and deformed compact uniformizations prove the
same dimension, so this actual derivative is a continuous linear equivalence
for the original weighted norms on both spaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology Bornology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

variable {Γ : Subgroup Deck}

/-- The genuine derivative of the independently defined actual normalized inverse germ. -/
def inverseBersDerivative (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    BersWeighted.Automorphic (deformedGroup hΓ ν) →L[ℂ] BersWeighted.Automorphic Γ :=
  fderiv ℂ (inverseBersGerm hΓ ν) 0

theorem hasFDerivAt_inverseBersGerm (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    [FiniteDimensional ℂ (BersWeighted.Automorphic Γ)]
    [FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν))] :
    HasFDerivAt (inverseBersGerm hΓ ν) (inverseBersDerivative hΓ ν) 0 := by
  exact ((analyticOnNhd_inverseBersGerm hΓ ν) 0
    (Metric.mem_ball_self (inverseSectionRadius_pos ν))).differentiableAt.hasFDerivAt

private theorem norm_le_of_inv_smul_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : E) (w : F) (a : ℂ) (C : ℝ) (ha0 : a ≠ 0)
    (hbound : ‖a⁻¹ • v‖ ≤ C * ‖w‖) : ‖v‖ ≤ C * ‖a • w‖ := by
  have hvscale : a • (a⁻¹ • v) = v := by
    rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hvnorm : ‖v‖ = ‖a‖ * ‖a⁻¹ • v‖ :=
    (congrArg (fun x : E => ‖x‖) hvscale).symm.trans (norm_smul a (a⁻¹ • v))
  have hsecant : ‖a • w‖ = ‖a‖ * ‖w‖ := norm_smul a w
  calc
    ‖v‖ = ‖a‖ * ‖a⁻¹ • v‖ := hvnorm
    _ ≤ ‖a‖ * (C * ‖w‖) := mul_le_mul_of_nonneg_left hbound (norm_nonneg a)
    _ = C * (‖a‖ * ‖w‖) := mul_left_comm _ _ _
    _ = C * ‖a • w‖ := congrArg (fun s : ℝ => C * s) hsecant.symm

private theorem inverseBersGerm_eventually_scaled_norm_bound
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    [FiniteDimensional ℂ (BersWeighted.Automorphic Γ)]
    [FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν))]
    (c : ℝ)
    (hb : ∀ φ : BersWeighted.Automorphic Γ,
      c * ‖φ - baseBersValue hΓ ν‖ < 1 / 2 →
      ‖bersTranslation hΓ ν φ‖ ≤ 12 * c * ‖φ - baseBersValue hΓ ν‖)
    (v : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    ∀ᶠ a : ℂ in cobounded ℂ, ‖v‖ ≤ (12 * c) *
      ‖a • (inverseBersGerm hΓ ν (a⁻¹ • v) - inverseBersGerm hΓ ν 0)‖ := by
  have hd := hasFDerivAt_inverseBersGerm hΓ ν
  have hq : Tendsto (fun a : ℂ => a⁻¹ • v) (cobounded ℂ) (𝓝 0) := by
    simpa only [zero_smul] using
      (tendsto_inv₀_cobounded : Tendsto (fun a : ℂ => a⁻¹) (cobounded ℂ) (𝓝 0)).smul
        (tendsto_const_nhds (x := v))
  have he : Tendsto
      (fun a : ℂ => inverseBersGerm hΓ ν (a⁻¹ • v) - baseBersValue hΓ ν)
      (cobounded ℂ) (𝓝 0) := by
    have he' := (hd.continuousAt.tendsto.comp hq).sub
      (tendsto_const_nhds (x := baseBersValue hΓ ν))
    rw [inverseBersGerm_zero, sub_self] at he'
    apply he'.congr'
    exact Eventually.of_forall fun a => by rfl
  have hsmall : ∀ᶠ a : ℂ in cobounded ℂ, ‖a⁻¹ • v‖ < 1 / 2 :=
    hq.eventually (Metric.ball_mem_nhds 0 (by norm_num : 0 < (1 / 2 : ℝ))) |>.mono
      (fun _ ha => mem_ball_zero_iff.mp ha)
  have hn : Tendsto
      (fun a : ℂ => c * ‖inverseBersGerm hΓ ν (a⁻¹ • v) - baseBersValue hΓ ν‖)
      (cobounded ℂ) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using
      (tendsto_const_nhds (x := c)).mul he.norm
  have himage : ∀ᶠ a : ℂ in cobounded ℂ,
      c * ‖inverseBersGerm hΓ ν (a⁻¹ • v) - baseBersValue hΓ ν‖ < 1 / 2 :=
    hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, himage, eventually_ne_cobounded (0 : ℂ)] with a ha hia ha0
  have hbound := hb (inverseBersGerm hΓ ν (a⁻¹ • v)) hia
  rw [bersTranslation_inverseBersGerm hΓ ν _ ha] at hbound
  have hbound' : ‖a⁻¹ • v‖ ≤
      (12 * c) * ‖inverseBersGerm hΓ ν (a⁻¹ • v) - inverseBersGerm hΓ ν 0‖ := by
    simpa only [inverseBersGerm_zero] using hbound
  exact norm_le_of_inv_smul_norm_le v
    (inverseBersGerm hΓ ν (a⁻¹ • v) - inverseBersGerm hΓ ν 0) a (12 * c) ha0 hbound'

/-- Actual coordinate norm control survives the genuine derivative limit in every direction. -/
theorem inverseBersDerivative_lower_norm_bound (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    [FiniteDimensional ℂ (BersWeighted.Automorphic Γ)]
    [FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν))] :
    ∃ C : ℝ, 0 < C ∧ ∀ v : BersWeighted.Automorphic (deformedGroup hΓ ν),
      ‖v‖ ≤ C * ‖inverseBersDerivative hΓ ν v‖ := by
  obtain ⟨c, hc, hb⟩ := bersTranslation_local_norm_bound hΓ ν
  refine ⟨12 * c, mul_pos (by norm_num) hc, ?_⟩
  intro v
  have hd := hasFDerivAt_inverseBersGerm hΓ ν
  have hlim := hd.lim v (tendsto_norm_cobounded_atTop (E := ℂ))
  simp only [zero_add] at hlim
  have hlimNorm : Tendsto
      (fun a : ℂ => (12 * c) *
        ‖a • (inverseBersGerm hΓ ν (a⁻¹ • v) - inverseBersGerm hΓ ν 0)‖)
      (cobounded ℂ) (𝓝 ((12 * c) * ‖inverseBersDerivative hΓ ν v‖)) :=
    tendsto_const_nhds.mul hlim.norm
  apply ge_of_tendsto hlimNorm
  exact inverseBersGerm_eventually_scaled_norm_bound hΓ ν c hb v

/-- Injectivity is a conclusion of the actual inverse estimate, not an input. -/
theorem inverseBersDerivative_injective (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    [FiniteDimensional ℂ (BersWeighted.Automorphic Γ)]
    [FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν))] :
    Function.Injective (inverseBersDerivative hΓ ν) := by
  obtain ⟨C, _, hb⟩ := inverseBersDerivative_lower_norm_bound hΓ ν
  intro v w he
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  have h := hb (v - w)
  rw [map_sub, he, sub_self, norm_zero, mul_zero] at h
  exact h

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

/-- The actual nonzero inverse-coordinate derivative is a genuine equivalence in both original norms. -/
def inverseBersDerivativeEquiv (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    BersWeighted.Automorphic (deformedGroup hΓ ν) ≃L[ℂ] BersWeighted.Automorphic Γ := by
  let e := TeichmullerSpace.weightedLinearBersEquiv R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp
  letI : FiniteDimensional ℂ (BersWeighted.Automorphic Γ) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
    deformed_weighted_finiteDimensional R hg hgenus hΓ hp ν
  letI : CompleteSpace (BersWeighted.Automorphic Γ) := BersWeighted.automorphic_completeSpace Γ
  letI : CompleteSpace (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
    BersWeighted.automorphic_completeSpace (deformedGroup hΓ ν)
  have hdimΓ : Module.finrank ℂ (BersWeighted.Automorphic Γ) = 3 * g - 3 := by
    simpa only [Module.finrank_fin_fun] using e.finrank_eq
  have hdim : Module.finrank ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν)) =
      Module.finrank ℂ (BersWeighted.Automorphic Γ) :=
    (deformed_weighted_finrank R hg hgenus hΓ hp ν).trans hdimΓ.symm
  have hinj := inverseBersDerivative_injective hΓ ν
  have hsurj : Function.Surjective (inverseBersDerivative hΓ ν) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ContinuousLinearEquiv.ofBijective (inverseBersDerivative hΓ ν)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)

@[simp] theorem inverseBersDerivativeEquiv_apply (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (v : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    inverseBersDerivativeEquiv R hp hg hgenus hΓ ν v = inverseBersDerivative hΓ ν v := rfl

/-- This equivalence is the genuine derivative of the independently defined actual germ. -/
theorem hasFDerivAt_inverseBersGerm_equiv (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    HasFDerivAt (inverseBersGerm hΓ ν)
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).toContinuousLinearMap 0 := by
  have he : (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).toContinuousLinearMap =
      fderiv ℂ (inverseBersGerm hΓ ν) 0 := by
    apply ContinuousLinearMap.ext
    intro v
    exact inverseBersDerivativeEquiv_apply R hp hg hgenus hΓ ν v
  rw [he]
  exact ((analyticOnNhd_inverseBersGerm_of_uniformization R hp hg hgenus hΓ ν) 0
    (Metric.mem_ball_self (inverseSectionRadius_pos ν))).differentiableAt.hasFDerivAt

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
