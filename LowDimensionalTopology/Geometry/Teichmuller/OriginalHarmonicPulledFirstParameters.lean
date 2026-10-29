module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicDoubleCircleControl
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPulledQuadraticZero
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# First parameter control of the actual pulled quadratic

The fixed double-circle norm average bounds the actual full-plane inner
integral and its quadratic remainder. On the physical parameter diagonal
this gives its full real derivative, measurable derivative field and one
compact basepoint Lipschitz bound.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC WeilPetersson

private theorem flatArea_sigmaFinite : SigmaFinite flatArea := by
  let : IsFiniteMeasureOnCompacts flatArea :=
    IsFiniteMeasureOnCompacts.comap' volume UpperHalfPlane.continuous_coe
      UpperHalfPlane.measurableEmbedding_coe
  infer_instance

private theorem hasFDerivAt_of_quadratic_remainder
    {f : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {ε D : ℝ} (hε : 0 < ε)
    (hrem : ∀ s : ℂ, ‖s‖ < ε → ‖f s - f 0 - L s‖ ≤ D * ‖s‖ ^ 2) :
    HasFDerivAt f L 0 := by
  have hbig : (fun s : ℂ => f s - f 0 - L s) =O[𝓝 0] fun s => ‖s‖ ^ 2 := by
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [ball_mem_nhds (0 : ℂ) hε] with s hs
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖s‖ : ℝ))] using
      hrem s (mem_ball_zero_iff.mp hs)
  have hsmall := hbig.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := ℂ) (by norm_num : 1 < 2))
  simpa only [hasFDerivAt_iff_isLittleO_nhds_zero, zero_add] using hsmall

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem kernel_integral_first_parameter_control
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    let P := fun s : ℂ => fun z : ℍ => ∫ ζ : ℍ,
      canonicalBiparameterKernelIntegrand R p qdir qtest s (conj s) z ζ ∂flatArea
    ∃ ε L : ℝ, 0 < ε ∧ 0 ≤ L ∧
      (∀ s : ℂ, ‖s‖ < ε → Measurable (P s)) ∧
      (∀ z ∈ K, DifferentiableAt ℝ (fun s : ℂ => P s z) 0) ∧
      ∀ s : ℂ, ‖s‖ < ε → ∀ z ∈ K, ‖P s z - P 0 z‖ ≤ L * ‖s‖ := by
  let : SigmaFinite flatArea := flatArea_sigmaFinite
  dsimp only
  obtain ⟨E, C, hE, hC, hjoint, hcontrol⟩ :=
    canonicalBiparameterKernel_common_ae_double_circle_control R p hp qdir qtest K hK
  generalize hkernel : canonicalBiparameterKernelIntegrand R p qdir qtest = G at *
  let r := E / 2
  have hr : 0 < r := half_pos hE
  have hrE : r < E := half_lt_self hE
  let ε := r / 2
  have hε : 0 < ε := half_pos hr
  let L := (8 / r) * C
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have heE : ε < E := (half_lt_self hr).trans hrE
  have hspatial (s : ℂ) (hs : ‖s‖ < ε) : Measurable (fun x : ℍ × ℍ =>
      G s (conj s) x.1 x.2) := by
    have hsE : s ∈ ball (0 : ℂ) E := mem_ball_zero_iff.mpr (hs.trans heE)
    have htE : conj s ∈ ball (0 : ℂ) E := by
      simpa only [mem_ball_zero_iff, norm_conj] using hs.trans heE
    let ss : ball (0 : ℂ) E := ⟨s, hsE⟩
    let tt : ball (0 : ℂ) E := ⟨conj s, htE⟩
    have hin : Measurable (fun x : ℍ × ℍ => (ss, (tt, x))) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    exact hjoint.comp hin
  have hPm (s : ℂ) (hs : ‖s‖ < ε) : Measurable (fun z : ℍ => ∫ ζ : ℍ,
      G s (conj s) z ζ ∂flatArea) :=
    (hspatial s hs).stronglyMeasurable.integral_prod_right'.measurable
  have h0ε : ‖(0 : ℂ)‖ < ε := by simpa only [norm_zero] using hε
  have hi (s : ℂ) (hs : ‖s‖ < ε) (z : ℍ) (hz : z ∈ K)
      (m : ℍ → ℝ) (hm : Integrable m flatArea)
      (hbound : ∀ᵐ ζ : ℍ ∂flatArea,
        ‖G s (conj s) z ζ‖ ≤ 4 * m ζ) :
      Integrable (fun ζ : ℍ =>
        G s (conj s) z ζ) flatArea := by
    apply (hm.const_mul 4).mono'
    · exact ((hspatial s hs).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact hbound
  refine ⟨ε, L, hε, hL, hPm, ?_, ?_⟩
  · intro z hz
    obtain ⟨m, A₁, A₂, hm0, hmm, hmi, hmC, hA₁m, hA₂m, hA₁i, hA₂i, hae⟩ :=
      hcontrol r hr hrE z hz
    let a := ∫ ζ : ℍ, A₁ ζ ∂flatArea
    let b := ∫ ζ : ℍ, A₂ ζ ∂flatArea
    let T : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ a +
      (ContinuousLinearMap.mul ℝ ℂ b).comp Complex.conjCLE.toContinuousLinearMap
    apply (hasFDerivAt_of_quadratic_remainder (L := T) hε
      (D := (8 / r ^ 2) * C) ?_).differentiableAt
    intro s hs
    have hsle : ‖s‖ ≤ r / 2 := hs.le
    have htle : ‖conj s‖ ≤ r / 2 := by simpa only [norm_conj] using hsle
    have h0le : ‖(0 : ℂ)‖ ≤ r / 2 := by simpa only [norm_zero] using hε.le
    have hIs := hi s hs z hz m hmi
      (hae.mono (fun _ h => (h.2.2 s (conj s) hsle htle).1))
    have hI0 := hi 0 h0ε z hz m hmi
      (hae.mono (fun _ h => by
        simpa only [map_zero] using (h.2.2 0 0 h0le h0le).1))
    simp only [map_zero] at hI0
    have hrew :
        (∫ ζ : ℍ, G s (conj s) z ζ ∂flatArea) -
        (∫ ζ : ℍ, G 0 (conj 0) z ζ ∂flatArea) -
          T s =
        ∫ ζ : ℍ, G s (conj s) z ζ -
          G 0 0 z ζ -
            A₁ ζ * s - A₂ ζ * conj s ∂flatArea := by
      simp only [T, add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.mul_apply', ContinuousLinearEquiv.coe_coe,
        Complex.conjCLE_apply, map_zero, sub_add_eq_sub_sub]
      rw [← integral_mul_const, ← integral_mul_const,
        ← integral_sub hIs hI0, ← integral_sub (hIs.sub' hI0) (hA₁i.mul_const s),
        ← integral_sub ((hIs.sub' hI0).sub' (hA₁i.mul_const s)) (hA₂i.mul_const (conj s))]
    rw [hrew]
    calc
      ‖∫ ζ : ℍ, G s (conj s) z ζ -
          G 0 0 z ζ -
            A₁ ζ * s - A₂ ζ * conj s ∂flatArea‖ ≤
          ∫ ζ : ℍ, ((8 / r ^ 2) * ‖s‖ ^ 2) * m ζ ∂flatArea := by
        apply norm_integral_le_of_norm_le (hmi.const_mul _)
        filter_upwards [hae] with ζ hζ
        have h := (hζ.2.2 s (conj s) hsle htle).2.2
        rw [norm_conj] at h
        convert h using 1; ring
      _ = ((8 / r ^ 2) * ‖s‖ ^ 2) * ∫ ζ : ℍ, m ζ ∂flatArea := integral_const_mul _ _
      _ ≤ ((8 / r ^ 2) * ‖s‖ ^ 2) * C := mul_le_mul_of_nonneg_left hmC (by positivity)
      _ = ((8 / r ^ 2) * C) * ‖s‖ ^ 2 := by ring
  · intro s hs z hz
    obtain ⟨m, A₁, A₂, hm0, hmm, hmi, hmC, hA₁m, hA₂m, hA₁i, hA₂i, hae⟩ :=
      hcontrol r hr hrE z hz
    have hsle : ‖s‖ ≤ r / 2 := hs.le
    have htle : ‖conj s‖ ≤ r / 2 := by simpa only [norm_conj] using hsle
    have h0le : ‖(0 : ℂ)‖ ≤ r / 2 := by simpa only [norm_zero] using hε.le
    have hIs := hi s hs z hz m hmi
      (hae.mono (fun _ h => (h.2.2 s (conj s) hsle htle).1))
    have hI0 := hi 0 h0ε z hz m hmi
      (hae.mono (fun _ h => by
        simpa only [map_zero] using (h.2.2 0 0 h0le h0le).1))
    simp only [map_zero] at hI0
    rw [map_zero, ← integral_sub hIs hI0]
    calc
      ‖∫ ζ : ℍ, G s (conj s) z ζ -
          G 0 0 z ζ ∂flatArea‖ ≤
          ∫ ζ : ℍ, ((8 / r) * ‖s‖) * m ζ ∂flatArea := by
        apply norm_integral_le_of_norm_le (hmi.const_mul _)
        filter_upwards [hae] with ζ hζ
        have h := (hζ.2.2 s (conj s) hsle htle).2.1
        rw [norm_conj] at h
        convert h using 1; ring
      _ = ((8 / r) * ‖s‖) * ∫ ζ : ℍ, m ζ ∂flatArea := integral_const_mul _ _
      _ ≤ ((8 / r) * ‖s‖) * C := mul_le_mul_of_nonneg_left hmC (by positivity)
      _ = L * ‖s‖ := by dsimp only [L]; ring

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation LiZhongQC WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "I" => Fin (3 * g - 3)
local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "ψ" => nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ
local notation "φ" => nativeWeilPeterssonBaseQuadratic R hp hg hgenus hΓ

private theorem pulled_axis_eq_actual_kernel_integral (j l : I) (s : ℂ) (z : ℍ) :
    ψ j (Pi.single l s) z = (12 / (Real.pi : ℂ)) * ∫ ζ : ℍ,
      canonicalBiparameterKernelIntegrand R p (q l) (q j) s (conj s) z ζ ∂flatArea := by
  have hmap := UpperHalfPlane.measurableEmbedding_coe.integral_map (μ := flatArea)
    (canonicalBiparameterKernelIntegrand R p (q l) (q j) s (conj s) z)
  rw [map_flat_coe] at hmap
  simpa only [nativeWeilPeterssonPulledQuadratic, nativeWeilPeterssonDeformationKernel,
    coordinateFamily_axis, canonicalBiparameterKernelIntegrand,
    canonicalBiparameterFamily_diagonal] using
    congrArg (fun w : ℂ => (12 / (Real.pi : ℂ)) * w) hmap

private theorem pulled_axis_compact_first_control (j l : I) (K : Set ℍ) (hK : IsCompact K) :
    ∃ ε L : ℝ, 0 < ε ∧ 0 ≤ L ∧
      (∀ s : ℂ, ‖s‖ < ε → Measurable (fun z : ℍ => ψ j (Pi.single l s) z)) ∧
      (∀ z ∈ K, DifferentiableAt ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0) ∧
      ∀ s : ℂ, ‖s‖ < ε → ∀ z ∈ K,
        ‖ψ j (Pi.single l s) z - φ j z‖ ≤ L * ‖s‖ := by
  obtain ⟨ε, L, hε, hL, hmeas, hdiff, hbound⟩ :=
    kernel_integral_first_parameter_control R p hp (q l) (q j) K hK
  let c : ℂ := 12 / (Real.pi : ℂ)
  let Lψ : ℝ := ‖c‖ * L
  have haxis (s : ℂ) (z : ℍ) :=
    pulled_axis_eq_actual_kernel_integral R hp hg hgenus hΓ j l s z
  refine ⟨ε, Lψ, hε, mul_nonneg (norm_nonneg _) hL, ?_, ?_, ?_⟩
  · intro s hs
    have hm : Measurable (fun z : ℍ => c * ∫ ζ : ℍ,
        canonicalBiparameterKernelIntegrand R p (q l) (q j) s (conj s) z ζ ∂flatArea) :=
      measurable_const.mul (hmeas s hs)
    convert hm using 1
    apply funext
    intro z
    exact haxis s z
  · intro z hz
    have hfun : (fun s : ℂ => ψ j (Pi.single l s) z) =
        (fun s : ℂ => c * ∫ ζ : ℍ,
          canonicalBiparameterKernelIntegrand R p (q l) (q j) s (conj s) z ζ ∂flatArea) :=
      funext (fun s => haxis s z)
    rw [hfun]
    exact (hdiff z hz).const_mul c
  · intro s hs z hz
    have hzero : ψ j (Pi.single l 0) z = φ j z := by
      simpa only [Pi.single_zero] using
        (nativeWeilPeterssonPulledQuadratic_zero R hp hg hgenus hΓ j z).2
    calc
      ‖ψ j (Pi.single l s) z - φ j z‖ =
          ‖c * ((∫ ζ : ℍ,
            canonicalBiparameterKernelIntegrand R p (q l) (q j) s (conj s) z ζ ∂flatArea) -
            ∫ ζ : ℍ, canonicalBiparameterKernelIntegrand R p (q l) (q j) 0 (conj 0) z ζ
              ∂flatArea)‖ := by
        rw [← hzero, haxis s z, haxis 0 z]
        congr 1
        ring
      _ ≤ ‖c‖ * (L * ‖s‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound s hs z hz) (norm_nonneg _)
      _ = Lψ * ‖s‖ := by dsimp only [Lψ]; ring

private theorem pulled_axis_direction_measurable (j l : I) (v : ℂ)
    (hdiff : ∀ z : ℍ, DifferentiableAt ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0)
    {ε : ℝ} (hε : 0 < ε)
    (hmeas : ∀ s : ℂ, ‖s‖ < ε → Measurable (fun z : ℍ => ψ j (Pi.single l s) z)) :
    Measurable (fun z : ℍ => fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 v) := by
  obtain ⟨a, ha⟩ := Filter.exists_seq_tendsto (𝓝[>] (0 : ℝ))
  let F : ℕ → ℍ → ℂ := fun n z => if ‖a n • v‖ < ε then
    (a n)⁻¹ • (ψ j (Pi.single l (a n • v)) z - ψ j (Pi.single l 0) z) else 0
  have h0 : ‖(0 : ℂ)‖ < ε := by simpa only [norm_zero] using hε
  have hFm (n : ℕ) : StronglyMeasurable (F n) := by
    by_cases hn : ‖a n • v‖ < ε
    · have hsub : StronglyMeasurable (fun z : ℍ =>
          ψ j (Pi.single l (a n • v)) z - ψ j (Pi.single l 0) z) :=
        ((hmeas _ hn).fun_sub (hmeas 0 h0)).stronglyMeasurable
      have hmul : StronglyMeasurable (fun z : ℍ => (a n)⁻¹ •
          (ψ j (Pi.single l (a n • v)) z - ψ j (Pi.single l 0) z)) :=
        stronglyMeasurable_const.fun_smul hsub
      simpa only [F, ite_eq_left hn] using hmul
    · simpa only [F, ite_eq_right hn] using
        (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℍ => (0 : ℂ)))
  have hscale : Tendsto (fun n => a n • v) atTop (𝓝 (0 : ℂ)) := by
    simpa only [zero_smul] using (ha.mono_right nhdsWithin_le_nhds).smul_const v
  have hsmall : ∀ᶠ n in atTop, ‖a n • v‖ < ε := by
    simpa only [mem_ball, dist_zero_right] using hscale.eventually (ball_mem_nhds (0 : ℂ) hε)
  have hlim : Tendsto F atTop
      (𝓝 (fun z : ℍ => fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 v)) := by
    rw [tendsto_pi_nhds]
    intro z
    have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      change HasFDerivAtFilter (fun t : ℝ => t • v)
        (ContinuousLinearMap.toSpanSingleton ℝ v) (𝓝 (0 : ℝ) ×ˢ pure 0)
      apply HasFDerivAtFilter.of_isLittleOTVS
      exact (Asymptotics.IsLittleOTVS.zero _ _).congr_left (fun t => by
        simp only [ContinuousLinearMap.toSpanSingleton_apply, sub_smul, sub_self,
          Pi.zero_apply])
    have hdir : HasDerivAt (fun t : ℝ => ψ j (Pi.single l (t • v)) z)
        (fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 v) 0 := by
      simpa only [Function.comp_def] using
        (hdiff z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp only [zero_smul])
    have hactual := hdir.tendsto_slope_zero_right.comp ha
    apply (tendsto_congr' (show (fun n => F n z) =ᶠ[atTop]
      (fun n => (a n)⁻¹ • (ψ j (Pi.single l (a n • v)) z - ψ j (Pi.single l 0) z)) from
        hsmall.mono (fun n hn => ite_eq_left hn))).2
    simpa only [Function.comp_def, zero_add, zero_smul] using hactual
  exact (stronglyMeasurable_of_tendsto atTop hFm hlim).measurable

private theorem complex_real_linear_map_from_directions (T : ℂ →L[ℝ] ℂ) :
    T = Complex.reCLM.smulRight (T 1) + Complex.imCLM.smulRight (T Complex.I) := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  calc
    T z = T (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg T hz
    _ = z.re • T 1 + z.im • T Complex.I := by rw [map_add, map_smul, map_smul]
    _ = (Complex.reCLM.smulRight (T 1) + Complex.imCLM.smulRight (T Complex.I)) z := rfl

/-- Along every actual harmonic coordinate axis the pulled quadratic has
its full real first derivative, a measurable real-linear derivative field,
and one basepoint Lipschitz bound on each compact source set. -/
theorem nativeWeilPeterssonPulledQuadratic_first_parameter_control :
    (∀ (j l : I) (z : ℍ),
      DifferentiableAt ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0) ∧
    (∀ j l : I,
      Measurable (fun z : ℍ =>
        fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0)) ∧
    ∀ (j l : I) (K : Set ℍ), IsCompact K →
      ∃ ε L : ℝ, 0 < ε ∧ 0 ≤ L ∧
        (∀ s : ℂ, ‖s‖ < ε →
          Measurable (fun z : ℍ => ψ j (Pi.single l s) z)) ∧
        ∀ s : ℂ, ‖s‖ < ε → ∀ z ∈ K,
          ‖ψ j (Pi.single l s) z - φ j z‖ ≤ L * ‖s‖ := by
  classical
  have hdiff (j l : I) (z : ℍ) :
      DifferentiableAt ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 := by
    obtain ⟨_, _, _, _, _, hd, _⟩ :=
      pulled_axis_compact_first_control R hp hg hgenus hΓ j l {z} isCompact_singleton
    exact hd z (mem_singleton z)
  refine ⟨hdiff, ?_, ?_⟩
  · intro j l
    obtain ⟨ε, _, hε, _, hm, _, _⟩ :=
      pulled_axis_compact_first_control R hp hg hgenus hΓ j l ∅ isCompact_empty
    have h₁ := pulled_axis_direction_measurable R hp hg hgenus hΓ j l 1 (hdiff j l) hε hm
    have hI := pulled_axis_direction_measurable R hp hg hgenus hΓ j l Complex.I
      (hdiff j l) hε hm
    let U₁ : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM
    let UI : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM
    have hM : Measurable (fun z : ℍ =>
        U₁ (fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 1) +
          UI (fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 Complex.I)) :=
      (U₁.continuous.measurable.comp h₁).fun_add (UI.continuous.measurable.comp hI)
    convert hM using 1
    apply funext
    intro z
    change fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 =
      Complex.reCLM.smulRight (fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 1) +
        Complex.imCLM.smulRight
          (fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0 Complex.I)
    exact complex_real_linear_map_from_directions
      (fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0)
  · intro j l K hK
    obtain ⟨ε, L, hε, hL, hm, _, hb⟩ :=
      pulled_axis_compact_first_control R hp hg hgenus hΓ j l K hK
    exact ⟨ε, L, hε, hL, hm, hb⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
