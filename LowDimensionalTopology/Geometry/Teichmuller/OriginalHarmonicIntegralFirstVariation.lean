module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPulledFirstParameters
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicInverseDensityControl
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicCoefficientIntegrals
public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# The two actual harmonic WP integral variations

The compact source-region bounds justify differentiation of the two
original coefficient integrals. The two derivative pairings are absolutely
integrable separately, and the actual reciprocal-density correction stays
in the resulting full real first-variation formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation LiZhongQC

private theorem product_basepoint_norm_bound
    {a a₀ b b₀ : ℂ} {u A B L M : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hL : 0 ≤ L) (_hM : 0 ≤ M)
    (ha₀ : ‖a₀‖ ≤ A) (hb₀ : ‖b₀‖ ≤ B)
    (ha : ‖a - a₀‖ ≤ L * u) (hb : ‖b - b₀‖ ≤ M * u) :
    ‖a * b - a₀ * b₀‖ ≤ ((A + L) * M + L * B) * u := by
  have ha' : ‖a‖ ≤ A + L := by
    have htriangle : ‖a‖ ≤ ‖a - a₀‖ + ‖a₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (a - a₀) a₀
    have hLu : L * u ≤ L := by nlinarith
    linarith
  have hidentity : a * b - a₀ * b₀ = a * (b - b₀) + (a - a₀) * b₀ := by ring
  rw [hidentity]
  calc
    ‖a * (b - b₀) + (a - a₀) * b₀‖ ≤
        ‖a * (b - b₀)‖ + ‖(a - a₀) * b₀‖ := norm_add_le _ _
    _ = ‖a‖ * ‖b - b₀‖ + ‖a - a₀‖ * ‖b₀‖ := by rw [norm_mul, norm_mul]
    _ ≤ (A + L) * (M * u) + (L * u) * B :=
      add_le_add (mul_le_mul ha' hb (norm_nonneg _) (by linarith [norm_nonneg a]))
        (mul_le_mul ha hb₀ (norm_nonneg _) (mul_nonneg hL hu₀))
    _ = ((A + L) * M + L * B) * u := by ring

private theorem harmonic_axis_weight_hasFDerivAt_zero (ν : ℂ) :
    HasFDerivAt (fun s : ℂ => (((1 - ‖s * ν‖ ^ 2) ^ 2 : ℝ) : ℂ))
      (0 : ℂ →L[ℝ] ℂ) 0 := by
  have hnorm : HasFDerivAt (fun s : ℂ => ‖s * ν‖ ^ 2)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
    simpa only [id_eq, zero_mul, map_zero, ContinuousLinearMap.zero_comp, smul_zero] using
      ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).mul_const ν).norm_sq
  have hreal : HasFDerivAt (fun s : ℂ => (1 - ‖s * ν‖ ^ 2) ^ 2)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
    simpa only [sub_zero, smul_zero] using
      ((hasFDerivAt_const (1 : ℝ) (0 : ℂ)).fun_sub hnorm).pow 2
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, ContinuousLinearMap.comp_zero] using
    Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) hreal

private theorem harmonic_axis_weight_basepoint_bound
    {ν s : ℂ} {N : ℝ} (_hN : 0 ≤ N) (hν : ‖ν‖ ≤ N) (hs : ‖s‖ ≤ 1) :
    ‖(((1 - ‖s * ν‖ ^ 2) ^ 2 : ℝ) : ℂ) - 1‖ ≤
      (2 * N ^ 2 + N ^ 4) * ‖s‖ := by
  let a : ℝ := ‖s * ν‖ ^ 2
  have ha₀ : 0 ≤ a := sq_nonneg _
  have hu₂ : ‖s‖ ^ 2 ≤ ‖s‖ := by nlinarith [norm_nonneg s]
  have hu₂₁ : ‖s‖ ^ 2 ≤ 1 := hu₂.trans hs
  have hu₄ : (‖s‖ ^ 2) ^ 2 ≤ ‖s‖ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ‖s‖) (sub_nonneg.mpr hu₂₁)]
  have ha : a ≤ N ^ 2 * ‖s‖ ^ 2 := by
    dsimp only [a]
    rw [norm_mul, mul_pow, mul_comm (‖s‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg ν) hν 2) (sq_nonneg _)
  have ha₂ : a ^ 2 ≤ N ^ 4 * ‖s‖ ^ 2 := by
    calc
      a ^ 2 ≤ (N ^ 2 * ‖s‖ ^ 2) ^ 2 := pow_le_pow_left₀ ha₀ ha 2
      _ = N ^ 4 * (‖s‖ ^ 2) ^ 2 := by ring
      _ ≤ N ^ 4 * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_left hu₄ (by positivity)
  have habs : |(1 - a) ^ 2 - 1| ≤ 2 * a + a ^ 2 := by
    calc
      |(1 - a) ^ 2 - 1| = |a ^ 2 - 2 * a| := by congr 1; ring
      _ ≤ |a ^ 2| + |2 * a| := abs_sub _ _
      _ = 2 * a + a ^ 2 := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]; ring
  calc
    ‖(((1 - ‖s * ν‖ ^ 2) ^ 2 : ℝ) : ℂ) - 1‖ = |(1 - a) ^ 2 - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * a + a ^ 2 := habs
    _ ≤ (2 * N ^ 2 + N ^ 4) * ‖s‖ ^ 2 := by nlinarith
    _ ≤ (2 * N ^ 2 + N ^ 4) * ‖s‖ := mul_le_mul_of_nonneg_left hu₂ (by positivity)

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "I" => Fin (3 * g - 3)
local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "ψ" => nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ
local notation "φ" => nativeWeilPeterssonBaseQuadratic R hp hg hgenus hΓ
local notation "Dψ" => nativeWeilPeterssonPulledQuadraticVariation R hp hg hgenus hΓ
include hp in
private theorem harmonicPlane_upper_continuous
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    Continuous (fun z : ℍ => harmonicPlane R p Q z) := by
  convert NativeHarmonicBeltrami.coefficient_continuous R p hp Q using 1
  apply funext
  intro z
  exact harmonicPlane_eq_coefficient R p Q z

private theorem first_outer_integral_derivative
    (F : Set ℍ) (hF : MeasurableSet F) (hK : IsCompact (closure F)) (j k l : I) :
    ∃ T : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun s : ℂ => ∫ z in F,
        harmonicPlane R p (q j) z * ψ k (Pi.single l s) z ∂WeilPetersson.flatArea) T 0 ∧
      ∀ a : ℂ,
        Integrable (fun z : ℍ => (z.im ^ 2 : ℂ) * Dψ k l a z * conj (φ j z))
          (WeilPetersson.flatArea.restrict F) ∧
        T a = WeilPetersson.quadraticPairing F (Dψ k l a) (φ j) := by
  let : IsFiniteMeasureOnCompacts WeilPetersson.flatArea :=
    IsFiniteMeasureOnCompacts.comap' (volume : Measure ℂ)
      UpperHalfPlane.continuous_coe UpperHalfPlane.measurableEmbedding_coe
  have hFlt : WeilPetersson.flatArea F < ⊤ :=
    (measure_mono (subset_closure : F ⊆ closure F)).trans_lt hK.measure_lt_top
  let : IsFiniteMeasure (WeilPetersson.flatArea.restrict F) :=
    isFiniteMeasure_restrict.mpr hFlt.ne
  let μ := WeilPetersson.flatArea.restrict F
  let ν : ℍ → ℂ := fun z => harmonicPlane R p (q j) z
  let DP : ℍ → ℂ →L[ℝ] ℂ := fun z =>
    fderiv ℝ (fun s : ℂ => ψ k (Pi.single l s) z) 0
  let J : ℂ → ℍ → ℂ := fun s z => ν z * ψ k (Pi.single l s) z
  let DJ : ℍ → ℂ →L[ℝ] ℂ := fun z => ν z • DP z
  obtain ⟨hdiff, hDmeas, hcompact⟩ :=
    nativeWeilPeterssonPulledQuadratic_first_parameter_control R hp hg hgenus hΓ
  obtain ⟨ε, L, hε, hL, hmeas, hbound⟩ := hcompact k l (closure F) hK
  have hν : Continuous ν := harmonicPlane_upper_continuous R hp (q j)
  obtain ⟨N₀, hN₀⟩ := hK.bddAbove_image hν.norm.continuousOn
  let N := max N₀ 0
  have hN : 0 ≤ N := le_max_right _ _
  have hνbound (z : ℍ) (hz : z ∈ closure F) : ‖ν z‖ ≤ N :=
    (hN₀ (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hzero (i : I) (z : ℍ) : ψ i (Pi.single l 0) z = φ i z := by
    simpa only [Pi.single_zero] using
      (nativeWeilPeterssonPulledQuadratic_zero R hp hg hgenus hΓ i z).2
  have hφ : Continuous (φ k) := WeilPetersson.liftQuadratic_continuous R p hp (q k)
  have hJ0 : Integrable (J 0) μ := by
    have hi : IntegrableOn (fun z : ℍ => ν z * φ k z) (closure F)
        WeilPetersson.flatArea :=
      (hν.mul hφ).continuousOn.integrableOn_compact hK
    have hiF := hi.mono_set (subset_closure : F ⊆ closure F)
    apply Integrable.congr hiF
    filter_upwards with z
    dsimp only [J]
    rw [hzero]
  have hJm (s : ℂ) (hs : s ∈ ball (0 : ℂ) ε) : AEStronglyMeasurable (J s) μ :=
    (hν.measurable.mul (hmeas s (mem_ball_zero_iff.mp hs))).aestronglyMeasurable
  let : NormedSpace ℂ (ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  let : IsBoundedSMul ℂ (ℂ →L[ℝ] ℂ) := NormedSpace.toIsBoundedSMul
  let : ContinuousSMul ℂ (ℂ →L[ℝ] ℂ) := IsBoundedSMul.continuousSMul
  have hDJm : AEStronglyMeasurable DJ μ :=
    (hν.measurable.stronglyMeasurable.fun_smul
      (hDmeas k l).stronglyMeasurable).aestronglyMeasurable
  have hLip : ∀ᵐ z : ℍ ∂μ, ∀ s ∈ ball (0 : ℂ) ε,
      ‖J s z - J 0 z‖ ≤ (N * L) * ‖s - 0‖ := by
    filter_upwards [ae_restrict_mem hF] with z hz
    intro s hs
    have hzK : z ∈ closure F := subset_closure hz
    have heq : J s z - J 0 z = ν z * (ψ k (Pi.single l s) z - φ k z) := by
      dsimp only [J]
      rw [hzero]
      ring
    rw [heq, norm_mul, sub_zero]
    calc
      ‖ν z‖ * ‖ψ k (Pi.single l s) z - φ k z‖ ≤ N * (L * ‖s‖) :=
        mul_le_mul (hνbound z hzK) (hbound s (mem_ball_zero_iff.mp hs) z hzK)
          (norm_nonneg _) hN
      _ = (N * L) * ‖s‖ := by ring
  have hDJ (z : ℍ) : HasFDerivAt (fun s : ℂ => J s z) (DJ z) 0 :=
    (hdiff k l z).hasFDerivAt.const_mul (ν z)
  obtain ⟨hDJi, hInt⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F := J) (F' := DJ) (bound := fun _ => N * L)
    (ball_mem_nhds (0 : ℂ) hε) hJm hJ0 hDJm hLip (integrable_const _)
      (Eventually.of_forall hDJ)
  refine ⟨∫ z : ℍ, DJ z ∂μ, hInt, ?_⟩
  intro a
  have heval (z : ℍ) : DJ z a = (z.im ^ 2 : ℂ) * Dψ k l a z * conj (φ j z) := by
    simp only [DJ, DP, ν, smul_apply, smul_eq_mul,
      harmonicPlane, nativeWeilPeterssonPulledQuadraticVariation,
      nativeWeilPeterssonBaseQuadratic, UpperHalfPlane.coe_im]
    ring
  have hpair : Integrable
      (fun z : ℍ => (z.im ^ 2 : ℂ) * Dψ k l a z * conj (φ j z)) μ := by
    exact (hDJi.apply_continuousLinearMap a).congr
      (Eventually.of_forall heval)
  refine ⟨hpair, ?_⟩
  rw [ContinuousLinearMap.integral_apply hDJi]
  unfold WeilPetersson.quadraticPairing WeilPetersson.weightedPairing
  simp only [Complex.ofReal_pow]
  exact integral_congr_ae (Eventually.of_forall heval)

private theorem second_outer_integral_derivative
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (F : Set ℍ) (hF : MeasurableSet F) (hK : IsCompact (closure F)) (j k l : I) :
    ∃ T : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun s : ℂ => ∫ z in F,
        ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) *
          (((1 - ‖s * harmonicPlane R p (q l) z‖ ^ 2) ^ 2 : ℝ) : ℂ) *
            ((coordinateDensity R p q (Pi.single l s) z)⁻¹ : ℂ)
              ∂WeilPetersson.flatArea) T 0 ∧
      ∀ a : ℂ, T a =
        WeilPetersson.quadraticPairing F (φ k) (Dψ j l a) +
        WeilPetersson.quadraticPairing F (Dψ k l a) (φ j) +
        nativeWeilPeterssonDensityCorrection R hp hg hgenus hΓ F j k l a := by
  let : IsFiniteMeasureOnCompacts WeilPetersson.flatArea :=
    IsFiniteMeasureOnCompacts.comap' (volume : Measure ℂ)
      UpperHalfPlane.continuous_coe UpperHalfPlane.measurableEmbedding_coe
  have hFlt : WeilPetersson.flatArea F < ⊤ :=
    (measure_mono (subset_closure : F ⊆ closure F)).trans_lt hK.measure_lt_top
  let : IsFiniteMeasure (WeilPetersson.flatArea.restrict F) :=
    isFiniteMeasure_restrict.mpr hFlt.ne
  let μ := WeilPetersson.flatArea.restrict F
  let ν : ℍ → ℂ := fun z => harmonicPlane R p (q l) z
  let r : ℂ → ℍ → ℂ := fun s z => ((coordinateDensity R p q (Pi.single l s) z)⁻¹ : ℂ)
  let δ : ℂ → ℍ → ℂ := fun s z => (((1 - ‖s * ν z‖ ^ 2) ^ 2 : ℝ) : ℂ)
  let DPj : ℍ → ℂ →L[ℝ] ℂ := fun z =>
    fderiv ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0
  let DPk : ℍ → ℂ →L[ℝ] ℂ := fun z =>
    fderiv ℝ (fun s : ℂ => ψ k (Pi.single l s) z) 0
  let Dr : ℍ → ℂ →L[ℝ] ℂ := fun z => fderiv ℝ (fun s : ℂ => r s z) 0
  let J : ℂ → ℍ → ℂ := fun s z =>
    ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) * δ s z * r s z
  let DJ : ℍ → ℂ →L[ℝ] ℂ := fun z =>
    ((z.im ^ 2 : ℂ) * conj (φ j z)) • DPk z +
      ((z.im ^ 2 : ℂ) * φ k z) •
        (Complex.conjCLE.toContinuousLinearMap.comp (DPj z)) +
      (φ k z * conj (φ j z)) • Dr z
  obtain ⟨hdiff, hDmeas, hcompact⟩ :=
    nativeWeilPeterssonPulledQuadratic_first_parameter_control R hp hg hgenus hΓ
  obtain ⟨εj, Lj, hεj, hLj, hmj, hbj⟩ := hcompact j l (closure F) hK
  obtain ⟨εk, Lk, hεk, hLk, hmk, hbk⟩ := hcompact k l (closure F) hK
  obtain ⟨εr, Lr, hεr, hLr, hbr⟩ :=
    canonicalFamily_inverse_density_compact_lipschitz R p hp (q l) (closure F) hK
  obtain ⟨_, _, _, _, _, _, _, ⟨εc, hεc, hC1⟩, _⟩ := hjets X R Γ p hp (q l)
  let ε := min (min εj εk) (min εr (min εc 1))
  have hε : 0 < ε := lt_min (lt_min hεj hεk) (lt_min hεr (lt_min hεc zero_lt_one))
  have hej : ε ≤ εj := (min_le_left _ _).trans (min_le_left _ _)
  have hek : ε ≤ εk := (min_le_left _ _).trans (min_le_right _ _)
  have her : ε ≤ εr := (min_le_right _ _).trans (min_le_left _ _)
  have hec : ε ≤ εc := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he1 : ε ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hzero (i : I) (z : ℍ) : ψ i (Pi.single l 0) z = φ i z := by
    simpa only [Pi.single_zero] using
      (nativeWeilPeterssonPulledQuadratic_zero R hp hg hgenus hΓ i z).2
  have hr0 (z : ℍ) : r 0 z = (z.im ^ 2 : ℂ) := by
    norm_num [r, coordinateDensity, coordinateFamily_axis, canonicalFamily_zero,
      jacobian, dz, dzbar, fderiv_id]
  have hδ0 (z : ℍ) : δ 0 z = 1 := by norm_num [δ]
  have hφj : Continuous (φ j) := WeilPetersson.liftQuadratic_continuous R p hp (q j)
  have hφk : Continuous (φ k) := WeilPetersson.liftQuadratic_continuous R p hp (q k)
  have hν : Continuous ν := harmonicPlane_upper_continuous R hp (q l)
  have hy : Continuous (fun z : ℍ => z.im ^ 2) := UpperHalfPlane.continuous_im.pow 2
  have hyC : Continuous (fun z : ℍ => (z.im ^ 2 : ℂ)) :=
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2
  let B : ℍ → ℝ := fun z => max ‖φ j z‖ (max ‖φ k z‖ (max ‖ν z‖ (z.im ^ 2)))
  have hB : Continuous B := hφj.norm.max (hφk.norm.max (hν.norm.max hy))
  obtain ⟨M₀, hM₀⟩ := hK.bddAbove_image hB.continuousOn
  let M := max M₀ 1
  have hM : 0 ≤ M := zero_le_one.trans (le_max_right _ _)
  have hMb (z : ℍ) (hz : z ∈ closure F) : B z ≤ M :=
    (hM₀ (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hbφj (z : ℍ) (hz : z ∈ closure F) : ‖φ j z‖ ≤ M :=
    (le_max_left _ _).trans (hMb z hz)
  have hbφk (z : ℍ) (hz : z ∈ closure F) : ‖φ k z‖ ≤ M :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hMb z hz)
  have hbν (z : ℍ) (hz : z ∈ closure F) : ‖ν z‖ ≤ M :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hMb z hz)
  have hby (z : ℍ) (hz : z ∈ closure F) : z.im ^ 2 ≤ M :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hMb z hz)
  let Lδ := 2 * M ^ 2 + M ^ 4
  let Lp := (M + Lk) * Lj + Lk * M
  let Lpd := (M ^ 2 + Lp) * Lδ + Lp
  let Ltotal := (M ^ 2 + Lpd) * Lr + Lpd * M
  have hLδ : 0 ≤ Lδ := by dsimp only [Lδ]; positivity
  have hLp : 0 ≤ Lp := by dsimp only [Lp]; positivity
  have hLpd : 0 ≤ Lpd := by dsimp only [Lpd]; positivity
  have hLtotal : 0 ≤ Ltotal := by dsimp only [Ltotal]; positivity
  have hrmeas (s : ℂ) (hs : ‖s‖ < εc) : Measurable (r s) := by
    let f : ℂ → ℂ := canonicalFamily R p (q l) s
    have hf : Continuous (fun z : ℍ => f z) :=
      (hC1 s hs).continuousOn.comp_continuous
        UpperHalfPlane.continuous_coe (fun z : ℍ => z.im_pos)
    have hm₁ : Measurable (fun z : ℍ => dz f z) :=
      (measurable_dz f).comp UpperHalfPlane.continuous_coe.measurable
    have hm₂ : Measurable (fun z : ℍ => dzbar f z) :=
      (measurable_dzbar f).comp UpperHalfPlane.continuous_coe.measurable
    have hJ : Measurable (fun z : ℍ => jacobian f z) := by
      simpa only [jacobian] using (hm₁.norm.pow_const 2).fun_sub (hm₂.norm.pow_const 2)
    have hρ : Measurable (fun z : ℍ => coordinateDensity R p q (Pi.single l s) z) := by
      simpa only [coordinateDensity, coordinateFamily_axis, f, Function.comp_def] using
        hJ.fun_div ((Complex.continuous_im.measurable.comp hf.measurable).pow_const 2)
    simpa only [r, Complex.ofReal_inv] using hρ.fun_inv.complex_ofReal
  have hδmeas (s : ℂ) : Measurable (δ s) :=
    ((measurable_const.sub
      ((measurable_const.mul hν.measurable).norm.pow_const 2)).pow_const 2).complex_ofReal
  have hJmeas (s : ℂ) (hs : s ∈ ball (0 : ℂ) ε) : AEStronglyMeasurable (J s) μ := by
    have hs' := mem_ball_zero_iff.mp hs
    exact ((((hmk s (hs'.trans_le hek)).mul
      (Complex.continuous_conj.measurable.comp (hmj s (hs'.trans_le hej)))).mul
      (hδmeas s)).mul (hrmeas s (hs'.trans_le hec))).aestronglyMeasurable
  have hDr0 (z : ℍ) : Dr z = 0 :=
    (hasFDerivAt_nativeWeilPeterssonInverseDensity_zero R hp hg hgenus hΓ hjets l z).fderiv
  have hDrmeas : Measurable Dr := by
    have heq : Dr = fun _ : ℍ => (0 : ℂ →L[ℝ] ℂ) := funext hDr0
    rw [heq]
    exact measurable_const
  have hconjDP : Measurable
      (fun z : ℍ => Complex.conjCLE.toContinuousLinearMap.comp (DPj z)) :=
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ Complex.conjCLE.toContinuousLinearMap).continuous.measurable.comp
      (hDmeas j l)
  have hconjφj : Measurable (fun z : ℍ => conj (φ j z)) :=
    Complex.continuous_conj.measurable.comp hφj.measurable
  let : NormedSpace ℂ (ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  let : IsBoundedSMul ℂ (ℂ →L[ℝ] ℂ) := NormedSpace.toIsBoundedSMul
  let : ContinuousSMul ℂ (ℂ →L[ℝ] ℂ) := IsBoundedSMul.continuousSMul
  have hDJmeas : AEStronglyMeasurable DJ μ :=
    ((((hyC.measurable.fun_mul hconjφj).stronglyMeasurable.fun_smul
      (hDmeas k l).stronglyMeasurable).fun_add
      ((hyC.measurable.fun_mul hφk.measurable).stronglyMeasurable.fun_smul
        hconjDP.stronglyMeasurable)).fun_add
      ((hφk.measurable.fun_mul hconjφj).stronglyMeasurable.fun_smul
        hDrmeas.stronglyMeasurable)).aestronglyMeasurable
  have hJ0 : Integrable (J 0) μ := by
    have hc : Continuous (fun z : ℍ => φ k z * conj (φ j z) * (z.im ^ 2 : ℂ)) :=
      (hφk.mul (Complex.continuous_conj.comp hφj)).mul
        hyC
    have hi : IntegrableOn (fun z : ℍ => φ k z * conj (φ j z) * (z.im ^ 2 : ℂ))
        (closure F) WeilPetersson.flatArea := hc.continuousOn.integrableOn_compact hK
    apply Integrable.congr (hi.mono_set (subset_closure : F ⊆ closure F))
    filter_upwards with z
    simp only [J, hzero, hδ0, hr0, mul_one]
  have hLip : ∀ᵐ z : ℍ ∂μ, ∀ s ∈ ball (0 : ℂ) ε,
      ‖J s z - J 0 z‖ ≤ Ltotal * ‖s - 0‖ := by
    filter_upwards [ae_restrict_mem hF] with z hz
    intro s hs
    have hs' := mem_ball_zero_iff.mp hs
    have hzK : z ∈ closure F := subset_closure hz
    have hs1 : ‖s‖ ≤ 1 := hs'.le.trans he1
    have hproduct : ‖ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) -
        φ k z * conj (φ j z)‖ ≤ Lp * ‖s‖ := by
      apply product_basepoint_norm_bound (norm_nonneg s) hs1 hLk hLj
        (hbφk z hzK) (by simpa only [norm_conj] using hbφj z hzK)
        (hbk s (hs'.trans_le hek) z hzK)
      simpa only [← map_sub, norm_conj] using hbj s (hs'.trans_le hej) z hzK
    have hbase : ‖φ k z * conj (φ j z)‖ ≤ M ^ 2 := by
      rw [norm_mul, norm_conj, pow_two]
      exact mul_le_mul (hbφk z hzK) (hbφj z hzK) (norm_nonneg _) hM
    have hproductδ : ‖ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) * δ s z -
        φ k z * conj (φ j z)‖ ≤ Lpd * ‖s‖ := by
      simpa only [norm_one, mul_one, Lpd] using
        product_basepoint_norm_bound (norm_nonneg s) hs1 hLp hLδ hbase
          (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hproduct
          (harmonic_axis_weight_basepoint_bound hM (hbν z hzK) hs1)
    have hrbound : ‖r s z - (z.im ^ 2 : ℂ)‖ ≤ Lr * ‖s‖ := by
      simpa only [r, coordinateDensity, coordinateFamily_axis, transportedHyperbolicDensity] using
        hbr s (hs'.trans_le her) z hzK
    have hmul := product_basepoint_norm_bound (norm_nonneg s) hs1 hLpd hLr hbase
      (by simpa only [norm_pow, Complex.norm_real, Real.norm_of_nonneg z.im_pos.le] using hby z hzK)
      hproductδ hrbound
    simpa only [J, hzero, hδ0, hr0, mul_one, sub_zero, Ltotal] using hmul
  have hDJ (z : ℍ) : HasFDerivAt (fun s : ℂ => J s z) (DJ z) 0 := by
    have hk : HasFDerivAt (fun s : ℂ => ψ k (Pi.single l s) z) (DPk z) 0 :=
      (hdiff k l z).hasFDerivAt
    have hj : HasFDerivAt (fun s : ℂ => conj (ψ j (Pi.single l s) z))
        (Complex.conjCLE.toContinuousLinearMap.comp (DPj z)) 0 :=
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (0 : ℂ)
        (hdiff j l z).hasFDerivAt
    have hδ : HasFDerivAt (fun s : ℂ => δ s z) (0 : ℂ →L[ℝ] ℂ) 0 :=
      harmonic_axis_weight_hasFDerivAt_zero (ν z)
    have hr : HasFDerivAt (fun s : ℂ => r s z) (Dr z) 0 :=
      (hasFDerivAt_nativeWeilPeterssonInverseDensity_zero
        R hp hg hgenus hΓ hjets l z).differentiableAt.hasFDerivAt
    have hprod := ((hk.fun_mul hj).fun_mul hδ).fun_mul hr
    convert hprod using 1
    apply ContinuousLinearMap.ext
    intro a
    simp only [DJ, hzero, hr0, hδ0, add_apply,
      smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, zero_apply, mul_zero,
      zero_add, mul_one, one_mul]
    ring
  obtain ⟨hDJi, hInt⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F := J) (F' := DJ) (bound := fun _ => Ltotal)
    (ball_mem_nhds (0 : ℂ) hε) hJmeas hJ0 hDJmeas hLip (integrable_const _)
      (Eventually.of_forall hDJ)
  obtain ⟨_, _, hpair₂⟩ := first_outer_integral_derivative R hp hg hgenus hΓ F hF hK j k l
  obtain ⟨_, _, hpairSwap⟩ := first_outer_integral_derivative R hp hg hgenus hΓ F hF hK k j l
  refine ⟨∫ z : ℍ, DJ z ∂μ, hInt, ?_⟩
  intro a
  have hpair₁ : Integrable
      (fun z : ℍ => (z.im ^ 2 : ℂ) * φ k z * conj (Dψ j l a z)) μ := by
    have hconj := Complex.conjCLE.toContinuousLinearMap.integrable_comp (hpairSwap a).1
    apply hconj.congr
    filter_upwards with z
    change conj ((z.im ^ 2 : ℂ) * Dψ j l a z * conj (φ k z)) = _
    simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hpair₂i := (hpair₂ a).1
  have heval (z : ℍ) : DJ z a =
      (z.im ^ 2 : ℂ) * φ k z * conj (Dψ j l a z) +
        (z.im ^ 2 : ℂ) * Dψ k l a z * conj (φ j z) +
        conj (φ j z) * φ k z * Dr z a := by
    simp only [DJ, DPj, DPk, add_apply,
      smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, nativeWeilPeterssonPulledQuadraticVariation]
    ring
  have hdensity : Integrable (fun z : ℍ => conj (φ j z) * φ k z * Dr z a) μ := by
    convert ((hDJi.apply_continuousLinearMap a).sub' hpair₁).sub' hpair₂i using 1
    apply funext
    intro z
    rw [heval]
    ring
  rw [ContinuousLinearMap.integral_apply hDJi]
  unfold WeilPetersson.quadraticPairing WeilPetersson.weightedPairing
    nativeWeilPeterssonDensityCorrection
  simp only [Complex.ofReal_pow]
  rw [← integral_add hpair₁ hpair₂i, ← integral_add (hpair₁.fun_add hpair₂i) hdensity]
  exact integral_congr_ae (Eventually.of_forall heval)

/-- The two original coefficient integrals have their full real first
variations on every genuine compact source region. Both pairing terms are
absolutely integrable separately, and the actual density correction is
retained. -/
theorem nativeWeilPeterssonHarmonicIntegralFirstVariation
    (hfree : ActsFreely Γ) (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) :
    LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth := by
  classical
  intro P F hF hK
  let h := nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth (basePoint R)
  have hFmeas : MeasurableSet F := hF.1.measurableSet
  have hfirst (j k l : I) : ∃ T : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun s : ℂ => h j k (Pi.single l s)) T 0 ∧
      ∀ a : ℂ,
        Integrable (fun z : ℍ => (z.im ^ 2 : ℂ) * Dψ k l a z * conj (φ j z))
          (WeilPetersson.flatArea.restrict F) ∧
        T a = WeilPetersson.quadraticPairing F (Dψ k l a) (φ j) := by
    obtain ⟨T, hd, hformula⟩ := first_outer_integral_derivative
      R hp hg hgenus hΓ F hFmeas hK j k l
    have heq : (fun s : ℂ => h j k (Pi.single l s)) =ᶠ[𝓝 0]
        (fun s : ℂ => ∫ z in F,
          harmonicPlane R p (q j) z * ψ k (Pi.single l s) z ∂WeilPetersson.flatArea) :=
      (nativeWeilPeterssonLocalCoefficient_axis_integral_representations
        R hp hg hgenus hΓ hfree hsmooth hjets P F hF j k l).mono (fun _ hs => hs.2.2.1)
    exact ⟨T, hd.congr_of_eventuallyEq heq, hformula⟩
  have hsecond (j k l : I) : ∃ T : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun s : ℂ => h j k (Pi.single l s)) T 0 ∧
      ∀ a : ℂ, T a =
        WeilPetersson.quadraticPairing F (φ k) (Dψ j l a) +
        WeilPetersson.quadraticPairing F (Dψ k l a) (φ j) +
        nativeWeilPeterssonDensityCorrection R hp hg hgenus hΓ F j k l a := by
    obtain ⟨T, hd, hformula⟩ := second_outer_integral_derivative
      R hp hg hgenus hΓ hjets F hFmeas hK j k l
    have heq : (fun s : ℂ => h j k (Pi.single l s)) =ᶠ[𝓝 0]
        (fun s : ℂ => ∫ z in F,
          ψ k (Pi.single l s) z * conj (ψ j (Pi.single l s) z) *
            (((1 - ‖s * harmonicPlane R p (q l) z‖ ^ 2) ^ 2 : ℝ) : ℂ) *
              ((coordinateDensity R p q (Pi.single l s) z)⁻¹ : ℂ)
                ∂WeilPetersson.flatArea) := by
      filter_upwards [nativeWeilPeterssonLocalCoefficient_axis_integral_representations
        R hp hg hgenus hΓ hfree hsmooth hjets P F hF j k l] with s hs
      simpa only [Complex.ofReal_inv, div_eq_mul_inv] using hs.2.2.2
    exact ⟨T, hd.congr_of_eventuallyEq heq, hformula⟩
  obtain ⟨hψdiff, _, _⟩ :=
    nativeWeilPeterssonPulledQuadratic_first_parameter_control R hp hg hgenus hΓ
  refine ⟨?_, hψdiff, ?_⟩
  · intro j k l
    obtain ⟨_, hd, _⟩ := hfirst j k l
    exact hd.differentiableAt
  · intro j k l a
    obtain ⟨T₁, hd₁, hformula₁⟩ := hfirst j k l
    obtain ⟨_, _, hformulaSwap⟩ := hfirst k j l
    obtain ⟨T₂, hd₂, hformula₂⟩ := hsecond j k l
    have hpair₁ : Integrable
        (fun z : ℍ => (z.im ^ 2 : ℂ) * φ k z * conj (Dψ j l a z))
          (WeilPetersson.flatArea.restrict F) := by
      have hc := Complex.conjCLE.toContinuousLinearMap.integrable_comp (hformulaSwap a).1
      apply hc.congr
      filter_upwards with z
      change conj ((z.im ^ 2 : ℂ) * Dψ j l a z * conj (φ k z)) = _
      simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
      ring
    refine ⟨hpair₁, (hformula₁ a).1, ?_, ?_⟩
    · rw [hd₂.fderiv]
      exact hformula₂ a
    · rw [hd₁.fderiv]
      exact (hformula₁ a).2

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
