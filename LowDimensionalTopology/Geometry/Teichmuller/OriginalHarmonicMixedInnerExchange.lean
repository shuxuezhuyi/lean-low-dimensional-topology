module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicDoubleCircleControl
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The finite mixed parameter derivative inside the actual inner integral

The common full-H majorant for the cross-half-plane kernel also bounds its
first two parameter derivatives by scalar Cauchy estimates. Two dominated
integral derivatives therefore give its actual mixed inner derivative.
Identification with the singular principal-value convolution remains separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC WeilPetersson

private theorem inner_deriv_norm_bound {f : ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball 0 r))
    (hb : ∀ t ∈ ball (0 : ℂ) r, ‖f t‖ ≤ M)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) (r / 2)) :
    ‖deriv f t‖ ≤ M / (r / 2) := by
  have hsub : closedBall t (r / 2) ⊆ ball (0 : ℂ) r := by
    intro u hu
    rw [mem_closedBall] at hu
    rw [mem_ball] at ht ⊢
    linarith [dist_triangle u t 0]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
    (hf.diffContOnCl_ball hsub) (fun u hu => hb u (hsub (sphere_subset_closedBall hu)))

private theorem inner_deriv_zero_aestronglyMeasurable
    {F : ℂ → ℍ → ℂ} {r : ℝ} (hr : 0 < r)
    (hm : ∀ s : ℂ, ‖s‖ < r → AEStronglyMeasurable (F s) flatArea)
    (hd : ∀ᵐ ζ : ℍ ∂flatArea, DifferentiableAt ℂ (fun s => F s ζ) 0) :
    AEStronglyMeasurable (fun ζ : ℍ => deriv (fun s => F s ζ) 0) flatArea := by
  obtain ⟨a, ha⟩ := Filter.exists_seq_tendsto (𝓝[≠] (0 : ℂ))
  let Q : ℕ → ℍ → ℂ := fun n ζ =>
    if ‖a n‖ < r then (a n)⁻¹ * (F (a n) ζ - F 0 ζ) else 0
  have h0 : ‖(0 : ℂ)‖ < r := by simpa only [norm_zero] using hr
  have hQ (n : ℕ) : AEStronglyMeasurable (Q n) flatArea := by
    by_cases hn : ‖a n‖ < r
    · simpa only [Q, ite_eq_left hn] using ((hm (a n) hn).fun_sub (hm 0 h0)).const_mul ((a n)⁻¹)
    · simpa only [Q, ite_eq_right hn] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℍ => (0 : ℂ)) flatArea)
  have hsmall : ∀ᶠ n in atTop, ‖a n‖ < r := by
    simpa only [mem_ball, dist_zero_right] using
      (ha.mono_right nhdsWithin_le_nhds).eventually (ball_mem_nhds (0 : ℂ) hr)
  apply aestronglyMeasurable_of_tendsto_ae atTop hQ
  filter_upwards [hd] with ζ hζ
  have hlim := hζ.hasDerivAt.tendsto_slope_zero.comp ha
  apply (tendsto_congr' (show (fun n => Q n ζ) =ᶠ[atTop]
    (fun n => (a n)⁻¹ * (F (a n) ζ - F 0 ζ)) from
      hsmall.mono (fun n hn => ite_eq_left hn))).2
  simpa only [zero_add, smul_eq_mul, Function.comp_def] using hlim

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem kernel_separately_holomorphic
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ζ : ℍ,
      (∀ t : ℂ, ‖t‖ < ε → DifferentiableOn ℂ
        (fun s => canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ) (ball 0 ε)) ∧
      (∀ s : ℂ, ‖s‖ < ε → DifferentiableOn ℂ
        (fun t => canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ) (ball 0 ε)) := by
  obtain ⟨ε₁, hε₁, _, hdzfirst, hdzsecond, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control R p hp qdir
  obtain ⟨ε₂, hε₂, hspec, hfirst, hsecond⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp qdir
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := min_le_right _ _
  refine ⟨ε, hε, ?_⟩
  intro z ζ
  have hzU : (z : ℂ) ∈ upperHalf ∪ lowerHalf := Or.inl z.im_pos
  have hζL : conj (ζ : ℂ) ∈ upperHalf ∪ lowerHalf := by
    right
    change (conj (ζ : ℂ)).im < 0
    simpa only [conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr ζ.im_pos
  have hdistinct : (z : ℂ) ≠ conj (ζ : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [conj_im, UpperHalfPlane.coe_im] at hi
    linarith [z.im_pos, ζ.im_pos]
  have hden (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      canonicalBiparameterFamily R p qdir s t z -
        canonicalBiparameterFamily R p qdir s t (conj (ζ : ℂ)) ≠ 0 := by
    obtain ⟨K, hK⟩ := (hspec s t (hs.trans_le he₂) (ht.trans_le he₂)).2.1
    apply sub_ne_zero.mpr
    exact fun h => hdistinct (hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h)
  let : NormedSpace ℂ ℂ := NormedField.toNormedSpace
  constructor
  · intro t ht
    have hz := ((hdzfirst t (ht.trans_le he₁) z hzU).1).mono (ball_subset_ball he₁)
    have hζ := ((hdzfirst t (ht.trans_le he₁) (conj (ζ : ℂ)) hζL).1).mono
      (ball_subset_ball he₁)
    have hvz := (hfirst t (ht.trans_le he₂) (z : ℂ)).mono (ball_subset_ball he₂)
    have hvζ := (hfirst t (ht.trans_le he₂) (conj (ζ : ℂ))).mono (ball_subset_ball he₂)
    change DifferentiableOn ℂ (fun s =>
      (dz (canonicalBiparameterFamily R p qdir s t) z *
        dz (canonicalBiparameterFamily R p qdir s t) (conj (ζ : ℂ)) /
          (canonicalBiparameterFamily R p qdir s t z -
            canonicalBiparameterFamily R p qdir s t (conj (ζ : ℂ))) ^ 2) ^ 2 *
        conj (harmonicPlane R p qtest (ζ : ℂ))) (ball 0 ε)
    exact (((hz.fun_mul hζ).fun_div ((hvz.fun_sub hvζ).fun_pow 2)
      (fun s hs => pow_ne_zero 2 (hden s t (mem_ball_zero_iff.mp hs) ht))).fun_pow 2).mul_const
        (conj (harmonicPlane R p qtest (ζ : ℂ)))
  · intro s hs
    have hz := ((hdzsecond s (hs.trans_le he₁) z hzU).1).mono (ball_subset_ball he₁)
    have hζ := ((hdzsecond s (hs.trans_le he₁) (conj (ζ : ℂ)) hζL).1).mono
      (ball_subset_ball he₁)
    have hvz := (hsecond s (hs.trans_le he₂) (z : ℂ)).mono (ball_subset_ball he₂)
    have hvζ := (hsecond s (hs.trans_le he₂) (conj (ζ : ℂ))).mono (ball_subset_ball he₂)
    change DifferentiableOn ℂ (fun t =>
      (dz (canonicalBiparameterFamily R p qdir s t) z *
        dz (canonicalBiparameterFamily R p qdir s t) (conj (ζ : ℂ)) /
          (canonicalBiparameterFamily R p qdir s t z -
            canonicalBiparameterFamily R p qdir s t (conj (ζ : ℂ))) ^ 2) ^ 2 *
        conj (harmonicPlane R p qtest (ζ : ℂ))) (ball 0 ε)
    exact (((hz.fun_mul hζ).fun_div ((hvz.fun_sub hvζ).fun_pow 2)
      (fun t ht => pow_ne_zero 2 (hden s t hs (mem_ball_zero_iff.mp ht)))).fun_pow 2).mul_const
        (conj (harmonicPlane R p qtest (ζ : ℂ)))

/-- The actual mixed derivative in the independent parameters passes through
the full upper-half-plane inner integral. Both derivative integrands have
compactly uniform L1 bounds. No singular convolution identity is assumed. -/
theorem canonicalBiparameterKernel_mixed_inner_parameter_exchange
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    let G := fun s t : ℂ => fun z ζ : ℍ =>
      canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ
    ∃ ε B₁ B₂ : ℝ, 0 < ε ∧ 0 ≤ B₁ ∧ 0 ≤ B₂ ∧ ∀ z ∈ K,
      (∀ s ∈ ball (0 : ℂ) ε,
        Integrable (fun ζ : ℍ => deriv (fun t : ℂ => G s t z ζ) 0) flatArea ∧
        HasDerivAt (fun t : ℂ => ∫ ζ : ℍ, G s t z ζ ∂flatArea)
          (∫ ζ : ℍ, deriv (fun t : ℂ => G s t z ζ) 0 ∂flatArea) 0 ∧
        (∫ ζ : ℍ, ‖deriv (fun t : ℂ => G s t z ζ) 0‖ ∂flatArea) ≤ B₁) ∧
      Integrable (fun ζ : ℍ =>
        deriv (fun s : ℂ => deriv (fun t : ℂ => G s t z ζ) 0) 0) flatArea ∧
      HasDerivAt
        (fun s : ℂ => deriv (fun t : ℂ => ∫ ζ : ℍ, G s t z ζ ∂flatArea) 0)
        (∫ ζ : ℍ, deriv (fun s : ℂ => deriv (fun t : ℂ => G s t z ζ) 0) 0
          ∂flatArea) 0 ∧
      (∫ ζ : ℍ, ‖deriv (fun s : ℂ => deriv (fun t : ℂ => G s t z ζ) 0) 0‖
        ∂flatArea) ≤ B₂ := by
  dsimp only
  obtain ⟨E₁, C, hE₁, hC, hjoint, hcontrol⟩ :=
    canonicalBiparameterKernel_common_ae_double_circle_control R p hp qdir qtest K hK
  obtain ⟨E₂, hE₂, hhol⟩ := kernel_separately_holomorphic R p hp qdir qtest
  generalize hkernel : canonicalBiparameterKernelIntegrand R p qdir qtest = g at *
  let E := min E₁ E₂
  have hE : 0 < E := lt_min hE₁ hE₂
  let r := E / 2
  have hr : 0 < r := half_pos hE
  have hrE : r < E := half_lt_self hE
  let a := r / 2
  have ha : 0 < a := half_pos hr
  have haE₁ : a < E₁ := (half_lt_self hr).trans (hrE.trans_le (min_le_left _ _))
  have haE₂ : a < E₂ := (half_lt_self hr).trans (hrE.trans_le (min_le_right _ _))
  have hrE₁ : r < E₁ := hrE.trans_le (min_le_left _ _)
  let G := fun s t : ℂ => fun z ζ : ℍ => g s t z ζ
  have hGm (s t : ℂ) (hs : s ∈ ball (0 : ℂ) a) (ht : t ∈ ball (0 : ℂ) a)
      (z : ℍ) : Measurable (G s t z) := by
    let ss : ball (0 : ℂ) E₁ := ⟨s,
      mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hs).trans haE₁)⟩
    let tt : ball (0 : ℂ) E₁ := ⟨t,
      mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ht).trans haE₁)⟩
    have hin : Measurable (fun ζ : ℍ => (ss, (tt, (z, ζ)))) :=
      measurable_const.prodMk
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    exact hjoint.comp hin
  have hfirst (ζ z : ℍ) (t : ℂ) (ht : t ∈ ball (0 : ℂ) a) :
      DifferentiableOn ℂ (fun s => G s t z ζ) (ball 0 a) :=
    ((hhol z ζ).1 t ((mem_ball_zero_iff.mp ht).trans haE₂)).mono
      (ball_subset_ball haE₂.le)
  have hsecond (ζ z : ℍ) (s : ℂ) (hs : s ∈ ball (0 : ℂ) a) :
      DifferentiableOn ℂ (fun t => G s t z ζ) (ball 0 a) :=
    ((hhol z ζ).2 s ((mem_ball_zero_iff.mp hs).trans haE₂)).mono
      (ball_subset_ball haE₂.le)
  have hhalf : a / 2 ≤ a := by linarith
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) a := mem_ball_self ha
  have hzeroHalf : (0 : ℂ) ∈ ball (0 : ℂ) (a / 2) := mem_ball_self (half_pos ha)
  refine ⟨a / 2, (8 / a) * C, (16 / a ^ 2) * C, half_pos ha,
    by positivity, by positivity, ?_⟩
  intro z hz
  obtain ⟨m, A₁, A₂, hm0, hmm, hmi, hmC, _, _, _, _, hae⟩ :=
    hcontrol r hr hrE₁ z hz
  have hb : ∀ᵐ ζ : ℍ ∂flatArea, ∀ s ∈ ball (0 : ℂ) a,
      ∀ t ∈ ball (0 : ℂ) a, ‖G s t z ζ‖ ≤ 4 * m ζ := by
    filter_upwards [hae] with ζ hζ s hs t ht
    exact (hζ.2.2 s t (mem_ball_zero_iff.mp hs).le
      (mem_ball_zero_iff.mp ht).le).1
  let A := fun s : ℂ => fun ζ : ℍ => deriv (fun t : ℂ => G s t z ζ) 0
  have hAm (s : ℂ) (hs : s ∈ ball (0 : ℂ) a) :
      AEStronglyMeasurable (A s) flatArea := by
    apply inner_deriv_zero_aestronglyMeasurable ha
      (fun t ht => (hGm s t hs (mem_ball_zero_iff.mpr ht) z).aestronglyMeasurable)
    exact Eventually.of_forall (fun ζ =>
      (hsecond ζ z s hs).differentiableAt (isOpen_ball.mem_nhds hzero))
  have hAb : ∀ᵐ ζ : ℍ ∂flatArea, ∀ s ∈ ball (0 : ℂ) a,
      ‖A s ζ‖ ≤ (8 / a) * m ζ := by
    filter_upwards [hb] with ζ hζ s hs
    calc
      ‖A s ζ‖ ≤ (4 * m ζ) / (a / 2) :=
        inner_deriv_norm_bound ha (hsecond ζ z s hs) (hζ s hs) hzeroHalf
      _ = (8 / a) * m ζ := by field_simp; ring
  have hAd : ∀ᵐ ζ : ℍ ∂flatArea,
      DifferentiableOn ℂ (fun s => A s ζ) (ball 0 a) := by
    filter_upwards [hb] with ζ hζ
    have hlocal : ∀ s₀ ∈ ball (0 : ℂ) a, ∀ t₀ ∈ ball (0 : ℂ) a,
        ∃ δ > 0, ball s₀ δ ⊆ ball (0 : ℂ) a ∧ ball t₀ δ ⊆ ball (0 : ℂ) a ∧
          ∃ M : ℝ, ∀ s ∈ ball s₀ δ, ∀ t ∈ ball t₀ δ, ‖G s t z ζ‖ ≤ M := by
      intro s₀ hs₀ t₀ ht₀
      obtain ⟨b, hb, hbP⟩ := Metric.isOpen_iff.mp isOpen_ball s₀ hs₀
      obtain ⟨c, hc, hcP⟩ := Metric.isOpen_iff.mp isOpen_ball t₀ ht₀
      refine ⟨min b c, lt_min hb hc,
        (ball_subset_ball (min_le_left _ _)).trans hbP,
        (ball_subset_ball (min_le_right _ _)).trans hcP, 4 * m ζ, ?_⟩
      intro s hs t ht
      exact hζ s (hbP (ball_subset_ball (min_le_left _ _) hs))
        t (hcP (ball_subset_ball (min_le_right _ _) ht))
    exact bB_h0_deriv_holo (fun t ht => hfirst ζ z t ht)
      (fun s hs => hsecond ζ z s hs) hlocal 0 hzero
  have hfirstIntegral (s : ℂ) (hs : s ∈ ball (0 : ℂ) a) :
      Integrable (A s) flatArea ∧
      HasDerivAt (fun t : ℂ => ∫ ζ : ℍ, G s t z ζ ∂flatArea)
        (∫ ζ : ℍ, A s ζ ∂flatArea) 0 := by
    have hI0 : Integrable (G s 0 z) flatArea := (hmi.const_mul 4).mono'
      (hGm s 0 hs hzero z).aestronglyMeasurable
      (hb.mono (fun ζ hζ => hζ s hs 0 hzero))
    apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t ζ => G s t z ζ)
      (F' := fun t ζ => deriv (fun u : ℂ => G s u z ζ) t)
      (bound := fun ζ => (8 / a) * m ζ) (ball_mem_nhds (0 : ℂ) (half_pos ha))
      (Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) (half_pos ha)) (fun t ht =>
        (hGm s t hs (ball_subset_ball hhalf ht) z).aestronglyMeasurable))
      hI0 (hAm s hs) ?_ (hmi.const_mul (8 / a)) ?_
    · filter_upwards [hb] with ζ hζ t ht
      calc
        ‖deriv (fun t : ℂ => G s t z ζ) t‖ ≤ (4 * m ζ) / (a / 2) :=
          inner_deriv_norm_bound ha (hsecond ζ z s hs) (hζ s hs) ht
        _ = (8 / a) * m ζ := by field_simp; ring
    · exact Eventually.of_forall (fun ζ t ht =>
        ((hsecond ζ z s hs).differentiableAt
          (isOpen_ball.mem_nhds (ball_subset_ball hhalf ht))).hasDerivAt)
  have hDm : AEStronglyMeasurable
      (fun ζ : ℍ => deriv (fun s : ℂ => A s ζ) 0) flatArea := by
    apply inner_deriv_zero_aestronglyMeasurable ha
      (fun s hs => hAm s (mem_ball_zero_iff.mpr hs))
    exact hAd.mono (fun ζ hζ => hζ.differentiableAt (isOpen_ball.mem_nhds hzero))
  have hDb : ∀ᵐ ζ : ℍ ∂flatArea, ∀ s ∈ ball (0 : ℂ) (a / 2),
      ‖deriv (fun s : ℂ => A s ζ) s‖ ≤ (16 / a ^ 2) * m ζ := by
    filter_upwards [hAd, hAb] with ζ hdζ hbζ s hs
    calc
      ‖deriv (fun s : ℂ => A s ζ) s‖ ≤ ((8 / a) * m ζ) / (a / 2) :=
        inner_deriv_norm_bound ha hdζ hbζ hs
      _ = (16 / a ^ 2) * m ζ := by field_simp; ring
  obtain ⟨hDint, hDderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := A) (F' := fun s ζ => deriv (fun s : ℂ => A s ζ) s)
    (bound := fun ζ => (16 / a ^ 2) * m ζ)
    (ball_mem_nhds (0 : ℂ) (half_pos ha))
    (Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) (half_pos ha)) (fun s hs =>
      hAm s (ball_subset_ball hhalf hs)))
    (hfirstIntegral 0 hzero).1 hDm hDb (hmi.const_mul (16 / a ^ 2))
    (hAd.mono (fun ζ hζ s hs =>
      (hζ.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hhalf hs))).hasDerivAt))
  have heq : (fun s : ℂ => deriv (fun t : ℂ => ∫ ζ : ℍ, G s t z ζ ∂flatArea) 0)
      =ᶠ[𝓝 0] fun s : ℂ => ∫ ζ : ℍ, A s ζ ∂flatArea := by
    filter_upwards [ball_mem_nhds (0 : ℂ) ha] with s hs
    exact (hfirstIntegral s hs).2.deriv
  refine ⟨?_, hDint, hDderiv.congr_of_eventuallyEq heq, ?_⟩
  · intro s hs
    have hs' := ball_subset_ball hhalf hs
    obtain ⟨hi, hd⟩ := hfirstIntegral s hs'
    refine ⟨hi, hd, ?_⟩
    calc
      (∫ ζ : ℍ, ‖A s ζ‖ ∂flatArea) ≤ ∫ ζ : ℍ, (8 / a) * m ζ ∂flatArea :=
        integral_mono_ae hi.norm (hmi.const_mul _) (hAb.mono (fun ζ hζ => hζ s hs'))
      _ = (8 / a) * ∫ ζ : ℍ, m ζ ∂flatArea := integral_const_mul _ _
      _ ≤ (8 / a) * C := mul_le_mul_of_nonneg_left hmC (by positivity)
  · calc
      (∫ ζ : ℍ, ‖deriv (fun s : ℂ => A s ζ) 0‖ ∂flatArea) ≤
          ∫ ζ : ℍ, (16 / a ^ 2) * m ζ ∂flatArea :=
        integral_mono_ae hDint.norm (hmi.const_mul _)
          (hDb.mono (fun ζ hζ => hζ 0 hzeroHalf))
      _ = (16 / a ^ 2) * ∫ ζ : ℍ, m ζ ∂flatArea := integral_const_mul _ _
      _ ≤ (16 / a ^ 2) * C := mul_le_mul_of_nonneg_left hmC (by positivity)

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
