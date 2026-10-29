module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceFundamentalIntegrability
public import LowDimensionalTopology.Geometry.Teichmuller.PoincareKernelSeries

/-!
# The literal Poincare seed of an integrable measurable coefficient

The coefficient stays unchanged inside the specified fundamental-domain
integral. Its integrability, rather than continuity or holomorphy, gives the
actual seed holomorphy and unweighted full-half-plane L1 bound.

The dominated differentiation and kernel-area arguments adapt
`h36p_c_beta_diff` and `h36p_c_beta_L1`, from Wu Xiaobin's
Li-Zhong-QC-formalization, commit `1c0d5473c020b66ed5106331a38a61536760b9b2`
(Apache-2.0), `LiZhongQC/Ch11/S36_Hamilton.lean`. The only changed analytic
input is genuine a.e. strong measurability. See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare

open Surfaces LiZhongQC

private theorem kernel_factor_aestronglyMeasurable {f : ℂ → ℂ} {μ : Measure ℂ}
    (hf : AEStronglyMeasurable f μ) (w : ℂ) (n : ℕ) :
    AEStronglyMeasurable (fun ζ => (ζ.im : ℂ) ^ 2 * f ζ / (conj ζ - w) ^ n) μ := by
  have ha : Measurable (fun ζ : ℂ => (ζ.im : ℂ) ^ 2) := by fun_prop
  have hd : Measurable (fun ζ : ℂ => (conj ζ - w) ^ n) := by fun_prop
  exact (ha.aestronglyMeasurable.mul hf).div₀ hd.aestronglyMeasurable

private theorem kernel_integrableOn {S : Set ℂ} (hS : MeasurableSet S)
    (hSH : S ⊆ upperHalf) {f : ℂ → ℂ} (hf : IntegrableOn f S)
    {w : ℂ} (hw : w ∈ upperHalf) :
    IntegrableOn (fun ζ => h36p_c_K f ζ w) S := by
  exact (hf.norm.div_const (16 * w.im ^ 2)).mono'
    (kernel_factor_aestronglyMeasurable hf.aestronglyMeasurable w 4)
    (ae_restrict_of_forall_mem hS fun ζ hζ => h36p_c_K_le f (hSH hζ) hw)

private theorem kernel_product_aemeasurable {S : Set ℂ} {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict S)) :
    AEMeasurable (fun p : ℂ × ℂ => h36p_c_K f p.2 p.1)
      ((volume.restrict upperHalf).prod (volume.restrict S)) := by
  have ha : Measurable (fun p : ℂ × ℂ => (p.2.im : ℂ) ^ 2) := by fun_prop
  have hd : Measurable (fun p : ℂ × ℂ => (conj p.2 - p.1) ^ 4) := by fun_prop
  exact (ha.aemeasurable.mul hf.aemeasurable.comp_snd).div hd.aemeasurable

/-- The specified seed is holomorphic on all of H for the original integrable
measurable coefficient; no continuity or holomorphy of that coefficient is used. -/
theorem seed_differentiableOn_of_integrableOn {S : Set ℂ} (hS : MeasurableSet S)
    (hSH : S ⊆ upperHalf) {f : ℂ → ℂ} (hf : IntegrableOn f S) :
    DifferentiableOn ℂ (seed S f) upperHalf := by
  have hd : DifferentiableOn ℂ (fun w => ∫ ζ in S, h36p_c_K f ζ w) upperHalf := by
    intro w₀ hw₀
    have hv : 0 < w₀.im := hw₀
    set δ : ℝ := w₀.im / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hball : ∀ w ∈ ball w₀ δ, δ ≤ w.im := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      have h1 := Complex.abs_im_le_norm (w - w₀)
      rw [sub_im] at h1
      have := (abs_le.1 (h1.trans hw.le)).1
      linarith
    have hballH : ∀ w ∈ ball w₀ δ, w ∈ upperHalf := fun w hw =>
      show 0 < w.im from lt_of_lt_of_le hδ (hball w hw)
    have hderiv : AEStronglyMeasurable
        (fun ζ => 4 * ((ζ.im : ℂ) ^ 2 * f ζ) / (conj ζ - w₀) ^ 5)
        (volume.restrict S) := by
      simpa only [mul_div_assoc] using
        (kernel_factor_aestronglyMeasurable hf.aestronglyMeasurable w₀ 5).const_mul 4
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict S) (F := fun w ζ => h36p_c_K f ζ w)
      (F' := fun w ζ => 4 * ((ζ.im : ℂ) ^ 2 * f ζ) / (conj ζ - w) ^ 5)
      (x₀ := w₀) (bound := fun ζ => 4 * ‖f ζ‖ / δ ^ 3) (ball_mem_nhds w₀ hδ)
      ((isOpen_upperHalf.eventually_mem hw₀).mono fun w hw =>
        (kernel_integrableOn hS hSH hf hw).aestronglyMeasurable)
      (kernel_integrableOn hS hSH hf hw₀) hderiv ?_
      ((hf.norm.const_mul 4).div_const _) ?_
    · exact key.2.differentiableAt.differentiableWithinAt
    · refine ae_restrict_of_forall_mem hS fun ζ hζ w hw => ?_
      have hy : 0 < ζ.im := hSH hζ
      have hN := h36p_c_im_add_le ζ w
      have hδw := hball w hw
      have hNpos : 0 < ‖conj ζ - w‖ := by linarith
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, div_le_div_iff₀ (by positivity) (by positivity)]
      have h5 : ζ.im ^ 2 * δ ^ 3 ≤ ‖conj ζ - w‖ ^ 5 := by
        calc
          ζ.im ^ 2 * δ ^ 3 ≤ (ζ.im + δ) ^ 2 * (ζ.im + δ) ^ 3 := by
            gcongr <;> linarith
          _ = (ζ.im + δ) ^ 5 := by ring
          _ ≤ ‖conj ζ - w‖ ^ 5 := by
            gcongr
            linarith
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [h4]
      nlinarith [mul_le_mul_of_nonneg_left h5 (norm_nonneg (f ζ))]
    · refine ae_restrict_of_forall_mem hS fun ζ hζ w hw => ?_
      have hne : conj ζ - w ≠ 0 := h36p_c_conj_sub_ne (hSH hζ) (hballH w hw)
      have h1 := ((hasDerivAt_id' w).const_sub (conj ζ)).pow 4
      have h2 := (hasDerivAt_const w ((ζ.im : ℂ) ^ 2 * f ζ)).div h1
        (pow_ne_zero 4 hne)
      unfold h36p_c_K
      convert h2 using 1
      norm_num
      field_simp
  exact hd.const_mul (12 / Real.pi : ℂ)

/-- The same literal seed is genuinely L1 on the entire original half-plane,
with no height weight or bounded-area assumption on the integration domain. -/
theorem seed_phiArea_lt_top_of_integrableOn {S : Set ℂ} (hS : MeasurableSet S)
    (hSH : S ⊆ upperHalf) {f : ℂ → ℂ} (hf : IntegrableOn f S) :
    phiArea (seed S f) upperHalf < ⊤ := by
  have hhi : ∫⁻ ζ in S, ENNReal.ofReal ‖f ζ‖ < ⊤ := by
    simpa only [HasFiniteIntegral, ofReal_norm] using hf.2
  have hA : ∫⁻ ζ in S, ENNReal.ofReal (‖f ζ‖ / 4) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal
      (by linarith [norm_nonneg (f ζ)])) hhi
  have hb : ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in S, h36p_c_K f ζ w‖ < ⊤ := by
    calc
      ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in S, h36p_c_K f ζ w‖ ≤
          ∫⁻ w in upperHalf, ∫⁻ ζ in S, ENNReal.ofReal ‖h36p_c_K f ζ w‖ := by
        refine lintegral_mono fun w => ?_
        simp_rw [ofReal_norm]
        exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ζ in S, ∫⁻ w in upperHalf, ENNReal.ofReal ‖h36p_c_K f ζ w‖ :=
        lintegral_lintegral_swap
          (kernel_product_aemeasurable hf.aestronglyMeasurable).norm.ennreal_ofReal
      _ = volume (ball (0 : ℂ) 1) * ∫⁻ ζ in S, ENNReal.ofReal (‖f ζ‖ / 4) :=
        h36p_c_tonelli hS hSH f
      _ < ⊤ := ENNReal.mul_lt_top measure_ball_lt_top hA
  unfold seed phiArea
  calc
    ∫⁻ w in upperHalf,
        ENNReal.ofReal ‖(12 / Real.pi : ℂ) * ∫ ζ in S, h36p_c_K f ζ w‖ =
        ENNReal.ofReal ‖(12 / Real.pi : ℂ)‖ *
          ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in S, h36p_c_K f ζ w‖ := by
      simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb

/-- The original compact uniformization gives both analytic seed inputs on
every actual given fundamental domain, retaining the same original measurable
coefficient and its a.e. weighted bound. No compactness of this domain is added. -/
theorem source_seed_differentiableOn_and_phiArea_lt_top
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict upperHalf))
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict upperHalf), ‖f z‖ * z.im ^ 2 ≤ M) :
    DifferentiableOn ℂ (seed F f) upperHalf ∧ phiArea (seed F f) upperHalf < ⊤ := by
  have hi := sourceFundamentalDomainH_integrable_of_weighted_bound R hΓ hp hF hf hb
  exact ⟨seed_differentiableOn_of_integrableOn hF.2.1 hF.1 hi,
    seed_phiArea_lt_top_of_integrableOn hF.2.1 hF.1 hi⟩

end LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare
