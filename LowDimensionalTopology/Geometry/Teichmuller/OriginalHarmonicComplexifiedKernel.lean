module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicCompactImages
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicSpatialControl
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11_IntegralOperators
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Uniform absolute integrability of the actual complexified kernel

The actual deformed lower half-plane stays separated from the compact
upper source set. The QC Jacobian formula and an exterior fourth-power
integral give a uniform L1 bound for the independent parameter family.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

private theorem kernel_norm_dz_le_fderiv (f : ℂ → ℂ) (z : ℂ) :
    ‖dz f z‖ ≤ ‖fderiv ℝ f z‖ := by
  have h₁ := (fderiv ℝ f z).le_opNorm (1 : ℂ)
  have hI := (fderiv ℝ f z).le_opNorm Complex.I
  simp only [norm_one, Complex.norm_I, mul_one] at h₁ hI
  calc
    ‖dz f z‖ =
        ‖fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I‖ / 2 := by
      simp only [dz, norm_div, Complex.norm_two]
    _ ≤ (‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z Complex.I‖) / 2 := by
      gcongr
      simpa only [norm_mul, Complex.norm_I, one_mul] using
        norm_sub_le (fderiv ℝ f z 1) (Complex.I * fderiv ℝ f z Complex.I)
    _ ≤ ‖fderiv ℝ f z‖ := by linarith

private theorem kernel_lintegral_fourth_exterior {ρ : ℝ} (hρ : 0 < ρ) (a : ℂ) :
    (∫⁻ w in {w : ℂ | ρ < ‖w - a‖}, ENNReal.ofReal (‖w - a‖⁻¹ ^ 4)) =
      ENNReal.ofReal (Real.pi / ρ ^ 2) := by
  have heq : (fun w : ℂ => ENNReal.ofReal (‖w - a‖⁻¹ ^ 4)) =ᵐ[
      volume.restrict {w : ℂ | ρ < ‖w - a‖}]
        fun w : ℂ => ‖w - a‖ₑ ^ (-(4 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet]
      with w hw
    have hwpos : 0 < ‖w - a‖ := hρ.trans hw
    rw [inv_pow, ENNReal.rpow_neg, ← ofReal_norm (w - a),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg (w - a)),
      ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [lintegral_congr_ae heq,
    lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num : (2 : ℝ) < 4) hρ a]
  have hscalar : -ρ ^ (2 - (4 : ℝ)) / (2 - 4) = (ρ ^ 2)⁻¹ / 2 := by
    norm_num [Real.rpow_neg hρ.le, Real.rpow_two, div_eq_mul_inv]
  rw [hscalar, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  congr 1
  simp only [div_eq_mul_inv]
  ring

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

/-- The literal inner integrand of the independent complexified family. -/
def canonicalBiparameterKernelIntegrand
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (s t : ℂ) (z : ℍ) (ζ : ℂ) : ℂ :=
  let f := canonicalBiparameterFamily R p qdir s t
  (dz f z * dz f (conj ζ) / (f z - f (conj ζ)) ^ 2) ^ 2 *
    conj (harmonicPlane R p qtest ζ)

/-- On one actual parameter bidisc the full upper-half-plane norm integral
has one finite bound for every point of the given compact source set. -/
theorem canonicalBiparameterKernel_uniform_integrable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (qdir qtest : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε → ∀ z ∈ K,
        IntegrableOn
          (canonicalBiparameterKernelIntegrand R p qdir qtest s t z)
          upperHalf ∧
        (∫ ζ : ℂ in upperHalf,
          ‖canonicalBiparameterKernelIntegrand R p qdir qtest s t z ζ‖) ≤ C := by
  classical
  let M : ℝ := ‖(NativeHarmonicBeltrami.ofQuadratic R p hp qtest).val‖
  have hM : 0 ≤ M := norm_nonneg _
  have hraw : IsBeltramiCoeff (harmonicPlane R p qtest) upperHalf M := by
    have hμ := planeRepresentative_isBeltramiCoeff
      (NativeHarmonicBeltrami.ofQuadratic R p hp qtest).val
    have hae : planeRepresentative
        (NativeHarmonicBeltrami.ofQuadratic R p hp qtest).val
          =ᵐ[volume.restrict upperHalf] harmonicPlane R p qtest :=
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp qtest
    refine ⟨hμ.1.congr hae, ?_⟩
    filter_upwards [hae, hμ.2] with w hw hb
    rwa [← hw]
  obtain ⟨ε₁, d, _, hε₁, hd, _, himage⟩ :=
    canonicalBiparameterFamily_compact_image_control R p hp qdir K hK
  obtain ⟨ε₂, _, hC1, _, _, hcompact⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control R p hp qdir
  obtain ⟨δ, D, hδ, hδε₂, _hD, hDz⟩ := hcompact K hK
  let ρ : ℝ := d / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let A : ℝ := 3 * D ^ 2 * M
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ A * (Real.pi / ρ ^ 2) := by positivity
  refine ⟨min ε₁ δ, A * (Real.pi / ρ ^ 2), lt_min hε₁ hδ, hC, ?_⟩
  intro s t hs ht z hz
  have hs₁ : ‖s‖ < ε₁ := hs.trans_le (min_le_left _ _)
  have ht₁ : ‖t‖ < ε₁ := ht.trans_le (min_le_left _ _)
  have hsδ : ‖s‖ < δ := hs.trans_le (min_le_right _ _)
  have htδ : ‖t‖ < δ := ht.trans_le (min_le_right _ _)
  let f := canonicalBiparameterFamily R p qdir s t
  let g := canonicalBiparameterKernelIntegrand R p qdir qtest s t z
  have hqc : IsKQC f univ 3 := (himage s t hs₁ ht₁).1.1
  have hLo : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  have hqcL : IsKQC f lowerHalf 3 := ac_t_isKQC_restrict hqc hLo (subset_univ _)
  have hCL : ContDiffOn ℝ 1 f lowerHalf :=
    (hC1 s t (hsδ.trans_le hδε₂) (htδ.trans_le hδε₂)).mono (fun _ hw => Or.inr hw)
  have hdif (w : ℂ) (hw : w ∈ lowerHalf) : DifferentiableAt ℝ f w :=
    (hCL.differentiableOn_one w hw).differentiableAt (hLo.mem_nhds hw)
  have hJ (w : ℂ) (hw : w ∈ lowerHalf) : 0 ≤ jacobian f w := by
    rw [ar_jacobian_eq_abs_det hqcL hw (hdif w hw)]
    exact abs_nonneg _
  have hsq (w : ℂ) (hw : w ∈ lowerHalf) : ‖dz f w‖ ^ 2 ≤ 3 * jacobian f w := by
    have h := ac_t_dilatation_of_differentiableAt hqcL hw (hdif w hw)
    have hm := mul_le_mul_of_nonneg_right h
      (add_nonneg (norm_nonneg (dz f w)) (norm_nonneg (dzbar f w)))
    unfold jacobian
    nlinarith [mul_nonneg (norm_nonneg (dz f w)) (norm_nonneg (dzbar f w)),
      sq_nonneg ‖dzbar f w‖]
  have hdz : ‖dz f z‖ ≤ D :=
    (kernel_norm_dz_le_fderiv f z).trans (hDz s t hsδ htδ z hz)
  have hdzsq : ‖dz f z‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdz 2
  have hsep (w : ℂ) (hw : w ∈ lowerHalf) : d ≤ ‖f w - f z‖ := by
    rw [norm_sub_rev]
    exact ((himage s t hs₁ ht₁).2 z hz).2.1 w (le_of_lt hw)
  let W : ℂ → ENNReal := fun w =>
    ENNReal.ofReal (jacobian f w) * ENNReal.ofReal (‖f w - f z‖⁻¹ ^ 4)
  have hpull : (∫⁻ w in lowerHalf, W w) =
      ∫⁻ v in f '' lowerHalf, ENNReal.ofReal (‖v - f z‖⁻¹ ^ 4) := by
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hLo.measurableSet
      (fun w hw => (hdif w hw).hasFDerivAt.hasFDerivWithinAt) hqcL.2.2.1.2.1]
    apply setLIntegral_congr_fun hLo.measurableSet
    intro w hw
    dsimp only [W]
    rw [ar_jacobian_eq_abs_det hqcL hw (hdif w hw)]
  have hsub : f '' lowerHalf ⊆ {v : ℂ | ρ < ‖v - f z‖} := by
    rintro v ⟨w, hw, rfl⟩
    exact (show ρ < d by dsimp only [ρ]; linarith).trans_le (hsep w hw)
  have hpull_le : (∫⁻ w in lowerHalf, W w) ≤ ENNReal.ofReal (Real.pi / ρ ^ 2) := by
    rw [hpull]
    exact (lintegral_mono_set hsub).trans_eq (kernel_lintegral_fourth_exterior hρ (f z))
  have hpre : (fun w : ℂ => conj w) ⁻¹' lowerHalf = upperHalf := by
    ext w
    change (conj w).im < 0 ↔ 0 < w.im
    simp only [Complex.conj_im, neg_lt_zero]
  have hreflect : (∫⁻ ζ in upperHalf, W (conj ζ)) = ∫⁻ w in lowerHalf, W w := by
    have h := gzE_conj_measurePreserving.setLIntegral_comp_preimage_emb
      Complex.conjLIE.toHomeomorph.measurableEmbedding W lowerHalf
    rwa [hpre] at h
  have hbound : (∫⁻ ζ in upperHalf, ‖g ζ‖ₑ) ≤
      ENNReal.ofReal (A * (Real.pi / ρ ^ 2)) := by
    calc
      _ ≤ ∫⁻ ζ in upperHalf, ENNReal.ofReal A * W (conj ζ) := by
        apply lintegral_mono_ae
        filter_upwards [hraw.2, ae_restrict_mem isOpen_upperHalf.measurableSet]
          with ζ hκ hζ
        have hw : conj ζ ∈ lowerHalf := by
          change (conj ζ).im < 0
          simpa only [Complex.conj_im] using neg_lt_zero.mpr hζ
        have he : ‖g ζ‖ =
            ‖dz f z‖ ^ 2 * ‖dz f (conj ζ)‖ ^ 2 * ‖harmonicPlane R p qtest ζ‖ *
              ‖f (conj ζ) - f z‖⁻¹ ^ 4 := by
          change ‖(dz f z * dz f (conj ζ) / (f z - f (conj ζ)) ^ 2) ^ 2 *
            conj (harmonicPlane R p qtest ζ)‖ = _
          simp only [norm_mul, norm_pow, norm_div, Complex.norm_conj]
          rw [norm_sub_rev (f z) (f (conj ζ))]
          simp only [div_eq_mul_inv, mul_pow, inv_pow, ← pow_mul]
          ring
        have h₁ := mul_le_mul hdzsq (hsq (conj ζ) hw)
          (sq_nonneg ‖dz f (conj ζ)‖) (sq_nonneg D)
        have h₂ := mul_le_mul h₁ hκ (norm_nonneg (harmonicPlane R p qtest ζ))
          (mul_nonneg (sq_nonneg D) (mul_nonneg (by norm_num) (hJ (conj ζ) hw)))
        have hb : ‖g ζ‖ ≤ A *
            (jacobian f (conj ζ) * ‖f (conj ζ) - f z‖⁻¹ ^ 4) := by
          rw [he]
          calc
            _ ≤ D ^ 2 * (3 * jacobian f (conj ζ)) * M *
                ‖f (conj ζ) - f z‖⁻¹ ^ 4 :=
              mul_le_mul_of_nonneg_right h₂ (by positivity)
            _ = _ := by dsimp only [A]; ring
        rw [← ofReal_norm (g ζ)]
        calc
          _ ≤ ENNReal.ofReal (A *
              (jacobian f (conj ζ) * ‖f (conj ζ) - f z‖⁻¹ ^ 4)) :=
            ENNReal.ofReal_le_ofReal hb
          _ = ENNReal.ofReal A * W (conj ζ) := by
            dsimp only [W]
            rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_mul (hJ (conj ζ) hw)]
      _ = ENNReal.ofReal A * ∫⁻ ζ in upperHalf, W (conj ζ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (Real.pi / ρ ^ 2) :=
        mul_le_mul_right (hreflect.trans_le hpull_le) _
      _ = _ := (ENNReal.ofReal_mul hA).symm
  have hfcont : Continuous f := continuousOn_univ.mp hqc.2.2.1.1
  have hfm : AEStronglyMeasurable (fun ζ : ℂ => f (conj ζ))
      (volume.restrict upperHalf) :=
    (hfcont.measurable.comp Complex.continuous_conj.measurable).aestronglyMeasurable.restrict
  have hdm : AEStronglyMeasurable (fun ζ : ℂ => dz f (conj ζ))
      (volume.restrict upperHalf) :=
    ((measurable_dz f).comp Complex.continuous_conj.measurable).aestronglyMeasurable.restrict
  have hgm : AEStronglyMeasurable g (volume.restrict upperHalf) := by
    change AEStronglyMeasurable
      (fun ζ : ℂ => (dz f z * dz f (conj ζ) / (f z - f (conj ζ)) ^ 2) ^ 2 *
        conj (harmonicPlane R p qtest ζ)) (volume.restrict upperHalf)
    exact (((aestronglyMeasurable_const.mul hdm).div₀
      ((aestronglyMeasurable_const.sub hfm).pow 2)).pow 2).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable hraw.1)
  have hint : IntegrableOn g upperHalf :=
    ⟨hgm, hasFiniteIntegral_iff_enorm.mpr (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  change (∫ ζ : ℂ in upperHalf, ‖g ζ‖) ≤ A * (Real.pi / ρ ^ 2)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbound

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
