module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergmanKernel
public import Mathlib.Tactic.FieldSimp

/-!
# The original measurable coefficient on every given fundamental domain

A compact original surface supplies a compact set meeting every original
matrix-group orbit. Unfolding a measurable compactly supported inverse-height
majorant proves integrability on any genuine fundamental domain. No regularity
or automorphy of the original coefficient is added.

The compact-orbit unfolding estimate adapts `QuadraticBergmanKernel.lean`,
`uniformizedQuadratic_integrableAutomorphic`, based on Wu Xiaobin's
Li-Zhong-QC-formalization, commit `1c0d5473c020b66ed5106331a38a61536760b9b2`
(Apache-2.0), `LiZhongQC/Ch11/S36_Hamilton.lean` (unfolding and the Mobius
height calculation). See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces LiZhongQC

/-- Every actual given fundamental domain of the same compact uniformizing
cover integrates the original measurable coefficient without its height weight.
Only the stated a.e. weighted bound is used; no continuity, holomorphicity or
automorphy of the coefficient, nor compactness of this domain, is assumed. -/
theorem sourceFundamentalDomainH_integrable_of_weighted_bound
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f ((volume : Measure ℂ).restrict upperHalf))
    (hb : ∃ M : ℝ, ∀ᵐ z ∂((volume : Measure ℂ).restrict upperHalf),
      ‖f z‖ * z.im ^ 2 ≤ M) :
    IntegrableOn f F := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  let : Countable Γ := (h36p_countable hΓ).to_subtype
  obtain ⟨K, hK, hcover⟩ := utm_exists_compact_translate hp
  obtain ⟨M, hM⟩ := hb
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  let ρ : ℂ → ℝ := fun z => C / z.im ^ 2
  have hρ0 (z : ℂ) : 0 ≤ ρ z := div_nonneg hC (sq_nonneg _)
  have hρ : ContinuousOn ρ upperHalf := by
    apply continuousOn_const.div (Complex.continuous_im.pow 2).continuousOn
    intro z hz
    exact pow_ne_zero 2 (ne_of_gt (show 0 < z.im from hz))
  let Kc : Set ℂ := UpperHalfPlane.coe '' K
  have hKc : IsCompact Kc := hK.image UpperHalfPlane.continuous_coe
  have hKH : Kc ⊆ upperHalf := by
    rintro _ ⟨z, _, rfl⟩
    exact z.im_pos
  let g : ℂ → ℝ≥0∞ := Kc.indicator (fun z => ENNReal.ofReal (ρ z))
  have hg : Measurable g := by
    have he : g = Kc.piecewise (fun z => ENNReal.ofReal (ρ z)) 0 := by
      rw [Set.piecewise_eq_indicator]
    rw [he]
    exact (ENNReal.continuous_ofReal.comp_continuousOn (hρ.mono hKH)).measurable_piecewise
      continuousOn_const hKc.measurableSet
  have hfin : ∫⁻ z in upperHalf, g z < ⊤ := by
    have hi : IntegrableOn ρ Kc := (hρ.mono hKH).integrableOn_compact hKc
    calc
      ∫⁻ z in upperHalf, g z ≤ ∫⁻ z, g z := setLIntegral_le_lintegral upperHalf g
      _ = ∫⁻ z in Kc, ENNReal.ofReal (ρ z) := lintegral_indicator hKc.measurableSet _
      _ < ⊤ := lt_of_le_of_lt (lintegral_mono fun z => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by
          simpa only [Real.norm_eq_abs] using le_abs_self (ρ z))) hi.2
  let T : Γ → ℂ → ℝ≥0∞ := fun γ z => g (h36p_m γ.val z) *
    ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4)
  have hTm : ∀ γ : Γ, AEMeasurable (T γ) (volume.restrict F) := by
    intro γ
    have hD : Measurable (fun z : ℂ =>
        ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4)) := by fun_prop
    exact ((hg.comp (h36p_m_measurable γ.val)).mul hD).aemeasurable
  refine ⟨AEStronglyMeasurable.mono_set hF.1 hf, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [← ofReal_norm]
  have hbound : (∫⁻ z in F, ENNReal.ofReal ‖f z‖) ≤ ∑' γ : Γ, ∫⁻ z in F, T γ z := by
    rw [← lintegral_tsum hTm]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hF.1 hM,
      ae_restrict_mem hF.2.1] with z hz hzF
    obtain ⟨γ, hγ, hγK⟩ := hcover ⟨z, hF.1 hzF⟩
    have hmem : h36p_m γ z ∈ Kc :=
      ⟨γ • (⟨z, hF.1 hzF⟩ : ℍ), hγK, (h36p_m_coe γ _).symm⟩
    have hnorm : ‖f z‖ ≤ ρ z :=
      (le_div_iff₀ (sq_pos_of_pos (show 0 < z.im from hF.1 hzF))).mpr
        (hz.trans (le_max_left _ _))
    have him : (h36p_m γ z).im =
        z.im / Complex.normSq ((γ 1 0 : ℂ) * z + γ 1 1) := by
      unfold h36p_m
      rw [Complex.div_im]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      rw [div_sub_div_same]
      congr 1
      linear_combination z.im * b33_d_det γ
    have hq : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr
      (k24_d_den_ne_zero (b33_d_det γ) (ne_of_gt (show 0 < z.im from hF.1 hzF)))
    have hρcov : ρ (h36p_m γ z) * ‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4 = ρ z := by
      dsimp only [ρ]
      rw [him, Complex.normSq_eq_norm_sq]
      have hy : z.im ≠ 0 := ne_of_gt (show 0 < z.im from hF.1 hzF)
      field_simp [hq, hy]
    let δ : Γ := ⟨γ, hγ⟩
    have he : ENNReal.ofReal (ρ z) = T δ z := by
      change ENNReal.ofReal (ρ z) =
        Kc.indicator (fun w => ENNReal.ofReal (ρ w)) (h36p_m γ z) *
          ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4)
      rw [indicator_of_mem hmem, ← ENNReal.ofReal_mul (hρ0 _), hρcov]
    exact (ENNReal.ofReal_le_ofReal hnorm).trans
      (he.le.trans (ENNReal.le_tsum (f := fun η : Γ => T η z) δ))
  refine lt_of_le_of_lt hbound ?_
  change (∑' γ : Γ, ∫⁻ z in F, g (h36p_m γ.val z) *
    ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4)) < ⊤
  rw [h36p_unfold hΓ hF hg]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin

end LowDimensionalTopology.Geometry.Teichmuller
