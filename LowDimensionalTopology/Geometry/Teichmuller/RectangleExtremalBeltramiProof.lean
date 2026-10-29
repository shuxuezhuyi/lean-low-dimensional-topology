module

public import LowDimensionalTopology.Geometry.Teichmuller.RectangleEndpointIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.RectangleEqualityIngredients
public import LowDimensionalTopology.Unproved.Quasiconformal.RectangleExtremalBeltrami

/-!
# The equality case of the general rectangle length-area estimate

The horizontal endpoint estimate and the quadratic energy estimate
force equality in two finite integrals. Their pointwise equalities,
together with positivity of the Jacobian, determine the Beltrami
coefficient. The boundary extension and all four ordered vertices are
retained through the actual endpoint producer.

The general quasiconformal and Jacobian APIs are reused from Wu Xiaobin's
attributed LiZhongQC library; see its source manifest and third-party notices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory LiZhongQC
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- Equality in the general quasiconformal rectangle length-area bound
forces the actual affine Beltrami coefficient almost everywhere. -/
theorem rectangleExtremalBeltrami :
    LowDimensionalTopology.Unproved.Quasiconformal.RectangleExtremalBeltrami := by
  intro r s hr hrs h H hqc himage hH hv
  have hs : 0 < s := hr.trans_le hrs
  have hK0 : 0 ≤ s / r := zero_le_one.trans hqc.2.1
  let μ : Measure ℂ := volume.restrict (rectangle r 1)
  let a : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖)
  let b : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ‖dz h z + dzbar h z‖
  let j : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (jacobian h z)
  have ha : Measurable a :=
    ENNReal.measurable_ofReal.comp ((measurable_dz h).norm.add (measurable_dzbar h).norm)
  have hj : Measurable j := by
    dsimp [j, jacobian]
    exact ENNReal.measurable_ofReal.comp
      (((measurable_dz h).norm.pow_const 2).sub ((measurable_dzbar h).norm.pow_const 2))
  have hba : b ≤ᵐ[μ] a := by
    filter_upwards with z
    exact ENNReal.ofReal_le_ofReal (norm_add_le (dz h z) (dzbar h z))
  have hstart : ENNReal.ofReal s ≤ ∫⁻ z, b z ∂μ := by
    simpa [μ, b] using
      rectangle_horizontal_endpoint_integral_lower_bound hr hs hqc himage hH hv
  have hsa : ENNReal.ofReal s ≤ ∫⁻ z, a z ∂μ :=
    hstart.trans (lintegral_mono_ae hba)
  have hcs : (∫⁻ z, a z ∂μ) ^ 2 ≤
      ENNReal.ofReal r * ∫⁻ z, a z ^ 2 ∂μ := by
    simpa [μ, volume_rectangle] using ac_n_c_sq_lintegral_le μ ha.aemeasurable
  have hsq : (fun z => a z ^ 2) ≤ᵐ[μ] fun z => ENNReal.ofReal (s / r) * j z := by
    filter_upwards [thm9_4_dilatation_ae hqc] with z hz
    have hsum0 : 0 ≤ ‖dz h z‖ + ‖dzbar h z‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hreal : (‖dz h z‖ + ‖dzbar h z‖) ^ 2 ≤ (s / r) * jacobian h z := by
      unfold jacobian
      nlinarith
    dsimp [a, j]
    rw [← ENNReal.ofReal_pow hsum0 2, ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal hreal
  have henergy_area : (∫⁻ z, a z ^ 2 ∂μ) ≤
      ENNReal.ofReal (s / r) * ∫⁻ z, j z ∂μ := by
    calc (∫⁻ z, a z ^ 2 ∂μ)
        ≤ ∫⁻ z, ENNReal.ofReal (s / r) * j z ∂μ := lintegral_mono_ae hsq
      _ = ENNReal.ofReal (s / r) * ∫⁻ z, j z ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have harea : (∫⁻ z, j z ∂μ) ≤ ENNReal.ofReal s := by
    have hle := lintegral_jacobian_le_volume_image hqc hqc.1.measurableSet
      (Subset.refl (rectangle r 1))
    simpa [μ, j, himage, volume_rectangle] using hle
  have hscale : ENNReal.ofReal r *
      (ENNReal.ofReal (s / r) * ENNReal.ofReal s) = (ENNReal.ofReal s) ^ 2 := by
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul hr.le,
      ← ENNReal.ofReal_pow hs.le 2]
    congr 1
    field_simp [hr.ne']
  have haupper : (∫⁻ z, a z ∂μ) ^ 2 ≤ (ENNReal.ofReal s) ^ 2 := by
    calc (∫⁻ z, a z ∂μ) ^ 2
        ≤ ENNReal.ofReal r * ∫⁻ z, a z ^ 2 ∂μ := hcs
      _ ≤ ENNReal.ofReal r *
          (ENNReal.ofReal (s / r) * ∫⁻ z, j z ∂μ) := by
          gcongr
      _ ≤ ENNReal.ofReal r *
          (ENNReal.ofReal (s / r) * ENNReal.ofReal s) := by
          gcongr
      _ = (ENNReal.ofReal s) ^ 2 := hscale
  have haeq : (∫⁻ z, a z ∂μ) = ENNReal.ofReal s := by
    apply le_antisymm _ hsa
    apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
    simpa only [ENNReal.rpow_two] using haupper
  have hbeq : (∫⁻ z, b z ∂μ) = ∫⁻ z, a z ∂μ := by
    apply le_antisymm (lintegral_mono_ae hba)
    rw [haeq]
    exact hstart
  have htriangle : b =ᵐ[μ] a :=
    ae_eq_of_ae_le_of_lintegral_le hba
      (by rw [hbeq, haeq]; exact ENNReal.ofReal_ne_top)
      ha.aemeasurable hbeq.ge
  have henergy_finite : (∫⁻ z, a z ^ 2 ∂μ) ≠ ∞ := by
    have hbound : (∫⁻ z, a z ^ 2 ∂μ) ≤
        ENNReal.ofReal (s / r) * ENNReal.ofReal s := by
      calc (∫⁻ z, a z ^ 2 ∂μ)
          = ∫⁻ z in rectangle r 1,
              ENNReal.ofReal ((‖dz h z‖ + ‖dzbar h z‖) ^ 2) := by
            apply lintegral_congr
            intro z
            exact (ENNReal.ofReal_pow
              (add_nonneg (norm_nonneg (dz h z)) (norm_nonneg (dzbar h z))) 2).symm
        _ ≤ ENNReal.ofReal (s / r) * volume (h '' rectangle r 1) :=
            rectangle_general_qc_energy_bound hqc hqc.1.measurableSet
              (Subset.refl (rectangle r 1))
        _ = ENNReal.ofReal (s / r) * ENNReal.ofReal s := by
            rw [himage, volume_rectangle]
            simp
    exact (hbound.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne
  have henergy_reverse : ENNReal.ofReal (s / r) * (∫⁻ z, j z ∂μ) ≤
      ∫⁻ z, a z ^ 2 ∂μ := by
    apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hr).ne'
      ENNReal.ofReal_ne_top).mp
    calc ENNReal.ofReal r * (ENNReal.ofReal (s / r) * ∫⁻ z, j z ∂μ)
        ≤ ENNReal.ofReal r *
          (ENNReal.ofReal (s / r) * ENNReal.ofReal s) := by
          gcongr
      _ = (ENNReal.ofReal s) ^ 2 := hscale
      _ = (∫⁻ z, a z ∂μ) ^ 2 := by rw [haeq]
      _ ≤ ENNReal.ofReal r * ∫⁻ z, a z ^ 2 ∂μ := hcs
  have hsaturation : (fun z => a z ^ 2) =ᵐ[μ]
      fun z => ENNReal.ofReal (s / r) * j z := by
    apply ae_eq_of_ae_le_of_lintegral_le hsq henergy_finite
      (measurable_const.mul hj).aemeasurable
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact henergy_reverse
  filter_upwards [htriangle, hsaturation, thm9_6_cor2_jacobian_pos hqc]
    with z htri hsat hjpos
  have hsum0 : 0 ≤ ‖dz h z‖ + ‖dzbar h z‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have htri_real : ‖dz h z + dzbar h z‖ = ‖dz h z‖ + ‖dzbar h z‖ :=
    (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) hsum0).mp htri
  have hsat_real : (‖dz h z‖ + ‖dzbar h z‖) ^ 2 = (s / r) * jacobian h z := by
    apply (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (mul_nonneg hK0 hjpos.le)).mp
    rw [ENNReal.ofReal_pow hsum0 2, ENNReal.ofReal_mul hK0]
    exact hsat
  have hlt : ‖dzbar h z‖ < ‖dz h z‖ := by
    change 0 < ‖dz h z‖ ^ 2 - ‖dzbar h z‖ ^ 2 at hjpos
    nlinarith [norm_nonneg (dz h z), norm_nonneg (dzbar h z)]
  change dzbar h z / dz h z = _
  exact rectangle_beltrami_of_pointwise_equalities hqc.2.1 hlt htri_real
    (by simpa only [jacobian] using hsat_real)

end LowDimensionalTopology.Geometry.Teichmuller
