module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertConvolutionDerivative
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLogKernel
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The logarithmic formula for the actual renormalized convolution

The actual convolution and an explicit logarithmic expression have equal
full real derivatives away from their two poles. Reflection at the
midpoint fixes their additive constant on the connected punctured plane.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The concrete difference of real logarithms with the convolution's
normalization. -/
def renormalizedLogNormKernel (w z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) * (realLogNormKernel z - realLogNormKernel (z - w))

theorem conj_renormalizedLogNormKernel (w z : ℂ) :
    conj (renormalizedLogNormKernel w z) = renormalizedLogNormKernel w z := by
  simp [renormalizedLogNormKernel, conj_realLogNormKernel, map_ofNat]

theorem differentiableAt_renormalizedLogNormKernel {w z : ℂ}
    (hz : z ≠ 0) (hzw : z ≠ w) :
    DifferentiableAt ℝ (renormalizedLogNormKernel w) z := by
  exact (differentiableAt_const (2 * (Real.pi : ℂ))).mul
    (((hasFDerivAt_realLogNormKernel hz).differentiableAt).sub
      (differentiableAt_shiftedRealLogNormKernel hzw))

theorem dz_renormalizedLogNormKernel {w z : ℂ}
    (hz : z ≠ 0) (hzw : z ≠ w) :
    LiZhongQC.dz (renormalizedLogNormKernel w) z =
      -(Real.pi : ℂ) / (z - w) + (Real.pi : ℂ) / z := by
  have h₁ := (hasFDerivAt_realLogNormKernel hz).differentiableAt
  have h₂ := differentiableAt_shiftedRealLogNormKernel hzw
  have hsub : DifferentiableAt ℝ
      (fun v : ℂ => realLogNormKernel v - realLogNormKernel (v - w)) z := by
    convert! h₁.sub h₂ using 1
  change LiZhongQC.dz
    (fun v : ℂ => (2 * (Real.pi : ℂ)) *
      (realLogNormKernel v - realLogNormKernel (v - w))) z = _
  rw [LiZhongQC.dz_mul (differentiableAt_const (2 * (Real.pi : ℂ))) hsub,
    LiZhongQC.dz_sub_pointwise h₁ h₂, dz_realLogNormKernel hz,
    dz_shiftedRealLogNormKernel hzw]
  have hc : LiZhongQC.dz (fun _ : ℂ => 2 * (Real.pi : ℂ)) z = 0 := by
    simp [LiZhongQC.dz]
  rw [hc, mul_zero, add_zero]
  field_simp [hz, sub_ne_zero.mpr hzw]
  ring

/-- The actual reference-zero convolution is identically zero. -/
theorem renormalizedInverseNormConvolution_zero (z : ℂ) :
    renormalizedInverseNormConvolution 0 z = 0 := by
  simp [renormalizedInverseNormConvolution,
    renormalizedInverseNormConvolutionIntegrand, renormalizedInverseNormKernel]

/-- Reflection of the literal integrand makes the actual convolution
vanish at the midpoint, including all totalized integrand values. -/
theorem renormalizedInverseNormConvolution_midpoint (w : ℂ) :
    renormalizedInverseNormConvolution w (w / 2) = 0 := by
  have heven (v : ℂ) : inverseNormKernel (-v) = inverseNormKernel v := by
    simp only [inverseNormKernel, norm_neg]
  have hreflect (t : ℂ) :
      renormalizedInverseNormConvolutionIntegrand (w / 2) w (w - t) =
        -renormalizedInverseNormConvolutionIntegrand (w / 2) w t := by
    have h₁ : (w - t) - w = -t := by ring
    have h₂ : inverseNormKernel (w - t) = inverseNormKernel (t - w) := by
      simp only [inverseNormKernel, norm_sub_rev]
    have h₃ : w / 2 - (w - t) = -(w / 2 - t) := by ring
    simp only [renormalizedInverseNormConvolutionIntegrand,
      renormalizedInverseNormKernel, h₁, h₂, h₃, heven]
    ring
  have hneg : renormalizedInverseNormConvolution w (w / 2) =
      -renormalizedInverseNormConvolution w (w / 2) := by
    unfold renormalizedInverseNormConvolution
    calc
      (∫ t : ℂ, renormalizedInverseNormConvolutionIntegrand (w / 2) w t) =
          ∫ t : ℂ, renormalizedInverseNormConvolutionIntegrand (w / 2) w (w - t) :=
        (integral_sub_left_eq_self
          (renormalizedInverseNormConvolutionIntegrand (w / 2) w) volume w).symm
      _ = ∫ t : ℂ, -renormalizedInverseNormConvolutionIntegrand (w / 2) w t :=
        integral_congr_ae (Eventually.of_forall hreflect)
      _ = -(∫ t : ℂ, renormalizedInverseNormConvolutionIntegrand (w / 2) w t) :=
        integral_neg _
  linear_combination (1 / 2 : ℂ) * hneg

private theorem fderiv_convolution_eq_logKernel {w z : ℂ}
    (hz : z ≠ 0) (hzw : z ≠ w) :
    fderiv ℝ (renormalizedInverseNormConvolution w) z =
      fderiv ℝ (renormalizedLogNormKernel w) z := by
  have hJ := differentiableAt_renormalizedInverseNormConvolution hz hzw
  have hL := differentiableAt_renormalizedLogNormKernel hz hzw
  have hJconj : (fun v => conj (renormalizedInverseNormConvolution w v)) =
      renormalizedInverseNormConvolution w :=
    funext (conj_renormalizedInverseNormConvolution w)
  have hLconj : (fun v => conj (renormalizedLogNormKernel w v)) =
      renormalizedLogNormKernel w := funext (conj_renormalizedLogNormKernel w)
  have hJbar : LiZhongQC.dzbar (renormalizedInverseNormConvolution w) z =
      conj (LiZhongQC.dz (renormalizedInverseNormConvolution w) z) := by
    simpa only [hJconj] using LiZhongQC.dzbar_conj hJ
  have hLbar : LiZhongQC.dzbar (renormalizedLogNormKernel w) z =
      conj (LiZhongQC.dz (renormalizedLogNormKernel w) z) := by
    simpa only [hLconj] using LiZhongQC.dzbar_conj hL
  have hdz : LiZhongQC.dz (renormalizedInverseNormConvolution w) z =
      LiZhongQC.dz (renormalizedLogNormKernel w) z :=
    (dz_renormalizedInverseNormConvolution hz hzw).trans
      (dz_renormalizedLogNormKernel hz hzw).symm
  ext v
  rw [LiZhongQC.fderiv_eq_dz_dzbar hJ, LiZhongQC.fderiv_eq_dz_dzbar hL,
    hJbar, hLbar, hdz]

/-- Away from its two evaluation poles, the actual renormalized
convolution equals the explicit real logarithmic difference. -/
theorem renormalizedInverseNormConvolution_eq_logKernel {w z : ℂ}
    (hz : z ≠ 0) (hzw : z ≠ w) :
    renormalizedInverseNormConvolution w z = renormalizedLogNormKernel w z := by
  by_cases hw : w = 0
  · subst w
    simp [renormalizedInverseNormConvolution_zero, renormalizedLogNormKernel]
  let s : Set ℂ := ({0, w} : Set ℂ)ᶜ
  have hfin : ({0, w} : Set ℂ).Finite := (finite_singleton w).insert 0
  have hopen : IsOpen s := hfin.isClosed.isOpen_compl
  have hconn : IsConnected s :=
    Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hfin.countable
  have hmem (x : ℂ) : x ∈ s ↔ x ≠ 0 ∧ x ≠ w := by simp [s]
  have hmid₀ : w / 2 ≠ 0 := div_ne_zero hw (by norm_num)
  have hmidw : w / 2 ≠ w := by
    intro h
    apply hw
    linear_combination (-2 : ℂ) * h
  have hmid : w / 2 ∈ s := (hmem _).mpr ⟨hmid₀, hmidw⟩
  have hLmid : renormalizedLogNormKernel w (w / 2) = 0 := by
    have heq : w / 2 - w = -(w / 2) := by ring
    simp only [renormalizedLogNormKernel, realLogNormKernel, heq, norm_neg,
      sub_self, mul_zero]
  have hJdiff : DifferentiableOn ℝ (renormalizedInverseNormConvolution w) s := by
    intro x hx
    obtain ⟨hx₀, hxw⟩ := (hmem x).mp hx
    exact (differentiableAt_renormalizedInverseNormConvolution
      hx₀ hxw).differentiableWithinAt
  have hLdiff : DifferentiableOn ℝ (renormalizedLogNormKernel w) s := by
    intro x hx
    obtain ⟨hx₀, hxw⟩ := (hmem x).mp hx
    exact (differentiableAt_renormalizedLogNormKernel hx₀ hxw).differentiableWithinAt
  have hderiv : ∀ x ∈ s,
      fderiv ℝ (renormalizedInverseNormConvolution w) x =
        fderiv ℝ (renormalizedLogNormKernel w) x := by
    intro x hx
    obtain ⟨hx₀, hxw⟩ := (hmem x).mp hx
    exact fderiv_convolution_eq_logKernel hx₀ hxw
  exact hopen.eqOn_of_fderiv_eq hconn.isPreconnected hJdiff hLdiff hderiv hmid
    ((renormalizedInverseNormConvolution_midpoint w).trans hLmid.symm)
    ((hmem z).mpr ⟨hz, hzw⟩)

/-- The explicit logarithmic expression agrees almost everywhere with
the original totalized integral, since its two evaluation poles are null. -/
theorem ae_renormalizedInverseNormConvolution_eq_logKernel (w : ℂ) :
    renormalizedInverseNormConvolution w =ᵐ[volume] renormalizedLogNormKernel w := by
  have h₀ : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    rw [ae_iff]
    simp
  have hw : ∀ᵐ z : ℂ ∂volume, z ≠ w := by
    rw [ae_iff]
    simp
  filter_upwards [h₀, hw] with z hz hzw
  exact renormalizedInverseNormConvolution_eq_logKernel hz hzw

end LowDimensionalTopology.Geometry.Quasiconformal
