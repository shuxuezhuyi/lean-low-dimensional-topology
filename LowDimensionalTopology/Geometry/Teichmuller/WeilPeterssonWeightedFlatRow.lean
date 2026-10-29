module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonWeightedAbsoluteKernel
public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The weighted Cauchy-square row for actual Euclidean half-plane area

The literal real-coordinate integral is transported through the existing
complex coordinate equivalence and the actual half-plane inclusion. Both
absolute convergence and the exact row mass use the same flat area measure
as the mixed WP source kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

/-- The weighted absolute row is genuinely integrable for the original
Euclidean area, with the same finite real-coordinate mass. -/
theorem cauchySquare_weighted_absolute_flatArea (ξ : ℍ) :
    Integrable (fun η : ℍ =>
      ‖cauchySquare (conj (ξ : ℂ)) η‖ * η.im ^ (-(1 / 2 : ℝ))) flatArea ∧
    (∫ η : ℍ, ‖cauchySquare (conj (ξ : ℂ)) η‖ * η.im ^ (-(1 / 2 : ℝ)) ∂flatArea) =
      Real.pi * (∫ t : ℝ in Ioi 0, t ^ (-(1 / 2 : ℝ)) / (1 + t)) *
        ξ.im ^ (-(1 / 2 : ℝ)) := by
  let f : ℂ → ℝ := fun z =>
    ‖cauchySquare (conj (ξ : ℂ)) z‖ * z.im ^ (-(1 / 2 : ℝ))
  let k : ℝ × ℝ → ℝ := fun p =>
    ‖cauchySquare (conj (ξ : ℂ)) ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ *
      p.2 ^ (-(1 / 2 : ℝ))
  have hiter := cauchySquare_weighted_absolute_iterated ξ
  have hkmeas : Measurable k := by
    unfold k cauchySquare
    fun_prop
  have hknorm (x y : ℝ) (hy : 0 < y) : ‖k (x, y)‖ = k (x, y) :=
    Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy.le _))
  have hk : Integrable k ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff' hkmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => hiter.1 y hy
    · have hi : Integrable (fun y : ℝ => ∫ x : ℝ, k (x, y))
          (volume.restrict (Ioi 0)) := hiter.2.1
      refine hi.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact integral_congr_ae (Eventually.of_forall fun x => (hknorm x y hy).symm)
  let e := Complex.measurableEquivRealProd
  have hcoord : f ∘ e.symm = k := by
    funext p
    rcases p with ⟨x, y⟩
    simp only [Function.comp_apply, e, LiZhongQC.measurableEquivRealProd_symm_apply']
    simp only [f, k, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      zero_add, add_zero]
  have hpre : e.symm ⁻¹' LiZhongQC.upperHalf = (univ : Set ℝ) ×ˢ Ioi 0 := by
    ext p
    simp [e, LiZhongQC.upperHalf, Complex.measurableEquivRealProd_symm_apply]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hem := e.symm.measurableEmbedding
  have hplane : IntegrableOn f LiZhongQC.upperHalf := by
    apply (hmp.integrableOn_comp_preimage hem).1
    rw [hpre, hcoord, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ]
    exact hk
  have hmass : (∫ z in LiZhongQC.upperHalf, f z) =
      ∫ y : ℝ in Ioi 0, ∫ x : ℝ, k (x, y) := by
    rw [← hmp.setIntegral_preimage_emb hem f LiZhongQC.upperHalf, hpre]
    change (∫ p in (univ : Set ℝ) ×ˢ Ioi 0, (f ∘ e.symm) p) = _
    rw [hcoord, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ]
    exact integral_prod_symm k hk
  have hmap : Measure.map UpperHalfPlane.coe flatArea =
      (volume : Measure ℂ).restrict LiZhongQC.upperHalf :=
    GammaMeasurableBeltrami.map_flat_coe
  have hflat : Integrable (fun η : ℍ => f (η : ℂ)) flatArea := by
    apply (UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff
      (μ := flatArea) (g := f)).mp
    rw [hmap]
    exact hplane
  refine ⟨?_, ?_⟩
  · simpa only [f, UpperHalfPlane.coe_im] using hflat
  · calc
      (∫ η : ℍ, ‖cauchySquare (conj (ξ : ℂ)) η‖ *
          η.im ^ (-(1 / 2 : ℝ)) ∂flatArea) = ∫ η : ℍ, f (η : ℂ) ∂flatArea := by
        simp only [f, UpperHalfPlane.coe_im]
      _ = ∫ z in LiZhongQC.upperHalf, f z := by
        rw [← hmap]
        exact (UpperHalfPlane.measurableEmbedding_coe.integral_map f).symm
      _ = ∫ y : ℝ in Ioi 0, ∫ x : ℝ, k (x, y) := hmass
      _ = _ := hiter.2.2

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
