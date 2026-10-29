module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonDiagonalAbsoluteMass
public import LowDimensionalTopology.Geometry.Teichmuller.SourceFundamentalIntegrability
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegionIntegral

/-!
# Absolute diagonal integration over the original given fundamental region

Compactness of the actual uniformized surface supplies inverse-height
integrability on every original region through the existing source bound.
The literal diagonal mass scaling and the two representatives' own a.e.
norm bounds give a genuinely integrable triple kernel. The diagonal mixed
integral itself is consequently integrable on that same given region.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include hp hF in
private theorem inverseHeight_integrableOn :
    IntegrableOn (fun ζ : ℍ => (ζ.im ^ 2)⁻¹) F flatArea := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let k : ℂ → ℂ := fun z => ((z.im ^ 2 : ℝ) : ℂ)⁻¹
  have hk : AEStronglyMeasurable k (volume.restrict LiZhongQC.upperHalf) := by
    exact (by unfold k; fun_prop : Measurable k).aestronglyMeasurable
  have hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖k z‖ * z.im ^ 2 ≤ M := by
    refine ⟨1, ae_restrict_of_forall_mem LiZhongQC.isOpen_upperHalf.measurableSet fun z hz => ?_⟩
    dsimp only [k]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z.im)]
    exact (inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt (show 0 < z.im from hz)))).le
  have hi := sourceFundamentalDomainH_integrable_of_weighted_bound R
    (LiZhongQC.utm_x_isFuchsian hp) hp (Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF) hk hb
  have ho := (Fuchsian.integrableOn_openPlanarRegion_iff_closedPlanarRegion
    hF.1 hF.2.2.2 k).mpr hi
  have he := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (image_subset_range UpperHalfPlane.coe F)).mp ho
  have hf : IntegrableOn (fun ζ : ℍ => ((ζ.im ^ 2 : ℝ) : ℂ)⁻¹) F flatArea := by
    simpa only [k, UpperHalfPlane.coe_injective.preimage_image, Function.comp_def,
      flatArea, UpperHalfPlane.coe_im] using he
  exact hf.norm.congr (Eventually.of_forall fun ζ => by
    change ‖(((ζ.im ^ 2 : ℝ) : ℂ)⁻¹)‖ = (ζ.im ^ 2)⁻¹
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ζ.im)])

private theorem diagonalIntegrand_ae_norm_bound (b c : Ambient) :
    ∀ᵐ p : ℍ × ℍ ∂(flatArea.prod flatArea), ∀ ζ : ℍ,
      ‖sesquilinearIntegrand (fun η => b η) (fun ξ => c ξ) ζ ζ p.1 p.2‖ ≤
        (‖b‖ * ‖c‖) * diagonalCrossAbsolute ζ p.1 p.2 := by
  filter_upwards
    [(Measure.quasiMeasurePreserving_snd (μ := flatArea) (ν := flatArea)).ae
        (ae_hyperbolic_iff.mp (lpInfinity_norm_ae_le b)),
      (Measure.quasiMeasurePreserving_fst (μ := flatArea) (ν := flatArea)).ae
        (ae_hyperbolic_iff.mp (lpInfinity_norm_ae_le c))] with p hp hq
  intro ζ
  unfold sesquilinearIntegrand diagonalCrossAbsolute
  simp only [norm_mul, Complex.norm_conj]
  have hn : 0 ≤ ‖cauchySquare (conj (p.1 : ℂ)) ζ‖ *
      ‖cauchySquare (conj (p.1 : ℂ)) p.2‖ * ‖cauchySquare p.2 (conj (ζ : ℂ))‖ := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left
    (mul_le_mul hp hq (norm_nonneg _) (norm_nonneg _)) hn]

include hp hF in
/-- The full actual mixed diagonal integrand is absolutely integrable on
the given original region and both original upper-half-plane variables. -/
theorem sesquilinear_diagonal_joint_integrable (b c : Ambient) :
    Integrable (fun w : ℍ × (ℍ × ℍ) =>
      sesquilinearIntegrand (fun η => b η) (fun ξ => c ξ) w.1 w.1 w.2.1 w.2.2)
      ((flatArea.restrict F).prod (flatArea.prod flatArea)) := by
  let f : ℍ × (ℍ × ℍ) → ℂ := fun w =>
    sesquilinearIntegrand (fun η => b η) (fun ξ => c ξ) w.1 w.1 w.2.1 w.2.2
  have hb : AEStronglyMeasurable (fun η : ℍ => b η) flatArea :=
    (Lp.aestronglyMeasurable b).mono_ac flat_absolutelyContinuous_hyperbolic
  have hc : AEStronglyMeasurable (fun ξ : ℍ => c ξ) flatArea :=
    (Lp.aestronglyMeasurable c).mono_ac flat_absolutelyContinuous_hyperbolic
  have hkm : Measurable (fun w : ℍ × (ℍ × ℍ) =>
      cauchySquare (conj (w.2.1 : ℂ)) w.1 * cauchySquare (conj (w.2.1 : ℂ)) w.2.2 *
        cauchySquare w.2.2 (conj (w.1 : ℂ))) := by
    unfold cauchySquare
    fun_prop
  have hfm : AEStronglyMeasurable f (flatArea.prod (flatArea.prod flatArea)) :=
    (hkm.aestronglyMeasurable.mul hb.comp_snd.comp_snd).mul hc.comp_fst.comp_snd.star
  let M : ℝ := (‖b‖ * ‖c‖) *
    ∫ p : ℍ × ℍ, diagonalCrossAbsolute UpperHalfPlane.I p.1 p.2 ∂(flatArea.prod flatArea)
  have hmass (ζ : ℍ) :
      (∫ p : ℍ × ℍ, ‖f (ζ, p)‖ ∂(flatArea.prod flatArea)) ≤ M * (ζ.im ^ 2)⁻¹ := by
    calc
      _ ≤ ∫ p : ℍ × ℍ, (‖b‖ * ‖c‖) * diagonalCrossAbsolute ζ p.1 p.2
          ∂(flatArea.prod flatArea) :=
        integral_mono_ae (sesquilinear_joint_integrable b c ζ ζ).norm
          ((diagonalCrossAbsolute_integrable_and_mass ζ).1.const_mul _)
          ((diagonalIntegrand_ae_norm_bound b c).mono fun p hp => hp ζ)
      _ = (‖b‖ * ‖c‖) * ∫ p : ℍ × ℍ, diagonalCrossAbsolute ζ p.1 p.2
          ∂(flatArea.prod flatArea) := integral_const_mul _ _
      _ = M * (ζ.im ^ 2)⁻¹ := by
        rw [(diagonalCrossAbsolute_integrable_and_mass ζ).2]
        dsimp only [M]
        ring
  have hout : Integrable (fun ζ : ℍ => ∫ p : ℍ × ℍ, ‖f (ζ, p)‖
      ∂(flatArea.prod flatArea)) (flatArea.restrict F) := by
    refine ((inverseHeight_integrableOn R hp P F hF).const_mul M).mono'
      hfm.norm.integral_prod_right'.restrict ?_
    exact Eventually.of_forall fun ζ => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hmass ζ
  have hfmF : AEStronglyMeasurable f ((flatArea.restrict F).prod (flatArea.prod flatArea)) :=
    hfm.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  exact (integrable_prod_iff hfmF).2
    ⟨Eventually.of_forall fun ζ => sesquilinear_joint_integrable b c ζ ζ, hout⟩

include hp hF in
/-- The original ordinary mixed kernel has a genuinely integrable diagonal
on that same given fundamental region. -/
theorem sesquilinear_diagonal_integrableOn (b c : Ambient) :
    IntegrableOn (fun ζ : ℍ => sesquilinear (fun η => b η) (fun ξ => c ξ) ζ ζ) F flatArea := by
  have hi := (sesquilinear_diagonal_joint_integrable R hp P F hF b c).integral_prod_left
  apply hi.congr
  exact Eventually.of_forall fun ζ => by
    exact integral_prod _ (sesquilinear_joint_integrable b c ζ ζ)

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
