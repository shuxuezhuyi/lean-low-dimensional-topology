module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonWeightedFlatRow
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCauchySquareComposition
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonKernelInnerIntegrability
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Absolute convergence of the original mixed WP double integral

The actual cross-kernel is split into two weighted square-integrable factors
on the product half-plane. Their squared row integrals reduce to the proved
weighted mass and the same equal-endpoint Cauchy-square composition. Existing
Hölder and Fubini theorems then give the original ordinary double integral,
including its actual native harmonic directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

private instance sourceFlatArea_sigmaFinite : SigmaFinite flatArea := by
  apply SigmaFinite.of_map flatArea UpperHalfPlane.measurableEmbedding_coe.measurable.aemeasurable
  rw [GammaMeasurableBeltrami.map_flat_coe]
  infer_instance

private def rowWeight (ξ : ℍ) : ℝ := ξ.im ^ (-(1 / 2 : ℝ))

private theorem rowWeight_pos (ξ : ℍ) : 0 < rowWeight ξ :=
  Real.rpow_pos_of_pos ξ.im_pos _

private theorem cauchySquare_opposite_norm (ξ η : ℍ) :
    ‖cauchySquare (conj (ξ : ℂ)) η‖ = ‖cauchySquare (conj (η : ℂ)) ξ‖ := by
  have hc : cauchySquare (conj (ξ : ℂ)) η =
      conj (cauchySquare (conj (η : ℂ)) ξ) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
    congr 1
    ring
  rw [hc, Complex.norm_conj]

private theorem cauchySquare_lower_norm (ξ z : ℍ) :
    ‖cauchySquare (conj (ξ : ℂ)) z‖ = ‖cauchySquare ξ (conj (z : ℂ))‖ := by
  have hc : cauchySquare (conj (ξ : ℂ)) z =
      conj (cauchySquare ξ (conj (z : ℂ))) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
  rw [hc, Complex.norm_conj]

private theorem cauchySquare_anchor_sq_integrable (z : ℍ) :
    Integrable (fun ξ : ℍ => ‖cauchySquare (conj (ξ : ℂ)) z‖ ^ 2) flatArea := by
  have hi := (cauchySquare_composition z z).1.re
  have hplane : IntegrableOn (fun ξ : ℂ =>
      ‖cauchySquare ξ (conj (z : ℂ))‖ ^ 2) LiZhongQC.upperHalf := by
    refine hi.congr_fun (fun ξ _ => ?_) LiZhongQC.isOpen_upperHalf.measurableSet
    have hc : cauchySquare (conj ξ) z = conj (cauchySquare ξ (conj (z : ℂ))) := by
      simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
    change (cauchySquare (conj ξ) z * cauchySquare ξ (conj (z : ℂ))).re =
      ‖cauchySquare ξ (conj (z : ℂ))‖ ^ 2
    rw [hc, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  change Integrable _ ((volume : Measure ℂ).restrict LiZhongQC.upperHalf) at hplane
  rw [← GammaMeasurableBeltrami.map_flat_coe] at hplane
  have hflat := UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp hplane
  change Integrable (fun ξ : ℍ => ‖cauchySquare ξ (conj (z : ℂ))‖ ^ 2) flatArea at hflat
  exact hflat.congr (Eventually.of_forall fun ξ =>
    congrArg (fun a : ℝ => a ^ 2) (cauchySquare_lower_norm ξ z).symm)

private def weightedRowFactor (z : ℍ) (p : ℍ × ℍ) : ℝ :=
  ‖cauchySquare (conj (p.1 : ℂ)) z‖ *
    Real.sqrt (‖cauchySquare (conj (p.1 : ℂ)) p.2‖ * rowWeight p.2 / rowWeight p.1)

private theorem weightedRowFactor_nonneg (z : ℍ) (p : ℍ × ℍ) :
    0 ≤ weightedRowFactor z p :=
  mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

private theorem weightedRowFactor_sq (z ξ η : ℍ) :
    weightedRowFactor z (ξ, η) ^ 2 =
      (‖cauchySquare (conj (ξ : ℂ)) z‖ ^ 2 / rowWeight ξ) *
        (‖cauchySquare (conj (ξ : ℂ)) η‖ * rowWeight η) := by
  unfold weightedRowFactor
  rw [mul_pow, Real.sq_sqrt (div_nonneg
    (mul_nonneg (norm_nonneg _) (rowWeight_pos η).le) (rowWeight_pos ξ).le)]
  ring

private theorem weightedRowFactor_memLp_two (z : ℍ) :
    MemLp (weightedRowFactor z) 2 (flatArea.prod flatArea) := by
  let M : ℝ := Real.pi * ∫ t : ℝ in Ioi 0, t ^ (-(1 / 2 : ℝ)) / (1 + t)
  have hm : Measurable (weightedRowFactor z) := by
    unfold weightedRowFactor rowWeight cauchySquare
    fun_prop
  have hrow (ξ : ℍ) := cauchySquare_weighted_absolute_flatArea ξ
  have hi (ξ : ℍ) : Integrable (fun η : ℍ => weightedRowFactor z (ξ, η) ^ 2) flatArea := by
    exact ((hrow ξ).1.const_mul
      (‖cauchySquare (conj (ξ : ℂ)) z‖ ^ 2 / rowWeight ξ)).congr
        (Eventually.of_forall fun η => (weightedRowFactor_sq z ξ η).symm)
  have he (ξ : ℍ) : (∫ η : ℍ, weightedRowFactor z (ξ, η) ^ 2 ∂flatArea) =
      M * ‖cauchySquare (conj (ξ : ℂ)) z‖ ^ 2 := by
    calc
      _ = (‖cauchySquare (conj (ξ : ℂ)) z‖ ^ 2 / rowWeight ξ) *
          ∫ η : ℍ, ‖cauchySquare (conj (ξ : ℂ)) η‖ * rowWeight η ∂flatArea := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun η => weightedRowFactor_sq z ξ η)
      _ = _ := by
        dsimp only [rowWeight]
        rw [(hrow ξ).2]
        change (‖cauchySquare (conj (ξ : ℂ)) z‖ ^ 2 / rowWeight ξ) *
          (M * rowWeight ξ) = _
        field_simp [(rowWeight_pos ξ).ne']
  have hnorm (ξ η : ℍ) : ‖weightedRowFactor z (ξ, η) ^ 2‖ =
      weightedRowFactor z (ξ, η) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
  have hout : Integrable (fun ξ : ℍ =>
      ∫ η : ℍ, ‖weightedRowFactor z (ξ, η) ^ 2‖ ∂flatArea) flatArea := by
    simp_rw [hnorm, he]
    exact (cauchySquare_anchor_sq_integrable z).const_mul M
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  exact (integrable_prod_iff (hm.pow_const (2 : ℕ)).aestronglyMeasurable).2
    ⟨Eventually.of_forall hi, hout⟩

private theorem weightedRowFactor_pair (ζ z ξ η : ℍ) :
    weightedRowFactor ζ (ξ, η) * weightedRowFactor z (η, ξ) =
      ‖cauchySquare (conj (ξ : ℂ)) ζ‖ *
        ‖cauchySquare (conj (ξ : ℂ)) η‖ * ‖cauchySquare η (conj (z : ℂ))‖ := by
  apply (sq_eq_sq₀ (mul_nonneg (weightedRowFactor_nonneg ζ _) (weightedRowFactor_nonneg z _))
    (by positivity)).1
  rw [mul_pow, weightedRowFactor_sq, weightedRowFactor_sq,
    cauchySquare_opposite_norm η ξ, ← cauchySquare_lower_norm η z]
  field_simp [(rowWeight_pos ξ).ne', (rowWeight_pos η).ne']

/-- The unchanged mixed integrand for actual L-infinity representatives is
absolutely integrable on the product of the two original half-planes. -/
theorem sesquilinear_joint_integrable
    (b c : GammaMeasurableBeltrami.Ambient) (ζ z : ℍ) :
    Integrable (fun p : ℍ × ℍ =>
      sesquilinearIntegrand (fun η => b η) (fun ξ => c ξ) ζ z p.1 p.2)
      (flatArea.prod flatArea) := by
  have hfactor : Integrable (fun p : ℍ × ℍ =>
      weightedRowFactor ζ p * weightedRowFactor z (Prod.swap p)) (flatArea.prod flatArea) := by
    exact ((weightedRowFactor_memLp_two ζ).integrable_mul
      ((weightedRowFactor_memLp_two z).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := flatArea) (ν := flatArea)))).congr
      (Eventually.of_forall fun p => rfl)
  have hkernel : Integrable (fun p : ℍ × ℍ =>
      ‖cauchySquare (conj (p.1 : ℂ)) ζ‖ *
        ‖cauchySquare (conj (p.1 : ℂ)) p.2‖ *
        ‖cauchySquare p.2 (conj (z : ℂ))‖) (flatArea.prod flatArea) :=
    hfactor.congr (Eventually.of_forall fun p => weightedRowFactor_pair ζ z p.1 p.2)
  have hb : AEStronglyMeasurable (fun η : ℍ => b η) flatArea :=
    (Lp.aestronglyMeasurable b).mono_ac GammaMeasurableBeltrami.flat_absolutelyContinuous_hyperbolic
  have hc : AEStronglyMeasurable (fun ξ : ℍ => c ξ) flatArea :=
    (Lp.aestronglyMeasurable c).mono_ac GammaMeasurableBeltrami.flat_absolutelyContinuous_hyperbolic
  have hkm : Measurable (fun p : ℍ × ℍ =>
      cauchySquare (conj (p.1 : ℂ)) ζ * cauchySquare (conj (p.1 : ℂ)) p.2 *
        cauchySquare p.2 (conj (z : ℂ))) := by
    unfold cauchySquare
    fun_prop
  refine (hkernel.const_mul (‖b‖ * ‖c‖)).mono'
    ((hkm.aestronglyMeasurable.mul hb.comp_snd).mul hc.comp_fst.star) ?_
  have hbBound : ∀ᵐ η : ℍ ∂flatArea, ‖b η‖ ≤ ‖b‖ :=
    GammaMeasurableBeltrami.ae_hyperbolic_iff.mp (lpInfinity_norm_ae_le b)
  have hcBound : ∀ᵐ ξ : ℍ ∂flatArea, ‖c ξ‖ ≤ ‖c‖ :=
    GammaMeasurableBeltrami.ae_hyperbolic_iff.mp (lpInfinity_norm_ae_le c)
  filter_upwards
    [(Measure.quasiMeasurePreserving_snd (μ := flatArea) (ν := flatArea)).ae hbBound,
     (Measure.quasiMeasurePreserving_fst (μ := flatArea) (ν := flatArea)).ae hcBound]
    with p hp hq
  have hnonneg : 0 ≤ ‖cauchySquare (conj (p.1 : ℂ)) ζ‖ *
      ‖cauchySquare (conj (p.1 : ℂ)) p.2‖ * ‖cauchySquare p.2 (conj (z : ℂ))‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  simp only [sesquilinearIntegrand, norm_mul, Complex.norm_conj]
  nlinarith [mul_le_mul_of_nonneg_left
    (mul_le_mul hp hq (norm_nonneg _) (norm_nonneg _)) hnonneg]

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- The actual native harmonic source directions have both ordinary
integrals defining the mixed kernel, at every pair of original upper points. -/
theorem nativeWeilPetersson_sesquilinearIntegralExists
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (ζ z : ℍ) :
    SourceKernel.SesquilinearIntegralExists (μ ν P F hF u) (μ ν P F hF v) ζ z := by
  let := C
  let b : Ambient := (TH ν P F hF hsmooth ((K (β ν.val)).symm u)).val.val
  let c : Ambient := (TH ν P F hF hsmooth ((K (β ν.val)).symm v)).val.val
  refine ⟨fun ξ => nativeWeilPetersson_sesquilinear_inner_integrable
    R hp hg hgenus hΓ hfree hsmooth ν P F hF u v ζ z ξ, ?_⟩
  exact (SourceKernel.sesquilinear_joint_integrable b c ζ z).integral_prod_left

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
