module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSesquilinearAbsolute
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerL2Identification
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBilinearTranspose
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerPrincipalValue
public import LowDimensionalTopology.Geometry.Teichmuller.SourceFundamentalIntegrability
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneMeasure
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegionIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Square estimates for the original cross kernels
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ComplexConjugate ENNReal Manifold ContDiff Pointwise

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces LiZhongQC GammaMeasurableBeltrami

private instance squareFlatArea_sigmaFinite : SigmaFinite flatArea := by
  apply SigmaFinite.of_map flatArea UpperHalfPlane.measurableEmbedding_coe.measurable.aemeasurable
  rw [map_flat_coe]
  infer_instance

private def squareRowWeight (ξ : ℍ) : ℝ := ξ.im ^ (-(1 / 2 : ℝ))

def squareRowMass : ℝ :=
  Real.pi * ∫ t : ℝ in Ioi 0, t ^ (-(1 / 2 : ℝ)) / (1 + t)

def squareCrossNorm (ξ η : ℍ) : ℝ :=
  ‖cauchySquare (conj (ξ : ℂ)) η‖

def squareCrossIntegral (f : ℍ → ℂ) (ξ : ℍ) : ℂ :=
  ∫ η : ℍ, cauchySquare (conj (ξ : ℂ)) η * f η ∂flatArea

private theorem squareRowWeight_pos (ξ : ℍ) : 0 < squareRowWeight ξ :=
  Real.rpow_pos_of_pos ξ.im_pos _

private theorem squareRowMass_nonneg : 0 ≤ squareRowMass := by
  apply mul_nonneg Real.pi_pos.le
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  exact div_nonneg (Real.rpow_nonneg ht0.le _) (by linarith)

theorem squareCrossNorm_symm (ξ η : ℍ) :
    squareCrossNorm ξ η = squareCrossNorm η ξ := by
  have hc : cauchySquare (conj (ξ : ℂ)) η =
      conj (cauchySquare (conj (η : ℂ)) ξ) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
    congr 1
    ring
  exact (congrArg norm hc).trans (Complex.norm_conj _)

private theorem squareCross_weighted_row (ξ : ℍ) :
    Integrable (fun η : ℍ => squareCrossNorm ξ η * squareRowWeight η) flatArea ∧
      (∫ η : ℍ, squareCrossNorm ξ η * squareRowWeight η ∂flatArea) =
        squareRowMass * squareRowWeight ξ :=
  cauchySquare_weighted_absolute_flatArea ξ

theorem squareCrossIntegral_memLp_two (f : ℍ → ℂ)
    (hf : MemLp f 2 flatArea) :
    MemLp (squareCrossIntegral f) 2 flatArea ∧
      (∫ ξ : ℍ, ‖squareCrossIntegral f ξ‖ ^ 2 ∂flatArea) ≤
        squareRowMass ^ 2 * ∫ η : ℍ, ‖f η‖ ^ 2 ∂flatArea := by
  let G : ℍ × ℍ → ℝ := fun p =>
    squareCrossNorm p.1 p.2 * squareRowWeight p.1 / squareRowWeight p.2 * ‖f p.2‖ ^ 2
  have hfSq : Integrable (fun η : ℍ => ‖f η‖ ^ 2) flatArea :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hGnonneg (p : ℍ × ℍ) : 0 ≤ G p := by
    exact mul_nonneg (div_nonneg
      (mul_nonneg (norm_nonneg _) (squareRowWeight_pos p.1).le)
      (squareRowWeight_pos p.2).le) (sq_nonneg _)
  have hGmeas : AEStronglyMeasurable G (flatArea.prod flatArea) := by
    have hk : Measurable (fun p : ℍ × ℍ =>
        squareCrossNorm p.1 p.2 * squareRowWeight p.1 / squareRowWeight p.2) := by
      unfold squareCrossNorm squareRowWeight cauchySquare
      fun_prop
    exact hk.aestronglyMeasurable.mul
      (hf.aestronglyMeasurable.norm.aemeasurable.pow_const 2).aestronglyMeasurable.comp_snd
  have hfactor (ξ η : ℍ) : G (ξ, η) =
      (squareCrossNorm η ξ * squareRowWeight ξ) * (‖f η‖ ^ 2 / squareRowWeight η) := by
    dsimp only [G]
    rw [squareCrossNorm_symm ξ η]
    ring
  have hcolumn (η : ℍ) : Integrable (fun ξ : ℍ => G (ξ, η)) flatArea :=
    ((squareCross_weighted_row η).1.mul_const (‖f η‖ ^ 2 / squareRowWeight η)).congr
      (Eventually.of_forall fun ξ => (hfactor ξ η).symm)
  have hcolumnValue (η : ℍ) : (∫ ξ : ℍ, G (ξ, η) ∂flatArea) =
      squareRowMass * ‖f η‖ ^ 2 := by
    calc
      _ = (∫ ξ : ℍ, squareCrossNorm η ξ * squareRowWeight ξ ∂flatArea) *
          (‖f η‖ ^ 2 / squareRowWeight η) := by
        rw [← integral_mul_const]
        exact integral_congr_ae (Eventually.of_forall fun ξ => hfactor ξ η)
      _ = _ := by
        rw [(squareCross_weighted_row η).2]
        field_simp [(squareRowWeight_pos η).ne']
  have hG : Integrable G (flatArea.prod flatArea) := by
    apply (integrable_prod_iff' hGmeas).2
    refine ⟨Eventually.of_forall hcolumn, ?_⟩
    have hnorm (ξ η : ℍ) : ‖G (ξ, η)‖ = G (ξ, η) :=
      Real.norm_of_nonneg (hGnonneg _)
    simp_rw [hnorm, hcolumnValue]
    exact hfSq.const_mul squareRowMass
  have hmajor : Integrable (fun ξ : ℍ =>
      squareRowMass * ∫ η : ℍ, G (ξ, η) ∂flatArea) flatArea :=
    hG.integral_prod_left.const_mul squareRowMass
  have hQmeas : AEStronglyMeasurable (squareCrossIntegral f) flatArea := by
    have hk : Measurable (fun p : ℍ × ℍ => cauchySquare (conj (p.1 : ℂ)) p.2) := by
      unfold cauchySquare
      fun_prop
    exact (hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  have hpoint : ∀ᵐ ξ ∂flatArea, ‖squareCrossIntegral f ξ‖ ^ 2 ≤
      squareRowMass * ∫ η : ℍ, G (ξ, η) ∂flatArea := by
    filter_upwards [hG.prod_right_ae] with ξ hξ
    let a : ℍ → ℝ := fun η => Real.sqrt (squareCrossNorm ξ η * squareRowWeight η)
    let b : ℍ → ℝ := fun η =>
      Real.sqrt (squareCrossNorm ξ η / squareRowWeight η) * ‖f η‖
    have haMeas : Measurable a := by
      unfold a squareCrossNorm squareRowWeight cauchySquare
      fun_prop
    have hbMeas : AEStronglyMeasurable b flatArea := by
      have hk : Measurable (fun η : ℍ =>
          Real.sqrt (squareCrossNorm ξ η / squareRowWeight η)) := by
        unfold squareCrossNorm squareRowWeight cauchySquare
        fun_prop
      exact hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.norm
    have haSq (η : ℍ) : a η ^ 2 = squareCrossNorm ξ η * squareRowWeight η :=
      Real.sq_sqrt (mul_nonneg (norm_nonneg _) (squareRowWeight_pos η).le)
    have hbSq (η : ℍ) : b η ^ 2 =
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 := by
      dsimp only [b]
      rw [mul_pow, Real.sq_sqrt
        (div_nonneg (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)
          (squareRowWeight_pos η).le)]
    have haLp : MemLp a 2 flatArea := by
      apply (memLp_two_iff_integrable_sq haMeas.aestronglyMeasurable).2
      exact (squareCross_weighted_row ξ).1.congr
        (Eventually.of_forall fun η => (haSq η).symm)
    have hbInt : Integrable (fun η : ℍ =>
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2) flatArea := by
      refine (hξ.const_mul (squareRowWeight ξ)⁻¹).congr ?_
      exact Eventually.of_forall fun η => by
        dsimp only [G]
        field_simp [(squareRowWeight_pos ξ).ne', (squareRowWeight_pos η).ne']
    have hbLp : MemLp b 2 flatArea := by
      apply (memLp_two_iff_integrable_sq hbMeas).2
      exact hbInt.congr (Eventually.of_forall fun η => (hbSq η).symm)
    have hab (η : ℍ) : ‖a η‖ * ‖b η‖ = squareCrossNorm ξ η * ‖f η‖ := by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      rw [← mul_assoc, ← Real.sqrt_mul
        (mul_nonneg (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)
          (squareRowWeight_pos η).le)]
      have he : (squareCrossNorm ξ η * squareRowWeight η) *
          (squareCrossNorm ξ η / squareRowWeight η) = squareCrossNorm ξ η ^ 2 := by
        field_simp [(squareRowWeight_pos η).ne']
      rw [he, Real.sqrt_sq (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)]
    have haNorm (η : ℍ) : ‖a η‖ ^ (2 : ℝ) =
        squareCrossNorm ξ η * squareRowWeight η := by
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      exact haSq η
    have hbNorm (η : ℍ) : ‖b η‖ ^ (2 : ℝ) =
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 := by
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      exact hbSq η
    have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
    have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
    have hcs := integral_mul_norm_le_Lp_mul_Lq hpq
      (show MemLp a (ENNReal.ofReal (2 : ℝ)) flatArea from htwo ▸ haLp)
      (show MemLp b (ENNReal.ofReal (2 : ℝ)) flatArea from htwo ▸ hbLp)
    have hbound : ‖squareCrossIntegral f ξ‖ ≤
        Real.sqrt (∫ η : ℍ, squareCrossNorm ξ η * squareRowWeight η ∂flatArea) *
          Real.sqrt (∫ η : ℍ,
            squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 ∂flatArea) := by
      calc
        _ ≤ ∫ η : ℍ, ‖cauchySquare (conj (ξ : ℂ)) η * f η‖ ∂flatArea :=
          norm_integral_le_integral_norm _
        _ = ∫ η : ℍ, ‖a η‖ * ‖b η‖ ∂flatArea := by
          apply integral_congr_ae
          exact Eventually.of_forall fun η => by
            change ‖cauchySquare (conj (ξ : ℂ)) η * f η‖ = ‖a η‖ * ‖b η‖
            rw [norm_mul]
            exact (hab η).symm
        _ ≤ _ := by
          simpa only [haNorm, hbNorm, ← Real.sqrt_eq_rpow] using hcs
    have hsquare := pow_le_pow_left₀ (norm_nonneg (squareCrossIntegral f ξ)) hbound 2
    have hrow0 : 0 ≤ ∫ η : ℍ, squareCrossNorm ξ η * squareRowWeight η ∂flatArea :=
      integral_nonneg fun η => mul_nonneg
        (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _) (squareRowWeight_pos η).le
    have hcol0 : 0 ≤ ∫ η : ℍ,
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 ∂flatArea :=
      integral_nonneg fun η => mul_nonneg
        (div_nonneg (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)
          (squareRowWeight_pos η).le) (sq_nonneg _)
    rw [mul_pow, Real.sq_sqrt hrow0, Real.sq_sqrt hcol0,
      (squareCross_weighted_row ξ).2] at hsquare
    have hrow : (∫ η : ℍ, G (ξ, η) ∂flatArea) =
        squareRowWeight ξ * ∫ η : ℍ,
          squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 ∂flatArea := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun η => by dsimp only [G]; ring
    rw [hrow]
    simpa only [mul_assoc] using hsquare
  have hsq : Integrable (fun ξ : ℍ => ‖squareCrossIntegral f ξ‖ ^ 2) flatArea := by
    apply hmajor.mono' (hQmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable
    filter_upwards [hpoint] with ξ hξ
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨(memLp_two_iff_integrable_sq_norm hQmeas).2 hsq, ?_⟩
  calc
    _ ≤ ∫ ξ : ℍ, squareRowMass * ∫ η : ℍ, G (ξ, η) ∂flatArea ∂flatArea :=
      integral_mono_ae hsq hmajor hpoint
    _ = squareRowMass * ∫ η : ℍ, ∫ ξ : ℍ, G (ξ, η) ∂flatArea ∂flatArea := by
      rw [integral_const_mul, ← integral_prod G hG, integral_prod_symm G hG]
    _ = _ := by
      simp_rw [hcolumnValue]
      rw [integral_const_mul]
      ring

theorem squareAnchor_memLp_two (ζ : ℍ) :
    MemLp (fun ξ : ℍ => cauchySquare (conj (ξ : ℂ)) ζ) 2 flatArea := by
  have hplane : IntegrableOn (fun ξ : ℂ =>
      ‖cauchySquare (conj ξ) ζ‖ ^ 2) upperHalf := by
    refine ((cauchySquare_composition ζ ζ).1.re).congr_fun (fun ξ _ => ?_)
      isOpen_upperHalf.measurableSet
    have hc : cauchySquare ξ (conj (ζ : ℂ)) =
        conj (cauchySquare (conj ξ) ζ) := by
      simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
    change (cauchySquare (conj ξ) ζ * cauchySquare ξ (conj (ζ : ℂ))).re =
      ‖cauchySquare (conj ξ) ζ‖ ^ 2
    rw [hc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hflat : Integrable (fun ξ : ℍ =>
      ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2) flatArea := by
    change Integrable _ ((volume : Measure ℂ).restrict upperHalf) at hplane
    rw [← map_flat_coe] at hplane
    exact UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp hplane
  have hm : Measurable (fun ξ : ℍ => cauchySquare (conj (ξ : ℂ)) ζ) := by
    unfold cauchySquare
    fun_prop
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 hflat

private theorem squareAmbient_mul_memLp_two (b : Ambient) (f : ℍ → ℂ)
    (hf : MemLp f 2 flatArea) :
    MemLp (fun ξ => b ξ * f ξ) 2 flatArea ∧
      (∫ ξ : ℍ, ‖b ξ * f ξ‖ ^ 2 ∂flatArea) ≤
        ‖b‖ ^ 2 * ∫ ξ : ℍ, ‖f ξ‖ ^ 2 ∂flatArea := by
  have hb : AEStronglyMeasurable (fun ξ : ℍ => b ξ) flatArea :=
    (Lp.aestronglyMeasurable b).mono_ac flat_absolutelyContinuous_hyperbolic
  have hm := hb.mul hf.aestronglyMeasurable
  have hfSq : Integrable (fun ξ : ℍ => ‖f ξ‖ ^ 2) flatArea :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hbound : ∀ᵐ ξ ∂flatArea,
      ‖b ξ * f ξ‖ ^ 2 ≤ ‖b‖ ^ 2 * ‖f ξ‖ ^ 2 := by
    filter_upwards [ae_hyperbolic_iff.mp (lpInfinity_norm_ae_le b)] with ξ hξ
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hξ 2) (sq_nonneg _)
  have hi : Integrable (fun ξ : ℍ => ‖b ξ * f ξ‖ ^ 2) flatArea := by
    apply (hfSq.const_mul (‖b‖ ^ 2)).mono'
      (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with ξ hξ
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).2 hi, ?_⟩
  calc
    _ ≤ ∫ ξ : ℍ, ‖b‖ ^ 2 * ‖f ξ‖ ^ 2 ∂flatArea :=
      integral_mono_ae hi (hfSq.const_mul (‖b‖ ^ 2)) hbound
    _ = _ := integral_const_mul _ _

theorem squareConj_memLp_two (f : ℍ → ℂ) (hf : MemLp f 2 flatArea) :
    MemLp (fun ξ => conj (f ξ)) 2 flatArea := by
  apply hf.of_le_mul (c := 1)
    (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Eventually.of_forall fun ξ => by simp only [Complex.norm_conj, one_mul, le_refl]

private theorem sesquilinear_eq_squareCross_twice (b c : Ambient) (ζ z : ℍ) :
    sesquilinear (fun η => b η) (fun ξ => c ξ) ζ z =
      squareCrossIntegral (fun η => b η * conj (squareCrossIntegral
        (fun ξ => c ξ * conj (cauchySquare (conj (ξ : ℂ)) ζ)) η)) z := by
  have hint := sesquilinear_joint_integrable b c ζ z
  unfold sesquilinear
  rw [← integral_prod _ hint, integral_prod_symm _ hint]
  unfold squareCrossIntegral
  apply integral_congr_ae
  refine Eventually.of_forall fun η => ?_
  have hswap : cauchySquare (conj (z : ℂ)) η =
      cauchySquare η (conj (z : ℂ)) := by
    unfold cauchySquare
    congr 1
    ring
  have hconj (ξ : ℍ) : conj (cauchySquare (conj (η : ℂ)) ξ) =
      cauchySquare (conj (ξ : ℂ)) η := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
    congr 1
    ring
  calc
    _ = ∫ ξ : ℍ, (cauchySquare (conj (z : ℂ)) η * b η) *
        conj (cauchySquare (conj (η : ℂ)) ξ *
          (c ξ * conj (cauchySquare (conj (ξ : ℂ)) ζ))) ∂flatArea := by
      apply integral_congr_ae
      refine Eventually.of_forall fun ξ => ?_
      simp only [sesquilinearIntegrand, map_mul, Complex.conj_conj, hconj, hswap]
      ring
    _ = (cauchySquare (conj (z : ℂ)) η * b η) *
        ∫ ξ : ℍ, conj (cauchySquare (conj (η : ℂ)) ξ *
          (c ξ * conj (cauchySquare (conj (ξ : ℂ)) ζ))) ∂flatArea :=
      integral_const_mul _ _
    _ = _ := by rw [integral_conj]; ring

theorem sesquilinear_row_square_bound (b c : Ambient) (ζ : ℍ) :
    MemLp (sesquilinear (fun η => b η) (fun ξ => c ξ) ζ) 2 flatArea ∧
      (∫ z : ℍ, ‖sesquilinear (fun η => b η) (fun ξ => c ξ) ζ z‖ ^ 2 ∂flatArea) ≤
        squareRowMass ^ 4 * ‖b‖ ^ 2 * ‖c‖ ^ 2 *
          ∫ ξ : ℍ, ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea := by
  let f : ℍ → ℂ := fun ξ => c ξ * conj (cauchySquare (conj (ξ : ℂ)) ζ)
  let h : ℍ → ℂ := fun η => b η * conj (squareCrossIntegral f η)
  have hf := squareAmbient_mul_memLp_two c
    (fun ξ : ℍ => conj (cauchySquare (conj (ξ : ℂ)) ζ))
    (squareConj_memLp_two _ (squareAnchor_memLp_two ζ))
  have hQ := squareCrossIntegral_memLp_two f hf.1
  have hh := squareAmbient_mul_memLp_two b
    (fun η => conj (squareCrossIntegral f η)) (squareConj_memLp_two _ hQ.1)
  have hQh := squareCrossIntegral_memLp_two h hh.1
  have he : sesquilinear (fun η => b η) (fun ξ => c ξ) ζ = squareCrossIntegral h := by
    funext z
    exact sesquilinear_eq_squareCross_twice b c ζ z
  rw [he]
  refine ⟨hQh.1, ?_⟩
  have hfBound : (∫ ξ : ℍ, ‖f ξ‖ ^ 2 ∂flatArea) ≤
      ‖c‖ ^ 2 * ∫ ξ : ℍ, ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea := by
    simpa only [Complex.norm_conj] using hf.2
  have hhBound : (∫ η : ℍ, ‖h η‖ ^ 2 ∂flatArea) ≤
      ‖b‖ ^ 2 * ∫ η : ℍ, ‖squareCrossIntegral f η‖ ^ 2 ∂flatArea := by
    simpa only [Complex.norm_conj] using hh.2
  calc
    _ ≤ squareRowMass ^ 2 * ∫ η : ℍ, ‖h η‖ ^ 2 ∂flatArea := hQh.2
    _ ≤ squareRowMass ^ 2 * (‖b‖ ^ 2 *
        ∫ η : ℍ, ‖squareCrossIntegral f η‖ ^ 2 ∂flatArea) :=
      mul_le_mul_of_nonneg_left hhBound (sq_nonneg _)
    _ ≤ squareRowMass ^ 2 * (‖b‖ ^ 2 *
        (squareRowMass ^ 2 * ∫ ξ : ℍ, ‖f ξ‖ ^ 2 ∂flatArea)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hQ.2 (sq_nonneg _)) (sq_nonneg _)
    _ ≤ squareRowMass ^ 2 * (‖b‖ ^ 2 *
        (squareRowMass ^ 2 * (‖c‖ ^ 2 *
          ∫ ξ : ℍ, ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfBound (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

/-- Every fixed row of the unchanged mixed source kernel is square
integrable for the original Euclidean area and actual bounded classes. -/
theorem sesquilinear_row_memLp_two (b c : Ambient) (ζ : ℍ) :
    MemLp (sesquilinear (fun η => b η) (fun ξ => c ξ) ζ) 2 flatArea :=
  (sesquilinear_row_square_bound b c ζ).1

theorem bilinear_eq_squareCross (u v : ℍ → ℂ) (ζ z : ℍ) :
    bilinear u v ζ z = -(Real.pi : ℂ) *
      squareCrossIntegral (fun η : ℍ => outerInput u v z η) ζ := by
  let f : ℂ → ℂ := outerInput u v z
  have hs : tsupport f ⊆ {ξ : ℂ | 0 ≤ ξ.im} := by
    apply closure_minimal ?_ (isClosed_le continuous_const Complex.continuous_im)
    intro ξ hξ
    by_contra hn
    have hnot : ¬0 < ξ.im := fun h => hn h.le
    apply hξ
    simp only [f, outerInput, upperExtension, hnot, dite_false]
  have hgap : ∀ ξ ∈ tsupport f, ζ.im ≤ ‖ξ - conj (ζ : ℂ)‖ := by
    intro ξ hξ
    calc
      ζ.im ≤ ξ.im + ζ.im := le_add_of_nonneg_left (hs hξ)
      _ = (ξ - conj (ζ : ℂ)).im := by
        simp only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add]
      _ ≤ |(ξ - conj (ζ : ℂ)).im| := le_abs_self _
      _ ≤ ‖ξ - conj (ζ : ℂ)‖ := Complex.abs_im_le_norm _
  let F : ℂ → ℂ := fun ξ => -(1 / (Real.pi : ℂ)) * f ξ / (ξ - conj (ζ : ℂ)) ^ 2
  have hzero : upperHalf.indicator F = F := by
    funext ξ
    by_cases hξ : ξ ∈ upperHalf
    · exact indicator_of_mem hξ _
    · rw [indicator_of_notMem hξ]
      simp only [F, f, outerInput, upperExtension,
        show ¬0 < ξ.im from hξ, dite_false, mul_zero, zero_div]
  have hplane : (∫ ξ : ℂ, F ξ) = ∫ η : ℍ, F η ∂flatArea := by
    calc
      _ = ∫ ξ : ℂ, upperHalf.indicator F ξ := by rw [hzero]
      _ = ∫ ξ in upperHalf, F ξ := integral_indicator isOpen_upperHalf.measurableSet
      _ = _ := by
        rw [← map_flat_coe]
        exact UpperHalfPlane.measurableEmbedding_coe.integral_map F
  have he : hilbertHSmooth f (conj (ζ : ℂ)) =
      -(1 / (Real.pi : ℂ)) *
        squareCrossIntegral (fun η : ℍ => outerInput u v z η) ζ := by
    calc
      _ = ∫ ξ : ℂ, F ξ := offsupp_hilbertHSmooth_eq_integral hgap ζ.im_pos
      _ = ∫ η : ℍ, F η ∂flatArea := hplane
      _ = _ := by
        unfold squareCrossIntegral
        rw [← integral_const_mul]
        apply integral_congr_ae
        refine Eventually.of_forall fun η => ?_
        have hd : ((η : ℂ) - conj (ζ : ℂ)) ^ 2 =
            (conj (ζ : ℂ) - η) ^ 2 := by ring
        dsimp only [F, f, cauchySquare]
        rw [hd]
        ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold bilinear
  rw [he]
  field_simp [hπ]

private theorem square_upperExtension_integral (u : ℍ → ℂ) :
    (∫ ξ : ℂ, ‖upperExtension u ξ‖ ^ 2) = ∫ η : ℍ, ‖u η‖ ^ 2 ∂flatArea := by
  let f : ℂ → ℝ := fun ξ => ‖upperExtension u ξ‖ ^ 2
  have he : upperHalf.indicator f = f := by
    funext ξ
    by_cases hξ : ξ ∈ upperHalf
    · exact indicator_of_mem hξ _
    · rw [indicator_of_notMem hξ]
      norm_num [f, upperExtension, show ¬0 < ξ.im from hξ]
  calc
    _ = ∫ ξ : ℂ, upperHalf.indicator f ξ := by rw [he]
    _ = ∫ ξ in upperHalf, f ξ := integral_indicator isOpen_upperHalf.measurableSet
    _ = ∫ η : ℍ, f η ∂flatArea := by
      rw [← map_flat_coe]
      exact UpperHalfPlane.measurableEmbedding_coe.integral_map f
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun η => by
        change ‖upperExtension u (η : ℂ)‖ ^ 2 = ‖u η‖ ^ 2
        rw [upperExtension, dite_eq_left (show 0 < (η : ℂ).im from η.im_pos)]

theorem squareAnchor_integral_le (ζ : ℍ) :
    (∫ ξ : ℍ, ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea) ≤
      Real.pi / (4 * ζ.im ^ 2) := by
  have hplane : (∫ ξ : ℂ in upperHalf, ‖cauchySquare (conj ξ) ζ‖ ^ 2) =
      (-(Real.pi : ℂ) * cauchySquare ζ (conj (ζ : ℂ))).re := by
    calc
      _ = ∫ ξ : ℂ in upperHalf,
          (cauchySquare (conj ξ) ζ * cauchySquare ξ (conj (ζ : ℂ))).re := by
        apply integral_congr_ae
        refine Eventually.of_forall fun ξ => ?_
        have hc : cauchySquare ξ (conj (ζ : ℂ)) =
            conj (cauchySquare (conj ξ) ζ) := by
          simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
        change ‖cauchySquare (conj ξ) ζ‖ ^ 2 =
          (cauchySquare (conj ξ) ζ * cauchySquare ξ (conj (ζ : ℂ))).re
        rw [hc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      _ = _ := (integral_re (cauchySquare_composition ζ ζ).1).trans
        (congrArg Complex.re (cauchySquare_composition ζ ζ).2)
  have hn : ‖(ζ : ℂ) - conj (ζ : ℂ)‖ ^ 2 = 4 * ζ.im ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, sub_re, conj_re, sub_im, conj_im,
      UpperHalfPlane.coe_im, sub_self]
    ring
  calc
    _ = ∫ ξ : ℂ in upperHalf, ‖cauchySquare (conj ξ) ζ‖ ^ 2 := by
      rw [← map_flat_coe]
      exact (UpperHalfPlane.measurableEmbedding_coe.integral_map (μ := flatArea)
        (fun ξ : ℂ => ‖cauchySquare (conj ξ) ζ‖ ^ 2)).symm
    _ = _ := hplane
    _ ≤ ‖-(Real.pi : ℂ) * cauchySquare ζ (conj (ζ : ℂ))‖ := Complex.re_le_norm _
    _ = _ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, cauchySquare, norm_div, norm_one, norm_pow, hn]
      ring

theorem outerQuadratic_row_square_bound
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (b : Ambient) (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ζ : ℍ) :
    MemLp (fun η : ℍ => outerInput (fun ξ => b ξ)
        (fun ξ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val ξ) ζ η) 2 flatArea ∧
      (∫ η : ℍ, ‖outerInput (fun ξ => b ξ)
        (fun ξ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val ξ) ζ η‖ ^ 2 ∂flatArea) ≤
      ‖b‖ ^ 2 * ‖(NativeHarmonicBeltrami.ofQuadratic R p hp q).val‖ ^ 2 *
        ∫ ξ : ℍ, ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea := by
  let a : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
  let f : ℂ → ℂ := innerInput (fun ξ => a ξ) ζ
  let g : ℍ → ℂ := fun η => outerInput (fun ξ => b ξ) (fun ξ => a ξ) ζ η
  have hmp : MeasurePreserving UpperHalfPlane.coe flatArea
      ((volume : Measure ℂ).restrict upperHalf) :=
    ⟨UpperHalfPlane.measurableEmbedding_coe.measurable, map_flat_coe⟩
  have hf : MemLp f 2 (volume : Measure ℂ) := innerInput_memLp_two a ζ
  have hH := hilbertH_memLp_two hf
  have hHflat : MemLp (fun η : ℍ => hilbertH f η) 2 flatArea :=
    (MemLp.mono_measure Measure.restrict_le_self hH.1).comp_measurePreserving hmp
  have hgPlane := outerInput_ofQuadratic_memLp_two R hp b q ζ
  have hg : MemLp g 2 flatArea :=
    (MemLp.mono_measure Measure.restrict_le_self hgPlane).comp_measurePreserving hmp
  have hlocal := hmp.quasiMeasurePreserving.ae
    (innerInput_ofQuadratic_hilbertHSmooth_eq_hilbertH_ae R hp q ζ)
  have he : g =ᵐ[flatArea] (fun η : ℍ => b η * hilbertH f η) := by
    filter_upwards [hlocal] with η hη
    change upperExtension (fun ξ : ℍ => b ξ * hilbertHSmooth f ξ) (η : ℂ) =
      b η * hilbertH f η
    rw [upperExtension, dite_eq_left (show 0 < (η : ℂ).im from η.im_pos), hη]
  have hb := squareAmbient_mul_memLp_two b (fun η : ℍ => hilbertH f η) hHflat
  have hHsq : Integrable (fun ξ : ℂ => ‖hilbertH f ξ‖ ^ 2) (volume : Measure ℂ) :=
    (memLp_two_iff_integrable_sq_norm hH.1.aestronglyMeasurable).1 hH.1
  have hrestrict : (∫ η : ℍ, ‖hilbertH f η‖ ^ 2 ∂flatArea) ≤
      ∫ ξ : ℂ, ‖hilbertH f ξ‖ ^ 2 := by
    calc
      _ = ∫ ξ in upperHalf, ‖hilbertH f ξ‖ ^ 2 := by
        rw [← map_flat_coe]
        exact (UpperHalfPlane.measurableEmbedding_coe.integral_map (μ := flatArea)
          (fun ξ : ℂ => ‖hilbertH f ξ‖ ^ 2)).symm
      _ ≤ _ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun ξ => sq_nonneg _) hHsq
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hnorm (v : ℂ → ℂ) (hv : MemLp v 2 (volume : Measure ℂ)) :
      (∫ ξ : ℂ, ‖v ξ‖ ^ 2) = ((eLpNorm v 2 volume) ^ (2 : ℝ)).toReal := by
    simpa only [Real.rpow_two, htwo] using
      (integral_norm_rpow_eq_toReal_pow (p := 2) (by norm_num) hv.aestronglyMeasurable)
  have hHnorm : (∫ ξ : ℂ, ‖hilbertH f ξ‖ ^ 2) = ∫ ξ : ℂ, ‖f ξ‖ ^ 2 := by
    rw [hnorm _ hH.1, hnorm _ hf, hH.2]
  have hK (ξ : ℍ) : cauchySquare ξ (conj (ζ : ℂ)) =
      conj (cauchySquare (conj (ξ : ℂ)) ζ) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
  have ha := squareAmbient_mul_memLp_two a
    (fun ξ : ℍ => conj (cauchySquare (conj (ξ : ℂ)) ζ))
    (squareConj_memLp_two _ (squareAnchor_memLp_two ζ))
  have hfBound : (∫ ξ : ℂ, ‖f ξ‖ ^ 2) ≤
      ‖a‖ ^ 2 * ∫ ξ : ℍ, ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea := by
    change (∫ ξ : ℂ, ‖upperExtension
      (fun η : ℍ => a η * cauchySquare η (conj (ζ : ℂ))) ξ‖ ^ 2) ≤ _
    rw [square_upperExtension_integral]
    simpa only [hK, Complex.norm_conj] using ha.2
  refine ⟨hg, ?_⟩
  calc
    _ = ∫ η : ℍ, ‖b η * hilbertH f η‖ ^ 2 ∂flatArea :=
      integral_congr_ae (he.mono fun η hη => congrArg (fun t : ℂ => ‖t‖ ^ 2) hη)
    _ ≤ ‖b‖ ^ 2 * ∫ η : ℍ, ‖hilbertH f η‖ ^ 2 ∂flatArea := hb.2
    _ ≤ ‖b‖ ^ 2 * ∫ ξ : ℂ, ‖hilbertH f ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hrestrict (sq_nonneg _)
    _ = ‖b‖ ^ 2 * ∫ ξ : ℂ, ‖f ξ‖ ^ 2 := by rw [hHnorm]
    _ ≤ ‖b‖ ^ 2 * (‖a‖ ^ 2 *
        ∫ ξ : ℍ, ‖cauchySquare (conj (ξ : ℂ)) ζ‖ ^ 2 ∂flatArea) :=
      mul_le_mul_of_nonneg_left hfBound (sq_nonneg _)
    _ = _ := by ring


theorem square_upperExtension_measurable (f : ℍ → ℂ) (hf : Measurable f) :
    Measurable (upperExtension f) := by
  classical
  have hcoe : Measurable (fun z : upperHalf => (⟨z.val, z.property⟩ : ℍ)) := by
    apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
    exact measurable_subtype_coe
  change Measurable (fun z : ℂ => if h : z ∈ upperHalf then f ⟨z, h⟩ else 0)
  exact (hf.comp hcoe).dite measurable_const isOpen_upperHalf.measurableSet

private theorem square_innerInput_eq (b : Ambient) (z : ℍ) (η : ℂ) :
    innerInput (fun ξ => b ξ) z η =
      upperExtension (fun ξ => b ξ) η * cauchySquare η (conj (z : ℂ)) := by
  by_cases hη : 0 < η.im
  · simp only [innerInput, upperExtension, hη, dite_true]
  · simp only [innerInput, upperExtension, hη, dite_false, zero_mul]

private theorem square_innerHilbert_stronglyMeasurable (b : Ambient)
    (hPV : ∀ z ξ : ℍ, PrincipalValueExists (innerInput (fun η => b η) z) ξ) :
    StronglyMeasurable (fun p : ℍ × ℍ =>
      hilbertHSmooth (innerInput (fun η => b η) p.1) p.2) := by
  let T : ℕ → ℍ × ℍ → ℂ := fun n p => -(1 / (Real.pi : ℂ)) *
    ∫ η in {η : ℂ | 1 / ((n : ℝ) + 1) < ‖η - p.2‖},
      innerInput (fun ξ => b ξ) p.1 η / (η - p.2) ^ 2
  have hT (n : ℕ) : StronglyMeasurable (T n) := by
    let G : (ℍ × ℍ) × ℂ → ℂ := fun p =>
      upperExtension (fun ξ => b ξ) p.2 *
        (cauchySquare p.2 (conj (p.1.1 : ℂ)) / (p.2 - p.1.2) ^ 2)
    let S : Set ((ℍ × ℍ) × ℂ) :=
      {p | 1 / ((n : ℝ) + 1) < ‖p.2 - p.1.2‖}
    have hS : MeasurableSet S :=
      measurableSet_lt measurable_const (by fun_prop)
    have hkernel : Measurable (fun p : (ℍ × ℍ) × ℂ =>
        cauchySquare p.2 (conj (p.1.1 : ℂ)) / (p.2 - p.1.2) ^ 2) := by
      unfold cauchySquare
      fun_prop
    have hG : StronglyMeasurable G := by
      have hb := square_upperExtension_measurable (fun ξ => b ξ)
        (Lp.stronglyMeasurable b).measurable
      exact ((hb.comp measurable_snd).mul hkernel).stronglyMeasurable
    have hi := (hG.indicator hS).integral_prod_right' (ν := (volume : Measure ℂ))
    have he : T n = fun p : ℍ × ℍ =>
        -(1 / (Real.pi : ℂ)) * ∫ η : ℂ, S.indicator G (p, η) := by
      funext p
      change -(1 / (Real.pi : ℂ)) *
        (∫ η in {η : ℂ | 1 / ((n : ℝ) + 1) < ‖η - p.2‖},
          innerInput (fun ξ => b ξ) p.1 η / (η - p.2) ^ 2) = _
      congr 1
      calc
        _ = ∫ η : ℂ, {η : ℂ | 1 / ((n : ℝ) + 1) < ‖η - p.2‖}.indicator
            (fun η => innerInput (fun ξ => b ξ) p.1 η / (η - p.2) ^ 2) η :=
          (integral_indicator (measurableSet_lt measurable_const
            (by fun_prop : Measurable (fun η : ℂ => ‖η - p.2‖)))).symm
        _ = _ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun η => by
            simp only [S, G, indicator_apply, mem_ofPred_eq, square_innerInput_eq, mul_div_assoc]
    rw [he]
    exact stronglyMeasurable_const.mul hi
  apply stronglyMeasurable_of_tendsto atTop hT
  apply tendsto_pi_nhds.2
  intro p
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by
        change (0 : ℝ) < 1 / ((n : ℝ) + 1)
        positivity⟩
  exact (hPV p.1 p.2).2.comp hr

theorem square_bilinear_stronglyMeasurable (b c : Ambient)
    (hPV : ∀ z ξ : ℍ, PrincipalValueExists (innerInput (fun η => c η) z) ξ) :
    StronglyMeasurable (fun p : ℍ × ℍ =>
      bilinear (fun η => b η) (fun η => c η) p.1 p.2) := by
  let H : ℍ × ℍ → ℂ := fun p => hilbertHSmooth (innerInput (fun η => c η) p.1) p.2
  have hH : StronglyMeasurable H := square_innerHilbert_stronglyMeasurable c hPV
  let G : (ℍ × ℍ) × ℍ → ℂ := fun p =>
    cauchySquare (conj (p.1.1 : ℂ)) p.2 * (b p.2 * H (p.1.2, p.2))
  have hkernel : Measurable (fun p : (ℍ × ℍ) × ℍ =>
      cauchySquare (conj (p.1.1 : ℂ)) p.2) := by unfold cauchySquare; fun_prop
  have hG : StronglyMeasurable G :=
    hkernel.stronglyMeasurable.mul (((Lp.stronglyMeasurable b).comp_measurable measurable_snd).mul
      (hH.comp_measurable (measurable_fst.snd.prodMk measurable_snd)))
  have hi := hG.integral_prod_right' (ν := flatArea)
  have he : (fun p : ℍ × ℍ => bilinear (fun η => b η) (fun η => c η) p.1 p.2) =
      (fun p => -(Real.pi : ℂ) * ∫ η : ℍ, G (p, η) ∂flatArea) := by
    funext p
    have hout (η : ℍ) :
        outerInput (fun ξ => b ξ) (fun ξ => c ξ) p.2 η =
          b η * hilbertHSmooth (innerInput (fun ξ => c ξ) p.2) η := by
      unfold outerInput upperExtension
      exact dite_eq_left (show (0 : ℝ) < (η : ℂ).im from η.im_pos)
    simpa only [squareCrossIntegral, G, H, hout] using
      bilinear_eq_squareCross (fun η => b η) (fun η => c η) p.1 p.2
  rw [he]
  exact stronglyMeasurable_const.mul hi

theorem square_sesquilinear_stronglyMeasurable (b c : Ambient) :
    StronglyMeasurable (fun p : ℍ × ℍ =>
      sesquilinear (fun η => b η) (fun η => c η) p.1 p.2) := by
  let G : ((ℍ × ℍ) × ℍ) × ℍ → ℂ := fun p =>
    sesquilinearIntegrand (fun η => b η) (fun η => c η) p.1.1.1 p.1.1.2 p.1.2 p.2
  have hkernel : Measurable (fun p : ((ℍ × ℍ) × ℍ) × ℍ =>
      cauchySquare (conj (p.1.2 : ℂ)) p.1.1.1 *
        cauchySquare (conj (p.1.2 : ℂ)) p.2 * cauchySquare p.2 (conj (p.1.1.2 : ℂ))) := by
    unfold cauchySquare
    fun_prop
  have hG : StronglyMeasurable G :=
    (hkernel.stronglyMeasurable.mul
      ((Lp.stronglyMeasurable b).comp_measurable measurable_snd)).mul
      ((Lp.stronglyMeasurable c).comp_measurable measurable_fst.snd).star
  exact (hG.integral_prod_right' (ν := flatArea)).integral_prod_right' (ν := flatArea)

theorem square_four_norm_le (a b c d e f : ℂ) :
    ‖(a + b) * conj (c + d) + 2 * e * conj f‖ ≤
      ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖e‖ ^ 2 + ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖a + b‖ * ‖c + d‖ + 2 * ‖e‖ * ‖f‖ := by
      simpa only [norm_mul, Complex.norm_conj, Complex.norm_ofNat] using
        norm_add_le ((a + b) * conj (c + d)) (2 * e * conj f)
    _ ≤ (‖a‖ + ‖b‖) * (‖c‖ + ‖d‖) + 2 * ‖e‖ * ‖f‖ :=
      add_le_add_left (mul_le_mul (norm_add_le a b) (norm_add_le c d)
        (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))) _
    _ ≤ _ := by
      nlinarith only [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖c‖ - ‖d‖),
        sq_nonneg (‖a‖ + ‖b‖ - (‖c‖ + ‖d‖)), sq_nonneg (‖e‖ - ‖f‖)]

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces LiZhongQC GammaMeasurableBeltrami

/-- The concrete positive pair of cross-half-plane kernels. -/
def absoluteCrossPair (ζ z : ℍ) : ℝ :=
  ∫ η : ℍ, squareCrossNorm z η * squareCrossNorm η ζ ∂flatArea

theorem absoluteCrossPair_nonneg (ζ z : ℍ) : 0 ≤ absoluteCrossPair ζ z :=
  integral_nonneg fun _η => mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem absoluteCrossPair_symm (ζ z : ℍ) :
    absoluteCrossPair ζ z = absoluteCrossPair z ζ := by
  unfold absoluteCrossPair
  apply integral_congr_ae
  exact Eventually.of_forall fun η => by
    calc
      squareCrossNorm z η * squareCrossNorm η ζ =
          squareCrossNorm η z * squareCrossNorm ζ η := by
        rw [squareCrossNorm_symm z η, squareCrossNorm_symm η ζ]
      _ = _ := mul_comm _ _

theorem absoluteCrossPair_literal (ζ z : ℍ) :
    absoluteCrossPair ζ z = ∫ η : ℍ, ‖cauchySquare η (conj (ζ : ℂ))‖ *
      ‖cauchySquare η (conj (z : ℂ))‖ ∂flatArea := by
  have hk (a b : ℍ) : squareCrossNorm a b = ‖cauchySquare b (conj (a : ℂ))‖ := by
    unfold squareCrossNorm
    have hs : cauchySquare (conj (a : ℂ)) b = cauchySquare b (conj (a : ℂ)) := by
      unfold cauchySquare
      congr 1
      ring
    exact congrArg norm hs
  unfold absoluteCrossPair
  apply integral_congr_ae
  exact Eventually.of_forall fun η => by
    change squareCrossNorm z η * squareCrossNorm η ζ =
      ‖cauchySquare η (conj (ζ : ℂ))‖ * ‖cauchySquare η (conj (z : ℂ))‖
    rw [squareCrossNorm_symm η ζ, hk ζ η, hk z η, mul_comm]

private theorem absoluteCrossPair_stronglyMeasurable :
    StronglyMeasurable (fun a : ℍ × ℍ => absoluteCrossPair a.1 a.2) := by
  have hm : Measurable (fun a : (ℍ × ℍ) × ℍ =>
      squareCrossNorm a.1.2 a.2 * squareCrossNorm a.2 a.1.1) := by
    unfold squareCrossNorm cauchySquare
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'

/-- The row square bound concerns only the literal pair of cross kernels. -/
theorem absoluteCrossPair_row_memLp_two (ζ : ℍ) :
    MemLp (absoluteCrossPair ζ) 2 flatArea ∧
      (∫ z : ℍ, ‖absoluteCrossPair ζ z‖ ^ 2 ∂flatArea) ≤
        squareRowMass ^ 2 * ∫ η : ℍ,
          ‖cauchySquare (conj (η : ℂ)) ζ‖ ^ 2 ∂flatArea := by
  let f : ℍ → ℂ := fun η => cauchySquare (conj (η : ℂ)) ζ
  have hf : MemLp f 2 flatArea := squareAnchor_memLp_two ζ

  let G : ℍ × ℍ → ℝ := fun p =>
    squareCrossNorm p.1 p.2 * squareRowWeight p.1 / squareRowWeight p.2 * ‖f p.2‖ ^ 2
  have hfSq : Integrable (fun η : ℍ => ‖f η‖ ^ 2) flatArea :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hGnonneg (p : ℍ × ℍ) : 0 ≤ G p := by
    exact mul_nonneg (div_nonneg
      (mul_nonneg (norm_nonneg _) (squareRowWeight_pos p.1).le)
      (squareRowWeight_pos p.2).le) (sq_nonneg _)
  have hGmeas : AEStronglyMeasurable G (flatArea.prod flatArea) := by
    have hk : Measurable (fun p : ℍ × ℍ =>
        squareCrossNorm p.1 p.2 * squareRowWeight p.1 / squareRowWeight p.2) := by
      unfold squareCrossNorm squareRowWeight cauchySquare
      fun_prop
    exact hk.aestronglyMeasurable.mul
      (hf.aestronglyMeasurable.norm.aemeasurable.pow_const 2).aestronglyMeasurable.comp_snd
  have hfactor (ξ η : ℍ) : G (ξ, η) =
      (squareCrossNorm η ξ * squareRowWeight ξ) * (‖f η‖ ^ 2 / squareRowWeight η) := by
    dsimp only [G]
    rw [squareCrossNorm_symm ξ η]
    ring
  have hcolumn (η : ℍ) : Integrable (fun ξ : ℍ => G (ξ, η)) flatArea :=
    ((squareCross_weighted_row η).1.mul_const (‖f η‖ ^ 2 / squareRowWeight η)).congr
      (Eventually.of_forall fun ξ => (hfactor ξ η).symm)
  have hcolumnValue (η : ℍ) : (∫ ξ : ℍ, G (ξ, η) ∂flatArea) =
      squareRowMass * ‖f η‖ ^ 2 := by
    calc
      _ = (∫ ξ : ℍ, squareCrossNorm η ξ * squareRowWeight ξ ∂flatArea) *
          (‖f η‖ ^ 2 / squareRowWeight η) := by
        rw [← integral_mul_const]
        exact integral_congr_ae (Eventually.of_forall fun ξ => hfactor ξ η)
      _ = _ := by
        rw [(squareCross_weighted_row η).2]
        field_simp [(squareRowWeight_pos η).ne']
  have hG : Integrable G (flatArea.prod flatArea) := by
    apply (integrable_prod_iff' hGmeas).2
    refine ⟨Eventually.of_forall hcolumn, ?_⟩
    have hnorm (ξ η : ℍ) : ‖G (ξ, η)‖ = G (ξ, η) :=
      Real.norm_of_nonneg (hGnonneg _)
    simp_rw [hnorm, hcolumnValue]
    exact hfSq.const_mul squareRowMass
  have hmajor : Integrable (fun ξ : ℍ =>
      squareRowMass * ∫ η : ℍ, G (ξ, η) ∂flatArea) flatArea :=
    hG.integral_prod_left.const_mul squareRowMass
  have hQmeas : AEStronglyMeasurable (absoluteCrossPair ζ) flatArea := by
    have hm : Measurable (fun a : ℍ × ℍ => squareCrossNorm a.1 a.2 * ‖f a.2‖) := by
      unfold f squareCrossNorm cauchySquare
      fun_prop
    exact hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hpoint : ∀ᵐ ξ ∂flatArea, ‖absoluteCrossPair ζ ξ‖ ^ 2 ≤
      squareRowMass * ∫ η : ℍ, G (ξ, η) ∂flatArea := by
    filter_upwards [hG.prod_right_ae] with ξ hξ
    let a : ℍ → ℝ := fun η => Real.sqrt (squareCrossNorm ξ η * squareRowWeight η)
    let b : ℍ → ℝ := fun η =>
      Real.sqrt (squareCrossNorm ξ η / squareRowWeight η) * ‖f η‖
    have haMeas : Measurable a := by
      unfold a squareCrossNorm squareRowWeight cauchySquare
      fun_prop
    have hbMeas : AEStronglyMeasurable b flatArea := by
      have hk : Measurable (fun η : ℍ =>
          Real.sqrt (squareCrossNorm ξ η / squareRowWeight η)) := by
        unfold squareCrossNorm squareRowWeight cauchySquare
        fun_prop
      exact hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.norm
    have haSq (η : ℍ) : a η ^ 2 = squareCrossNorm ξ η * squareRowWeight η :=
      Real.sq_sqrt (mul_nonneg (norm_nonneg _) (squareRowWeight_pos η).le)
    have hbSq (η : ℍ) : b η ^ 2 =
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 := by
      dsimp only [b]
      rw [mul_pow, Real.sq_sqrt
        (div_nonneg (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)
          (squareRowWeight_pos η).le)]
    have haLp : MemLp a 2 flatArea := by
      apply (memLp_two_iff_integrable_sq haMeas.aestronglyMeasurable).2
      exact (squareCross_weighted_row ξ).1.congr
        (Eventually.of_forall fun η => (haSq η).symm)
    have hbInt : Integrable (fun η : ℍ =>
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2) flatArea := by
      refine (hξ.const_mul (squareRowWeight ξ)⁻¹).congr ?_
      exact Eventually.of_forall fun η => by
        dsimp only [G]
        field_simp [(squareRowWeight_pos ξ).ne', (squareRowWeight_pos η).ne']
    have hbLp : MemLp b 2 flatArea := by
      apply (memLp_two_iff_integrable_sq hbMeas).2
      exact hbInt.congr (Eventually.of_forall fun η => (hbSq η).symm)
    have hab (η : ℍ) : ‖a η‖ * ‖b η‖ = squareCrossNorm ξ η * ‖f η‖ := by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      rw [← mul_assoc, ← Real.sqrt_mul
        (mul_nonneg (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)
          (squareRowWeight_pos η).le)]
      have he : (squareCrossNorm ξ η * squareRowWeight η) *
          (squareCrossNorm ξ η / squareRowWeight η) = squareCrossNorm ξ η ^ 2 := by
        field_simp [(squareRowWeight_pos η).ne']
      rw [he, Real.sqrt_sq (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)]
    have haNorm (η : ℍ) : ‖a η‖ ^ (2 : ℝ) =
        squareCrossNorm ξ η * squareRowWeight η := by
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      exact haSq η
    have hbNorm (η : ℍ) : ‖b η‖ ^ (2 : ℝ) =
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 := by
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      exact hbSq η
    have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
    have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
    have hcs := integral_mul_norm_le_Lp_mul_Lq hpq
      (show MemLp a (ENNReal.ofReal (2 : ℝ)) flatArea from htwo ▸ haLp)
      (show MemLp b (ENNReal.ofReal (2 : ℝ)) flatArea from htwo ▸ hbLp)
    have hbound : ‖absoluteCrossPair ζ ξ‖ ≤
        Real.sqrt (∫ η : ℍ, squareCrossNorm ξ η * squareRowWeight η ∂flatArea) *
          Real.sqrt (∫ η : ℍ,
            squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 ∂flatArea) := by
      calc
        _ = ∫ η : ℍ, squareCrossNorm ξ η * ‖f η‖ ∂flatArea := by
          exact Real.norm_of_nonneg (integral_nonneg fun η =>
            mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ∫ η : ℍ, ‖a η‖ * ‖b η‖ ∂flatArea := by
          apply integral_congr_ae
          exact Eventually.of_forall fun η => (hab η).symm
        _ ≤ _ := by
          simpa only [haNorm, hbNorm, ← Real.sqrt_eq_rpow] using hcs
    have hsquare := pow_le_pow_left₀ (norm_nonneg (absoluteCrossPair ζ ξ)) hbound 2
    have hrow0 : 0 ≤ ∫ η : ℍ, squareCrossNorm ξ η * squareRowWeight η ∂flatArea :=
      integral_nonneg fun η => mul_nonneg
        (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _) (squareRowWeight_pos η).le
    have hcol0 : 0 ≤ ∫ η : ℍ,
        squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 ∂flatArea :=
      integral_nonneg fun η => mul_nonneg
        (div_nonneg (show 0 ≤ squareCrossNorm ξ η from norm_nonneg _)
          (squareRowWeight_pos η).le) (sq_nonneg _)
    rw [mul_pow, Real.sq_sqrt hrow0, Real.sq_sqrt hcol0,
      (squareCross_weighted_row ξ).2] at hsquare
    have hrow : (∫ η : ℍ, G (ξ, η) ∂flatArea) =
        squareRowWeight ξ * ∫ η : ℍ,
          squareCrossNorm ξ η / squareRowWeight η * ‖f η‖ ^ 2 ∂flatArea := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun η => by dsimp only [G]; ring
    rw [hrow]
    simpa only [mul_assoc] using hsquare
  have hsq : Integrable (fun ξ : ℍ => ‖absoluteCrossPair ζ ξ‖ ^ 2) flatArea := by
    apply hmajor.mono' (hQmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable
    filter_upwards [hpoint] with ξ hξ
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨(memLp_two_iff_integrable_sq_norm hQmeas).2 hsq, ?_⟩
  calc
    _ ≤ ∫ ξ : ℍ, squareRowMass * ∫ η : ℍ, G (ξ, η) ∂flatArea ∂flatArea :=
      integral_mono_ae hsq hmajor hpoint
    _ = squareRowMass * ∫ η : ℍ, ∫ ξ : ℍ, G (ξ, η) ∂flatArea ∂flatArea := by
      rw [integral_const_mul, ← integral_prod G hG, integral_prod_symm G hG]
    _ = _ := by
      simp_rw [hcolumnValue]
      rw [integral_const_mul]
      ring


end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces LiZhongQC GammaMeasurableBeltrami

theorem square_inverseHeight_integrable
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    IntegrableOn (fun ζ : ℍ => (ζ.im ^ 2)⁻¹) F flatArea := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let f : ℂ → ℂ := fun z => ((z.im ^ 2)⁻¹ : ℝ)
  have hm : Measurable f := by unfold f; fun_prop
  have hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict upperHalf), ‖f z‖ * z.im ^ 2 ≤ M := by
    refine ⟨1, ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet fun z hz => ?_⟩
    have hz0 : z.im ≠ 0 := ne_of_gt (show 0 < z.im from hz)
    simp only [f, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg z.im)),
      inv_mul_cancel₀ (pow_ne_zero 2 hz0)]
  have hi := sourceFundamentalDomainH_integrable_of_weighted_bound R
    (utm_x_isFuchsian hp) hp (Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF)
    hm.aestronglyMeasurable.restrict hb
  have ho := (Fuchsian.integrableOn_openPlanarRegion_iff_closedPlanarRegion
    hF.1 hF.2.2.2 f).mpr hi
  have hflat := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (image_subset_range UpperHalfPlane.coe F)).mp ho
  have hc : IntegrableOn (fun ζ : ℍ => (((ζ.im ^ 2)⁻¹ : ℝ) : ℂ)) F flatArea := by
    simpa only [f, flatArea, Function.comp_def, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_injective.preimage_image] using hflat
  simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using hc.re

/-- The concrete pair of cross kernels is in L² on each original
fundamental-region cylinder of the compact uniformizing surface. -/
theorem absoluteCrossPair_region_memLp_two
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    MemLp (fun a : ℍ × ℍ => absoluteCrossPair a.1 a.2) 2
      ((flatArea.restrict F).prod flatArea) := by
  let W : ℍ × ℍ → ℝ := fun a => absoluteCrossPair a.1 a.2
  let D : ℝ := squareRowMass ^ 2 * Real.pi / 4
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hW : StronglyMeasurable W := absoluteCrossPair_stronglyMeasurable
  have hsq : StronglyMeasurable (fun a : ℍ × ℍ => W a ^ 2) := hW.pow 2
  have hrow (ζ : ℍ) : Integrable (fun z : ℍ => W (ζ, z) ^ 2) flatArea := by
    exact (memLp_two_iff_integrable_sq (absoluteCrossPair_row_memLp_two ζ).1.aestronglyMeasurable).1
      (absoluteCrossPair_row_memLp_two ζ).1
  have hb (ζ : ℍ) : (∫ z : ℍ, W (ζ, z) ^ 2 ∂flatArea) ≤ D * (ζ.im ^ 2)⁻¹ := by
    calc
      _ ≤ squareRowMass ^ 2 * ∫ η : ℍ,
          ‖cauchySquare (conj (η : ℂ)) ζ‖ ^ 2 ∂flatArea := by
        simpa only [W, Real.norm_eq_abs, sq_abs] using (absoluteCrossPair_row_memLp_two ζ).2
      _ ≤ squareRowMass ^ 2 * (Real.pi / (4 * ζ.im ^ 2)) :=
        mul_le_mul_of_nonneg_left (squareAnchor_integral_le ζ) (sq_nonneg _)
      _ = _ := by dsimp only [D]; field_simp [pow_ne_zero 2 ζ.im_pos.ne']
  have hmass : Integrable (fun ζ : ℍ => ∫ z : ℍ, W (ζ, z) ^ 2 ∂flatArea)
      (flatArea.restrict F) := by
    apply ((square_inverseHeight_integrable R hp P F hF).const_mul D).mono'
      hsq.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun ζ => by
      rw [Real.norm_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
      exact hb ζ
  have hjoint : Integrable (fun a : ℍ × ℍ => W a ^ 2)
      ((flatArea.restrict F).prod flatArea) := by
    apply (integrable_prod_iff hsq.aestronglyMeasurable).2
    refine ⟨Eventually.of_forall hrow, ?_⟩
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hmass
  exact (memLp_two_iff_integrable_sq hW.aestronglyMeasurable).2 hjoint

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
