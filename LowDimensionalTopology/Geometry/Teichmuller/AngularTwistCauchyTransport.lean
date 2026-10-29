module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyPullback
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Change of variables in the transported angular Cauchy integral

The inverse real Möbius transformation preserves the upper half-plane.
Its real Jacobian and the Beltrami phase combine to the square of its
complex derivative. Absolute integrability is transferred together with
the actual area integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The literal normalized kernel after the inverse Möbius substitution. -/
def transportedCauchyKernel (γ : Deck) (z η : ℂ) : ℂ :=
  (1 / ((-(γ 1 0 : ℂ)) * η + γ 0 0) ^ 2) ^ 2 *
    Quasiconformal.firstVariationKernel z
      (LiZhongQC.mobiusFn (γ 1 1) (-(γ 0 1 : ℂ)) (-(γ 1 0 : ℂ)) (γ 0 0) η)

/-- Inverse Möbius substitution transfers both genuine absolute integrability
and the actual normalized upper-plane area integral, at every evaluation point. -/
theorem pullbackCauchyTerm_change_variables (θ : Width) (γ : Deck) (z : ℂ) :
    IntegrableOn (fun η : ℂ => infinitesimalZeroExtension θ η *
      transportedCauchyKernel γ z η) {η : ℂ | 0 < η.im} (volume : Measure ℂ) ∧
    pullbackCauchyTerm θ γ z = -(1 / (Real.pi : ℂ)) *
      ∫ η in {η : ℂ | 0 < η.im},
        infinitesimalZeroExtension θ η * transportedCauchyKernel γ z η := by
  let H : Set ℂ := LiZhongQC.upperHalf
  let M : ℂ → ℂ := LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
  let S : ℂ → ℂ :=
    LiZhongQC.mobiusFn (γ 1 1) (-(γ 0 1 : ℂ)) (-(γ 1 0 : ℂ)) (γ 0 0)
  let D : ℂ → ℂ := fun η => 1 / ((-(γ 1 0 : ℂ)) * η + γ 0 0) ^ 2
  let f : ℂ → ℂ := fun ζ => pullbackInfinitesimalZeroExtension θ γ ζ *
    Quasiconformal.firstVariationKernel z ζ
  have hH : MeasurableSet H := LiZhongQC.isOpen_upperHalf.measurableSet
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe γ
  have hdetSR : γ 1 1 * γ 0 0 - (-γ 0 1) * (-γ 1 0) = 1 := by
    calc _ = γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := by ring
         _ = 1 := hdetR
  have hpos : 0 < γ 1 1 * γ 0 0 - (-γ 0 1) * (-γ 1 0) := by
    rw [hdetSR]
    exact zero_lt_one
  have hdetSC : (γ 1 1 : ℂ) * γ 0 0 - (-(γ 0 1 : ℂ)) * (-(γ 1 0 : ℂ)) = 1 := by
    calc _ = (γ 0 0 : ℂ) * γ 1 1 - (γ 0 1 : ℂ) * γ 1 0 := by ring
         _ = 1 := LiZhongQC.h23l_b_det γ
  have hconf : LiZhongQC.IsConformalOnto S H H := by
    simpa only [S, H, Complex.ofReal_neg] using
      (LiZhongQC.isConformalOnto_mobius_upperHalf hpos)
  have hdenS (η : ℂ) (hη : η ∈ H) :
      (-(γ 1 0 : ℂ)) * η + γ 0 0 ≠ 0 := by
    simpa only [Complex.ofReal_neg] using
      (LiZhongQC.mobiusFn_den_ne_zero_real (ne_of_gt hpos) hη)
  have hSderiv (η : ℂ) (hη : η ∈ H) : HasDerivAt S (D η) η := by
    have hd := LiZhongQC.hasDerivAt_mobiusFn
      (a := (γ 1 1 : ℂ)) (b := -(γ 0 1 : ℂ)) (hdenS η hη)
    rw [hdetSC] at hd
    exact hd
  have hDf : ∀ η ∈ H,
      HasFDerivWithinAt S (fderiv ℝ S η) H η := by
    intro η hη
    exact ((hSderiv η hη).differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hi : IntegrableOn f H (volume : Measure ℂ) :=
    (integrable_pullbackInfinitesimalZeroExtension_mul_firstVariationKernel θ γ z).integrableOn
  have hiImage : IntegrableOn f (S '' H) (volume : Measure ℂ) := by
    rw [hconf.2.2]
    exact hi
  have hiJac : IntegrableOn (fun η => |(fderiv ℝ S η).det| • f (S η))
      H (volume : Measure ℂ) :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (volume : Measure ℂ) hH hDf hconf.2.1 f).mp hiImage
  have hswap := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure ℂ) hH hDf hconf.2.1 f
  rw [hconf.2.2] at hswap
  have heq (η : ℂ) (hη : η ∈ H) :
      |(fderiv ℝ S η).det| • f (S η) =
        infinitesimalZeroExtension θ η * transportedCauchyKernel γ z η := by
    have hSη : S η ∈ H := by
      rw [← hconf.2.2]
      exact mem_image_of_mem S hη
    have hMS : M (S η) = η := by
      have h := LiZhongQC.mobiusFn_inv_apply
        (a := (γ 1 1 : ℂ)) (b := -(γ 0 1 : ℂ))
        (c := -(γ 1 0 : ℂ)) (d := (γ 0 0 : ℂ))
        (by rw [hdetSC]; exact one_ne_zero) (hdenS η hη)
      simpa only [M, S, neg_neg] using h
    have hdenRel : (γ 1 0 : ℂ) * S η + γ 1 1 =
        1 / ((-(γ 1 0 : ℂ)) * η + γ 0 0) := by
      have h := LiZhongQC.mobiusFn_inv_den_eq
        (a := (γ 1 1 : ℂ)) (b := -(γ 0 1 : ℂ))
        (c := -(γ 1 0 : ℂ)) (d := (γ 0 0 : ℂ)) (hdenS η hη)
      simpa only [S, hdetSC, neg_neg] using h
    have hMderiv : HasDerivAt M
        (1 / ((γ 1 0 : ℂ) * S η + γ 1 1) ^ 2) (S η) := by
      have hd := LiZhongQC.hasDerivAt_mobiusFn
        (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ))
        (LiZhongQC.h23l_b_den_ne γ hSη)
      rw [LiZhongQC.h23l_b_det γ] at hd
      exact hd
    have hderM : deriv M (S η) = (D η)⁻¹ := by
      rw [hMderiv.deriv, hdenRel]
      simp only [D, one_div, inv_pow, inv_inv]
    have hcoef : pullbackInfinitesimalZeroExtension θ γ (S η) =
        infinitesimalZeroExtension θ η * (D η / conj (D η)) := by
      calc
        _ = infinitesimalZeroExtension θ (M (S η)) *
            (conj (deriv M (S η)) / deriv M (S η)) :=
          pullbackInfinitesimalZeroExtension_eq_derivative θ γ hSη
        _ = _ := by rw [hMS, hderM]; simp only [map_inv₀, inv_div_inv]
    have hjac : (fderiv ℝ S η).det = ‖D η‖ ^ 2 := by
      have hd := hSderiv η hη
      have h := LiZhongQC.det_fderiv_eq_jacobian
        (hd.differentiableAt.restrictScalars ℝ)
      rw [LiZhongQC.jacobian, (LiZhongQC.cauchyRiemann_iff.1 hd.differentiableAt).2,
        LiZhongQC.dz_eq_deriv hd.differentiableAt, hd.deriv] at h
      simpa only [ContinuousLinearMap.det, norm_zero, zero_pow (by decide : 2 ≠ 0),
        sub_zero] using h
    have hD : D η ≠ 0 := one_div_ne_zero (pow_ne_zero 2 (hdenS η hη))
    have hcD : conj (D η) ≠ 0 := (map_ne_zero _).mpr hD
    have hnorm : ((‖D η‖ ^ 2 : ℝ) : ℂ) = D η * conj (D η) := by
      rw [Complex.mul_conj, ← Complex.sq_norm]
    rw [hjac, abs_of_nonneg (sq_nonneg ‖D η‖), Complex.real_smul]
    dsimp only [f]
    rw [hcoef]
    change ((‖D η‖ ^ 2 : ℝ) : ℂ) *
        ((infinitesimalZeroExtension θ η * (D η / conj (D η))) *
          Quasiconformal.firstVariationKernel z (S η)) =
      infinitesimalZeroExtension θ η * ((D η) ^ 2 *
        Quasiconformal.firstVariationKernel z (S η))
    rw [hnorm]
    field_simp [hcD]
  have hiT : IntegrableOn (fun η => infinitesimalZeroExtension θ η *
      transportedCauchyKernel γ z η) H (volume : Measure ℂ) :=
    hiJac.congr_fun heq hH
  have hI : pullbackCauchyTerm θ γ z = -(1 / (Real.pi : ℂ)) * ∫ ζ in H, f ζ := by
    rw [pullbackCauchyTerm_eq_upperHalfPlane]
    apply congrArg (fun c : ℂ => -(1 / (Real.pi : ℂ)) * c)
    apply setIntegral_congr_fun hH
    intro ζ hζ
    exact (congrArg (fun c : ℂ => c * Quasiconformal.firstVariationKernel z ζ)
      (pullbackInfinitesimalZeroExtension_eq_derivative θ γ hζ)).symm
  refine ⟨hiT, ?_⟩
  calc
    pullbackCauchyTerm θ γ z = -(1 / (Real.pi : ℂ)) * ∫ ζ in H, f ζ := hI
    _ = -(1 / (Real.pi : ℂ)) * ∫ η in H, |(fderiv ℝ S η).det| • f (S η) :=
      congrArg (fun c : ℂ => -(1 / (Real.pi : ℂ)) * c) hswap
    _ = -(1 / (Real.pi : ℂ)) * ∫ η in H,
        infinitesimalZeroExtension θ η * transportedCauchyKernel γ z η := by
      apply congrArg (fun c : ℂ => -(1 / (Real.pi : ℂ)) * c)
      exact setIntegral_congr_fun hH heq

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
