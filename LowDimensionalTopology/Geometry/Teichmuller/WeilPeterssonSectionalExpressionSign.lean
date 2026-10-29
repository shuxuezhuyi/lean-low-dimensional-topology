module

public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
public import Mathlib.Tactic.Linarith

/-!
# A strict sign consumer for the actual WP sectional coordinate expression

The analytic inputs use the source-corrected kernels and explicit regularity.
For A the outer point is lower bar ζ. For B the coefficient arguments follow
English C in (7.59) and LearningMath printed 810, footnote 21; English (7.61)
prints conflicting coefficient arguments, which are not used here.
The squared-modulus algebra, equality-case argument and original-metric
positivity are proved here. No expression is identified with Riemann curvature.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

/-- Vertical continuity upgrades each a.e.-zero section before evaluating its
diagonal. No product-a.e. statement is evaluated on a measure-zero diagonal. -/
theorem integral_energy_pos_of_diagonal_ne_zero (μ : ℍ → ℂ) (F : Set ℍ)
    (hinner : ∀ ζ : ℍ, Integrable (energy μ ζ) flatArea)
    (houter : IntegrableOn (fun ζ => ∫ z : ℍ, energy μ ζ z ∂flatArea) F flatArea)
    (hcont : ∀ ζ : ℍ, Continuous (sesquilinear μ μ ζ))
    (htrace : (∫ ζ in F, sesquilinear μ μ ζ ζ ∂flatArea) ≠ 0) :
    0 < ∫ ζ in F, ∫ z : ℍ, energy μ ζ z ∂flatArea ∂flatArea := by
  have hnonneg (ζ : ℍ) : 0 ≤ ∫ z : ℍ, energy μ ζ z ∂flatArea :=
    integral_nonneg (energy_nonneg μ ζ)
  have hne : (∫ ζ in F, ∫ z : ℍ, energy μ ζ z ∂flatArea ∂flatArea) ≠ 0 := by
    intro heq
    have hae : (fun ζ => ∫ z : ℍ, energy μ ζ z ∂flatArea) =ᵐ[flatArea.restrict F] 0 :=
      (integral_eq_zero_iff_of_nonneg hnonneg houter).mp heq
    have hdiag : (fun ζ => sesquilinear μ μ ζ ζ) =ᵐ[flatArea.restrict F] 0 := by
      filter_upwards [hae] with ζ hζ
      have henergy : energy μ ζ =ᵐ[flatArea] 0 :=
        (integral_eq_zero_iff_of_nonneg (energy_nonneg μ ζ) (hinner ζ)).mp hζ
      have hkernel : sesquilinear μ μ ζ =ᵐ[flatArea] 0 := by
        filter_upwards [henergy] with z hz
        have hsq : ‖sesquilinear μ μ ζ z‖ ^ 2 = 0 := by
          change energy μ ζ z = 0 at hz
          unfold energy at hz
          nlinarith [sq_nonneg ‖sesquilinear μ μ ζ z‖,
            sq_nonneg ‖bilinear μ μ ζ z + bilinear μ μ ζ z‖]
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      have hzero : sesquilinear μ μ ζ = (0 : ℍ → ℂ) :=
        Measure.eq_of_ae_eq hkernel (hcont ζ) continuous_const
      exact congrFun hzero ζ
    apply htrace
    rw [integral_congr_ae hdiag]
    simp only [Pi.zero_apply, integral_zero]
  exact lt_iff_le_and_ne.mpr ⟨integral_nonneg hnonneg, Ne.symm hne⟩

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth
local notation "C4" => nativeWeilPeterssonLoweredContraction R hp hg hgenus hΓ hfree hsmooth
local notation "S" => nativeWeilPeterssonHolomorphicSectionalExpression R hp hg hgenus hΓ hfree hsmooth

variable (hvariation : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
    R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include hvariation hF

/-- Specializing the full analytic formula proves its literal square-sum
consequence; this is not a sign premise in the analytic input. -/
theorem nativeWeilPeterssonSectionalExpression_eq_kernelEnergy (v : E) :
    S a v ((chart a) (β ν.val)) =
      -(((12 / Real.pi ^ 5) *
        ∫ ζ in F, ∫ z : ℍ, SourceKernel.energy (μ ν P F hF v) ζ z ∂flatArea ∂flatArea : ℝ) : ℂ) := by
  have h := (hvariation a ν P F hF).2.2 v v v v
  have hcast :
      (∫ ζ in F, ∫ z : ℍ,
        SourceKernel.four (μ ν P F hF v) (μ ν P F hF v)
          (μ ν P F hF v) (μ ν P F hF v) ζ z ∂flatArea ∂flatArea) =
      ((∫ ζ in F, ∫ z : ℍ,
        SourceKernel.energy (μ ν P F hF v) ζ z ∂flatArea ∂flatArea : ℝ) : ℂ) := by
    simp only [SourceKernel.four_self, integral_complex_ofReal]
  rw [hcast, ← Complex.ofReal_mul] at h
  change -(C4 a v v v v ((chart a) (β ν.val))) = _
  exact congrArg Neg.neg h

/-- Reality of this particular quartic follows from the actual square-integral formula. -/
theorem nativeWeilPeterssonSectionalExpression_im_zero (v : E) :
    (S a v ((chart a) (β ν.val))).im = 0 := by
  rw [nativeWeilPeterssonSectionalExpression_eq_kernelEnergy
    R hp hg hgenus hΓ hfree hsmooth hvariation a ν P F hF v]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]

/-- Strict negativity of the actual coordinate expression at every original
coefficient point, conditional on the two precise analytic inputs. -/
theorem nativeWeilPeterssonSectionalExpression_re_neg
    (hcontrol : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth) (v : E) (hv : v ≠ 0) :
    (S a v ((chart a) (β ν.val))).re < 0 := by
  rcases hcontrol a ν P F hF v with ⟨hinner, houter, hcont, htrace⟩
  let Q : ℂ := ∑ j, ∑ k, v j * conj (v k) * coeff a j k ((chart a) (β ν.val))
  have hQ : 0 < Q.re := nativeWeilPeterssonCoefficientQuadratic_pos
    R hp hg hgenus hΓ hfree hsmooth a v ((chart a) (β ν.val)) hv
  have htracene : (∫ ζ in F,
      SourceKernel.sesquilinear (μ ν P F hF v) (μ ν P F hF v) ζ ζ ∂flatArea) ≠ 0 := by
    intro hzero
    have hprod := congrArg Complex.re (htrace.symm.trans hzero)
    change (((-(Real.pi ^ 2 / 12) : ℝ) : ℂ) * Q).re = 0 at hprod
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hprod
    have hc : 0 < Real.pi ^ 2 / 12 := div_pos (pow_pos Real.pi_pos _) (by norm_num)
    nlinarith [mul_pos hc hQ]
  have henergy := SourceKernel.integral_energy_pos_of_diagonal_ne_zero
    (μ ν P F hF v) F hinner houter hcont htracene
  rw [nativeWeilPeterssonSectionalExpression_eq_kernelEnergy
    R hp hg hgenus hΓ hfree hsmooth hvariation a ν P F hF v,
    Complex.neg_re, Complex.ofReal_re]
  have hc : 0 < 12 / Real.pi ^ 5 := div_pos (by norm_num) (pow_pos Real.pi_pos _)
  linarith [mul_pos hc henergy]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
