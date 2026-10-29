module

public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonMixedKernelControl
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateFrame
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Order

/-!
# Strict signs of the original WP Ricci and scalar coordinate expressions

The frame comes from the actual positive coefficient matrix, not from a
presumed orthonormality of the canonical Bers basis. The scalar expression
is the inverse-Hermitian trace. Its twice-real-part normalization records
the full real trace for the source convention g = 2 Re h. Identification
with a Levi-Civita connection and its Ricci/scalar curvature is separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

/-- The source four-kernel contraction in the slots (u,v,v,u). -/
def mixedEnergy (μ ν : ℍ → ℂ) (ζ z : ℍ) : ℝ :=
  ‖bilinear μ ν ζ z + bilinear ν μ ζ z‖ ^ 2 + 2 * ‖sesquilinear μ ν ζ z‖ ^ 2

theorem mixedEnergy_nonneg (μ ν : ℍ → ℂ) (ζ z : ℍ) : 0 ≤ mixedEnergy μ ν ζ z :=
  add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))

@[simp] theorem four_mixed (μ ν : ℍ → ℂ) (ζ z : ℍ) :
    four μ ν ν μ ζ z = (mixedEnergy μ ν ζ z : ℂ) := by
  unfold four mixedEnergy
  rw [add_comm (bilinear ν μ ζ z) (bilinear μ ν ζ z)]
  calc
    _ = (bilinear μ ν ζ z + bilinear ν μ ζ z) *
          conj (bilinear μ ν ζ z + bilinear ν μ ζ z) +
        2 * (sesquilinear μ ν ζ z * conj (sesquilinear μ ν ζ z)) := by ring
    _ = _ := by
      rw [Complex.mul_conj', Complex.mul_conj']
      push_cast
      ring

/-- Vertical continuity is used before evaluating at z = ζ. -/
theorem ae_kernel_zero_of_mixedEnergy_integral_zero (μ ν : ℍ → ℂ) (F : Set ℍ)
    (hi : ∀ ζ : ℍ, Integrable (mixedEnergy μ ν ζ) flatArea)
    (ho : IntegrableOn (fun ζ => ∫ z : ℍ, mixedEnergy μ ν ζ z ∂flatArea) F flatArea)
    (hc : ∀ ζ : ℍ, Continuous (sesquilinear μ ν ζ))
    (hz : (∫ ζ in F, ∫ z : ℍ, mixedEnergy μ ν ζ z ∂flatArea ∂flatArea) = 0) :
    ∀ᵐ ζ ∂flatArea.restrict F, ∀ z, sesquilinear μ ν ζ z = 0 := by
  have hn (ζ : ℍ) : 0 ≤ ∫ z : ℍ, mixedEnergy μ ν ζ z ∂flatArea :=
    integral_nonneg (mixedEnergy_nonneg μ ν ζ)
  filter_upwards [(integral_eq_zero_iff_of_nonneg hn ho).mp hz] with ζ hζ
  have he : mixedEnergy μ ν ζ =ᵐ[flatArea] 0 :=
    (integral_eq_zero_iff_of_nonneg (mixedEnergy_nonneg μ ν ζ) (hi ζ)).mp hζ
  have hB : sesquilinear μ ν ζ =ᵐ[flatArea] 0 := by
    filter_upwards [he] with z hz
    have hs : ‖sesquilinear μ ν ζ z‖ ^ 2 = 0 := by
      change mixedEnergy μ ν ζ z = 0 at hz
      unfold mixedEnergy at hz
      nlinarith [sq_nonneg ‖sesquilinear μ ν ζ z‖,
        sq_nonneg ‖bilinear μ ν ζ z + bilinear ν μ ζ z‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  exact congrFun (Measure.eq_of_ae_eq hB (hc ζ) continuous_const)

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth
local notation "raised" => nativeWeilPeterssonRaisedInverseCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "L" => nativeWeilPeterssonLoweredCurvatureExpression R hp hg hgenus hΓ hfree hsmooth
local notation "Ric" => nativeWeilPeterssonRicciExpression R hp hg hgenus hΓ hfree hsmooth
local notation "Q" => nativeWeilPeterssonDirectionalRicciExpression R hp hg hgenus hΓ hfree hsmooth
local notation "C4" => nativeWeilPeterssonLoweredContraction R hp hg hgenus hΓ hfree hsmooth

/-- The inverse-Hermitian trace of the existing Ricci coefficient expression.
This equals the source's displayed diagonal trace in an h-orthonormal frame. -/
def nativeWeilPeterssonScalarExpression (a : TeichmullerSpace.{0,0} R) (t : E) : ℂ :=
  ∑ j, ∑ k, raised a j k t * Ric a j k t

/-- The full real-trace normalization for g = 2 Re h, still only an expression.
No identification with geometric scalar curvature is asserted here. -/
def nativeWeilPeterssonRealScalarExpression (a : TeichmullerSpace.{0,0} R) (t : E) : ℝ :=
  2 * (nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a t).re

/-- Correct lowering slots and conjugation, using the actual raised inverse.
The purely finite identity has no fundamental-region or analytic premise. -/
theorem nativeWeilPeterssonDirectionalRicciExpression_eq_frame
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ) (b : Module.Basis I ℂ E)
    (hframe : ∀ l r : I, raised a l r ((chart a) (β ν.val)) = ∑ α, b α l * conj (b α r))
    (v : E) :
    Q a v ((chart a) (β ν.val)) = -∑ α, conj (C4 a (b α) v v (b α) ((chart a) (β ν.val))) := by
  classical
  let f (α r j k l : I) : ℂ :=
    conj (L a r j k l ((chart a) (β ν.val))) * conj (b α r) * v j * conj (v k) * b α l
  have hperm :
      (∑ α, ∑ r, ∑ j, ∑ k, ∑ l, f α r j k l) =
        ∑ j, ∑ k, ∑ l, ∑ r, ∑ α, f α r j k l := by
    calc
      _ = ∑ r, ∑ j, ∑ k, ∑ l, ∑ α, f α r j k l := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = ∑ j, ∑ k, ∑ l, ∑ r, ∑ α, f α r j k l := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
  calc
    Q a v ((chart a) (β ν.val)) = -(∑ j, ∑ k, ∑ l, ∑ r,
        raised a l r ((chart a) (β ν.val)) * conj (L a r j k l ((chart a) (β ν.val))) * v j * conj (v k)) := by
      simp only [nativeWeilPeterssonDirectionalRicciExpression,
        nativeWeilPeterssonRicciExpression_eq_lowered_contraction,
        Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    _ = -(∑ j, ∑ k, ∑ l, ∑ r, ∑ α, f α r j k l) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro r _
      rw [hframe]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α _
      dsimp only [f]
      ring
    _ = -(∑ α, ∑ r, ∑ j, ∑ k, ∑ l, f α r j k l) :=
      congrArg (fun z : ℂ => -z) hperm.symm
    _ = -∑ α, conj (C4 a (b α) v v (b α) ((chart a) (β ν.val))) := by
      simp only [nativeWeilPeterssonLoweredContraction, map_sum, map_mul,
        Complex.conj_conj, f]

theorem nativeWeilPeterssonDirectionalRicciExpression_eq_mixedEnergy
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (b : Module.Basis I ℂ E)
    (hframe : ∀ l r : I, raised a l r ((chart a) (β ν.val)) = ∑ α, b α l * conj (b α r))
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth) (v : E) :
    Q a v ((chart a) (β ν.val)) = -(((12 / Real.pi ^ 5) * ∑ α,
      ∫ ζ in F, ∫ z : ℍ, SourceKernel.mixedEnergy
        (μ ν P F hF (b α)) (μ ν P F hF v) ζ z ∂flatArea ∂flatArea : ℝ) : ℂ) := by
  let J (α : I) : ℝ := ∫ ζ in F, ∫ z : ℍ, SourceKernel.mixedEnergy
    (μ ν P F hF (b α)) (μ ν P F hF v) ζ z ∂flatArea ∂flatArea
  have hα (α : I) :
      C4 a (b α) v v (b α) ((chart a) (β ν.val)) = (((12 / Real.pi ^ 5) * J α : ℝ) : ℂ) := by
    simpa only [J, SourceKernel.four_mixed, integral_complex_ofReal, Complex.ofReal_mul] using
      (hvary a ν P F hF).2.2 (b α) v v (b α)
  rw [nativeWeilPeterssonDirectionalRicciExpression_eq_frame
    R hp hg hgenus hΓ hfree hsmooth a ν b hframe]
  calc
    -(∑ α, conj (C4 a (b α) v v (b α) ((chart a) (β ν.val)))) =
        -(∑ α, (((12 / Real.pi ^ 5) * J α : ℝ) : ℂ)) := by
      simp_rw [hα, Complex.conj_ofReal]
    _ = -(((∑ α, (12 / Real.pi ^ 5) * J α : ℝ) : ℂ)) := by
      rw [Complex.ofReal_sum]
    _ = -((((12 / Real.pi ^ 5) * ∑ α, J α : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]

/-- Reality follows from the literal mixed square-integral formula. -/
theorem nativeWeilPeterssonDirectionalRicciExpression_im_zero_of_frame
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (b : Module.Basis I ℂ E)
    (hframe : ∀ l r : I, raised a l r ((chart a) (β ν.val)) = ∑ α, b α l * conj (b α r))
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth) (v : E) :
    (Q a v ((chart a) (β ν.val))).im = 0 := by
  rw [nativeWeilPeterssonDirectionalRicciExpression_eq_mixedEnergy
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF b hframe hvary v]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]

theorem nativeWeilPeterssonDirectionalRicciExpression_re_neg_of_frame
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (b : Module.Basis I ℂ E)
    (hframe : ∀ l r : I, raised a l r ((chart a) (β ν.val)) = ∑ α, b α l * conj (b α r))
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hmixed : Unproved.Teichmuller.WeilPeterssonMixedKernelControl
      R hp hg hgenus hΓ hfree hsmooth)
    (hdiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth) (v : E) (hv : v ≠ 0) :
    (Q a v ((chart a) (β ν.val))).re < 0 := by
  classical
  let J (α : I) : ℝ := ∫ ζ in F, ∫ z : ℍ, SourceKernel.mixedEnergy
    (μ ν P F hF (b α)) (μ ν P F hF v) ζ z ∂flatArea ∂flatArea
  have hJ (α : I) : 0 ≤ J α := integral_nonneg fun ζ =>
    integral_nonneg (SourceKernel.mixedEnergy_nonneg _ _ ζ)
  have hpos : 0 < ∑ α, J α := by
    by_contra hnotpos
    have hzsum : (∑ α, J α) = 0 :=
      le_antisymm (le_of_not_gt hnotpos) (Finset.sum_nonneg fun α _ => hJ α)
    have hzJ (α : I) : J α = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => hJ α)).mp hzsum α (Finset.mem_univ α)
    have hB (α : I) : ∀ᵐ ζ ∂flatArea.restrict F, ∀ z,
        SourceKernel.sesquilinear (μ ν P F hF (b α)) (μ ν P F hF v) ζ z = 0 := by
      rcases (hmixed ν P F hF v).2 (b α) with ⟨hi, ho, hc⟩
      exact SourceKernel.ae_kernel_zero_of_mixedEnergy_integral_zero
        _ _ F hi ho hc (hzJ α)
    let B : E →ₗ[ℂ] (ℍ → ℍ → ℂ) := IsLinearMap.mk' _ (hmixed ν P F hF v).1
    have hBsum : B v = ∑ α, b.repr v α • B (b α) := by
      calc
        B v = B (∑ α, b.repr v α • b α) := congrArg B (b.sum_repr v).symm
        _ = ∑ α, b.repr v α • B (b α) := by
          rw [map_sum]
          simp only [map_smul]
    have hd : (fun ζ => SourceKernel.sesquilinear
        (μ ν P F hF v) (μ ν P F hF v) ζ ζ) =ᵐ[flatArea.restrict F] 0 := by
      filter_upwards [Filter.eventually_all.mpr hB] with ζ hζ
      change B v ζ ζ = 0
      rw [hBsum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro α _
      exact mul_eq_zero_of_right _ (hζ α ζ)
    have ht := (hdiag a ν P F hF v).2.2.2
    have ht0 : (∫ ζ in F, SourceKernel.sesquilinear
        (μ ν P F hF v) (μ ν P F hF v) ζ ζ ∂flatArea) = 0 := by
      rw [integral_congr_ae hd]
      simp only [Pi.zero_apply, integral_zero]
    have he := congrArg Complex.re (ht.symm.trans ht0)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.zero_re] at he
    have hQ := nativeWeilPeterssonCoefficientQuadratic_pos
      R hp hg hgenus hΓ hfree hsmooth a v ((chart a) (β ν.val)) hv
    have hc : 0 < Real.pi ^ 2 / 12 := div_pos (pow_pos Real.pi_pos _) (by norm_num)
    nlinarith [mul_pos hc hQ]
  rw [nativeWeilPeterssonDirectionalRicciExpression_eq_mixedEnergy
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF b hframe hvary v,
    Complex.neg_re, Complex.ofReal_re]
  exact neg_neg_of_pos (mul_pos (div_pos (by norm_num) (pow_pos Real.pi_pos _)) hpos)

/-- Completeness converts the inverse-Hermitian trace into its frame trace. -/
theorem nativeWeilPeterssonScalarExpression_eq_frame
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ) (b : Module.Basis I ℂ E)
    (hframe : ∀ l r : I, raised a l r ((chart a) (β ν.val)) = ∑ α, b α l * conj (b α r)) :
    nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val)) =
      ∑ α, Q a (b α) ((chart a) (β ν.val)) := by
  classical
  calc
    nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val)) =
        ∑ j, ∑ k, ∑ α, Ric a j k ((chart a) (β ν.val)) * b α j * conj (b α k) := by
      unfold nativeWeilPeterssonScalarExpression
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hframe, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α _
      ring
    _ = ∑ j, ∑ α, ∑ k, Ric a j k ((chart a) (β ν.val)) * b α j * conj (b α k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ α, ∑ j, ∑ k, Ric a j k ((chart a) (β ν.val)) * b α j * conj (b α k) :=
      Finset.sum_comm
    _ = ∑ α, Q a (b α) ((chart a) (β ν.val)) := rfl

theorem nativeWeilPeterssonScalarExpression_im_zero_of_frame
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (b : Module.Basis I ℂ E)
    (hframe : ∀ l r : I, raised a l r ((chart a) (β ν.val)) = ∑ α, b α l * conj (b α r))
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth) :
    (nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))).im = 0 := by
  rw [nativeWeilPeterssonScalarExpression_eq_frame
    R hp hg hgenus hΓ hfree hsmooth a ν b hframe, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro α _
  exact nativeWeilPeterssonDirectionalRicciExpression_im_zero_of_frame
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF b hframe hvary (b α)

theorem nativeWeilPeterssonScalarExpression_re_neg_of_frame
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (b : Module.Basis I ℂ E)
    (hframe : ∀ l r : I, raised a l r ((chart a) (β ν.val)) = ∑ α, b α l * conj (b α r))
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hmixed : Unproved.Teichmuller.WeilPeterssonMixedKernelControl
      R hp hg hgenus hΓ hfree hsmooth)
    (hdiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth) :
    (nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))).re < 0 := by
  rw [nativeWeilPeterssonScalarExpression_eq_frame
    R hp hg hgenus hΓ hfree hsmooth a ν b hframe, Complex.re_sum]
  apply Finset.sum_neg
  · intro α _
    exact nativeWeilPeterssonDirectionalRicciExpression_re_neg_of_frame
      R hp hg hgenus hΓ hfree hsmooth a ν P F hF b hframe hvary hmixed hdiag
      (b α) (b.ne_zero α)
  · have hn : 0 < 3*g-3 := by omega
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The original positive WP matrix supplies the complete frame. -/
theorem nativeWeilPeterssonDirectionalRicciExpression_im_zero
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth) (v : E) :
    (Q a v ((chart a) (β ν.val))).im = 0 := by
  obtain ⟨b₀, hb₀⟩ := nativeWeilPeterssonCoordinateFrame_exists
    R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))
  exact nativeWeilPeterssonDirectionalRicciExpression_im_zero_of_frame
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF b₀ hb₀ hvary v

/-- Strict negativity for every nonzero original coordinate vector. No frame
or sign hypothesis is an input to this public conclusion. -/
theorem nativeWeilPeterssonDirectionalRicciExpression_re_neg
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hmixed : Unproved.Teichmuller.WeilPeterssonMixedKernelControl
      R hp hg hgenus hΓ hfree hsmooth)
    (hdiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth) (v : E) (hv : v ≠ 0) :
    (Q a v ((chart a) (β ν.val))).re < 0 := by
  obtain ⟨b₀, hb₀⟩ := nativeWeilPeterssonCoordinateFrame_exists
    R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))
  exact nativeWeilPeterssonDirectionalRicciExpression_re_neg_of_frame
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF b₀ hb₀ hvary hmixed hdiag v hv

theorem nativeWeilPeterssonScalarExpression_im_zero
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth) :
    (nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))).im = 0 := by
  obtain ⟨b₀, hb₀⟩ := nativeWeilPeterssonCoordinateFrame_exists
    R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))
  exact nativeWeilPeterssonScalarExpression_im_zero_of_frame
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF b₀ hb₀ hvary

theorem nativeWeilPeterssonScalarExpression_re_neg
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hmixed : Unproved.Teichmuller.WeilPeterssonMixedKernelControl
      R hp hg hgenus hΓ hfree hsmooth)
    (hdiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth) :
    (nativeWeilPeterssonScalarExpression R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))).re < 0 := by
  obtain ⟨b₀, hb₀⟩ := nativeWeilPeterssonCoordinateFrame_exists
    R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val))
  exact nativeWeilPeterssonScalarExpression_re_neg_of_frame
    R hp hg hgenus hΓ hfree hsmooth a ν P F hF b₀ hb₀ hvary hmixed hdiag

/-- The source normalization g = 2 Re h contributes a positive factor 2. -/
theorem nativeWeilPeterssonRealScalarExpression_neg
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hmixed : Unproved.Teichmuller.WeilPeterssonMixedKernelControl
      R hp hg hgenus hΓ hfree hsmooth)
    (hdiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth) :
    nativeWeilPeterssonRealScalarExpression R hp hg hgenus hΓ hfree hsmooth a ((chart a) (β ν.val)) < 0 := by
  exact mul_neg_of_pos_of_neg (by norm_num)
    (nativeWeilPeterssonScalarExpression_re_neg
      R hp hg hgenus hΓ hfree hsmooth a ν P F hF hvary hmixed hdiag)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
