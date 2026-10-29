module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicNormalCoefficients
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm
public import LowDimensionalTopology.Geometry.Teichmuller.SourceCompactFundamentalDomain
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Finite-coordinate closedness at the actual WP base point

The full differentiability premise concerns the existing actual coordinate
form. It is supplied at each deformed reference by the inverse of the actual
local tensor pullback, without a smoothness family over reference surfaces.
The independent integral variations kill the coordinate axes; differentiability
then kills the full coefficient derivatives and the actual form derivative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

/-- A finite complex coordinate decomposition upgrades zero axis derivatives
only when the whole function is already real differentiable. -/
private theorem wp_hasFDerivAt_zero_of_axes
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin n → ℂ) → F} (hf : DifferentiableAt ℝ f 0)
    (ha : ∀ j, HasFDerivAt (fun s : ℂ => f (Pi.single j s))
      (0 : ℂ →L[ℝ] F) 0) :
    HasFDerivAt f (0 : (Fin n → ℂ) →L[ℝ] F) 0 := by
  classical
  have hs (j : Fin n) (z : ℂ) : fderiv ℝ f 0 (Pi.single j z) = 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f 0) (Pi.single j (0 : ℂ)) := by
      simpa only [Pi.single_zero] using hf.hasFDerivAt
    have hc := hf'.comp 0
      (hasFDerivAt_single (𝕜 := ℝ) (E := fun _ : Fin n => ℂ) (i := j) (0 : ℂ))
    have hu := hc.unique (ha j)
    have hsingle :
        (fun i => ((Pi.single j (ContinuousLinearMap.id ℝ ℂ) :
          Fin n → (ℂ →L[ℝ] ℂ)) i) z) = Pi.single j z := by
      ext i
      by_cases hij : i = j
      · subst i
        simp
      · simp [hij]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_pi',
      hsingle, zero_apply] using congrArg (fun L : ℂ →L[ℝ] F => L z) hu
  have hd : fderiv ℝ f 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ j, Pi.single j (v j) := by ext j; simp
    rw [hv, map_sum]
    simp only [hs, Finset.sum_const_zero, zero_apply]
  simpa only [hd] using hf.hasFDerivAt

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "h" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The actual coordinate form evaluates the original complex tangent form
on the actual inverse complex Bers frame. -/
theorem nativeWeilPeterssonCoordinateForm_complexFrame (a : TeichmullerSpace.{0,0} R)
    (t v w : E) :
    nativeWeilPeterssonFundamentalRealCoordinateForm
        R hp hg hgenus hΓ hfree hsmooth a t ![v, w] =
      nativeWeilPeterssonFundamentalForm R hp hg hgenus hΓ hfree hsmooth
        ((chart a).symm t) ![(K ((chart a).symm t)).symm v,
          (K ((chart a).symm t)).symm w] := by
  rw [nativeWeilPeterssonFundamentalRealCoordinateForm_apply,
    nativeWeilPeterssonRealFundamentalForm_inverse_coordinates]

/-- The English-normalized real form recovers both parts of each actual
Hermitian coefficient, with no regularity assumption. -/
theorem nativeWeilPeterssonLocalCoefficient_from_coordinateForm (j k : I) (t : E) :
    h j k t =
      (-1 / 2 : ℂ) * (Ω t ![Complex.I • Pi.single j 1, Pi.single k 1] : ℂ) -
        (Complex.I / 2) * (Ω t ![Pi.single j 1, Pi.single k 1] : ℂ) := by
  let := C
  let a := (chart (basePoint R)).symm t
  let : InnerProductSpace.Core ℂ (TangentSpace TI a) :=
    nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth a
  rw [nativeWeilPeterssonCoordinateForm_complexFrame,
    nativeWeilPeterssonCoordinateForm_complexFrame,
    nativeWeilPeterssonFundamentalForm_apply,
    nativeWeilPeterssonFundamentalForm_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_smul,
    InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
  change h j k t = (-1 / 2 : ℂ) * (-2 * (Complex.I * h j k t).im : ℝ) -
    (Complex.I / 2) * (-2 * (h j k t).im : ℝ)
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]; ring

/-- Differentiability of the whole original real form supplies genuine
full differentiability of its original complex coefficients. -/
theorem differentiableAt_nativeWeilPeterssonBaseCoefficient_of_coordinateForm
    (hΩ : DifferentiableAt ℝ Ω 0) (j k : I) : DifferentiableAt ℝ (h j k) 0 := by
  have h₁ := Complex.ofRealCLM.differentiableAt.comp 0
    (hΩ.continuousAlternatingMap_apply_const ![Complex.I • Pi.single j 1, Pi.single k 1])
  have h₂ := Complex.ofRealCLM.differentiableAt.comp 0
    (hΩ.continuousAlternatingMap_apply_const ![Pi.single j 1, Pi.single k 1])
  apply ((h₁.const_mul (-1 / 2 : ℂ)).sub (h₂.const_mul (Complex.I / 2))).congr_of_eventuallyEq
  exact Eventually.of_forall fun t =>
    nativeWeilPeterssonLocalCoefficient_from_coordinateForm R hp hg hgenus hΓ hfree hsmooth j k t

/-- Source axis cancellation and actual full differentiability imply a zero
real Frechet derivative of every original Hermitian coefficient. -/
theorem hasFDerivAt_nativeWeilPeterssonBaseCoefficient_zero
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (hΩ : DifferentiableAt ℝ Ω 0) (j k : I) :
    HasFDerivAt (h j k) (0 : E →L[ℝ] ℂ) 0 := by
  obtain ⟨F, hF, hcompact⟩ := exists_sourceCompactHalfPlaneFundamentalRegion R hΓ hp
  apply wp_hasFDerivAt_zero_of_axes
    (differentiableAt_nativeWeilPeterssonBaseCoefficient_of_coordinateForm
      R hp hg hgenus hΓ hfree hsmooth hΩ j k)
  intro l
  exact hasFDerivAt_nativeWeilPeterssonAxisCoefficient_zero_of_integralVariation
    R hp hg hgenus hΓ hfree hsmooth hvariation hjets
    (sourceHalfPlaneFuchsianGroup hΓ) F hF hcompact j k l

/-- The actual form is the finite first-linear coefficient expression; this
retains the English factor and the original inverse tangent frame. -/
theorem nativeWeilPeterssonCoordinateForm_eq_finiteRealPairing (v w t : E) :
    Ω t ![v, w] =
      2 * (∑ j, ∑ k, (Complex.I • v) j * conj (w k) * h j k t).re := by
  let := C
  rw [nativeWeilPeterssonCoordinateForm_complexFrame,
    nativeWeilPeterssonFundamentalForm_eq_realBilinForm]
  change 2 * ((nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth _).inner
    ((K _).symm w) (Complex.I • (K _).symm v)).re = _
  rw [← map_smul]
  exact nativeWeilPeterssonRealCoordinatePairing_eq_sum R hp hg hgenus hΓ hfree hsmooth
    (basePoint R) (Complex.I • v) w t

/-- The whole existing coordinate form has zero derivative, rather than
only its restrictions to the source's complex axes. -/
theorem hasFDerivAt_nativeWeilPeterssonBaseCoordinateForm_zero
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (hΩ : DifferentiableAt ℝ Ω 0) :
    HasFDerivAt Ω (0 : E →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ)) 0 := by
  classical
  have hc := hasFDerivAt_nativeWeilPeterssonBaseCoefficient_zero
    R hp hg hgenus hΓ hfree hsmooth hvariation hjets hΩ
  have heval (v w : E) : HasFDerivAt (fun t => Ω t ![v, w]) (0 : E →L[ℝ] ℝ) 0 := by
    have hsum : HasFDerivAt
        (fun t => ∑ j, ∑ k, (Complex.I • v) j * conj (w k) * h j k t)
        (0 : E →L[ℝ] ℂ) 0 := by
      have hterm (j k : I) : HasFDerivAt
          (fun t : E => ((Complex.I • v) j * conj (w k)) * h j k t)
          (0 : E →L[ℝ] ℂ) 0 := by
        simpa only [Function.comp_def, ContinuousLinearMap.mul_apply',
          ContinuousLinearMap.comp_zero] using
          (((ContinuousLinearMap.mul ℝ ℂ) ((Complex.I • v) j * conj (w k))).hasFDerivAt.comp
            0 (hc j k))
      simpa only [Finset.sum_const_zero] using
        (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
          HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => hterm j k)))
    have hr := (Complex.reCLM.hasFDerivAt.comp 0 hsum).const_mul (2 : ℝ)
    have hr' : HasFDerivAt
        (fun t => 2 * (∑ j, ∑ k, (Complex.I • v) j * conj (w k) * h j k t).re)
        (0 : E →L[ℝ] ℝ) 0 := by simpa using hr
    apply hr'.congr_of_eventuallyEq
    exact Eventually.of_forall fun t =>
      nativeWeilPeterssonCoordinateForm_eq_finiteRealPairing
        R hp hg hgenus hΓ hfree hsmooth v w t
  have hd : fderiv ℝ Ω 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousAlternatingMap.ext
    intro v
    have he := congrArg (fun L : E →L[ℝ] ℝ => L a) (heval (v 0) (v 1)).fderiv
    rw [fderiv_continuousAlternatingMap_apply_const_apply hΩ] at he
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    simpa [hv] using he
  simpa only [hd] using hΩ.hasFDerivAt

/-- The actual base coordinate form is closed at the origin under the exact
integral variation and Eichler inputs, plus independently supplied differentiability. -/
theorem extDeriv_nativeWeilPeterssonBaseCoordinateForm_zero
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (hΩ : DifferentiableAt ℝ Ω 0) : extDeriv Ω 0 = 0 := by
  have hd := (hasFDerivAt_nativeWeilPeterssonBaseCoordinateForm_zero
    R hp hg hgenus hΓ hfree hsmooth hvariation hjets hΩ).fderiv
  rw [extDeriv, hd]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
