module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicVariations

/-!
# The independent source WP integral-variation obligation

This is the analytic input behind Imayoshi--Taniguchi (7.41), (7.43)--(7.45).
It concerns the unchanged native WP coefficients, literal normalized-map
kernel and actual source density. Neither closedness, coefficient symmetry,
nor a zero WP derivative is included in the proposition.

The two formulas retain both real directions in each complex parameter.
The density term has deliberately not been eliminated: its elimination is
a separate proved consequence of the canonical Eichler-jet input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "φ" => nativeWeilPeterssonBaseQuadratic R hp hg hgenus hΓ
local notation "Dψ" => nativeWeilPeterssonPulledQuadraticVariation R hp hg hgenus hΓ
local notation "ψ" => nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ
local notation "h" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The concrete two-integral first-variation formulas at the original base
point in its actual Bers coordinates, for every genuine compact source region.
The remaining work is analytic differentiation and change of variables. -/
def WeilPeterssonHarmonicIntegralFirstVariation : Prop :=
  ∀ (P : Geometry.Fuchsian.HalfPlaneFuchsianGroup (Γ.map Geometry.Hyperbolic.realSLMobius)) (F : Set ℍ),
    Geometry.Fuchsian.IsHalfPlaneFundamentalRegion P F → IsCompact (closure F) →
      (∀ j k l : I, DifferentiableAt ℝ (fun s : ℂ => h j k (Pi.single l s)) 0) ∧
      (∀ (j l : I) (z : ℍ),
        DifferentiableAt ℝ (fun s : ℂ => ψ j (Pi.single l s) z) 0) ∧
      ∀ (j k l : I) (a : ℂ),
        Integrable (fun z => (z.im ^ 2 : ℂ) * φ k z * conj (Dψ j l a z))
          (WeilPetersson.flatArea.restrict F) ∧
        Integrable (fun z => (z.im ^ 2 : ℂ) * Dψ k l a z * conj (φ j z))
          (WeilPetersson.flatArea.restrict F) ∧
        fderiv ℝ (fun s : ℂ => h j k (Pi.single l s)) 0 a =
          WeilPetersson.quadraticPairing F (φ k) (Dψ j l a) +
          WeilPetersson.quadraticPairing F (Dψ k l a) (φ j) +
          nativeWeilPeterssonDensityCorrection R hp hg hgenus hΓ F j k l a ∧
        fderiv ℝ (fun s : ℂ => h j k (Pi.single l s)) 0 a =
          WeilPetersson.quadraticPairing F (Dψ k l a) (φ j)

end LowDimensionalTopology.Unproved.Teichmuller
