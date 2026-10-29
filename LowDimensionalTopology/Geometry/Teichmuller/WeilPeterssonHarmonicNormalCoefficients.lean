module

public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation

/-!
# The source WP first-variation cancellation in the actual Bers chart

This module proves the complete cancellation in source (7.44)--(7.47),
conditionally on the independent literal integral-variation obligation and
the existing canonical Eichler-jet obligation. It does not declare global
Kählerity or identify the analytic obligation with a proved result.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "φ" => nativeWeilPeterssonBaseQuadratic R hp hg hgenus hΓ
local notation "Dψ" => nativeWeilPeterssonPulledQuadraticVariation R hp hg hgenus hΓ
local notation "h" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The actual source correction vanishes, before using either WP variation formula. -/
theorem nativeWeilPeterssonDensityCorrection_zero
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (F : Set ℍ) (j k l : I) (a : ℂ) :
    nativeWeilPeterssonDensityCorrection R hp hg hgenus hΓ F j k l a = 0 := by
  unfold nativeWeilPeterssonDensityCorrection
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [(hasFDerivAt_nativeWeilPeterssonInverseDensity_zero
      R hp hg hgenus hΓ hjets l z).fderiv]
    simp

/-- Comparing the two genuine first-variation formulas kills both slot terms,
so both real directions of each original complex-coordinate derivative vanish. -/
theorem hasFDerivAt_nativeWeilPeterssonAxisCoefficient_zero_of_integralVariation
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hcompact : IsCompact (closure F)) (j k l : I) :
    HasFDerivAt (fun s : ℂ => h j k (Pi.single l s)) (0 : ℂ →L[ℝ] ℂ) 0 := by
  obtain ⟨hcoeff, _, hv⟩ := hvariation P F hF hcompact
  have hfirst (j k l : I) (a : ℂ) :
      WeilPetersson.quadraticPairing F (φ k) (Dψ j l a) = 0 := by
    obtain ⟨_, _, hfull, hsingle⟩ := hv j k l a
    have heq :
        WeilPetersson.quadraticPairing F (φ k) (Dψ j l a) +
          WeilPetersson.quadraticPairing F (Dψ k l a) (φ j) =
        0 + WeilPetersson.quadraticPairing F (Dψ k l a) (φ j) := by
      simpa [nativeWeilPeterssonDensityCorrection_zero R hp hg hgenus hΓ hjets]
        using hfull.symm.trans hsingle
    exact add_right_cancel heq
  have hd : fderiv ℝ (fun s : ℂ => h j k (Pi.single l s)) 0 = 0 := by
    ext a
    rw [(hv j k l a).2.2.2]
    have hc := WeilPetersson.quadraticPairing_conj F (φ j) (Dψ k l a)
    rw [hfirst k j l a, map_zero] at hc
    exact hc.symm
  simpa only [hd] using (hcoeff j k l).hasFDerivAt

/-- Both Wirtinger slots vanish in the unchanged original WP coefficient. -/
theorem nativeWeilPeterssonAxisCoefficient_wirtinger_zero_of_integralVariation
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hcompact : IsCompact (closure F)) (j k l : I) :
    dz (fun s : ℂ => h j k (Pi.single l s)) 0 = 0 ∧
      dzbar (fun s : ℂ => h j k (Pi.single l s)) 0 = 0 := by
  have hd := (hasFDerivAt_nativeWeilPeterssonAxisCoefficient_zero_of_integralVariation
    R hp hg hgenus hΓ hfree hsmooth hvariation hjets P F hF hcompact j k l).fderiv
  constructor <;> simp [dz, dzbar, hd]

/-- The exact source symmetry (7.37) holds at the original base point. -/
theorem nativeWeilPeterssonBaseCoefficient_symmetry_of_integralVariation
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (hcompact : IsCompact (closure F)) (j k l : I) :
    dz (fun s : ℂ => h j k (Pi.single l s)) 0 =
      dz (fun s : ℂ => h l k (Pi.single j s)) 0 := by
  rw [(nativeWeilPeterssonAxisCoefficient_wirtinger_zero_of_integralVariation
    R hp hg hgenus hΓ hfree hsmooth hvariation hjets P F hF hcompact j k l).1,
    (nativeWeilPeterssonAxisCoefficient_wirtinger_zero_of_integralVariation
    R hp hg hgenus hΓ hfree hsmooth hvariation hjets P F hF hcompact l k j).1]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
