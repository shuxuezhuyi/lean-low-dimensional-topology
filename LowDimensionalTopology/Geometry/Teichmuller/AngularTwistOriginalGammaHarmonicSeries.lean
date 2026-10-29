module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalGammaBersSeries
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicDecomposition
public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesConvergence

/-!
# The harmonic representative of the same original-cover direction

The actual transported coefficient determines its Riesz quadratic on the
original covering. Its reflected Bers derivative identifies that quadratic
with the literal full-cyclic endpoint series. The harmonic projection and
its genuine infinitesimal kernel therefore retain the same direction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped UpperHalfPlane ComplexConjugate Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open Surfaces GammaMeasurableBeltrami

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The same given original coefficient has its actual endpoint Petersson
series and the precise harmonic representative modulo the true Bers kernel. -/
theorem givenAngularInfinitesimal_originalGamma_harmonic_series
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (Γ : Subgroup Deck) (hΓ : LiZhongQC.IsFuchsian Γ) (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (A : Deck) (hAΓ : A ∈ Γ)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (Q : Deck) (s : ℝ) (hs : 0 < s)
    (hQA : Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
      Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))
    (ν : Space (LiZhongQC.conjGroup Γ Q))
    (hν : (ν.val : ℍ → ℂ) =ᵐ[volume]
      (fun z : ℍ => rightCosetInfinitesimalSum (canonicalBandWidth s hs)
        (LiZhongQC.conjGroup Γ Q) s (z : ℂ)))
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel
          (projectiveDilationSubgroup (LiZhongQC.conjGroup Γ Q) s)),
        rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs)
          (LiZhongQC.conjGroup Γ Q) s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs)
          (LiZhongQC.conjGroup Γ Q) s v ζ ≠ 0 → u = v)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    let νOriginal : Space Γ := coefficientRealMobiusIsometry Γ Q ν
    let CA := Quotient (QuotientGroup.rightRel
      (Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
        (Subgroup.zpowers (Hyperbolic.realSLMobius A))))
    ∃ Ψ : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      (∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
        ∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
          QuadraticBergman.uniformizedQuadratic R p Ψ z =
              GeodesicSeries.peterssonSeries Γ A hA ht ρ z ∧
            HasSum (fun u : CA =>
              GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hA ht)
                  (LiZhongQC.h36p_m (ρ u).val z) *
                (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2)
              (QuadraticBergman.uniformizedQuadratic R p Ψ z) ∧
            Summable (fun u : CA =>
              ‖GeodesicSeries.seed (Hyperbolic.hHyperbolicAxis A hA ht)
                  (LiZhongQC.h36p_m (ρ u).val z) *
                (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2‖)) ∧
      NativePetersson.harmonicProjection R P p hp F hF νOriginal =
        (-(Complex.I / (Real.pi : ℂ))) •
          NativeHarmonicBeltrami.ofQuadratic R p hp Ψ ∧
      νOriginal - (-(Complex.I / (Real.pi : ℂ))) •
          NativeHarmonicBeltrami.ofQuadratic R p hp Ψ ∈
        NativePetersson.infinitesimalSubmodule Γ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let νOriginal : Space Γ := coefficientRealMobiusIsometry Γ Q ν
  let CA := Quotient (QuotientGroup.rightRel
    (Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
      (Subgroup.zpowers (Hyperbolic.realSLMobius A))))
  let r := NativePetersson.toQuadratic R P p hp F hF
    (NativePetersson.rieszQuadratic R P p hp F hF νOriginal)
  let c : ℂ := -Complex.I * (Real.pi : ℂ)
  let a : ℂ := -(Complex.I / (Real.pi : ℂ))
  let Ψ := c • r
  have hD (ρ : CA → Γ) (hρ : ∀ u : CA, Quotient.mk _ (ρ u) = u)
      (z : ℂ) (hz : z ∈ LiZhongQC.lowerHalf) :
      LiZhongQC.bersDerivative (planeRepresentative νOriginal.val) z =
        (Complex.I / (2 * (Real.pi : ℂ))) *
          conj (GeodesicSeries.peterssonSeries Γ A hA ht ρ (conj z)) := by
    have he := (givenAngularInfinitesimal_originalGamma_bers_series
      Γ hΓ A hAΓ hA ht Q s hs hQA ν hν hsep).2 ρ hρ z hz
    rw [BersWeighted.fderiv_automorphicProjection hΓ] at he
    exact (BersWeighted.integralOperator_decode_eqOn νOriginal hz).symm.trans he
  have hΨ (ρ : CA → Γ) (hρ : ∀ u : CA, Quotient.mk _ (ρ u) = u)
      (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      QuadraticBergman.uniformizedQuadratic R p Ψ z =
        GeodesicSeries.peterssonSeries Γ A hA ht ρ z := by
    have hw : conj z ∈ LiZhongQC.lowerHalf := by
      change (conj z).im < 0
      rw [Complex.conj_im]
      exact neg_lt_zero.mpr hz
    have hlin : QuadraticBergman.uniformizedQuadratic R p Ψ z =
        c * QuadraticBergman.uniformizedQuadratic R p r z := by
      change WeilPetersson.liftQuadratic R.toRiemannAtlas p (c • r) ⟨z, hz⟩ =
        c * WeilPetersson.liftQuadratic R.toRiemannAtlas p r ⟨z, hz⟩
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    have hr : QuadraticBergman.uniformizedQuadratic R p r z =
        -2 * conj (LiZhongQC.bersDerivative (planeRepresentative νOriginal.val) (conj z)) :=
      NativePetersson.uniformized_rieszQuadratic_eq_bersDerivative R P p hp F hF νOriginal hz
    rw [hlin, hr, hD ρ hρ (conj z) hw]
    simp only [Complex.conj_conj, map_mul, map_div₀, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    dsimp only [c]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] ;
      ring_nf ; simp only [Complex.I_sq] ; ring
  have hH : NativePetersson.harmonicProjection R P p hp F hF νOriginal =
      a • NativeHarmonicBeltrami.ofQuadratic R p hp Ψ := by
    have hb : NativeHarmonicBeltrami.ofQuadratic R p hp r =
        NativePetersson.harmonicProjection R P p hp F hF νOriginal :=
      (NativePetersson.harmonicProjection_apply R P p hp F hF νOriginal).symm
    change NativePetersson.harmonicProjection R P p hp F hF νOriginal =
      a • NativeHarmonicBeltrami.ofQuadratic R p hp (c • r)
    rw [NativeHarmonicBeltrami.ofQuadratic_smul, hb, smul_smul]
    have hac : a * conj c = 1 := by
      dsimp only [a, c]
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] ;
        ring_nf ; simp only [Complex.I_sq] ; ring
    rw [hac, one_smul]
  have hN := NativePetersson.sub_harmonicProjection_mem_infinitesimal R P p hp F hF νOriginal
  rw [hH] at hN
  refine ⟨Ψ, ?_, hH, hN⟩
  intro ρ hρ z hz
  have hs := GeodesicSeries.geodesicSeries_hasSum_norm Γ hΓ A hAΓ hA ht ρ hρ z hz
  refine ⟨hΨ ρ hρ z hz, ?_, hs.2⟩
  simpa only [hΨ ρ hρ z hz, GeodesicSeries.peterssonSeries] using hs.1

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
