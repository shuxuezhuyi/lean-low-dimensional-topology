module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistPeterssonSeriesReflection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicDecomposition
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistActualBersSeries

/-!
# The harmonic series of one given angular infinitesimal

The supplied whole coefficient, angular support and original covering remain
fixed. Its actual reflected Bers derivative determines the same global
quadratic differential and its harmonic representative. No covering matrix,
normalizer or new coefficient is chosen in this calculation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open LowDimensionalTopology.Geometry.Surfaces

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ
local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The given entire angular direction has its precise harmonic representative
and the same convergent Petersson series for every actual coset section. -/
theorem givenAngularInfinitesimal_exists_harmonic_series
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v)
    (ν : GammaMeasurableBeltrami.Space Γ)
    (hν : (ν.val : ℍ → ℂ) =ᵐ[volume]
      (fun z : ℍ => rightCosetInfinitesimalSum θ Γ s (z : ℂ)))
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let m : Γ → ℂ → ℂ := fun γ =>
      LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
    ∃ Θ : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      (∀ ρ : C → Γ, (∀ u : C, Quotient.mk _ (ρ u) = u) →
        (∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
          HasSum (fun u : C => (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
            (QuadraticBergman.uniformizedQuadratic R p Θ z) ∧
          Summable (fun u : C => ‖(deriv (m (ρ u)) z / m (ρ u) z) ^ 2‖)) ∧
        TendstoLocallyUniformlyOn
          (fun (E : Finset C) (z : ℂ) =>
            ∑ u ∈ E, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
          (QuadraticBergman.uniformizedQuadratic R p Θ)
          (atTop : Filter (Finset C)) LiZhongQC.upperHalf) ∧
      NativePetersson.harmonicProjection R P p hp F hF ν =
        (-(Complex.I / (Real.pi : ℂ))) •
          NativeHarmonicBeltrami.ofQuadratic R p hp Θ ∧
      ν - (-(Complex.I / (Real.pi : ℂ))) •
          NativeHarmonicBeltrami.ofQuadratic R p hp Θ ∈
        NativePetersson.infinitesimalSubmodule Γ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let m : Γ → ℂ → ℂ := fun γ =>
    LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
  let hΓ : LiZhongQC.IsFuchsian Γ := LiZhongQC.utm_x_isFuchsian hp
  have hconverges := rightCosetPeterssonSeries_upperHalf θ Γ s hsep
  let r := NativePetersson.toQuadratic R P p hp F hF
    (NativePetersson.rieszQuadratic R P p hp F hF ν)
  let c : ℂ := -Complex.I * (Real.pi : ℂ)
  let a : ℂ := -(Complex.I / (Real.pi : ℂ))
  let Θ := c • r
  have hD (ρ : C → Γ) (hρ : ∀ u : C, Quotient.mk _ (ρ u) = u)
      (z : ℂ) (hz : z ∈ LiZhongQC.lowerHalf) :
      LiZhongQC.bersDerivative (GammaMeasurableBeltrami.planeRepresentative ν.val) z =
        (Complex.I / (2 * (Real.pi : ℂ))) *
          conj (∑' u : C, (deriv (m (ρ u)) (conj z) / m (ρ u) (conj z)) ^ 2) := by
    have he := rightCosetInfinitesimalSum_fderiv_bers θ Γ s hΓ hsep ν hν hz
    rw [BersWeighted.fderiv_automorphicProjection hΓ] at he
    have hz' : conj z ∈ LiZhongQC.upperHalf := by
      change 0 < (conj z).im
      rw [Complex.conj_im]
      exact neg_pos.mpr hz
    calc
      _ = iteratedDeriv 3 (LiZhongQC.ahVar (rightCosetInfinitesimalSum θ Γ s)) z :=
        (BersWeighted.integralOperator_decode_eqOn ν hz).symm.trans he
      _ = (Complex.I / (2 * (Real.pi : ℂ))) *
          ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2 :=
        (((rightCosetCauchySeries_thirdDerivative θ Γ s hsep).2 ρ hρ).2 z hz).2
      _ = _ := by
        congr 1
        rw [Complex.conj_tsum]
        apply tsum_congr
        intro u
        simpa only [Complex.conj_conj] using
          (squaredLogDeriv_mobius_conj (ρ u).val hz')
  have hΘ (ρ : C → Γ) (hρ : ∀ u : C, Quotient.mk _ (ρ u) = u)
      (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      QuadraticBergman.uniformizedQuadratic R p Θ z =
        ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2 := by
    have hw : conj z ∈ LiZhongQC.lowerHalf := by
      change (conj z).im < 0
      rw [Complex.conj_im]
      exact neg_lt_zero.mpr hz
    have hlin : QuadraticBergman.uniformizedQuadratic R p Θ z =
        c * QuadraticBergman.uniformizedQuadratic R p r z := by
      change WeilPetersson.liftQuadratic R.toRiemannAtlas p (c • r) ⟨z, hz⟩ =
        c * WeilPetersson.liftQuadratic R.toRiemannAtlas p r ⟨z, hz⟩
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    have hr : QuadraticBergman.uniformizedQuadratic R p r z =
        -2 * conj (LiZhongQC.bersDerivative
          (GammaMeasurableBeltrami.planeRepresentative ν.val) (conj z)) :=
      NativePetersson.uniformized_rieszQuadratic_eq_bersDerivative R P p hp F hF ν hz
    rw [hlin, hr, hD ρ hρ (conj z) hw]
    simp only [Complex.conj_conj, map_mul, map_div₀, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    dsimp only [c]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] ;
      ring_nf ; simp only [Complex.I_sq] ; ring
  have hH : NativePetersson.harmonicProjection R P p hp F hF ν =
      a • NativeHarmonicBeltrami.ofQuadratic R p hp Θ := by
    have hb : NativeHarmonicBeltrami.ofQuadratic R p hp r =
        NativePetersson.harmonicProjection R P p hp F hF ν :=
      (NativePetersson.harmonicProjection_apply R P p hp F hF ν).symm
    change NativePetersson.harmonicProjection R P p hp F hF ν =
      a • NativeHarmonicBeltrami.ofQuadratic R p hp (c • r)
    rw [NativeHarmonicBeltrami.ofQuadratic_smul, hb, smul_smul]
    have hac : a * conj c = 1 := by
      dsimp only [a, c]
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] ;
        ring_nf ; simp only [Complex.I_sq] ; ring
    rw [hac, one_smul]
  have hN := NativePetersson.sub_harmonicProjection_mem_infinitesimal R P p hp F hF ν
  rw [hH] at hN
  refine ⟨Θ, ?_, hH, hN⟩
  intro ρ hρ
  obtain ⟨hpoint, hlocal⟩ := hconverges ρ hρ
  refine ⟨?_, hlocal.congr_right ?_⟩
  · intro z hz
    have hs := (hpoint z hz).1
    rw [← hΘ ρ hρ z hz] at hs
    exact ⟨hs, (hpoint z hz).2⟩
  · intro z hz
    exact (hΘ ρ hρ z hz).symm

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
