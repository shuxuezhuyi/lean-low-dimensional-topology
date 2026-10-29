module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalLengthCoefficientTangent
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBasePointIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHermitianCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicPeterssonSeries
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegionIntegral
public import LowDimensionalTopology.Unproved.Teichmuller.WolpertLengthDuality

/-!
# Original pointwise length duality from the same harmonic direction

The original compatible coefficient and its literal full-period quadratic
series give the contraction of the selected native WP form at the actual
identity marking. Every real tangent direction is an actual coefficient
projection derivative, so the scalar variation determines the full covector.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces

/-- The original harmonic twist formula has the full English contraction
factor in the literal Hermitian integral, for every compatible direction. -/
theorem harmonicTwist_fundamental_pairing
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (ν : GammaMeasurableBeltrami.Space Γ)
    (Ψ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hH : harmonicProjection R P p hp F hF ν =
      (-(Complex.I / (Real.pi : ℂ))) • NativeHarmonicBeltrami.ofQuadratic R p hp Ψ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    -2 * (WeilPetersson.beltramiPairing F
      (harmonicProjection R P p hp F hF ν).val
      (harmonicProjection R P p hp F hF μ).val).im =
        (2 / Real.pi) *
          (pairing R P p hp F hF μ ((toQuadratic R P p hp F hF).symm Ψ)).re := by
  let a : ℂ := -(Complex.I / (Real.pi : ℂ))
  let q := (toQuadratic R P p hp F hF).symm Ψ
  have hriesz : rieszQuadratic R P p hp F hF ν = conj a • q := by
    calc
      _ = rieszQuadratic R P p hp F hF (harmonicProjection R P p hp F hF ν) :=
        (rieszQuadratic_harmonicProjection R P p hp F hF ν).symm
      _ = _ := by rw [hH, rieszQuadratic_smul, rieszQuadratic_ofQuadratic]
  have hlinear : pairing R P p hp F hF μ (conj a • q) =
      conj a * pairing R P p hp F hF μ q := by
    exact (pairingLinear R P p hp F hF μ).map_smul (conj a) q
  have hright : WeilPetersson.beltramiPairing F
      (harmonicProjection R P p hp F hF μ).val
      (harmonicProjection R P p hp F hF ν).val =
        conj a * pairing R P p hp F hF μ q := by
    have h := (harmonicProjection_hermitian_compatibility R P p hp F hF μ ν).2.2.2
    rw [hriesz] at h
    exact h.trans hlinear
  have hpair : WeilPetersson.beltramiPairing F
      (harmonicProjection R P p hp F hF ν).val
      (harmonicProjection R P p hp F hF μ).val =
        a * conj (pairing R P p hp F hF μ q) := by
    calc
      _ = conj (WeilPetersson.beltramiPairing F
          (harmonicProjection R P p hp F hF μ).val
          (harmonicProjection R P p hp F hF ν).val) :=
        (WeilPetersson.beltramiPairing_conj F _ _).symm
      _ = _ := by rw [hright]; simp only [map_mul, Complex.conj_conj]
  rw [hpair]
  dsimp only [a]
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, zero_div, neg_zero, zero_mul, zero_add]
  ring

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "B" => Space Γ
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "b" => basePoint R
local notation "r" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus

/-- A genuine original coefficient direction whose harmonic representative is
the same endpoint series satisfies native length duality at the original base.
The supplied scalar regularity is the existing marked-length differential. -/
theorem originalCoefficientDirection_length_duality_at_basePoint
    (α : LiZhongQC.Loop X) (A : Deck) (hAΓ : A ∈ Γ)
    (hcov : LiZhongQC.Covers p A α)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hLength : letI := C; MDifferentiableAt RI 𝓘(ℝ) (lengthOf α) b)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (ν : B) (Ψ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hΨ :
      let CA := Quotient (QuotientGroup.rightRel
        (Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
          (Subgroup.zpowers (Hyperbolic.realSLMobius A))))
      ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
        ∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
          QuadraticBergman.uniformizedQuadratic R p Ψ z =
            GeodesicSeries.peterssonSeries Γ A hA ht ρ z)
    (hH : NativePetersson.harmonicProjection R P p hp F hF ν =
      (-(Complex.I / (Real.pi : ℂ))) • NativeHarmonicBeltrami.ofQuadratic R p hp Ψ) :
    letI := C
    Unproved.Teichmuller.WolpertLengthDualityAt R hp hg hgenus hΓ hfree hsmooth
      b α ((r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 ν)) := by
  let := C
  let CA := Quotient (QuotientGroup.rightRel
    (Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
      (Subgroup.zpowers (Hyperbolic.realSLMobius A))))
  let ρ : CA → Γ := fun u => Quotient.out u
  have hρ (u : CA) : Quotient.mk _ (ρ u) = u := Quotient.out_eq u
  let q := (NativePetersson.toQuadratic R P p hp F hF).symm Ψ
  let Θ : ℂ → ℂ := GeodesicSeries.peterssonSeries Γ A hA ht ρ
  have hFc : LiZhongQC.IsFundamentalDomainH Γ (Fuchsian.closedPlanarRegion F) :=
    Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF
  have hpair (μ : B) : NativePetersson.pairing R P p hp F hF μ q =
      LiZhongQC.beltramiPairing (Fuchsian.closedPlanarRegion F)
        (planeRepresentative μ.val) Θ := by
    rw [NativePetersson.pairing_eq_planar, LinearEquiv.apply_symm_apply]
    calc
      _ = ∫ z in Fuchsian.closedPlanarRegion F,
          planeRepresentative μ.val z * QuadraticBergman.uniformizedQuadratic R p Ψ z :=
        Fuchsian.integral_openPlanarRegion_eq_closedPlanarRegion hF.1 hF.2.2.2 _
      _ = _ := by
        apply setIntegral_congr_fun hFc.2.1
        intro z hz
        change planeRepresentative μ.val z * QuadraticBergman.uniformizedQuadratic R p Ψ z =
          planeRepresentative μ.val z * Θ z
        rw [hΨ ρ hρ z (hFc.1 hz)]
  intro z
  let K := canonicalDerivativeQuotientTangentEquiv R hg hgenus hP hΓ hfree hp hsmooth
  obtain ⟨qz, hqz⟩ := K.surjective (r b z)
  obtain ⟨μ, hμ⟩ := Submodule.Quotient.mk_surjective _ qz
  have hμz : mfderiv 𝓘(ℂ, B) TI β 0 μ = r b z := by
    rw [mfderiv_coefficientProjection_eq_quotient, hμ]
    exact hqz
  have hz : (r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 μ) = z := by
    rw [hμz, ContinuousLinearEquiv.symm_apply_apply]
  rw [← hz]
  change -2 * ((nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth b).inner
      (mfderiv 𝓘(ℂ, B) TI β 0 μ) (mfderiv 𝓘(ℂ, B) TI β 0 ν)).im = _
  have hcore := nativeWeilPeterssonCore_basePoint_integral R hp hg hgenus hΓ hfree hsmooth
    P F hF (mfderiv 𝓘(ℂ, B) TI β 0 ν) (mfderiv 𝓘(ℂ, B) TI β 0 μ)
  have hamb (ξ : B) :
      (baseTangentHarmonicEquiv R hg hgenus hΓ hfree hp hsmooth P F hF
        (mfderiv 𝓘(ℂ, B) TI β 0 ξ)).val.val =
      (NativePetersson.harmonicProjection R P p hp F hF ξ).val := by
    exact congrArg
      (fun η : NativePetersson.Harmonic R P p hp F hF => η.val.val)
      (baseTangentHarmonicEquiv_derivative R hg hgenus hΓ hfree hp hsmooth P F hF ξ)
  have hcore' := hcore.trans (congrArg₂
    (fun u v : Ambient => WeilPetersson.beltramiPairing F u v) (hamb ν) (hamb μ))
  refine (congrArg (fun w : ℂ => -2 * w.im) hcore').trans ?_
  exact (NativePetersson.harmonicTwist_fundamental_pairing R P p hp F hF ν Ψ hH μ).trans
    ((congrArg (fun w : ℂ => (2 / Real.pi) * w.re) (hpair μ)).trans
      (marked_length_mfderiv_coefficient_direction R hp hg hgenus hΓ hfree hsmooth
        α A hAΓ hcov hA ht hLength μ ρ hρ (Fuchsian.closedPlanarRegion F) hFc).symm)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
