module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonDiagonalFundamentalIntegrability
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonDiagonalDomainExchange
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonDiagonalComposition

/-!
# The diagonal mixed-kernel trace for the actual original harmonic functions

The original coefficient classes agree with the literal harmonic functions
only almost everywhere. The proved product estimates transfer through that
equality. Genuine absolute integrability then justifies each Fubini step,
the same-domain exchange, and the two ordinary computed integrals. The
result is the original first-linear Petersson pairing with its exact scalar.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces GammaMeasurableBeltrami QuadraticBergman

local notation "Q" => ℍ × (ℍ × ℍ)
local notation "λQ" => flatArea.prod (flatArea.prod flatArea)

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (p : ℍ → X) {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

include hp in
private theorem harmonicMixed_integrands_ae
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∀ᵐ a : ℍ × ℍ ∂(flatArea.prod flatArea), ∀ ζ z : ℍ,
      sesquilinearIntegrand (fun η => NativeHarmonicBeltrami.ambient R p hp q η)
        (fun ξ => NativeHarmonicBeltrami.ambient R p hp r ξ) ζ z a.1 a.2 =
      sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) ζ z a.1 a.2 := by
  have hq := ae_hyperbolic_iff.mp (NativeHarmonicBeltrami.ambient_coe_ae R p hp q)
  have hr := ae_hyperbolic_iff.mp (NativeHarmonicBeltrami.ambient_coe_ae R p hp r)
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := flatArea) (ν := flatArea)).ae hq,
    (Measure.quasiMeasurePreserving_fst (μ := flatArea) (ν := flatArea)).ae hr]
    with a hqa hra
  intro ζ z
  simp only [sesquilinearIntegrand, hqa, hra]

include hp in
private theorem harmonicMixed_joint_integrable
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ζ z : ℍ) :
    Integrable (fun a : ℍ × ℍ => sesquilinearIntegrand
      (NativeHarmonicBeltrami.coefficient R p q) (NativeHarmonicBeltrami.coefficient R p r)
        ζ z a.1 a.2) (flatArea.prod flatArea) :=
  (sesquilinear_joint_integrable (NativeHarmonicBeltrami.ambient R p hp q)
    (NativeHarmonicBeltrami.ambient R p hp r) ζ z).congr
      ((harmonicMixed_integrands_ae R p hp q r).mono fun _a ha => ha ζ z)

variable (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include hp hF in
/-- The actual diagonal trace equals the same original first-linear
Petersson pairing, with the full negative squared-pi-over-twelve factor. -/
theorem harmonic_sesquilinear_diagonal_trace
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    (∫ ζ in F, sesquilinear (NativeHarmonicBeltrami.coefficient R p q)
      (NativeHarmonicBeltrami.coefficient R p r) ζ ζ ∂flatArea) =
      (-(Real.pi ^ 2 / 12) : ℂ) * WeilPetersson.beltramiPairing F
        (NativeHarmonicBeltrami.coefficient R p q) (NativeHarmonicBeltrami.coefficient R p r) := by
  let f : Q → ℂ := fun w => sesquilinearIntegrand
    (NativeHarmonicBeltrami.coefficient R p q) (NativeHarmonicBeltrami.coefficient R p r)
      w.1 w.1 w.2.1 w.2.2
  have hfirst : Integrable f ((flatArea.restrict F).prod (flatArea.prod flatArea)) := by
    apply (sesquilinear_diagonal_joint_integrable R hp P F hF
      (NativeHarmonicBeltrami.ambient R p hp q)
      (NativeHarmonicBeltrami.ambient R p hp r)).congr
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := flatArea.restrict F) (ν := flatArea.prod flatArea)).ae
        (harmonicMixed_integrands_ae R p hp q r)] with w hw
    exact hw w.1 w.1
  have hfirstMeasure : λQ.restrict {w : Q | w.1 ∈ F} =
      (flatArea.restrict F).prod (flatArea.prod flatArea) := by
    have he : {w : Q | w.1 ∈ F} = F ×ˢ (univ : Set (ℍ × ℍ)) := by ext w; simp
    rw [he, ← Measure.prod_restrict, Measure.restrict_univ]
  have hlastMeasure : λQ.restrict {w : Q | w.2.2 ∈ F} =
      flatArea.prod (flatArea.prod (flatArea.restrict F)) := by
    have he : {w : Q | w.2.2 ∈ F} = (univ : Set ℍ) ×ˢ ((univ : Set ℍ) ×ˢ F) := by ext w; simp
    rw [he, ← Measure.prod_restrict, Measure.restrict_univ,
      ← Measure.prod_restrict, Measure.restrict_univ]
  have hfirstSet : IntegrableOn f {w : Q | w.1 ∈ F} λQ := by
    change Integrable f (λQ.restrict {w : Q | w.1 ∈ F})
    rw [hfirstMeasure]
    exact hfirst
  have hexchange := harmonic_diagonal_domain_exchange R p hp P F hF q r
  have hlastSet := hexchange.1.mp hfirstSet
  have hlast : Integrable f (flatArea.prod (flatArea.prod (flatArea.restrict F))) := by
    change Integrable f (λQ.restrict {w : Q | w.2.2 ∈ F}) at hlastSet
    rwa [hlastMeasure] at hlastSet
  calc
    _ = ∫ ζ in F, ∫ a : ℍ × ℍ, f (ζ, a) ∂(flatArea.prod flatArea) ∂flatArea := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ζ => (integral_prod _
        (harmonicMixed_joint_integrable R p hp q r ζ ζ)).symm
    _ = ∫ w in {w : Q | w.1 ∈ F}, f w ∂λQ := by
      rw [hfirstMeasure]
      exact (integral_prod f hfirst).symm
    _ = ∫ w in {w : Q | w.2.2 ∈ F}, f w ∂λQ := hexchange.2
    _ = ∫ η in F, ∫ ξ : ℍ, ∫ ζ : ℍ, f (ζ, (ξ, η)) ∂flatArea ∂flatArea ∂flatArea := by
      rw [hlastMeasure, integral_prod_symm f hlast]
      exact integral_prod_symm (fun a : ℍ × ℍ => ∫ ζ : ℍ, f (ζ, a) ∂flatArea)
        hlast.integral_prod_right
    _ = ∫ η in F, (-(Real.pi ^ 2 / 12) : ℂ) * NativeHarmonicBeltrami.coefficient R p q η *
        uniformizedQuadratic R p r (η : ℂ) ∂flatArea := by
      apply integral_congr_ae
      exact Eventually.of_forall fun η => (harmonic_diagonal_composed_integral R p hp q r η).2
    _ = (-(Real.pi ^ 2 / 12) : ℂ) *
        ∫ η in F, NativeHarmonicBeltrami.coefficient R p q η *
          uniformizedQuadratic R p r (η : ℂ) ∂flatArea := by
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    _ = _ := by
      congr 1
      unfold WeilPetersson.beltramiPairing WeilPetersson.weightedPairing
      apply integral_congr_ae
      exact Eventually.of_forall fun η => by
        dsimp only
        rw [NativeHarmonicBeltrami.coefficient_eq_uniformized R p r η]
        simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj,
          Complex.ofReal_inv, Complex.ofReal_pow]
        field_simp [η.im_ne_zero]

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
