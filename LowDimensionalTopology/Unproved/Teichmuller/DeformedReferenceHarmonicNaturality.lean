module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative

/-!
# The local harmonic differential law for an actual deformed reference

The reference map is the existing inverse-precomposition map for the actual
normalized marking R to Rν. This independent prerequisite only compares the
actual harmonic L-infinity classes under an actual real Mobius lift between
the two uniformizations of the same marked target. It contains no WP pairing,
metric, smoothness, invariant-form or closedness conclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller
open GammaMeasurableBeltrami NormalizedCoefficientTransport TeichmullerSpace

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree

/-- Near each actual centre, the genuine differential of the actual reference
change pulls harmonic coefficients back by the same real Mobius map that
identifies the actual target covers. The original coefficient ball and exact
translated coefficient are retained, as is the genuine preimage region. -/
def DeformedReferenceHarmonicNaturality : Prop :=
  letI := C
  ∀ ν : Ball Γ,
    let Y := deformedNativeSurface R hgenus hΓ hp ν
    let hY := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
    let hpY := deformedNativeSurface_uniformization R hgenus hΓ hp ν
    let _Δ := deformedGroup hΓ ν
    let hΔ := (deformedGroup_spec hΓ ν).1
    let hfY := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
    letI := canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth
    let βY := coefficientProjection Y hg hY hP hΔ hfY hpY
    let A := deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
    ∃ V : Set (TeichmullerSpace.{0,0} R), IsOpen V ∧ β ν.val ∈ V ∧
      ∀ (μ : Ball Γ), β μ.val ∈ V →
        ∀ (P : Geometry.Fuchsian.HalfPlaneFuchsianGroup
          ((deformedGroup hΓ μ).map Geometry.Hyperbolic.realSLMobius))
          (F : Set ℍ) (hF : Geometry.Fuchsian.IsHalfPlaneFundamentalRegion P F),
          let κ := translatedBall hΓ ν μ
          ∃ (M : Deck) (_hpoint : A (β μ.val) = βY κ.val)
            (P' : Geometry.Fuchsian.HalfPlaneFuchsianGroup
              ((deformedGroup hΔ κ).map Geometry.Hyperbolic.realSLMobius))
            (hF' : Geometry.Fuchsian.IsHalfPlaneFundamentalRegion P' ((fun z : ℍ => M • z) ⁻¹' F))
            (c : (deformedTargetSource Y hY hΔ hpY κ).carrier ≃ₜ
              (deformedTargetSource R hgenus hΓ hp μ).carrier),
            RiemannAnalyticMap (deformedNativeSurface Y hY hΔ hpY κ).toRiemannAtlas
              (deformedNativeSurface R hgenus hΓ hp μ).toRiemannAtlas c ∧
            (∀ z : ℍ, c (deformedTargetCover Y hY hΔ hpY κ z) =
              deformedTargetCover R hgenus hΓ hp μ (M • z)) ∧
            ∀ v : TangentSpace TI (β μ.val),
              (nonzeroTangentHarmonicEquiv Y hpY hg hY hΔ hfY κ P'
                ((fun z : ℍ => M • z) ⁻¹' F) hF' hsmooth
                  (tangentSpaceCast TI (A (β μ.val)) (βY κ.val)
                    (mfderiv TI TI A (β μ.val) v))).val.val =
                pullback M (TH μ P F hF hsmooth v).val.val

end LowDimensionalTopology.Unproved.Teichmuller
