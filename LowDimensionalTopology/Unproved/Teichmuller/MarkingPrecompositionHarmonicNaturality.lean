module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonCore
public import LowDimensionalTopology.Geometry.Teichmuller.QCModularGammaAction

/-!
# Harmonic representatives under the original change of marking

The target of `SourceReferenceChange.marked` is definitionally unchanged.
What is not yet connected to that observation is the differential of the
actual Bers-holomorphic change of marking. This concrete obligation states
its harmonic-coefficient law under the genuine real Möbius lift between the
two normalized target uniformizations. It contains no WP pairing or metric.

The downstream invariant-form consumers use this bridge together with the
proved real-Möbius change of variables for the literal Petersson integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open LowDimensionalTopology.Geometry
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open GammaMeasurableBeltrami NormalizedCoefficientTransport TeichmullerSpace
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

local notation "TI" => 𝓘(ℂ, Fin (3*g-3) → ℂ)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "T" => gammaWeilPeterssonTangentHarmonicEquiv R hp hg hgenus hΓ hsmooth
local notation "Y" => deformedNativeSurface R hgenus hΓ hp
local notation "q" => deformedTargetCover R hgenus hΓ hp

/-- Inverse precomposition of the marking acts on actual harmonic tangent
coefficients by the real Möbius lift of the same marked-target identification.
The integration region is the genuine preimage region for that same lift. -/
def MarkingPrecompositionHarmonicNaturality : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  letI := C
  letI := mΓ
  letI := CG
  ∀ (f : SourceQCModular.Aut X) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F),
    let A := referenceGammaEquiv R R hg hgenus hgenus f.val f.property hΓ hΓ hp hp
    ∃ (ν' : Ball Γ) (M : Deck)
      (_hpoint : A (D (β ν.val)) = D (β ν'.val))
      (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν').map Hyperbolic.realSLMobius))
      (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' ((fun z : ℍ => M • z) ⁻¹' F))
      (c : (deformedTargetSource R hgenus hΓ hp ν').carrier ≃ₜ
        (deformedTargetSource R hgenus hΓ hp ν).carrier),
      RiemannAnalyticMap (Y ν').toRiemannAtlas (Y ν).toRiemannAtlas c ∧
      (∀ z : ℍ, c (q ν' z) = q ν (M • z)) ∧
      ∀ v : TangentSpace TI (D (β ν.val)),
        (T ν' P' ((fun z : ℍ => M • z) ⁻¹' F) hF'
          (tangentSpaceCast TI (A (D (β ν.val))) (D (β ν'.val))
            (mfderiv TI TI A (D (β ν.val)) v))).val.val =
          pullback M (T ν P F hF v).val.val

end LowDimensionalTopology.Unproved.Teichmuller
