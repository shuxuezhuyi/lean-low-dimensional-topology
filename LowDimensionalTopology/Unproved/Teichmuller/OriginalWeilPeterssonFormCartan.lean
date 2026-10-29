module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWeilPeterssonFormLieDerivative
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Classical identities for the original WP form along a given actual flow

Cartan's identity and the vector-field evaluation identity use the existing
pullback-time Lie derivative. They supply neither Hamiltonian length duality,
closedness, a zero Lie derivative nor a generated FN field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

local notation "T" => Geometry.Teichmuller.TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "ωWP" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "Along" => nativeWeilPeterssonFormLieDerivativeAlong
  R hp hg hgenus hΓ hfree hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

/-- Cartan and evaluation for this original smooth WP form and this given
local flow, before any Hamiltonian, closedness or invariance assertion. -/
def OriginalWeilPeterssonFormCartanAlong
    (_hWP : WeilPeterssonLocalCoefficientSmoothness R hp hg hgenus hΓ hfree hsmooth)
    (V : TopologicalSpace.Opens T) (ε : ℝ) (hε : 0 < ε) (Φ : ℝ → T → T) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    (W Y Z : FormInterior.SmoothVectorField RI (M := T)) →
    (hzero : ∀ r ∈ V, Φ 0 r = r) →
    (hflow : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
      ∀ r ∈ V, s+t ∈ Ioo (-ε) ε → Φ t r ∈ V → Φ (s+t) r = Φ s (Φ t r)) →
    (hΦ : ContMDiffOn (𝓘(ℝ).prod RI) RI ∞
      (fun z : ℝ × T => Φ z.1 z.2) (Ioo (-ε) ε ×ˢ (V : Set T))) →
    (hgen : ∀ t ∈ Ioo (-ε) ε, ∀ r ∈ V,
      mfderiv 𝓘(ℝ) RI (fun s : ℝ => Φ s r) t
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) = W (Φ t r)) → Prop := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W Y Z hzero hflow hΦ hgen
  let Lie := fun (q : T) (hq : q ∈ V) =>
    Along q V hq ε hε Φ W hzero hflow hΦ hgen
  let ξ := fun z : E => D ((c).symm z) (W ((c).symm z))
  let η := fun z : E => (Ω z).curryLeft (ξ z)
  exact
    (∀ (q : T) (hq : q ∈ V) (a b : TangentSpace RI q),
      Lie q hq ![a,b] =
        extDerivWithin η (c).target (c q) ![D q a,D q b] +
        extDerivWithin Ω (c).target (c q) ![D q (W q),D q a,D q b]) ∧
    (∀ (q : T) (hq : q ∈ V),
      Lie q hq ![Y q,Z q] =
        mvfderiv RI (fun r => ωWP r ![Y r,Z r]) q (W q) -
          ωWP q ![VectorField.mlieBracket RI W Y q,Z q] -
          ωWP q ![Y q,VectorField.mlieBracket RI W Z q])

end LowDimensionalTopology.Unproved.Teichmuller
