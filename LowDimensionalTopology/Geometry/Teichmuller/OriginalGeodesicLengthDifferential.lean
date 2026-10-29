module

public import LowDimensionalTopology.Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLengthAnalytic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The native real-analytic marked-length differential

The scalar Fricke germ and the forward coordinate compatibility give native
real-analytic marked length. Its real covector is the literal differential;
the differential coefficients in the actual tangent charts are analytic.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff Bundle

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation TeichmullerSpace

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
variable (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
variable (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, Fin (6 * g - 6) → ℝ)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth

/-- The real differential of the same original marked geodesic length. -/
def originalClosedGeodesic_nativeLengthDifferential
    {M : HyperbolicSurfaceModel R.toRiemannSurface} (q : OriginalClosedGeodesic M) :
    letI := C
    ∀ a : T, TangentSpace RI a →L[ℝ] ℝ :=
  letI := C
  mvfderiv RI (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop)

/-- The same scalar length is real analytic and genuinely differentiable
at every native point. Its cotangent-coordinate coefficients are analytic,
and its named real covector is the actual differential everywhere. -/
theorem originalClosedGeodesic_nativeLength_realAnalytic_differential
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (hFrickeBers : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      R hg hgenus hΓ hfree hp hsmooth hA)
    {M : HyperbolicSurfaceModel R.toRiemannSurface} (q : OriginalClosedGeodesic M) :
    letI := C
    letI : IsManifold RI ω T :=
      (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth).isManifold_singleton
    let L : T → ℝ :=
      markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop
    let dL := originalClosedGeodesic_nativeLengthDifferential
      R hg hgenus hΓ hfree hp hsmooth q
    ContMDiff RI 𝓘(ℝ, ℝ) ω L ∧
      (∀ a : T, MDifferentiableAt RI 𝓘(ℝ, ℝ) L a) ∧
      (∀ a : T,
        ContMDiffAt RI 𝓘(ℝ, E →L[ℝ] ℝ) ω
          (inTangentCoordinates RI 𝓘(ℝ, ℝ) id L
            (mfderiv RI 𝓘(ℝ, ℝ) L) a) a) ∧
      ∀ a : T, dL a = mvfderiv RI L a := by
  let := R.compactSpace
  let := C
  let : IsManifold RI ω T :=
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth).isManifold_singleton
  let L : T → ℝ :=
    markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop
  have hFC : ContMDiff RI FI ω (finiteFrickeCoordinates hA) := hFrickeBers
  have hvalue (a : T) :
      frickeGeodesicLength R hg hgenus hA hAlt q.toLoop
        ⟨finiteFrickeCoordinates hA a, ⟨a, rfl⟩⟩ = L a := by
    refine Quotient.inductionOn a ?_
    intro m
    exact frickeGeodesicLength_coordinates R hg hgenus hA hAlt q.toLoop m
  have hL : ContMDiff RI 𝓘(ℝ, ℝ) ω L := by
    intro a
    let v : nativeFrickeImage hA := ⟨finiteFrickeCoordinates hA a, ⟨a, rfl⟩⟩
    obtain ⟨F, hF, W, hW, hEq⟩ := frickeGeodesicLength_exists_analytic_germ
      R hg hgenus hA hAlt q.toLoop q.not_isNullHomotopicLoop v
    have hFreg : ContMDiffAt FI 𝓘(ℝ, ℝ) ω F (finiteFrickeCoordinates hA a) :=
      hF.contDiffAt.contMDiffAt
    apply (hFreg.comp a (hFC a)).congr_of_eventuallyEq
    have hnear : ∀ᶠ b in 𝓝 a, finiteFrickeCoordinates hA b ∈ W :=
      hFC.continuous.continuousAt.preimage_mem_nhds hW
    filter_upwards [hnear] with b hb
    exact ((hEq ⟨finiteFrickeCoordinates hA b, ⟨b, rfl⟩⟩ hb).trans (hvalue b)).symm
  refine ⟨hL, ?_, ?_, ?_⟩
  · intro a
    exact (hL a).mdifferentiableAt (by simp)
  · intro a
    exact (hL a).mfderiv_const (m := ω) (by simp)
  · intro a
    rfl

end LowDimensionalTopology.Geometry.Teichmuller
