module

public import LowDimensionalTopology.Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceHarmonicAmbient
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceGeometricWitness

/-! The complete original harmonic reference prerequisite, using its actual witnesses. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

/-- The actual full coefficient square, geometric witness and all-point
ambient harmonic law establish the unchanged concrete reference proposition. -/
theorem deformedReferenceHarmonicNaturality :
    LowDimensionalTopology.Unproved.Teichmuller.DeformedReferenceHarmonicNaturality
      R hp hg hgenus hΓ hfree hsmooth := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let β := coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp
  intro ν
  let Y := deformedNativeSurface R hgenus hΓ hp ν
  let hY := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
  let hpY := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  let hΔ := And.left (deformedGroup_spec hΓ ν)
  let hfY := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
  let := canonicalComplexChartedSpace Y hg hY (canonicalHandleGroupPresentation g)
    hΔ hfY hpY hsmooth
  let βY := coefficientProjection Y hg hY (canonicalHandleGroupPresentation g)
    hΔ hfY hpY
  let A := deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
  refine ⟨univ, isOpen_univ, mem_univ _, ?_⟩
  intro μ _ P F hF
  let κ := translatedBall hΓ ν μ
  have hpoint : A (β μ.val) = βY κ.val := by
    dsimp only [A, β, βY]
    rw [coefficientProjection_ball R hg hgenus hΓ hfree hp μ,
      coefficientProjection_ball Y hg hY hΔ hfY hpY κ]
    exact deformedReferenceChangeEquiv_coefficientProjection
      R hp hg hgenus hΓ hfree ν μ
  obtain ⟨P', hF', c, hc, hcover⟩ :=
    exists_deformedReferenceGeometricWitness R hp hgenus hΓ ν μ P F hF
  refine ⟨(1 : Deck), hpoint, P', hF', c, hc, hcover, ?_⟩
  intro v
  have h := deformedReferenceChangeEquiv_harmonic_ambient
    R hp hg hgenus hΓ hfree hsmooth ν μ P F hF P'
      ((fun z : ℍ => (1 : Deck) • z) ⁻¹' F) hF' v
  simpa only [GammaMeasurableBeltrami.pullback_one] using h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
