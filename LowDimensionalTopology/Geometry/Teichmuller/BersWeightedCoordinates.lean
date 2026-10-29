module

public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicTarget
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersCoordinates
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual weighted Bers functions in the existing linear coordinate chart

The existing coordinates use holomorphic automorphic functions with their
canonical zero extension. Every such function is bounded in the Bers norm for
the compact uniformized surface. This gives an exact linear equivalence with
the native weighted supremum realization, and hence a continuous equivalence
for its actual norm. The chosen coordinate map itself is unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped ENNReal UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

/-- Decode retains the actual source function as a complex-linear map. -/
def toSourceLinear (Γ : Subgroup GammaMeasurableBeltrami.Deck) :
    Automorphic Γ →ₗ[ℂ] LiZhongQC.automorphicQD Γ where
  toFun := Automorphic.toSource
  map_add' φ ψ := by
    apply Subtype.ext
    simpa only [Automorphic.toSource, Submodule.coe_add, decodeLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk] using
      map_add decodeLinearMap φ.val ψ.val
  map_smul' a φ := by
    apply Subtype.ext
    simpa only [Automorphic.toSource, Submodule.coe_smul, decodeLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply] using
      map_smul decodeLinearMap a φ.val

/-- Finite Bers norm gives the literal uniform square-height bound. -/
theorem weightedBound_of_finiteNorm {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (φ : LiZhongQC.automorphicQD Γ) (hφ : LiZhongQC.bersNormL (φ : ℂ → ℂ) < ⊤) :
    ∃ C : ℝ, ∀ z ∈ LiZhongQC.lowerHalf, ‖(φ : ℂ → ℂ) z‖ * z.im ^ 2 ≤ C := by
  refine ⟨(LiZhongQC.bersNormL (φ : ℂ → ℂ)).toReal, fun z hz => ?_⟩
  have hb : ENNReal.ofReal (‖(φ : ℂ → ℂ) z‖ * z.im ^ 2) ≤
      LiZhongQC.bersNormL (φ : ℂ → ℂ) :=
    le_iSup₂_of_le z hz le_rfl
  have hr := ENNReal.toReal_mono hφ.ne hb
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (sq_nonneg _))] using hr

/-- Exact equality of the actual function models whenever all source forms
have finite Bers norm. The compact-surface consumer proves this hypothesis. -/
def sourceEquivOfFiniteNorm (Γ : Subgroup GammaMeasurableBeltrami.Deck)
    (hfinite : ∀ φ : LiZhongQC.automorphicQD Γ,
      LiZhongQC.bersNormL (φ : ℂ → ℂ) < ⊤) :
    Automorphic Γ ≃ₗ[ℂ] LiZhongQC.automorphicQD Γ :=
  LinearEquiv.ofBijective (toSourceLinear Γ)
    ⟨Automorphic.toSource_injective, fun φ =>
      ⟨Automorphic.ofSource φ (weightedBound_of_finiteNorm φ (hfinite φ)),
        Automorphic.toSource_ofSource φ _⟩⟩

@[simp] theorem sourceEquivOfFiniteNorm_apply
    (Γ : Subgroup GammaMeasurableBeltrami.Deck)
    (hfinite : ∀ φ : LiZhongQC.automorphicQD Γ,
      LiZhongQC.bersNormL (φ : ℂ → ℂ) < ⊤) (φ : Automorphic Γ) :
    sourceEquivOfFiniteNorm Γ hfinite φ = φ.toSource := rfl

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- The existing chosen linear coordinate map on the faithful weighted model. -/
def weightedLinearBersEquiv :
    BersWeighted.Automorphic Γ ≃ₗ[ℂ] (Fin (3 * g - 3) → ℂ) :=
  (BersWeighted.sourceEquivOfFiniteNorm Γ
    (linearBersCoordinates_spec R hg hgenus hPresentation hΓ hp).1).trans
      (linearBersCoordinates R hg hgenus hPresentation hΓ hp).toLinearEquiv

/-- Continuity is for the literal weighted supremum norm, proved by actual
finite dimensionality of this same vector space. -/
def weightedLinearBersCoordinates :
    BersWeighted.Automorphic Γ ≃L[ℂ] (Fin (3 * g - 3) → ℂ) := by
  let e := weightedLinearBersEquiv R hg hgenus hPresentation hΓ hp
  letI : FiniteDimensional ℂ (BersWeighted.Automorphic Γ) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact e.toContinuousLinearEquiv

/-- The source function and the original coordinate values are retained literally. -/
@[simp] theorem weightedLinearBersCoordinates_apply (φ : BersWeighted.Automorphic Γ) :
    weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp φ =
      linearBersCoordinates R hg hgenus hPresentation hΓ hp φ.toSource := rfl

/-- Inverting these coordinates recovers the actual original automorphic function. -/
theorem weightedLinearBersCoordinates_symm_toSource (v : Fin (3 * g - 3) → ℂ) :
    ((weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp).symm v).toSource =
      (linearBersCoordinates R hg hgenus hPresentation hΓ hp).symm v := by
  apply (linearBersCoordinates R hg hgenus hPresentation hΓ hp).injective
  rw [← weightedLinearBersCoordinates_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
