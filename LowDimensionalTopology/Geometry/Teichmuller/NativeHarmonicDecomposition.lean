module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicProjection
public import LowDimensionalTopology.Geometry.Teichmuller.BersDerivativeQuotient
public import Mathlib.LinearAlgebra.Projection

/-!
# The actual harmonic complement of infinitesimally trivial coefficients

The harmonic subspace is the image of the literal bounded harmonic projection,
with its inherited original L-infinity norm. Idempotence gives the direct sum;
the actual Bers integral restricts to a continuous linear equivalence onto the
original weighted automorphic target. The planar pairing is unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

local notation "B" => GammaMeasurableBeltrami.Space Γ
local notation "H" => harmonicProjection R P p hp F hF

/-- Harmonic classes are exactly the image of the actual harmonic projection. -/
def harmonicSubmodule : Submodule ℂ B := (H).toLinearMap.range

abbrev Harmonic := ↥(harmonicSubmodule R P p hp F hF)

/-- A class is harmonic precisely when the literal harmonic projection fixes it. -/
theorem mem_harmonicSubmodule_iff (μ : B) :
    μ ∈ harmonicSubmodule R P p hp F hF ↔ H μ = μ := by
  constructor
  · rintro ⟨ν, rfl⟩
    exact harmonicProjection_idempotent R P p hp F hF ν
  · intro hμ
    exact ⟨μ, hμ⟩

/-- Harmonic classes are exactly the literal harmonic coefficients of all original
holomorphic quadratic differentials. -/
theorem mem_harmonicSubmodule_iff_exists_quadratic (μ : B) :
    μ ∈ harmonicSubmodule R P p hp F hF ↔
      ∃ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        NativeHarmonicBeltrami.ofQuadratic R p hp q = μ := by
  constructor
  · intro hμ
    refine ⟨toQuadratic R P p hp F hF (rieszQuadratic R P p hp F hF μ), ?_⟩
    exact (harmonicProjection_apply R P p hp F hF μ).symm.trans
      ((mem_harmonicSubmodule_iff R P p hp F hF μ).mp hμ)
  · rintro ⟨q, rfl⟩
    exact (mem_harmonicSubmodule_iff R P p hp F hF _).mpr
      (harmonicProjection_fixes_ofQuadratic R P p hp F hF q)

/-- The actual bounded projection is a projection in Mathlib's precise sense. -/
theorem harmonicProjection_isProj :
    LinearMap.IsProj (harmonicSubmodule R P p hp F hF) (H).toLinearMap where
  map_mem μ := ⟨μ, rfl⟩
  map_id μ hμ := (mem_harmonicSubmodule_iff R P p hp F hF μ).mp hμ

/-- The full harmonic space and the genuine Bers derivative kernel are complements. -/
theorem harmonic_infinitesimal_isCompl :
    IsCompl (harmonicSubmodule R P p hp F hF) (infinitesimalSubmodule Γ) := by
  have h := (harmonicProjection_isProj R P p hp F hF).isCompl
  change IsCompl (harmonicSubmodule R P p hp F hF) (H).ker at h
  rwa [harmonicProjection_ker R P p hp F hF] at h

/-- Subtracting the literal harmonic part gives an actual infinitesimal coefficient. -/
theorem sub_harmonicProjection_mem_infinitesimal (μ : B) :
    μ - H μ ∈ infinitesimalSubmodule Γ := by
  rw [← harmonicProjection_ker R P p hp F hF]
  change H (μ - H μ) = 0
  rw [map_sub, harmonicProjection_idempotent, sub_self]

/-- Every actual coefficient has its explicit harmonic-plus-infinitesimal decomposition. -/
theorem eq_harmonic_add_infinitesimal (μ : B) :
    ∃ (h : Harmonic R P p hp F hF) (n : infinitesimalSubmodule Γ),
      h.val + n.val = μ := by
  exact ⟨⟨H μ, ⟨μ, rfl⟩⟩,
    ⟨μ - H μ, sub_harmonicProjection_mem_infinitesimal R P p hp F hF μ⟩,
    by rw [add_comm, sub_add_cancel]⟩

/-- The harmonic subspace is closed in the original coefficient Banach space. -/
theorem harmonicSubmodule_isClosed :
    IsClosed (harmonicSubmodule R P p hp F hF : Set B) := by
  have he : (harmonicSubmodule R P p hp F hF : Set B) = {μ : B | H μ = μ} :=
    Set.ext fun μ => mem_harmonicSubmodule_iff R P p hp F hF μ
  rw [he]
  exact isClosed_eq (H).continuous continuous_id

/-- Completeness is inherited from the genuine L-infinity norm. -/
theorem harmonic_completeSpace : CompleteSpace (Harmonic R P p hp F hF) :=
  (harmonicSubmodule_isClosed R P p hp F hF).isComplete.completeSpace_coe

/-- The book's unchanged planar pairing agrees with that of the literal harmonic part. -/
theorem planar_pairing_harmonicProjection (μ : B)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    (∫ z in UpperHalfPlane.coe '' F,
      GammaMeasurableBeltrami.planeRepresentative μ.val z *
        QuadraticBergman.uniformizedQuadratic R p q z) =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative (H μ).val z *
          QuadraticBergman.uniformizedQuadratic R p q z := by
  have he := congrArg
    (fun f : StrongDual ℂ (Space R P p hp F hF) =>
      f ((toQuadratic R P p hp F hF).symm q))
    (pairingMap_harmonicProjection R P p hp F hF μ)
  simpa only [pairingMap_apply, pairing_eq_planar,
    LinearEquiv.apply_symm_apply] using he.symm

/-- Restrict the actual Bers derivative to its literal harmonic directions. -/
def harmonicDerivative (hΓ : LiZhongQC.IsFuchsian Γ) :
    Harmonic R P p hp F hF →L[ℂ] BersWeighted.Automorphic Γ :=
  (BersWeighted.automorphicIntegralOperator hΓ).comp
    (harmonicSubmodule R P p hp F hF).subtypeL

@[simp] theorem harmonicDerivative_apply (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : Harmonic R P p hp F hF) :
    harmonicDerivative R P p hp F hF hΓ μ =
      BersWeighted.automorphicIntegralOperator hΓ μ.val := by
  simp only [harmonicDerivative, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-- The actual derivative loses no harmonic direction. -/
theorem harmonicDerivative_injective (hΓ : LiZhongQC.IsFuchsian Γ) :
    Function.Injective (harmonicDerivative R P p hp F hF hΓ) := by
  intro μ ν he
  apply Subtype.ext
  have hval := congrArg Subtype.val he
  simp only [harmonicDerivative_apply, BersWeighted.automorphicIntegralOperator_val] at hval
  have hn : μ.val - ν.val ∈ infinitesimalSubmodule Γ := by
    change BersWeighted.integralOperator Γ (μ.val - ν.val) = 0
    rw [map_sub, hval, sub_self]
  have hh : H (μ.val - ν.val) = 0 := by
    change μ.val - ν.val ∈ (H).ker
    rw [harmonicProjection_ker R P p hp F hF]
    exact hn
  rw [map_sub,
    (mem_harmonicSubmodule_iff R P p hp F hF μ.val).mp μ.property,
    (mem_harmonicSubmodule_iff R P p hp F hF ν.val).mp ν.property] at hh
  exact sub_eq_zero.mp hh

/-- Every actual weighted automorphic differential has a genuine harmonic preimage. -/
theorem harmonicDerivative_surjective (hΓ : LiZhongQC.IsFuchsian Γ) :
    Function.Surjective (harmonicDerivative R P p hp F hF hΓ) := by
  intro φ
  obtain ⟨μ, hμ⟩ := BersWeighted.automorphicIntegralOperator_surjective R p hp hΓ φ
  refine ⟨⟨H μ, ⟨μ, rfl⟩⟩, ?_⟩
  rw [harmonicDerivative_apply, ← hμ]
  apply Subtype.ext
  simpa only [BersWeighted.automorphicIntegralOperator_val] using
    harmonicProjection_bers R P p hp F hF μ

/-- The derivative induces the actual harmonic-to-Bers isomorphism in the original norms. -/
def harmonicDerivativeEquiv (hΓ : LiZhongQC.IsFuchsian Γ) :
    Harmonic R P p hp F hF ≃L[ℂ] BersWeighted.Automorphic Γ := by
  letI : CompleteSpace (Harmonic R P p hp F hF) :=
    harmonic_completeSpace R P p hp F hF
  letI : CompleteSpace (BersWeighted.Automorphic Γ) :=
    BersWeighted.automorphic_completeSpace Γ
  exact ContinuousLinearEquiv.ofBijective (harmonicDerivative R P p hp F hF hΓ)
    (LinearMap.ker_eq_bot.mpr (harmonicDerivative_injective R P p hp F hF hΓ))
    (LinearMap.range_eq_top.mpr (harmonicDerivative_surjective R P p hp F hF hΓ))

@[simp] theorem harmonicDerivativeEquiv_apply (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : Harmonic R P p hp F hF) :
    harmonicDerivativeEquiv R P p hp F hF hΓ μ =
      BersWeighted.automorphicIntegralOperator hΓ μ.val := by
  simp only [harmonicDerivativeEquiv, ContinuousLinearEquiv.coeFn_ofBijective,
    harmonicDerivative_apply]

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
